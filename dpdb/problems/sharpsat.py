# -*- coding: future_fstrings -*-
import logging
from collections import defaultdict

from dpdb.reader import CnfReader
from dpdb.problem import *
from dpdb.treedecomp import Node
from .sat_util import *
from psycopg2 import sql

logger = logging.getLogger(__name__)

class SharpSat(Problem):

    def __init__(self, name, pool, store_formula=False, **kwargs):
        super().__init__(name, pool, **kwargs)
        self.store_formula = store_formula

    def td_node_column_def(self,var):
        return td_node_column_def(var)

    def td_node_extra_columns(self):
        return [("model_count","NUMERIC")]

    def candidate_extra_cols(self,node):
        return ["{} AS model_count".format(
                " * ".join(set([var2cnt(node,v) for v in node.vertices] +
                               [node2cnt(n) for n in node.children])) if node.vertices or node.children else "1"
                )]

    def bag_formula_id(self, node):
        return node.id

    def subtree_formula_id(self, node):
        return node.id + self.td.num_bags + 1

    def assignment_extra_cols(self,node, do_projection=True):
        if do_projection:
            return ["sum(model_count) AS model_count"]
        else:
            return []

    def print_proof_line(self, l_type, l_id, l_count, l_data):
        l = [l_type, l_id, l_count, *l_data, 0]
        print(" ".join(map(str, l)))

    def print_component_def(self, id, node, recursive=False):
        clauses = set()
        nodes = node.children_recursive if recursive else [node]
        vertices = []
        for n in nodes:
            vertices.extend(n.vertices)

        vertice_set = set(vertices)
        for v in vertices:
            for d in self.var_clause_dict[v]:
                for key, val in d.items():
                    if key.issubset(vertice_set):
                        clauses.add(self.clause_index_dict[val])

        print("c", ["bag", "subtree"][int(recursive)], "formula for", node.id)
        self.print_proof_line("cd", id, 0, clauses)

    def filter(self,node):
        #print (self.var_clause_dict, node.id)
        return filter(self.var_clause_dict, node)

    def print_define_clauses(self):

        # define clauses
        for id, c in enumerate(self.clauses):
            id += 1
            self.print_proof_line("f", id, 0, c)
            self.clause_index_dict[frozenset(c)] = id


    def prepare_input(self, fname):
        input = CnfReader.from_file(fname)
        self.num_vars = input.num_vars
        self.num_clauses = input.num_clauses
        self.clauses = input.clauses
        self.var_clause_dict = defaultdict(set)
        self.clause_index_dict = defaultdict(set)

        self.print_define_clauses()
        return cnf2primal(input.num_vars, input.clauses, self.var_clause_dict)

    def setup_extra(self):
        def create_tables():
            self.db.ignore_next_praefix()
            self.db.create_table("problem_sharpsat", [
                ("id", "INTEGER NOT NULL PRIMARY KEY REFERENCES PROBLEM(id)"),
                ("num_vars", "INTEGER NOT NULL"),
                ("num_clauses", "INTEGER NOT NULL"),
                ("model_count", "NUMERIC")
            ])

        def insert_data():
            self.db.ignore_next_praefix()
            self.db.insert("problem_sharpsat",("id","num_vars","num_clauses"),
                (self.id, self.num_vars, self.num_clauses))
            if "faster" not in self.kwargs or not self.kwargs["faster"]:
                self.db.ignore_next_praefix()
                self.db.insert("problem_option",("id", "name", "value"),(self.id,"store_formula",self.store_formula))
                if self.store_formula:
                    store_clause_table(self.db, self.clauses)

        create_tables()
        insert_data()

    def print_model_claims(self):
        for node in self.td.nodes:
            val_names = {True: "t", False: "f"}

            num_children = len(node.children)

            self.print_component_def(self.bag_formula_id(node), node)
            self.print_component_def(self.subtree_formula_id(node), node, recursive=True)

            # IF / leaf
            if num_children <= 1:
                claim_id = self.bag_formula_id(node)
                if num_children == 1:
                    print ("c", "I/F node")
                elif num_children == 0:
                    print ("c", "Leaf Node")

                pseudo_leaf = Node(node.id, node.vertices)
                pseudo_leaf.parent = node.parent

                q = "{} {}".format(self.assignment_select(pseudo_leaf, do_projection=False), self.filter(node))
                q = self.db.replace_dynamic_tabs(q)

                print ("c", q)
                for model in self.db.exec_and_fetchall(sql.SQL(q)):
                    self.print_proof_line("m", claim_id, 0, [v if model[node.vertices.index(v)] else -v for v in node.vertices])

                # we need a projection claim as well
                if set(node.vertices) != set(node.stored_vertices):
                    partial_assignment = node.stored_vertices
                    for model in self.db.select(node2tab(node), ["model_count"] + [var2col(v) for v in partial_assignment], fetchall=True):
                        formula_id = self.subtree_formula_id(node)
                        lm = list(model)
                        self.print_proof_line("p", formula_id, lm[0], [var if v else -var for v, var in zip(lm[1:], node.stored_vertices)])

            # Join Node
            elif num_children > 1:
                print ("c", "join of", num_children)
                print ("c", "join projection", node.id, node.vertices, node.stored_vertices)
                partial_assignment = node.stored_vertices
                for model in self.db.select(node2tab(node), ["model_count"] + [var2col(v) for v in partial_assignment], fetchall=True):
                    formula_id = self.subtree_formula_id(node)
                    lm = list(model)
                    self.print_proof_line("j", formula_id, lm[0], [var if v else -var for v, var in zip(lm[1:], node.stored_vertices)])

    def after_solve(self):
        self.print_model_claims()
        root_tab = f"td_node_{self.td.root.id}"
        sum_count = self.db.replace_dynamic_tabs(f"(select coalesce(sum(model_count),0) from {root_tab})")
        self.db.ignore_next_praefix()
        model_count = self.db.update("problem_sharpsat",["model_count"],[sum_count],[f"ID = {self.id}"],"model_count")[0]
        logger.info("Problem has %d models", model_count)

def var2cnt(node,var):
    if node.needs_introduce(var):
        return "1"
    else:
        return "{}.model_count".format(var2tab_alias(node,var))

def node2cnt(node):
    return "{}.model_count".format(node2tab_alias(node))

args.specific[SharpSat] = dict(
    help="Solve #SAT instances (count number of models)",
    aliases=["#sat"],
    options={
        "--store-formula": dict(
            dest="store_formula",
            help="Store formula in database",
            action="store_true",
        )
    }
)

