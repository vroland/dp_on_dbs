# -*- coding: future_fstrings -*-
import logging
import sys
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
        self.pseudo_nodes = 0

    def td_node_column_def(self,var):
        return td_node_column_def(var)

    def td_node_extra_columns(self):
        return [("model_count","NUMERIC")]

    def candidate_extra_cols(self,node):
        return ["{} AS model_count".format(
                " * ".join(set([var2cnt(node,v) for v in node.vertices] +
                               [node2cnt(n) for n in node.children])) if node.vertices or node.children else "1"
                )]

    def subtree_formula_id(self, node):
        return node.id

    def issue_pseudo_id(self):
        self.pseudo_nodes += 1
        return self.td.num_bags + self.pseudo_nodes

    def assignment_extra_cols(self,node, do_projection=True):
        if do_projection:
            return ["sum(model_count) AS model_count"]
        else:
            return []

    def print_proof_line(self, l_type, l_id, l_count, l_data):
        l = [l_type, l_id, l_count, *l_data, 0]
        print(" ".join(map(str, l)))

    def print_component_def(self, id, node):
        recursive_vertices = []
        for n in node.children_recursive:
            recursive_vertices.extend(n.vertices)

        recursive_vertice_set = set(recursive_vertices)
        local_vertice_set = set(node.vertices)

        recursive_clauses = covering_clauses(recursive_vertice_set, self.var_clause_dict)
        recursive_clause_idx = [self.clause_index_dict[c] for c in recursive_clauses]
        local_clauses = covering_clauses(local_vertice_set, self.var_clause_dict)
        local_clause_idx = [self.clause_index_dict[c] for c in local_clauses]

        print("\nc", "bag", "formula for", node.id)
        self.print_proof_line("cv", id, 0, sorted(recursive_vertice_set))
        self.print_proof_line("cd", id, 0, sorted(recursive_clause_idx))
        self.print_proof_line("lv", id, 0, sorted(local_vertice_set))
        self.print_proof_line("ld", id, 0, sorted(local_clause_idx))

    def print_local_dummy_component(self, id, node):
        local_vertice_set = set(node.vertices)

        local_clauses = covering_clauses(local_vertice_set, self.var_clause_dict)
        local_clause_idx = [self.clause_index_dict[c] for c in local_clauses]

        self.print_proof_line("cv", id, 0, sorted(local_vertice_set))
        self.print_proof_line("cd", id, 0, sorted(local_clause_idx))
        self.print_proof_line("lv", id, 0, sorted(local_vertice_set))
        self.print_proof_line("ld", id, 0, sorted(local_clause_idx))

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

    def model_claim_query_of(self, node):
        pseudo_leaf = Node(node.id, node.vertices)
        pseudo_leaf.parent = node.parent

        q = "{} {}".format(self.assignment_select(pseudo_leaf, do_projection=False), self.filter(node))
        return self.db.replace_dynamic_tabs(q)

    def print_model_claim_of(self, node):
        claim_id = self.subtree_formula_id(node)
        q = self.model_claim_query_of(node)

        for model in self.db.exec_and_fetchall(sql.SQL(q)):
            self.print_proof_line("m", claim_id, 0, [v if model[node.vertices.index(v)] else -v for v in node.vertices])

    def print_projection_claim_of(self, node, formula_id):
        partial_assignment = node.stored_vertices
        for model in self.db.select(node2tab(node), ["model_count"] + [var2col(v) for v in partial_assignment], fetchall=True):
            lm = list(model)
            self.print_proof_line("p", formula_id, lm[0], [var if v else -var for v, var in zip(lm[1:], node.stored_vertices)])

    def print_model_claims(self):
        for node in self.td.nodes:
            val_names = {True: "t", False: "f"}

            num_children = len(node.children)

            self.print_component_def(self.subtree_formula_id(node), node)
            #self.print_component_def(self.subtree_formula_id(node), node, recursive=True)

            # IF / leaf
            if num_children <= 1:
                if num_children == 1:
                    print ("c", "I/F node", node.id, "is parent of", node.children[0].id)
                elif num_children == 0:
                    print ("c", "Leaf Node")

                self.print_model_claim_of(node)

                # we need a projection claim as well
                if set(node.vertices) != set(node.stored_vertices):
                    self.print_projection_claim_of(node, self.subtree_formula_id(node))

            # Join Node
            elif num_children > 1:
                child_vars = []
                for child in node.children:
                    child_vars.extend(child.vertices)

                child_clauses = []
                for child in node.children:
                    child_clauses.extend(covering_clauses(set(child.vertices), self.var_clause_dict))
                missing_clauses = covering_clauses(set(node.vertices), self.var_clause_dict) - set(child_clauses)

                introduce_vars = set(node.vertices) - set(child_vars)

                self.print_model_claim_of(node)

                # node has additional introduce vars or clauses
                if introduce_vars or missing_clauses:

                    # pseudo node must not be projected,
                    # otherwise we could wrongly include
                    # solutions of other children
                    q = self.model_claim_query_of(node)

                    dummy_id = self.issue_pseudo_id()
                    print ("c", "dummy component for introduce vars of", self.subtree_formula_id(node))
                    self.print_local_dummy_component(dummy_id, node)

                    for model in self.db.exec_and_fetchall(sql.SQL(q)):
                        l = list(model)
                        models = [var if v else -var for v, var in zip(l, node.vertices) if v is not None]
                        self.print_proof_line("m", dummy_id, 0, models)
                        self.print_proof_line("p", dummy_id, 1, models)

                print ("c", node.id, "join of", [self.subtree_formula_id(n) for n in node.children])
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

