# -*- coding: future_fstrings -*-
import logging
import sys
from collections import defaultdict
import subprocess

from dpdb.reader import CnfReader
from dpdb.problem import *
from dpdb.treedecomp import Node
from .sat_util import *
from psycopg2 import sql
from itertools import product

logger = logging.getLogger(__name__)

class SharpSat(Problem):

    def __init__(self, name, pool, store_formula=False, **kwargs):
        super().__init__(name, pool, **kwargs)
        self.store_formula = store_formula
        self.pseudo_nodes = 1

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
            return ["model_count AS model_count"]

    def print_proof_line(self, l_type, *data):
        l = [l_type, *data, 0]
        print(" ".join(map(str, l)))

    def vertices_recursive(self, node):
        recursive_vertices = []
        for n in node.children_recursive:
            recursive_vertices.extend(n.vertices)

        return recursive_vertices

    def print_component_def(self, id, node):

        recursive_vertices = self.vertices_recursive(node)

        recursive_vertice_set = set(recursive_vertices)
        local_vertice_set = set(node.vertices)

        recursive_clauses = covering_clauses(recursive_vertice_set, self.var_clause_dict)
        recursive_clause_idx = [self.clause_index_dict[c] for c in recursive_clauses]
        local_clauses = covering_clauses(local_vertice_set, self.var_clause_dict)

        print("\nc", "bag", "formula for", node.id)
        self.print_proof_line("d", id, *sorted(recursive_vertice_set), 0, *sorted(recursive_clause_idx))
        for child in node.children:
            self.print_proof_line("jc", self.subtree_formula_id(child), id)

    def filter(self,node):
        #print (self.var_clause_dict, node.id)
        return filter(self.var_clause_dict, node)

    def print_define_clauses(self):

        self.print_proof_line("p", "st", self.num_vars, len(self.clauses))

        # define clauses
        for id, c in enumerate(self.clauses):
            id += 1
            self.print_proof_line("f", id, *c)
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
        q = "{} {}".format(self.assignment_select(node, do_projection=False), self.filter(node))
        return self.db.replace_dynamic_tabs(q)

    def model_list_of(self, node):
        q = self.model_claim_query_of(node)
        models = []
        for model in self.db.exec_and_fetchall(sql.SQL(q)):
            # last is model count column
            model = list(model)[:-1]
            models.append([v if model[node.vertices.index(v)] else -v for v in node.vertices])
        return models

    def print_leaf_claim_of(self, node):
        claim_id = self.subtree_formula_id(node)

        claims = []
        for model in self.model_list_of(node):
            self.print_proof_line("m", claim_id, 1, *model)
            claims.append(model)
        return claims

    def unsatisfiability_proof(self, node, claims):
        #variable_mapping = { v : i + 1 for i, v in enumerate(variables)}

        variables = self.vertices_recursive(node)
        clauses = covering_clauses(variables, self.var_clause_dict)
        problem_string = " ".join(map(str, ["p", "cnf", max(variables), len(clauses) + len(claims)])) + "\n"
        for clause in clauses:
            problem_string += " ".join(map(str, [l for l in clause if abs(l) in variables] + [0])) + "\n"

        for clause in claims:
            problem_string += " ".join(map(str, [-l for l in clause] + [0])) + "\n"

        result = subprocess.run(["./minisat", "-verb=0", "/dev/stdin", "/dev/stderr"], input=problem_string, capture_output=True, encoding="utf-8")
        last_line = result.stdout.strip().split("\n")[-1].strip()
        if not last_line == "UNSATISFIABLE":
            print ("proof failed:", node.id, file=sys.stderr)
            print (problem_string)
            print (result.stderr)
            assert False

        proof = []
        for l in result.stderr.strip().split("\n"):
            l = l.strip()
            if l[0] == "d" or l[-1] != "0":
                continue
            proof.append(list(map(int, l.split(" ")))[:-1])

        return proof

    def print_join_leaf(self, node):
        claim_id = self.subtree_formula_id(node)
        pseudo_id = self.issue_pseudo_id()
        pseudo_leaf = Node(node.id, node.vertices)
        pseudo_leaf.parent = node.parent
        print("c introduce join leaf id ", pseudo_id, "for", claim_id);

        clauses = covering_clauses(node.vertices, self.var_clause_dict)
        lc = [self.clause_index_dict[c] for c in clauses]
        self.print_proof_line("d", pseudo_id, *sorted(node.vertices), 0, *sorted(lc))
        self.print_proof_line("jc", pseudo_id, claim_id)

        for model in self.model_list_of(pseudo_leaf):
            self.print_proof_line("m", pseudo_id, 1, *model)

    def print_extension_claim_of(self, node):
        list_id = self.subtree_formula_id(node)
        child_id = self.subtree_formula_id(node.children[0])
        q = "{} {}".format(self.assignment_select(node, do_projection=False), self.filter(node))
        q = self.db.replace_dynamic_tabs(q)

        extended_models = []
        # fixme: inefficient
        for model in self.db.exec_and_fetchall(sql.SQL(q)):
            lm = list(model)
            int_mod = [var if v else -var for v, var in zip(lm[:-1], node.vertices)]
            self.print_proof_line("e", list_id, child_id, lm[-1], *int_mod)
            extended_models.append(int_mod)

        for model in self.model_list_of(node):
            if not model in extended_models:
                self.print_proof_line("e", list_id, child_id, 0, *model)

        return extended_models

    def print_projection_claim_of(self, node, formula_id):
        partial_assignment = node.stored_vertices

        self.print_proof_line("xf", formula_id, *node.vertices, 0, *[])

        projection_sum = 0
        for model in self.db.select(node2tab(node), ["model_count"] + [var2col(v) for v in partial_assignment], fetchall=True):
            lm = list(model)
            int_mod = [var if v else -var for v, var in zip(lm[1:], node.stored_vertices)]

            self.print_proof_line("a", formula_id, lm[0], *int_mod)
            projection_sum += lm[0]

        if node.stored_vertices:
            # make a composition claim containing the whole bag
            self.print_proof_line("a", formula_id, projection_sum, *[])

    def print_model_claims(self):
        for node in self.td.nodes:
            val_names = {True: "t", False: "f"}

            num_children = len(node.children)
            formula_id = self.subtree_formula_id(node)

            self.print_component_def(formula_id, node)
            #self.print_component_def(self.subtree_formula_id(node), node, recursive=True)

            # IF / leaf
            if num_children <= 1:
                claims = []
                if num_children == 1:
                    print ("c", "I/F node", node.id, "is parent of", node.children[0].id)
                    claims = self.print_extension_claim_of(node)
                elif num_children == 0:
                    print ("c", "Leaf Node")
                    claims = self.print_leaf_claim_of(node)

                proof = self.unsatisfiability_proof(node, claims)
                self.print_proof_line("xp", formula_id, formula_id)
                for step in proof:
                    self.print_proof_line("xs", formula_id, *step)

                # we need a projection claim as well
                if set(node.vertices) != set(node.stored_vertices):
                    self.print_projection_claim_of(node, formula_id)

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

                if missing_clauses or introduce_vars:
                    self.print_join_leaf(node)


                print ("c", node.id, "join of", [self.subtree_formula_id(n) for n in node.children])
                print ("c", "join projection", node.id, node.vertices, node.stored_vertices)

                # join claims
                nonzero = []
                q = "{} {}".format(self.assignment_select(node, do_projection=False), self.filter(node))
                q = self.db.replace_dynamic_tabs(q)
                for model in self.db.exec_and_fetchall(sql.SQL(q)):
                    lm = list(model)
                    int_mod = [var if v else -var for v, var in zip(lm[:-1], node.vertices)]
                    self.print_proof_line("j", formula_id, lm[-1], *int_mod)
                    nonzero.append(int_mod)

                proof = self.unsatisfiability_proof(node, nonzero)
                self.print_proof_line("xp", formula_id, formula_id)
                for step in proof:
                    self.print_proof_line("xs", formula_id, *step)

                # projection
                if node.stored_vertices != node.vertices:
                    for model in self.model_list_of(node):
                        if model not in nonzero:
                            self.print_proof_line("j", formula_id, 0, *model)

                    self.print_proof_line("xf", formula_id, *node.vertices, 0, *[])

                    partial_assignment = node.stored_vertices
                    projection_sum = 0
                    for model in self.db.select(node2tab(node), ["model_count"] + [var2col(v) for v in partial_assignment], fetchall=True):
                        formula_id = self.subtree_formula_id(node)
                        lm = list(model)
                        int_mod = [var if v else -var for v, var in zip(lm[1:], node.stored_vertices)]

                        self.print_proof_line("a", formula_id, lm[0], *int_mod)
                        projection_sum += lm[0]

                    # make a composition claim containing the whole bag
                    if node.stored_vertices:
                        self.print_proof_line("a", formula_id, projection_sum, *[])

    def after_solve(self):
        self.print_model_claims()
        root_tab = f"td_node_{self.td.root.id}"
        sum_count = self.db.replace_dynamic_tabs(f"(select coalesce(sum(model_count),0) from {root_tab})")
        self.db.ignore_next_praefix()
        model_count = self.db.update("problem_sharpsat",["model_count"],[sum_count],[f"ID = {self.id}"],"model_count")[0]
        print ("c root component: ", self.td.root.id)
        self.print_proof_line("xf", self.td.root.id, *self.td.root.vertices, 0, *[])
        self.print_proof_line("a", self.td.root.id, model_count, *[])
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

