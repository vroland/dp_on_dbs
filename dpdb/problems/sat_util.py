# -*- coding: future_fstrings -*-
from dpdb.problem import *
from collections import defaultdict

class hashabledict(dict):
    def __hash__(self):
        return hash(frozenset(self))

def cnf2primal (num_vars, clauses, var_clause_dict = defaultdict(set)):
    edges = set([])
    for clause in clauses:
        atoms = [abs(lit) for lit in clause]
        clause_set = hashabledict({frozenset(atoms): frozenset(clause)})
        for i in atoms:
            var_clause_dict[i].add(clause_set)
            for j in atoms:
                if i < j:
                    edges.add((i,j))
    return (num_vars, edges)

def td_node_column_def(var):
    return (var2col(var), "BOOLEAN")

def lit2var (lit):
    return var2col(abs(lit))

def lit2val (lit):
    return str(lit > 0)

def lit2expr (lit):
    if lit > 0:
        return var2col(lit)
    else:
        return "NOT {}".format(lit2var(lit))

def covering_clauses(vertice_set, var_clause_dict):
    cur_cl = set()
    for v in vertice_set:
        candidates = var_clause_dict[v]
        for d in candidates:
            for key, val in d.items():
                if key.issubset(vertice_set):
                    cur_cl.add(val)
    return cur_cl

def filter(var_clause_dict, node):
    cur_cl = covering_clauses(set(node.vertices), var_clause_dict)

    if len(cur_cl) > 0:
        return "WHERE {0}".format(
            "({0})".format(") AND (".join(
                [" OR ".join(map(lit2expr,clause)) for clause in cur_cl]
            )))
    else:
        return ""

def store_clause_table(db, clauses):
    db.drop_table("sat_clause")
    num_vars = len(clauses)
    db.create_table("sat_clause", map(td_node_column_def,range(1,num_vars+1)))
    for clause in clauses:
        db.insert("sat_clause",list(map(lit2var,clause)),list(map(lit2val,clause)))
