#env python3

import sys
import subprocess
from collections import defaultdict
from itertools import product

# contains clauses as lists of literals
clauses_dict = {}
# contains components as sets of variables
component_variables = {}
# contains a list of models (list of clauses) for each component id
component_models = defaultdict(set)
# list of local ("model") variables by component id
component_local_variables = {}
# list of local ("model") clauses by component id
component_local_clauses = {}
# clauses by covered by component
component_clauses = {}
# list of join claims by component
component_joins  = defaultdict(set)
# list of composition components
component_compositions  = defaultdict(set)
# list of child components for each component
component_children  = defaultdict(set)

# lookup for which variables occur in which clauses
variable_clauses = defaultdict(set)

def parse_proof(input_file):
    for line in input_file.readlines():
        if not line.strip():
            continue

        split = line.strip().split(" ")
        if split[0] == "c":
            continue

        l_type, l_id, l_count, l_rest = split[0], int(split[1]), int(split[2]), list(map(int, split[3:]))

        # has end marker
        assert l_rest[-1] == 0
        l_data = l_rest[:-1]

        if l_type == "f":
            clauses_dict[l_id] = frozenset(l_data)
            for l in l_data:
                variable_clauses[abs(l)].add(frozenset(l_data))

        elif l_type == "cv":
            component_variables[l_id] = frozenset(l_data)

        elif l_type == "lv":
            component_local_variables[l_id] = frozenset(l_data)

        elif l_type == "cd":
            component_clauses[l_id] = frozenset([clauses_dict[c] for c in l_data])

        elif l_type == "ld":
            component_local_clauses[l_id] = frozenset([clauses_dict[c] for c in l_data])

        elif l_type == "m":
            component_models[l_id].add(frozenset(l_data))

        elif l_type == "j":
            component_joins[l_id].add((l_count, frozenset(l_data)))

        elif l_type == "a":
            component_compositions[l_id].add((l_count, frozenset(l_data)))

        elif l_type == "cc":
            component_children[l_data[0]].add(l_id)

        else:
            print ("unknown line type:", l_type)
            sys.exit(1)

    # insert empty projection component
    component_clauses[-1] = frozenset()
    component_variables[-1] = frozenset()
    component_models[-1] = {frozenset()}
    component_local_clauses[-1] = frozenset()
    component_local_variables[-1] = frozenset()

def check_model(component_id, model):
    model_set = set(model)
    if not set([abs(l) for l in model]) == component_local_variables[component_id]:
        return False
    for clause in component_local_clauses[component_id]:
        if not model_set & set(clause):
            return False
    return True

def map_lit(variable_mapping, l):
    var = variable_mapping[abs(l)]
    return var if l > 0 else -var

# map clause variables and project
def map_clause(variable_mapping, clause):
    return [map_lit(variable_mapping, l) for l in clause if abs(l) in variable_mapping]


def component_unsatisfiable(component, additional_clauses):
    clauses = set(component_clauses[component])
    clauses |= additional_clauses

    # set of all original variable names
    variables = component_local_variables[component]
    variable_mapping = { v : i + 1 for i, v in enumerate(variables)}

    problem_string = " ".join(map(str, ["p", "cnf", len(variables), len(clauses)])) + "\n"
    for clause in clauses:
        problem_string += " ".join(map(str, map_clause(variable_mapping, clause) + [0])) + "\n"

    result = subprocess.run(["minisat", "-verb=0", "-strict", "/dev/stdin", "/dev/stdout"], input=problem_string, capture_output=True, encoding="utf-8")
    last_line = result.stdout.strip().split("\n")[-1].strip()
    if not last_line == "UNSATISFIABLE":
        print ("model claim", component, "failed:", last_line, file=sys.stderr)
        print (problem_string)
        print ("mapping:", variable_mapping)
        print (result.stdout)
        return False
    return True

def check_projection_model_completeness(component_id, projection_assignment):

    clauses = set()
    # add projection assignment
    for l in projection_assignment:
        clauses.add(frozenset([l]))

    # add negated models -> -(a ^ b) => (-a or -b)
    for model in component_models[component]:
        if projection_assignment <= model:
            clauses.add(frozenset([-l for l in model]))

    return component_unsatisfiable(component_id, clauses)


# checks correctness of component models.
# new: does not check completeness, this is checked in projection
def check_model_correctness(component_id):
    # local variables and clauses must be subsets of subtree equivalents
    if not component_local_variables[component_id] <= component_variables[component_id] \
         or not component_local_clauses[component_id] <= component_clauses[component_id]:
            print ("local variables / clauses not in subtree sets!");
            sys.exit(1)

    for model in component_models[component]:
        # check if this is actually a model
        if not check_model(component, model):
            print ("model claim", component, "failed:", model, "is no model!")
            print ("applicable clauses:", component_clauses[component])
            sys.exit(1)

    # all models of a component must use the same variables:
    if len(set([frozenset([abs(l) for l in m]) for m in component_models[component_id]])) > 1:
        print ("differing model variables in", component, "!")
        sys.exit(1)

def flatten(l):
    return [val for sublist in l for val in sublist]


def clause_index_list(clauses):
    cl = []
    for key, val in clauses_dict.items():
        if val in clauses:
            cl.append(key)
    assert len(cl) == len(clauses)
    return cl

def combine_projections(projections):
    # fixme: only supports unit clauses
    reduced = True
    projections = [p for p in projections if p != set()]
    new = set()
    while reduced:
        new = set()
        reduced = False
        for c in projections:
            # cannot handle this right now
            if len(c) != 1:
                return False

            if {-list(c)[0]} in projections:
                reduced = True
                continue
            else:
                new.add(c)
        projections = new
    if not new:
        return set({frozenset({})})
    return new


def get_projection_or_join(component_id):
    return component_joins.get(component_id, component_compositions.get(component_id))

def all_projections():
    result = defaultdict(set)
    for c, p in component_joins.items():
        result[c] |= p
    for c, p in component_compositions.items():
        result[c] |= p
    return result

# enforce ordering on components (projections) to avoid cyclic proofs
# thus, children must have either fewer variables or equal vars and a longer projection
def is_subprojection_of(p1, c1, p2, c2):
    c1v = component_variables[c1]
    c2v = component_variables[c2]
    p1v = {abs(l) for l in p1}
    p2v = {abs(l) for l in p2}
    c1lv = component_local_variables[c1]
    c2lv = component_local_variables[c2]

    # cannot re-introduce projected-away vars in parent or child
    if (c1v - p1v) & (p2v | c2lv) != set():
        return False

    if c1v < c2v:
        return True

    if c1v != c2v:
        return False

    if p2 < p1:
        return True

    if p2 != p1:
        return False

    if c2lv < c1lv:
        return True

    return False

# can these components, projections be safely joined?
def join_compatible(c1, p1, c2, p2):
    c1v = component_variables[c1]
    c2v = component_variables[c2]
    p1v = {abs(l) for l in p1}
    p2v = {abs(l) for l in p2}
    return (c1v - p1v) & c2v == set() and (c2v - p2v) & c1v == set();

def subprojections_complete_wrt(component_id, projection):
    #this is a leaf projection
    if component_id == -1:
        return True

    projection_clauses = set()
    # add negated projections -> -(a ^ b) => (-a or -b)
    for (_, p) in all_projections()[component_id]:
        projection_clauses.add(frozenset([-l for l in p]))

    for l in projection:
        if l in component_variables[component_id]:
            projection_clauses.add(frozenset([l]))

    complete = component_unsatisfiable(component_id, projection_clauses)

    print (component_id, projection, complete)
    if not complete:
        print ("subprojections incomplete: ", component_id, projection)
        return False
    return complete

def check_join_claim(component_id):

    for c_join, p_join in component_joins[component_id]:

        subcomponents = component_children[component_id]

        # FIXME: ensure join compatibility among subcomponents

        # subcomponents combine to parent
        if not {v for c in subcomponents for v in component_variables[c]} | component_local_variables[component_id] == component_variables[component_id]:
            print ("incomplete children for", component_id);
            return False

        if not {d for c in subcomponents for d in component_clauses[c]} | component_local_clauses[component_id] == component_clauses[component_id]:
            print ("incomplete children for", component_id);
            return False

        # check underlying model claim completeness
        if not check_projection_model_completeness(component_id, p_join):
            print ("model claims for component", component_id, "incomplete for projection", p_join, "!")
            return False

        join_table = [(1, m) for m in component_models[component_id] if assignment_compatible(m, p_join)]
        used_projections = []
        for comp_id in subcomponents:
            new_table = []
            for c, a in join_table:
                comp_projections = all_projections()[comp_id]
                projection_assignments = [p[1] for p in comp_projections]

                applicable_projections = []
                for (c_sub, a_sub) in comp_projections:
                    if not is_subprojection_of(a_sub, comp_id, p_join, component_id):
                        continue

                    if any([not join_compatible(comp_id, a_sub, p[0], p[1]) for p in used_projections if p[0] != comp_id]):
                        print ("info: for", component_id, set(p_join),":", comp_id, set(a_sub), "has join incompatible projection!")
                        continue

                    # remove projections of which more general versions exist
                    more_general = [p for p in comp_projections if p[1] < a_sub and assignment_compatible(a_sub, a)]
                    if assignment_compatible(a_sub, a) and not more_general:
                        applicable_projections.append((c_sub, a_sub))

                for (c_sub, a_sub) in applicable_projections:
                    if assignment_compatible(a_sub, a):
                        new_table.append((c_sub * c, a | a_sub))
                        used_projections.append((comp_id, a_sub))

            join_table = new_table

        c_join_check = 0
        for c, a in join_table:
            c_join_check += c

        if c_join_check != c_join:
            print ("check for join", component_id, subcomponents, "failed for", set(p_join), ": is" , c_join_check, "but should be", c_join)
            return False

    return True

def assignment_compatible(a1, a2):
    return not any([-l in a2 for l in a1])

def check_composition_claim(component_id, projection, count):

    clauses = component_clauses[component_id]
    variables = component_variables[component_id]

    applicable_projections = []
    for origin_comp in component_children[component_id]:
        if component_variables[origin_comp] != variables:
            return False
        if component_clauses[origin_comp] != clauses:
            return False

        for c, origin_proj in get_projection_or_join(origin_comp):
            if not is_subprojection_of(origin_proj, origin_comp, projection, component_id):
                continue

            if origin_proj > projection:
                # projections must not overlap!
                # currently, we only accept unit clauses
                assert len(origin_proj) == 1
                applicable_projections.append((c, origin_proj))

    # currently, we only use unit literals so this should work
    assert combine_projections([p[1] for p in applicable_projections]) == {projection}

    # the same projection may be constructed in multiple ways
    applicable_projections = set(applicable_projections)

    combined_count = 0;
    for c, origin_proj in applicable_projections:
        combined_count += c

    if count != combined_count:
        print ("composition claim for", component_id, projection, "could not be verified: expected", count, "got", combined_count);
        return False
    return True

def get_root_claim():
    all_vars = set()
    all_clauses = set()
    for c, v in component_variables.items():
        all_vars |= v
        all_clauses |= component_clauses[c]

    for c in component_variables:
        if component_variables[c] == all_vars and component_clauses[c] == all_clauses:
            for p in all_projections()[c]:
                # project away all variables
                if p[1] == set():
                    return (c, p[0])
    print ("no root claim found!")
    sys.exit(1)

if __name__ == "__main__":
    print ("parsing...", file=sys.stderr)
    parse_proof(sys.stdin)
    print (len(clauses_dict), "clauses.", file=sys.stderr)
    print (len(component_variables), "components.", file=sys.stderr)
    print (len(component_models), "model claims.", file=sys.stderr)
    print (len(component_joins), "component join claims.", file=sys.stderr)
    print (len(component_compositions), "component composition claims.", file=sys.stderr)

    for component in component_models.keys():
        check_model_correctness(component)

    print ("model claim correctness verified.", file=sys.stderr)

    for component, l in component_compositions.items():
        for (count, projection) in l:
            if not check_composition_claim(component, projection, count):
                print ("composition claim", component, set(projection), "failed!")
                sys.exit(1)

    print ("composition claims verified.", file=sys.stderr);

    for component, l in component_joins.items():
        checked = check_join_claim(component)
        if not checked:
            print ("join claim", component, "failed!")
            sys.exit(1)
        print ("join claim for", component, "verified.")


    print ("join claims verified.", file=sys.stderr);

    r_comp, r_count = get_root_claim()
    print ("model count", r_count, "of root component", r_comp, "verified!")
