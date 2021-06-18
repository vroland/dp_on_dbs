import sys
import subprocess
from collections import defaultdict

# contains clauses as lists of literals
clauses_dict = {}
# contains components as sets of variables
component_variables = {}
# contains a list of models (list of clauses) for each component id
component_models = defaultdict(list)
# list of projection claims per component id
component_projections = defaultdict(list)
# clauses by covered by component
component_clauses = {}

def parse_proof(input_file):
    global component_clauses

    for line in input_file.readlines():
        split = line.strip().split(" ")
        if split[0] == "c":
            continue

        l_type, l_id, l_count, l_rest = split[0], int(split[1]), int(split[2]), list(map(int, split[3:]))

        # has end marker
        assert l_rest[-1] == 0
        l_data = l_rest[:-1]

        if l_type == "f":
            clauses_dict[l_id] = frozenset(l_data)

        elif l_type == "cv":
            component_variables[l_id] = set(l_data)

        elif l_type == "m":
            component_models[l_id].append(frozenset(l_data))

        elif l_type == "p":
            component_projections[l_id].append((l_count, l_data))

    def get_component_clauses(component_id):
        variables = component_variables[component_id]
        clauses = filter(lambda clause: set([abs(l) for l in clause]) <= variables, clauses_dict.values())
        return set(clauses)

    component_clauses = { c_id : get_component_clauses(c_id) for c_id in component_variables.keys() }

def check_model(component_id, model):
    model_set = set(model)
    for clause in component_clauses[component_id]:
        if not model_set & set(clause):
            return False
    return True

def map_lit(variable_mapping, l):
    var = variable_mapping[abs(l)]
    return var if l > 0 else -var

def check_model_claims(component_id):
    clauses = component_clauses[component]

    # add negated models -> -(a ^ b) => (-a or -b)
    for model in component_models[component]:
        # check if this is actually a model
        if not check_model(component, model):
            print ("model claim", component, "failed:", model, "is no model.")
            sys.exit(1)

        clauses.add(frozenset([-l for l in model]))


    # set of all original variable names
    variables = component_variables[component]
    variable_mapping = { v : i + 1 for i, v in enumerate(variables)}

    problem_string = " ".join(map(str, ["p", "cnf", len(variables), len(clauses)])) + "\n"
    for clause in clauses:
        problem_string += " ".join(map(str, [map_lit(variable_mapping, l) for l in clause] + [0])) + "\n"

    result = subprocess.run(["minisat", "-verb=0", "-strict"], input=problem_string, capture_output=True, encoding="utf-8")
    last_line = result.stdout.strip().split("\n")[-1].strip()
    if not last_line == "UNSATISFIABLE":
        print ("model claim", component, "failed:", last_line, file=sys.stderr)
        print (problem_string)
        sys.exit(2)

def largest_subclaim_cover(component_id):
    covered_clauses = component_clauses[component_id]

    # find sub-projection
    best_subprojection = 0
    best_subprojection_clauses = set()
    for c_id, c_vars in component_variables.items():
        if c_id == component_id:
            continue

        comp_clauses = component_clauses[c_id]
        common = comp_clauses & covered_clauses
        if comp_clauses <= covered_clauses and len(common) > len(best_subprojection_clauses):
            best_subprojection = c_id
            best_subprojection_clauses = common

    if not best_subprojection:
        print ("leaf projection?", component_id)
    else:
        print ("best subprojection:", component_id, "->", best_subprojection, "remaining clauses:", covered_clauses - best_subprojection_clauses)

def check_projection_claim(component_id, count, partial_assignment):
    largest_subclaim_cover(component_id)

if __name__ == "__main__":
    parse_proof(sys.stdin)
    print (len(clauses_dict), "clauses.", file=sys.stderr)
    print (len(component_variables), "components.", file=sys.stderr)
    print (len(component_models), "model claims.", file=sys.stderr)

    for component in component_models.keys():
        check_model_claims(component)

    print ("model claims verified (according to minisat).", file=sys.stderr)

    for component, l in component_projections.items():
        for (c, a) in l:
            check_projection_claim(component, c, a)
            break
