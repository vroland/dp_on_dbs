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
# list of join claims by component
component_joins  = defaultdict(list)

def parse_proof(input_file):
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
            component_variables[l_id] = frozenset(l_data)

        elif l_type == "cd":
            component_clauses[l_id] = frozenset([clauses_dict[c] for c in l_data])

        elif l_type == "m":
            component_models[l_id].append(frozenset(l_data))

        elif l_type == "p":
            component_projections[l_id].append((l_count, frozenset(l_data)))

        elif l_type == "j":
            component_joins[l_id].append((l_count, frozenset(l_data)))

    # insert empty projection component
    component_clauses[-1] = frozenset()
    component_projections[-1] = [(1, frozenset())]
    component_variables[-1] = frozenset()

    #component_clauses = { c_id : get_component_clauses(c_id) for c_id in component_variables.keys() }

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
    clauses = set(component_clauses[component])

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

def largest_subprojection(component_id, pool=None, covered_clauses=None, covered_vars=None):
    if pool is None:
        pool=(set(component_projections.keys()) | set(component_joins.keys()))

    # clauses and variables used for fitness measure
    if covered_clauses is None:
        covered_clauses = component_clauses[component_id]
    if covered_vars is None:
        covered_vars = component_variables[component_id]

    # find sub-projection
    best_subprojection = -1
    # tuple of (matching clauses, matching variables)
    best_subprojection_value = (-1, -1)
    for c_id in pool:
        if c_id == component_id:
            continue

        comp_vars = component_variables[c_id]
        comp_clauses = component_clauses[c_id]
        common = comp_clauses & covered_clauses
        comp_value = (len(common), len(covered_vars & comp_vars))
        if comp_clauses <= component_clauses[component_id] and comp_vars <= component_variables[component_id] and comp_value > best_subprojection_value:

            best_subprojection = c_id
            best_subprojection_value = comp_value

    return best_subprojection

def clause_index_list(clauses):
    cl = list(clauses_dict.values())
    return [cl.index(c) + 1 for c in clauses]

# this is actually the set cover problem, we're using a greedy algorithm here
def find_covering_components(component_id):
    pool=(set(component_projections.keys()) | set(component_joins.keys()))
    children = []

    comp_vars = component_variables[component_id]
    comp_clauses = component_clauses[component_id]
    child_vars = set()
    child_clauses = set()
    while pool and (child_clauses != comp_clauses or child_vars != comp_vars):
        clauses_left = comp_clauses - child_clauses
        vars_left = comp_vars - child_vars
        largest = largest_subprojection(component_id, pool, clauses_left, vars_left)
        #print ("it", component_id, largest, children, clause_index_list(clauses_left), vars_left)
        # the trivial component is returned
        if largest == -1:
            assert clauses_left or vars_left
            print ("cannot verify", component_id, ": clauses", clause_index_list(clauses_left), "and vars", vars_left, "not covered.")
            return None

        children.append(largest)
        pool.remove(largest)
        child_vars |= component_variables[largest]
        child_clauses |= component_clauses[largest]

    print ("children for", component_id, children)


def check_join_claim(component_id):
    find_covering_components(component_id)
    return True

def assignment_compatible(a1, a2):
    return len(a1 | a2) == len(set([abs(l) for l in a1]) | set([abs(l) for l in a2]))

def check_projection(comp_proj, comp_source, comp_bridge):
    source_assignments = component_projections[comp_source] if comp_source in component_projections else component_joins[comp_source]

    source_vars = component_variables[comp_source]

    counted_models = set()
    for c_proj, a_proj in component_projections[comp_proj]:
        c_proj_check = 0
        for bridge_assignment in component_models[comp_bridge]:
            # the projected assignment must be a restriction of the bridge_assignment
            if not a_proj <= bridge_assignment:
                continue

            # bridge assignment restricted to source component variables
            restricted_bridge_assignment = set([l for l in bridge_assignment if abs(l) in source_vars])

            for c_source, a_source in source_assignments:
                # this assignment fits to the restricted bridge assignment
                if restricted_bridge_assignment <= a_source:
                    c_proj_check += c_source
                    counted_models.add(bridge_assignment)

        if c_proj_check != c_proj:
            print ("check for", comp_proj, comp_source, "failed:", *a_proj, ":", c_proj_check, "<->", c_proj)
            return False

    # there are models left that where not projected
    for model in set(component_models[comp_bridge]) - counted_models:
        for _, a_source in source_assignments:
            if assignment_compatible(model, a_source):
                print ("incomplete projection", comp_proj, "model", model, "not covered.")
                return False

    return True

def check_projection_claim(component_id):
    # the trivial projection is valid
    if component_id == -1:
        return True

    predecessor = largest_subprojection(component_id)
    assert predecessor != 0

    comp_vars = component_variables[component_id]
    pred_vars = component_variables[predecessor]


    # we must find a model claim that add the valid
    # assignments for the missing clauses
    clauses_needed = component_clauses[component_id] - component_clauses[predecessor]

    assert predecessor in component_projections or predecessor in component_joins
    assert comp_vars > pred_vars

    introduce_vars = comp_vars - pred_vars

    bridge_component = 0
    for key, value in component_clauses.items():
        candidate_vars = component_variables[key]
        # the current component adds additional clauses
        if clauses_needed and value == clauses_needed and candidate_vars <= comp_vars:
            bridge_component = key
            break
        # no clauses added
        elif not clauses_needed and candidate_vars == introduce_vars:
            bridge_component = key
            break
    else:
        print ("no bridge component found for", component_id, predecessor)
        return False

    return check_projection(component_id, predecessor, bridge_component)


if __name__ == "__main__":
    parse_proof(sys.stdin)
    print (len(clauses_dict), "clauses.", file=sys.stderr)
    print (len(component_variables), "components.", file=sys.stderr)
    print (len(component_models), "model claims.", file=sys.stderr)
    print (len(component_projections), "component projection claims.", file=sys.stderr)
    print (len(component_joins), "component join claims.", file=sys.stderr)

    for component in component_models.keys():
        check_model_claims(component)

    print ("model claims verified (according to minisat).", file=sys.stderr)

    for component, l in component_projections.items():
        checked = check_projection_claim(component)
        if not checked:
            print ("projection claim", component, "failed!")
            sys.exit(1)

    print ("projection claims verified.")

    for component, l in component_joins.items():
        checked = check_join_claim(component)
        if not checked:
            print ("join claim", component, "failed!")
            sys.exit(1)
