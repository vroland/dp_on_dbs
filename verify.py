#env python3

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
# list of local ("model") variables by component id
component_local_variables = {}
# list of local ("model") clauses by component id
component_local_clauses = {}
# clauses by covered by component
component_clauses = {}
# list of join claims by component
component_joins  = defaultdict(list)
# list of composition components
component_compositions  = defaultdict(list)

# lookup for which variables occur in which clauses
variable_clauses = defaultdict(list)

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
                variable_clauses[abs(l)].append(frozenset(l_data))

        elif l_type == "cv":
            component_variables[l_id] = frozenset(l_data)

        elif l_type == "lv":
            component_local_variables[l_id] = frozenset(l_data)

        elif l_type == "cd":
            component_clauses[l_id] = frozenset([clauses_dict[c] for c in l_data])

        elif l_type == "ld":
            component_local_clauses[l_id] = frozenset([clauses_dict[c] for c in l_data])

        elif l_type == "m":
            component_models[l_id].append(frozenset(l_data))

        elif l_type == "p":
            component_projections[l_id].append((l_count, frozenset(l_data)))

        elif l_type == "j":
            component_joins[l_id].append((l_count, frozenset(l_data)))

        elif l_type == "a":
            component_compositions[l_id].append((l_count, frozenset(l_data)))

        else:
            print ("unknown line type:", l_type)
            sys.exit(1)

    # insert empty projection component
    component_clauses[-1] = frozenset()
    component_projections[-1] = [(1, frozenset())]
    component_variables[-1] = frozenset()
    component_local_clauses[-1] = frozenset()
    component_local_variables[-1] = frozenset()

    return

    duplicates = defaultdict(list)
    for comp in all_projections():
        duplicates[component_hash(comp)].append(comp)
    duplicates = {k : l for k, l in duplicates.items() if len(l) > 1}

    for l in duplicates.values():
        for comp in l[1:]:
            component_clauses.pop(comp, None)
            component_variables.pop(comp, None)
            component_local_variables.pop(comp, None)
            component_local_clauses.pop(comp, None)
            component_projections.pop(comp, None)
            component_joins.pop(comp, None)
            component_compositions.pop(comp, None)
            component_models.pop(comp, None)

        print ("deleting", *l[1:], "as duplicates of", l[0])

def component_hash(component_id):
    h = 0
    h ^= hash(component_variables[component_id])
    h ^= hash(component_clauses[component_id])
    if component_id in component_local_variables:
        h ^= hash(component_local_clauses[component_id])
        h ^= hash(component_local_variables[component_id])
    h ^= hash(frozenset(component_models.get(component_id, [])))
    l = get_projection_or_join(component_id)
    if l:
        h ^= hash(frozenset(l))
    return h

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


def check_projection_completeness(component_id, projection_assignment):
    clauses = set(component_local_clauses[component])

    # add negated models -> -(a ^ b) => (-a or -b)
    for model in component_models[component]:
        if projection_assignment <= model:
            clauses.add(frozenset([-l for l in model]))

    # add projection assignment
    for l in projection_assignment:
        clauses.add(frozenset([l]))

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
    if len(set([frozenset([abs(l) for l in m]) for m in component_models[component_id]])) != 1:
        print ("differing model variables in", component, "!")
        sys.exit(1)

def flatten(l):
    return [val for sublist in l for val in sublist]


# FIXME: overhaul this
def projection_vars_of(component_id):
    comp_projection_lits = set()
    if component_id in component_projections:
        comp_projection_lits = component_projections[component_id][0][1]
        # we assume all projections of this component use the same variables
        assert len(set([p[1] for p in component_projections[component_id]])) == 1
    elif component_id in component_joins:
        comp_projection_lits = component_joins[component_id][0][1]
        # we assume all projections of this component use the same variables
        assert len(set([p[1] for p in component_joins[component_id]])) == 1
    elif component_id in component_compositions:
        comp_projection_lits = component_compositions[component_id][0][1]
        # we assume all projections of this component use the same variables
        assert len(set([p[1] for p in component_compositions[component_id]])) == 1
    else:
        print (component_id, "is not a projection");
        sys.exit(1);

    return frozenset([abs(l) for l in comp_projection_lits])

def largest_subprojection(component_id, parent_projection, pool=None, covered_clauses=None, covered_vars=None):
    if pool is None:
        pool=(set(component_projections.keys()) | set(component_joins.keys()) | set(component_compositions.keys()))

    # clauses and variables used for fitness measure
    if covered_clauses is None:
        covered_clauses = component_clauses[component_id]
    if covered_vars is None:
        covered_vars = component_variables[component_id]

    # find sub-projection
    best_subprojection = -1
    # tuple of (matching clauses, matching variables)
    best_subprojection_value = (-1, -1)

    parent_model_vars = component_local_variables[component_id]
    parent_projection_vars = projection_vars_of(component_id)

    for c_id in pool:
        if c_id == component_id:
            continue

        comp_vars = component_variables[c_id]
        comp_clauses = component_clauses[c_id]
        common = comp_clauses & covered_clauses
        comp_value = (len(common), len(covered_vars & comp_vars))

        comp_projection_vars = projection_vars_of(c_id)
        projected_away = comp_vars - comp_projection_vars

        # cannot re-introduce projected away variables
        allowed = component_variables[component_id] & projected_away == set()

        # enforce ordering on components to avoid cyclic proofs
        # thus, children must have either fewer variables or equal vars and a longer projection
        in_variable_hierarchy = comp_vars < component_variables[component_id] or (comp_vars == component_variables[component_id] and comp_projection_vars > parent_projection_vars) or (comp_vars == component_variables[component_id] and component_local_variables[component_id] < component_local_variables.get(c_id, set()))

        has_suitable_projection = any([assignment_compatible(parent_projection, p[1]) for p in get_projection_or_join(c_id)])

        if comp_clauses <= component_clauses[component_id] \
            and in_variable_hierarchy \
            and allowed \
            and comp_value > best_subprojection_value \
            and assignment_compatible(comp_projection_vars, parent_projection_vars) \
            and has_suitable_projection:

            best_subprojection = c_id
            best_subprojection_value = comp_value
            print (comp_projection_vars, parent_projection_vars)

    return best_subprojection

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
            assert len(c) == 1
            if {-list(c)[0]} in projections:
                reduced = True
                continue
            else:
                new.add(c)
        projections = new
    return new


# this is actually the set cover problem, we're using a greedy algorithm here
def find_covering_components(parent_comp, join_projection, subprojections, cover=(), covered_variables=set(), covered_clauses=set(), return_all=False):

    results = set()

    comp_vars = component_variables[parent_comp]
    comp_clauses = component_clauses[parent_comp]

    remaining_clause_pool = set()
    for subcmp, _ in subprojections:
        remaining_clause_pool |= component_clauses[subcmp]

    # abort because the clauses we are looking for are not present in the remaining components
    clauses_present = (remaining_clause_pool >= (comp_clauses - covered_clauses))

    sort_key = lambda p: (len(component_variables[p[0]]), len(component_clauses[p[0]]))

    # there is still search to do
    if (covered_variables < comp_vars or covered_clauses < comp_clauses) and clauses_present:

        for subprojection in sorted(list(subprojections), key=sort_key, reverse=True):
            subcomp, (_, p_sub) = subprojection
            assert is_subprojection_of(p_sub, subcomp, join_projection, parent_comp)

            # compatible with all currently added components
            if all([join_compatible(subcomp, p_sub, co, po) for co, po in cover]):
                # filter out subprojections of subprojections
                applicable_projections = set()
                for subproj in subprojections:
                    comp, (_, proj) = subproj

                    if comp == subcomp:
                        continue

                    compatible = join_compatible(comp, proj, subcomp, p_sub)
                    already_covered = any([is_subprojection_of(proj, comp, p, co) for co, p in cover])
                    if not already_covered and compatible:
                        applicable_projections.add(subproj)

                # break symmetry by eliminating all smaller components
                #eliminated = {p for p in subprojections if p[0] <= subcomp}
                #eliminated |= {p for p in subprojections if not join_compatible(p[0], p[1][1],subcomp, p_sub)}
                result = find_covering_components(
                        parent_comp,
                        join_projection,
                        applicable_projections,
                        cover + ((subcomp, p_sub),),
                        covered_variables | component_variables[subcomp],
                        covered_clauses | component_clauses[subcomp]
                )
                if result:
                    if return_all:
                        results |= result
                    else:
                        return result


    # cannot append additional subcomponents
    if not results:
        covered_projections = [p for _, p in cover]

        # set of components is non-covering
        if covered_clauses != comp_clauses or covered_variables != comp_vars or combine_projections(covered_projections) != {join_projection}:
            return set()

        # a valid set of subcomponents
        return {cover}

    return results


def get_projection_or_join(component_id):
    return component_projections.get(component_id, component_joins.get(component_id, component_compositions.get(component_id)))

def all_projections():
    result = dict(component_projections)
    result.update(component_joins)
    result.update(component_compositions)
    return result

# enforce ordering on components (projections) to avoid cyclic proofs
# thus, children must have either fewer variables or equal vars and a longer projection
def is_subprojection_of(p1, c1, p2, c2):
    c1v = component_variables[c1]
    c2v = component_variables[c2]

    if c1v < c2v:
        # complete components are joinable
        if p1 == set():
            return True
        # otherwise the child must be a specialization
        return p1 >= p2

    if c1v != c2v:
        return False

    if p2 < p1:
        return True

    return False

# can these components, projections be safely joined?
def join_compatible(c1, p1, c2, p2):
    c1v = component_variables[c1]
    c2v = component_variables[c2]
    p1v = {abs(l) for l in p1}
    p2v = {abs(l) for l in p2}
    return (c1v - p1v) & c2v == set() and (c2v - p2v) & c1v == set()

def check_join_claim(component_id):

    for c_join, p_join in component_joins[component_id]:

        applicable_projections = {(c, p) for c, l in all_projections().items() for p in l if is_subprojection_of(p[1], c, p_join, component_id)}

        # the trivial component does not add anything
        applicable_projections.remove((-1, (1, frozenset())))

        # FIXME: ensure join compatibility among subcomponents
        subcomponent_sets = find_covering_components(component_id, p_join, applicable_projections)
        if not subcomponent_sets:
            return False

        #fixme: check completeness of subcomponent projections for this join

        for subcomponents in subcomponent_sets:
            join_table = [(1, p_join)]
            for comp_id, _ in subcomponents:
                new_table = []
                for c_sub, a_sub in get_projection_or_join(comp_id):
                    for c, a in join_table:
                        if assignment_compatible(a_sub, a):
                            new_table.append((c_sub * c, a | a_sub))
                join_table = new_table

            projections_used = set()
            c_join_check = 0
            for c, a in join_table:
                c_join_check += c
                projections_used.add(frozenset(a))

            if c_join_check != c_join:
                print ("check for join", component_id, subcomponents, "failed for", set(p_join), ": is" , c_join_check, "but should be", c_join)
                return False

            # there are unused assignments in the join table
            if set([frozenset(a) for c, a in join_table]) - projections_used:
                print ("join claim", component_id, "incomplete!")
                return False

    return True

def assignment_compatible(a1, a2):
    return len(a1 | a2) == len(set([abs(l) for l in a1]) | set([abs(l) for l in a2]))

def check_projection(comp_proj, comp_source):
    source_assignments = component_projections[comp_source] if comp_source in component_projections else component_joins[comp_source]

    source_vars = component_variables[comp_source]


    for c_proj, a_proj in component_projections[comp_proj]:

        # check underlying model claim completeness
        if not check_projection_completeness(comp_proj, a_proj):
            print ("model claims for component", comp_proj, "incomplete for projection", a_proj, "!")
            return False

        if not comp_proj in component_local_variables \
            or comp_proj not in component_local_clauses \
            or comp_proj not in component_models:

            print ("projected component", comp_proj, "does not have models!")
            return False

        c_proj_check = 0
        counted_models = set()
        for bridge_assignment in component_models[comp_proj]:
            # the projected assignment must be a restriction of the bridge_assignment
            if not a_proj <= bridge_assignment:
                continue

            for c_source, a_source in source_assignments:
                # this assignment fits to the restricted bridge assignment
                if assignment_compatible(bridge_assignment, a_source):
                    c_proj_check += c_source
                    counted_models.add(bridge_assignment)

        if c_proj_check != c_proj:
            print ("check for projection of", comp_proj, "from", comp_source, "failed for", *a_proj, ": is ", c_proj_check, "instead of", c_proj)
            return False

        # there are models left that where not projected
        for _, a_source in source_assignments:
            for model in set(component_models[comp_proj]) - counted_models:
                if assignment_compatible(model, a_source):
                    print ("incomplete projection", comp_proj, "model", model, "not covered.")
                    return False

    return True

def check_projection_claim(component_id):
    # the trivial projection is valid
    if component_id == -1:
        return True

    predecessor = -1
    # not a leaf projection
    if component_local_variables[component_id] != component_variables[component_id] \
            or component_local_clauses[component_id] != component_clauses[component_id]:

        assert False
        # fixme: do this by-claim
        predecessor = largest_subprojection(component_id, projection)
        assert predecessor > 0

    comp_vars = component_variables[component_id]
    pred_vars = component_variables[predecessor]


    # we must find a model claim that add the valid
    # assignments for the missing clauses
    clauses_needed = component_clauses[component_id] - component_clauses[predecessor]

    assert predecessor in component_projections or predecessor in component_joins
    assert comp_vars > pred_vars

    print ("checking projection", component_id, "with predecessor", predecessor)
    return check_projection(component_id, predecessor)

def check_composition_claim(component_id, projection, count):

    clauses = component_clauses[component_id]
    variables = component_variables[component_id]

    applicable_projections = []
    for origin_comp in component_variables.keys():
        if component_variables[origin_comp] != variables:
            continue
        if component_clauses[origin_comp] != clauses:
            continue

        for count, origin_proj in get_projection_or_join(origin_comp):
            if origin_proj > projection:
                # projections must not overlap!
                # currently, we only accept unit clauses
                assert len(origin_proj) == 1
                applicable_projections.append((count, origin_proj))

    # currently, we only use unit literals so this should work
    assert combine_projections([p[1] for p in applicable_projections]) == set(projection)

    # the same projection may be constructed in multiple ways
    applicable_projections = set(applicable_projections)

    combined_count = 0;
    for c, origin_proj in applicable_projections:
        combined_count += c

    if count != combined_count:
        print ("composition claim for", component_id, projection, "could not be verified: expected", count, "got", combined_count);
        return False
    return True

if __name__ == "__main__":
    print ("parsing...", file=sys.stderr)
    parse_proof(sys.stdin)
    print (len(clauses_dict), "clauses.", file=sys.stderr)
    print (len(component_variables), "components.", file=sys.stderr)
    print (len(component_models), "model claims.", file=sys.stderr)
    print (len(component_projections), "component projection claims.", file=sys.stderr)
    print (len(component_joins), "component join claims.", file=sys.stderr)
    print (len(component_compositions), "component composition claims.", file=sys.stderr)

    for component in component_models.keys():
        check_model_correctness(component)

    print ("model claim correctness verified.", file=sys.stderr)

    for component, l in component_compositions.items():
        for (count, projection) in l:
            if not check_composition_claim(component, projection, count):
                print ("composition claim", component, "failed!")
                sys.exit(1)

    print ("composition claims verified.", file=sys.stderr);

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
        print ("join claim for", component, "verified.")
