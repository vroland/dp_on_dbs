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
# list of projection claims per component id
component_projections = defaultdict(set)
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

        elif l_type == "p":
            component_projections[l_id].add((l_count, frozenset(l_data)))

        elif l_type == "j":
            component_joins[l_id].add((l_count, frozenset(l_data)))

        elif l_type == "a":
            component_compositions[l_id].add((l_count, frozenset(l_data)))

        else:
            print ("unknown line type:", l_type)
            sys.exit(1)

    # insert empty projection component
    component_clauses[-1] = frozenset()
    component_projections[-1] = {(1, frozenset())}
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
            subcomp, (c_sub, p_sub) = subprojection
            assert is_subprojection_of(p_sub, subcomp, join_projection, parent_comp)

            # compatible with all currently added components
            if all([join_compatible(subcomp, p_sub, co, po[1]) for co, po in cover]):
                # filter out subprojections of subprojections
                applicable_projections = set()
                for subproj in subprojections:
                    comp, (_, proj) = subproj

                    if comp == subcomp:
                        continue

                    compatible = join_compatible(comp, proj, subcomp, p_sub)

                    already_covered = any([is_subprojection_of(proj, comp, p[1], co) for co, p in cover])

                    if not already_covered and compatible:
                        applicable_projections.add(subproj)

                result = find_covering_components(
                        parent_comp,
                        join_projection,
                        applicable_projections,
                        cover + ((subcomp, (c_sub, p_sub)),),
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
        if covered_variables != comp_vars or covered_clauses != comp_clauses:
            return set()
        covered_projections = [p[1] for _, p in cover]

        #print (parent_comp, join_projection, cover, covered_projections)
        projections_complete = combine_projections(covered_projections) == {join_projection}

        if not projections_complete:
            projections_complete = all([subprojections_complete_wrt(p[0], join_projection) for p in cover])


        # set of components is non-covering
        if covered_clauses != comp_clauses or covered_variables != comp_vars or not projections_complete:
            return set()

        # return only components
        return {tuple([p[0] for p in cover])}

    return results


def get_projection_or_join(component_id):
    return component_projections.get(component_id, component_joins.get(component_id, component_compositions.get(component_id)))

def all_projections():
    result = defaultdict(set)
    for c, p in component_projections.items():
        result[c] |= p
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

def applicable_projections_for(component_id, projection):
    return {(c, p) for c, l in all_projections().items() for p in l if is_subprojection_of(p[1], c, projection, component_id) and assignment_compatible(p[1], projection)}
    #   and subprojection_complete_wrt(c, projection)

def check_join_claim(component_id):

    for c_join, p_join in component_joins[component_id]:

        applicable_projections = applicable_projections_for(component_id, p_join)

        # the trivial component does not add anything
        applicable_projections.remove((-1, (1, frozenset())))

        # FIXME: ensure join compatibility among subcomponents
        subcomponent_sets = find_covering_components(component_id, p_join, applicable_projections)
        if not subcomponent_sets:
            print ("no subcomponents found for ", component_id, set(p_join))
            return False

        #fixme: check completeness of subcomponent projections for this join

        print (component_id, "subcomponent_sets:", subcomponent_sets)

        for subcomponents in subcomponent_sets:
            join_table = [(1, p_join)]
            for comp_id in subcomponents:
                new_table = []
                for c, a in join_table:
                    comp_projections = all_projections()[comp_id]
                    projection_assignments = [p[1] for p in comp_projections]

                    applicable_projections = []
                    for (c_sub, a_sub) in comp_projections:
                        # remove projections of which more general versions exist
                        more_general = [p for p in comp_projections if p[1] < a_sub and assignment_compatible(a_sub, a)]
                        if assignment_compatible(a_sub, a) and not more_general:
                            applicable_projections.append((c_sub, a_sub))
                        #else:
                            #print (comp_id, ":", "remove", c_sub, a_sub, "in favour of", more_general)

                    for (c_sub, a_sub) in applicable_projections:
                        if assignment_compatible(a_sub, a):
                            new_table.append((c_sub * c, a | a_sub))
                join_table = new_table
                #print (comp_id, join_table)

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


def check_projection_claim(component_id, projection, count):
    # the trivial projection is valid
    if component_id == -1:
        return True

    comp_vars = component_variables[component_id]
    comp_clauses = component_clauses[component_id]
    comp_local_vars = component_local_variables[component_id]
    comp_local_clauses = component_local_clauses[component_id]

    # check underlying model claim completeness
    if not check_projection_model_completeness(component_id, projection):
        print ("model claims for component", component_id, "incomplete for projection", projection, "!")
        return False

    applicable_projections = applicable_projections_for(component_id, projection)

    # subcomponent combines to parent
    completes = lambda c, p: \
        component_variables[c] | comp_local_vars == comp_vars \
            and component_clauses[c] | comp_local_clauses == comp_clauses \
            and assignment_compatible(p[1], projection)

    applicable_projections = {(c, p) for c, p in applicable_projections if completes(c, p)}


    if applicable_projections == set():
        print ("no possible subprojections found for", component_id, set(projection), "!")
        sys.exit(1)

    # FIXME: cannot use projections from different components
    by_component = defaultdict(list)
    for c, p in applicable_projections:
        by_component[c].append((c, p))

    print ("source projections for", component_id, set(projection), ":", dict(by_component))
    # FIXME: check applicable_projections completeness

    found = False
    # one combination is probably sufficient:
    for subcomponent, subprojections in by_component.items():

        # all subprojections must be of the same level
        subprojection_vars = {frozenset({abs(l) for l in p[1][1]}) for p in subprojections}
        assert len(subprojection_vars) == 1

        subprojection_vars = subprojection_vars.pop()


        # this is not a leaf projection
        #if subprojections[0] != (-1, (1, frozenset())):
        #    projection_clauses = set()

        #    # add negated projections -> -(a ^ b) => (-a or -b)
        #    for _, (_, p) in subprojections:
        #        projection_clauses.add(frozenset([-l for l in p]))

        #    # add parent projection as constraints
        #    for l in projection:
        #        projection_clauses.add(frozenset({l}))

        #    complete = component_unsatisfiable(component_id, projection_clauses)

        #    if not complete:
        #        print ("subprojections incomplete: ", subprojections)
        #        continue

        joint_assignments = []
        for c_sub, (co, a_sub) in subprojections:
            for a in component_models[component_id]:
                if assignment_compatible(a_sub, a):
                    joint_assignments.append((co, a | a_sub))

        c_proj_check = 0
        for (cnt, assignment) in joint_assignments:
            if assignment >= projection:
                c_proj_check += cnt

        # incomplete subcomponent, skip
        if c_proj_check < count:
            continue

        if c_proj_check > count:
            print ("check for projection of", component_id, "from", subprojections, "failed for", set(projection), ": is ", c_proj_check, "instead of", count)
            return False

        assert c_proj_check == count
        found = True

    return found

def check_composition_claim(component_id, projection, count):

    clauses = component_clauses[component_id]
    variables = component_variables[component_id]

    applicable_projections = []
    for origin_comp in component_variables.keys():
        if component_variables[origin_comp] != variables:
            continue
        if component_clauses[origin_comp] != clauses:
            continue

        for c, origin_proj in get_projection_or_join(origin_comp):
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
                print ("composition claim", component, set(projection), "failed!")
                sys.exit(1)

    print ("composition claims verified.", file=sys.stderr);

    # for component, l in component_projections.items():
    #     for (count, projection) in l:
    #         checked = check_projection_claim(component, projection, count)
    #         if not checked:
    #             print ("projection claim", component, set(projection), "failed!")
    #             sys.exit(1)

    # print ("projection claims verified.")

    for component, l in component_joins.items():
        checked = check_join_claim(component)
        if not checked:
            print ("join claim", component, "failed!")
            sys.exit(1)
        print ("join claim for", component, "verified.")
