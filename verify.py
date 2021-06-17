import sys
import subprocess
from collections import defaultdict

# contains clauses as lists of literals
clauses_dict = {}
# contains components as lists of clauses
component_dict = {}

# contains a list of models (list of clauses) for each component id
component_models = defaultdict(list)

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
            clauses_dict[l_id] = l_data

        elif l_type == "cd":
            component_dict[l_id] = l_data

        elif l_type == "m":
            component_models[l_id].append(l_data)

def map_lit(variable_mapping, l):
    var = variable_mapping[abs(l)]
    return var if l > 0 else -var

if __name__ == "__main__":
    parse_proof(sys.stdin)
    print (len(clauses_dict), "clauses.", file=sys.stderr)
    print (len(component_dict), "component formulae.", file=sys.stderr)
    print (len(component_models), "model claims.", file=sys.stderr)

    for component, models in component_models.items():
        clauses = []
        # print bag formula
        for clause_id in component_dict[component]:
            clauses.append(clauses_dict[clause_id])

        # print negated models -> -(a ^ b) => (-a or -b)
        for model in component_models[component]:
            clauses.append([-l for l in model])


        # set of all original variable names
        variables = set()
        for c in clauses:
            variables = variables | set([abs(l) for l in c])

        variable_mapping = { v : i + 1 for i, v in enumerate(variables)}

        problem_string = " ".join(map(str, ["p", "cnf", len(variables), len(clauses)])) + "\n"
        for clause in clauses:
            problem_string += " ".join(map(str, [map_lit(variable_mapping, l) for l in clause] + [0])) + "\n"

        result = subprocess.run(["minisat", "-verb=0", "-strict"], input=problem_string, capture_output=True, encoding="utf-8")
        last_line = result.stdout.strip().split("\n")[-1].strip()
        if not last_line == "UNSATISFIABLE":
            print ("model claim", component, "failed:", last_line, file=sys.stderr)
            print (problem_string)
            sys.exit(1)

    print ("model claims verified (according to minisat).", file=sys.stderr)
