import subprocess


def get_ipc_formula_premises(adjacency_matrix):
    n = len(adjacency_matrix)
    premises = []

    # Helper to return a vertex variable at a given step.
    def v(vertex, step):
        return f"v_{vertex+1}_{step}"

    def v_not(vertex, step):
        return f"v_{vertex+1}_not_{step}"

    # Helper for the additional variable for closing condition.
    # def v_prime(vertex):
    #     return f"v_{vertex+1}_prime_1"

    # (a) Initial premise: (a_1 → b^1 → ... → z^1 → 1) → 0
    for a in range(n):
        antecedents = [v_not(x, 1) for x in range(n) if a != x]
        premise = f"({v(a, 1)} → " + " → ".join(antecedents) + f" → goal1) → goal0"
        premises.append(premise)

    # (b) For each step i = 2,..., n, for each vertex a and for every incoming edge (b,a)
    # add: a1 → ... → ai-1 → bi-1 → (ai → bi → ... → zi → i) → i-1
    for i in range(2, n + 1):
        for a in range(n):
            for b in range(n):
                if a != b and adjacency_matrix[b][a] == 1:
                    antecedents = [v_not(a, j) for j in range(1, i)]  # a1, ..., ai-1
                    antecedents.append(v(b, i - 1))  # then bi-1
                    # For the consequent, list ai and then all bi, ..., zi for x ≠ a in increasing order.
                    consequent_vars = [v(a, i)]
                    consequent_vars.extend(v_not(x, i) for x in range(n) if x != a)
                    consequent = "(" + " → ".join(consequent_vars) + f" → goal{i})"
                    premise = (
                        " → ".join(antecedents) + " → " + consequent + f" → goal{i-1}"
                    )
                    premises.append(premise)

    # (c) Closing premise: bn → a'1 → n for each edge (b,a) in E
    # for a in range(n):
    #     for b in range(n):
    #         if a != b and adjacency_matrix[b][a] == 1:
    #             premises.append(f"{v(b, n)} → {v_prime(a)} → goal{n}")
    return premises


def get_ipc_formula(adjacency_matrix, premises):
    n = len(adjacency_matrix)
    premises = map(lambda x: f"({x})", premises)
    # The overall IPC formula: n → (all premises) → 0.
    formula = f"goal{n} → " + " → ".join(premises) + " → goal0"
    return formula


def get_lean_file(formula, n):
    # Generate declarations for vertex variables using 'variable' syntax.
    decls = []
    for a in range(n):
        for step in range(1, n + 1):
            decls.append(f"variable (v_{a+1}_{step} : Prop)")
            decls.append(f"variable (v_{a+1}_not_{step} : Prop)")
        decls.append(f"variable (v_{a+1}_prime_1 : Prop)")
        decls.append(f"variable (goal{a} : Prop)")
    decls.append(f"variable (goal{n} : Prop)")

    decl_block = "\n".join(decls)
    # Build the complete Lean file content with necessary imports.
    lean_file = f"""/- Automatically generated Lean file for Hamilton cycle IPC formula -/
import Mathlib.Tactic.ITauto

{decl_block}

theorem ipc_formula : 
  {formula} := 
by itauto

#print ipc_formula
"""
    return lean_file


if __name__ == "__main__":
    # Example graph: 3-cycle (edges: 0->1, 1->2, 2->0)
    adj_matrix_cycle = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]

    adjacency_matrix = adj_matrix_cycle
    premises = get_ipc_formula_premises(adjacency_matrix)
    formula_cycle = get_ipc_formula(adj_matrix_cycle, premises)
    lean_file_cycle = get_lean_file(formula_cycle, len(adj_matrix_cycle))

    with open("HamiltonToItauto/Formula.lean", "w+") as f:
        f.write(lean_file_cycle)

    # Run lake build
    completed = subprocess.run(["lake", "build"], check=True, capture_output=True)

    # Get info lines in stdout
    stdout = completed.stdout.decode("utf-8")
    info_lines = [line for line in stdout.splitlines() if "info" in line]
    assert "HamiltonToItauto/Formula.lean" in info_lines[0]

    parse_info = info_lines[1]

    # fun  (v_1_1 : Prop) (v_1_not_1 : Prop) (v_1_2 : Prop) ( ...
    fun_decl = "fun " + parse_info.split("fun")[1].split("=>")[0]

    #  h1 (fun (h10 : v_1_1) (h11 : v_2_not_1) (h12 : v_3_not_1)
    #  h5 h11 h10 (fun (h7696 : v_2_2) (h7697 : v_1_not_2) (h7698 : v_3_not_2)
    #  h9 h12 h7698 h7696 (fun (h7708 : v_3_3) (h7709 : v_1_not_3) (h7710 : v_2_not_3)
    #  h0)))
    body = parse_info.split("=>")[1:]

    # ['h1', 'h5', 'h9', 'h0']
    assumptions_names = [part.split(" ")[1] for part in body[:-1]] + ["h0"]
    # h0 corresponds to 'goal{n}' and h1 to premises[0]
    # ignore last assumption, it is always 'h0'
    assumptions = [premises[int(name[1:]) - 1] for name in assumptions_names[:-1]]

    # for l in assumptions:
    #    print(l)
    # (v_1_1 → v_2_not_1 → v_3_not_1 → goal1) → goal0
    # v_2_not_1 → v_1_1 → (v_2_2 → v_1_not_2 → v_3_not_2 → goal2) → goal1
    # v_3_not_1 → v_3_not_2 → v_2_2 → (v_3_3 → v_1_not_3 → v_2_not_3 → goal3) → goal2

    variables_used = [assumption.split('(')[1].split(' ')[0] for assumption in assumptions]
    vs = [variable.split('_')[0] for variable in variables_used]
    assert all(v == 'v' for v in vs)
    vertices = [int(variable.split('_')[1]) for variable in variables_used]
    steps = [int(variable.split('_')[2]) for variable in variables_used]
    assert sorted(vertices) == list(range(1, len(adj_matrix_cycle) + 1))

    print(vertices)
