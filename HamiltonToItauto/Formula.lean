/- Automatically generated Lean file for Hamilton cycle IPC formula -/
import Mathlib.Tactic.ITauto

variable (v_1_1 : Prop)
variable (v_1_not_1 : Prop)
variable (v_1_2 : Prop)
variable (v_1_not_2 : Prop)
variable (v_1_3 : Prop)
variable (v_1_not_3 : Prop)
variable (v_1_prime_1 : Prop)
variable (goal0 : Prop)
variable (v_2_1 : Prop)
variable (v_2_not_1 : Prop)
variable (v_2_2 : Prop)
variable (v_2_not_2 : Prop)
variable (v_2_3 : Prop)
variable (v_2_not_3 : Prop)
variable (v_2_prime_1 : Prop)
variable (goal1 : Prop)
variable (v_3_1 : Prop)
variable (v_3_not_1 : Prop)
variable (v_3_2 : Prop)
variable (v_3_not_2 : Prop)
variable (v_3_3 : Prop)
variable (v_3_not_3 : Prop)
variable (v_3_prime_1 : Prop)
variable (goal2 : Prop)
variable (goal3 : Prop)

theorem ipc_formula :
  goal3 → ((v_1_1 → v_2_not_1 → v_3_not_1 → goal1) → goal0) → ((v_2_1 → v_1_not_1 → v_3_not_1 → goal1) → goal0) → ((v_3_1 → v_1_not_1 → v_2_not_1 → goal1) → goal0) → (v_1_not_1 → v_3_1 → (v_1_2 → v_2_not_2 → v_3_not_2 → goal2) → goal1) → (v_2_not_1 → v_1_1 → (v_2_2 → v_1_not_2 → v_3_not_2 → goal2) → goal1) → (v_3_not_1 → v_2_1 → (v_3_2 → v_1_not_2 → v_2_not_2 → goal2) → goal1) → (v_1_not_1 → v_1_not_2 → v_3_2 → (v_1_3 → v_2_not_3 → v_3_not_3 → goal3) → goal2) → (v_2_not_1 → v_2_not_2 → v_1_2 → (v_2_3 → v_1_not_3 → v_3_not_3 → goal3) → goal2) → (v_3_not_1 → v_3_not_2 → v_2_2 → (v_3_3 → v_1_not_3 → v_2_not_3 → goal3) → goal2) → goal0 :=
by itauto

#print ipc_formula
