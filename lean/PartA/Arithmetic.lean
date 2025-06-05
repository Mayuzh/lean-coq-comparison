import Mathlib.Data.Nat.Basic

/-!
# Arithmetic Theorems in ℕ
This file formalizes basic arithmetic equalities using natural number induction and Lean tactics.
-/

set_option maxRecDepth 256

-- n + 0 = n
theorem add_zero (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.succ_add, ih]


-- 0 + n = n
theorem zero_add (n : ℕ) : 0 + n = n := by
  simp

-- n + m = m + n (commutativity of addition)
theorem add_comm (m n : ℕ) : m + n = n + m := by
  induction n with
  | zero =>
    rw [Nat.add_zero, Nat.zero_add]
  | succ n ih =>
    rw [Nat.add_succ, ih, Nat.succ_add]

-- n * 0 = 0
theorem mul_zero (n : ℕ) : n * 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Nat.succ_mul, ih]

-- n * 1 = n
theorem mul_one (n : ℕ) : n * 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [Nat.succ_mul, ih]
