import Mathlib.Data.Nat.Basic

theorem add_zero (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]