import Mathlib.Data.Nat.Basic

-- ∀ n, n + 0 = n
theorem add_zero (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.succ_add, ih]

-- ∀ n m, n + m = m + n
theorem add_comm (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero =>
    rw [Nat.zero_add, Nat.add_zero]
  | succ n ih =>
    rw [Nat.succ_add, ih, ← Nat.add_succ]
