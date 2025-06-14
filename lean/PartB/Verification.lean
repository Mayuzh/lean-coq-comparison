import Mathlib.Data.List.Basic
import Mathlib.Tactic

section Verification

variable [LinearOrder α]

-- Custom insert to avoid conflict
def myInsert (x : α) : List α → List α
| []       => [x]
| (h::t) => if x ≤ h then x :: h :: t else h :: myInsert x t

-- Membership theorem: after inserting, y is either the new element or was already in the list
theorem mem_myInsert {x y : α} {l : List α} :
  y ∈ myInsert x l → y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [myInsert]
  | cons h t ih =>
    simp [myInsert]
    split_ifs with hle
    · simp; intro h'; exact Or.inl h'
    · simp; intro h'
      cases h' with
      | inl hy => exact Or.inr (Or.inl hy)
      | inr hy =>
          cases ih hy with
          | inl eq => exact Or.inl eq
          | inr hin => exact Or.inr (Or.inr hin)

end Verification
