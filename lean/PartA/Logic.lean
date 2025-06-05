-- A ∧ B → B ∧ A
theorem my_and_comm {A B : Prop} (h : A ∧ B) : B ∧ A := by
  cases h with
  | intro ha hb => exact ⟨hb, ha⟩

-- ¬¬A → A (requires classical logic)
open Classical

theorem not_not_implies (A : Prop) : ¬¬A → A := by
  intro h
  by_cases ha : A
  · exact ha
  · contradiction
