# Part A: Hands-on Formalization – Coq vs. Lean

This section of the project contains basic formalizations implemented in both Lean and Coq, as part of a comparative evaluation of the two proof assistants.

## Structure
lean/
├── PartA/
│   ├── Arithmetic.v
│   ├── Logic.v
│   └── Basic.v
coq/
├── PartA/
│   ├── Arithmetic.lean
│   ├── Logic.lean
│   └── Basic.lean
README.md


## Contents

### Logic

- `A ∧ B → B ∧ A` (and_comm)
- `¬¬A → A` (classical logic)
- `p → (q → p)` (implication chaining)

These theorems highlight differences in:
- Tactic ergonomics (`intro`, `destruct`, `cases`, etc.)
- Treatment of classical vs. constructive logic

### Arithmetic

- `∀ n, n + 0 = n` (add_zero)
- `∀ m n, m + n = n + m` (add_comm)

These were formalized using:
- Structural induction on natural numbers
- Basic rewrites and associativity rules

## How to Run

### Coq

```bash
coqc Arithmetic.v
coqc Logic.v
