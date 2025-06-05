# Part A: Hands-on Formalization – Coq vs. Lean

This section of the project contains basic formalizations implemented in both Lean and Coq, as part of a comparative evaluation of the two proof assistants.

## Structure
```text
LEAN-CoQ-COMPARISON/
├── coq/
│   └── PartA/
│       ├── Arithmetic.v       # Natural number proofs (add_zero, add_comm)
│       ├── Basic.v           # First examples and experiments
│       ├── Logic.v           # Propositional logic (and_comm, etc.)
│       └── _CoqProject       # Coq project config file
│
├── lean/
│   └── PartA/
│       ├── Arithmetic.lean   # Natural number proofs (add_zero, add_comm)
│       ├── Basic.lean        # First examples and experiments
│       ├── Intro.lean        # Intro-level Lean examples and tutorial code
│       └── Logic.lean        # Propositional logic (and_comm, etc.)
│
├── LeanCoqComp/              # Shared code or utilities (currently unused)
│
├── README.md                 # Project description and comparison writeup
├── lakefile.lean             # Lean build setup
├── lakefile.toml             # Lean build config
├── lean-toolchain            # Lean version lock
└── .github/                  # CI configuration
```

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
