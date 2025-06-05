# Part A: Hands-on Formalization – Coq vs. Lean

This section of the project contains basic formalizations implemented in both Lean and Coq, as part of a comparative evaluation of the two proof assistants.

## Structure
```text
LEAN-CoQ-COMPARISON/
├── coq/
│   └── PartA/
│       ├── Basic.v           # First examples and experiments
│       ├── Logic.v           # Propositional logic (and_comm, etc.)
│       ├── Arithmetic.v      # Natural number proofs (add_zero, add_comm)
│       ├── Tree.v            # Binary tree definition, functions, and theorems (e.g. mirror_involutive)
│       └── _CoqProject       # Coq project config file
│
├── lean/
│   └── PartA/
│       ├── Intro.lean        # Intro-level Lean examples and tutorial code
│       ├── Basic.lean        # First examples and experiments
│       ├── Logic.lean        # Propositional logic (and_comm, etc.)
│       ├── Arithmetic.lean   # Natural number proofs (add_zero, add_comm)
│       └── Tree.lean         # Binary tree definition, functions, and theorems (e.g. mirror_involutive)
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

### Trees

- Binary tree definition using `leaf` and `node`
- Functions: `size`, `member`, `mirror`
- Theorem: `mirror (mirror t) = t` (mirror_involutive)

This section tests:
- Pattern matching and recursion over inductive types
- Structural proofs using inductive hypotheses
- Reasoning about symmetry and correctness of recursive functions

## How to Run

### Lean

These files are intended to be run interactively using the Lean 4 extension in Visual Studio Code

### Coq

Make sure you have Coq installed and configured (e.g. via OPAM).

To compile individual Coq files:

```bash
coqc Arithmetic.v
coqc Logic.v
coqc Tree.v

