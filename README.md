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
```
# Part B: Ecosystem Comparison – Algebra and Verification

This section extends the comparison to real-world proof development styles, with a focus on algebra libraries and small-scale verification tasks in both ecosystems.

## Structure
```text
LEAN-CoQ-COMPARISON/
├── coq/
│   └── PartB/
│       ├── Algebra.v         # MathComp algebra structures: monoid, group, ring
│       └── Verification.v    # Software Foundations-style expression evaluation
│
├── lean/
│   └── PartB/
│       ├── Algebra.lean      # Mathlib algebra structures: monoid, group, ring
│       └── Verification.lean # Verified insertion correctness for lists

```

## Contents

### Algebra Libraries

#### Lean (Mathlib)

- Algebraic structures built using typeclasses (`[Semigroup]`, `[Monoid]`, `[Group]`, `[Ring]`).
- Very flexible inheritance and generic theorem reuse.
- Simplified declarations and automatic inference of instances.
- Extensive automation using tactics such as `simp`, `rw`, `linarith`, `aesop`.

#### Coq (MathComp)

- Algebraic hierarchy constructed with canonical structures (`monoidType`, `groupType`, `ringType`).
- More rigid but very compositional, ensuring strict hierarchy correctness.
- Proofs built compactly using `rewrite` and `ssreflect` idioms.
- Automation is more lightweight but very controlled.

### Small-Scale Verification

#### Lean (`Verification.lean`)

- Verified insertion into a sorted list (`myInsert` function).
- Recursive definition using pattern matching.
- Induction performed using tactic blocks (`induction`, `cases`, `split_ifs`).
- Automation through `simp` for equality reasoning.

#### Coq (`Verification.v`)

- Miniature expression language (`aexp`) and evaluator (`aeval`) correctness.
- Structural recursion via `Fixpoint`.
- Proofs use standard `intros`, `simpl`, and `reflexivity` tactics.
- Small correctness theorems about determinism and evaluation behavior.

### Key Comparison Summary

| Aspect | Lean (Mathlib) | Coq (MathComp) |
|--------|----------------|----------------|
| Algebra design | Typeclasses | Canonical Structures |
| Inductive types | Pattern matching | Inductive + match |
| Recursion | Implicit (`def`) | `Fixpoint` with annotations |
| Tactics | `simp`, `aesop`, `linarith` | `rewrite`, `ssreflect` |
| Verification idioms | Functional programming style | Proof engineering style |
| Ecosystem maturity | Modern, growing | Mature, stable |
