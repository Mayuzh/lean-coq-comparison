import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

section AlgebraExamples

variable {R : Type*} [Ring R]

-- Monoid identity: 1 * x = x
example (x : R) : 1 * x = x := one_mul x

-- Monoid identity: x * 1 = x := mul_one x
example (x : R) : x * 1 = x := mul_one x

-- Associativity of multiplication
example (x y z : R) : x * (y * z) = (x * y) * z := by rw [mul_assoc]

-- Additive inverse (negation)
example (x : R) : x + -x = 0 := by simp

-- Commutativity of addition
example (x y : R) : x + y = y + x := by rw [add_comm]

end AlgebraExamples
