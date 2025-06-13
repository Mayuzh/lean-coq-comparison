From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AlgebraExamples.

Variable R : ringType.

(* Monoid identity: 1 * x = x *)
Lemma mul1r_example (x : R) : 1 * x = x.
Proof. by rewrite mul1r. Qed.

(* Monoid identity: x * 1 = x *)
Lemma mulr1_example (x : R) : x * 1 = x.
Proof. by rewrite mulr1. Qed.

(* Associativity of multiplication *)
Lemma mul_assoc_example (x y z : R) : x * (y * z) = (x * y) * z.
Proof. by rewrite mulrA. Qed.

(* Additive inverse *)
Lemma addNr_example (x : R) : x + -x = 0.
Proof. by rewrite addNr. Qed.

(* Commutativity of addition *)
Lemma addrC_example (x y : R) : x + y = y + x.
Proof. by rewrite addrC. Qed.

End AlgebraExamples.

(* Instantiate with integers as ringType *)
Example Z_ring : ringType := int_ringType.

Check mul1r_example Z_ring.
Check addrC_example Z_ring.
