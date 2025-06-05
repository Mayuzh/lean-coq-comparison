(* arithmetic.v *)
Require Import Arith.

Theorem add_zero : forall n : nat, n + 0 = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem zero_add : forall n : nat, 0 + n = n.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n as [| n' IH].
  - simpl. intros. rewrite <- plus_n_O. reflexivity.
  - intros. simpl. rewrite IH. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem mul_zero : forall n : nat, n * 0 = 0.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem mul_one : forall n : nat, n * 1 = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
