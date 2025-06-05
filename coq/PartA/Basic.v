From Coq Require Import Arith.Arith.

(* ∀ n, n + 0 = n *)
Lemma add_n_0 : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* ∀ n m, n + m = m + n *)
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IH].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. rewrite <- Nat.add_succ_r. reflexivity.
Qed.
