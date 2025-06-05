Require Import Classical.

(* A /\ B -> B /\ A *)
Theorem and_comm : forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B [HA HB].
  split; assumption.
Qed.

(* ~~A -> A (requires classical logic) *)
Theorem not_not_implies : forall A : Prop, ~~A -> A.
Proof.
  intros A H.
  apply NNPP.
  assumption.
Qed.
