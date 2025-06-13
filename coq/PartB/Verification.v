From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.

(* Simple arithmetic expressions *)
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp.

(* Evaluation function *)
Fixpoint aeval (e : aexp) : nat :=
  match e with
  | ANum n => n
  | APlus e1 e2 => aeval e1 + aeval e2
  end.

(* Sample theorem: deterministic evaluation *)
Theorem aeval_deterministic : forall e, exists! n, aeval e = n.
Proof.
  intros. exists (aeval e). split.
  - reflexivity.
  - intros. subst. reflexivity.
Qed.

(* Another simple lemma *)
Theorem aeval_plus : forall n m,
  aeval (APlus (ANum n) (ANum m)) = n + m.
Proof.
  intros. simpl. reflexivity.
Qed.
