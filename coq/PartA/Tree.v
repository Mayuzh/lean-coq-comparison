Inductive BTree : Type :=
| leaf : BTree
| node : BTree -> nat -> BTree -> BTree.

Fixpoint mirror (t : BTree) : BTree :=
  match t with
  | leaf => leaf
  | node l v r => node (mirror r) v (mirror l)
  end.

Fixpoint size (t : BTree) : nat :=
  match t with
  | leaf => 0
  | node l _ r => 1 + size l + size r
  end.

Fixpoint member (x : nat) (t : BTree) : bool :=
  match t with
  | leaf => false
  | node l v r =>
      if Nat.eqb x v then true
      else member x l || member x r
  end.

Definition exampleTree := node (node leaf 1 leaf) 2 (node leaf 3 leaf).

Compute size exampleTree.       (* 3 *)
Compute mirror exampleTree.     (* Check output tree *)
Compute member 3 exampleTree.   (* true *)
Compute member 4 exampleTree.   (* false *)

Lemma mirror_involutive : forall t : BTree, mirror (mirror t) = t.
Proof.
  induction t as [| l IHl v r IHr].
  - reflexivity.
  - simpl. rewrite IHr, IHl. reflexivity.
Qed.

Compute (mirror (mirror exampleTree)).