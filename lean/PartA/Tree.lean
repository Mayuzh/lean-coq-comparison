inductive BTree
| leaf : BTree
| node : BTree → Nat → BTree → BTree

def mirror : BTree → BTree
  | BTree.leaf => BTree.leaf
  | BTree.node l v r => BTree.node (mirror r) v (mirror l)

def size : BTree → Nat
  | BTree.leaf => 0
  | BTree.node l _ r => 1 + size l + size r

def member (x : Nat) : BTree → Bool
  | BTree.leaf => false
  | BTree.node l v r =>
      if x = v then true
      else member x l || member x r
