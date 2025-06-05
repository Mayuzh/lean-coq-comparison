import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

inductive BTree where
  | leaf : BTree
  | node : BTree → Nat → BTree → BTree
deriving Repr, BEq

open BTree

def mirror : BTree → BTree
  | leaf => leaf
  | node l v r => node (mirror r) v (mirror l)

def size : BTree → Nat
  | leaf => 0
  | node l _ r => 1 + size l + size r

def member (x : Nat) : BTree → Bool
  | leaf => false
  | node l v r => if x = v then true else member x l || member x r

def exampleTree : BTree := node (node leaf 1 leaf) 2 (node leaf 3 leaf)

#eval size exampleTree        -- 3
#eval mirror exampleTree      -- tree
#eval member 3 exampleTree    -- true
#eval member 4 exampleTree    -- false

theorem mirror_involutive : ∀ t : BTree, mirror (mirror t) = t := by
  intro t
  induction t with
  | leaf => rfl
  | node l v r ih_l ih_r =>
    simp [mirror, ih_l, ih_r]

#check mirror_involutive  -- Should show its type: ∀ (t : BTree), mirror (mirror t) = t
#eval mirror (mirror exampleTree) == exampleTree  -- Should return `true`
