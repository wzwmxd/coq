Require Import List.
Require Import Arith.

Inductive rbtree:=
|NULL:rbtree
|RBTree (key:nat) (color:nat) (p:rbtree) (l:rbtree) (r:rbtree):rbtree.

left_rotate (T:rbtree) (x:nat):rbtree:=
  