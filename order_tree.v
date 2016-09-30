Require Import Arith.
Require Import List.

Inductive tree:=
|NULL:tree
|Tree:nat->tree->tree->tree.

Fixpoint eval_nodes (t:tree):nat:=
  match t with
  |NULL=>O
  |Tree _ l r=>S ((eval_nodes l)+(eval_nodes r))
  end.

Fixpoint insert (e:nat) (t:tree):tree:=
  match t with
  |NULL=>Tree e NULL NULL
  |Tree x l r=>if leb e x then Tree x (insert e l) r
               else Tree x l (insert e r)
  end.

Fixpoint insert_from_list (t:tree) (l:list nat):tree:=
  match l with
  |nil=>t
  |x::l'=>insert_from_list (insert x t) l'
  end.

Fixpoint locate (t:tree) (e:nat):nat:=
  match t with
  |NULL=>0
  |Tree x l r=>if beq_nat x e then S ((locate l e)+(locate r e))
               else (locate l 2)+(locate r e)
  end.

Eval vm_compute in locate (Tree 1 NULL NULL) 2.