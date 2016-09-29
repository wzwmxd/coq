Inductive natural:=
|Zero:natural
|Succ:natural->natural.

Fixpoint add (n:natural) (m:natural):natural:=
  match n with
  |Zero=>m
  |Succ n'=>Succ (add n' m)
  end.
Fixpoint mul (n:natural) (m:natural):natural:=
  match n with
  |Zero=>Zero
  |Succ n'=>add m (mul n' m)
  end.

Lemma add_zero_l:forall (n:natural), add Zero n=n.
  induction n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma add_zero_r:forall (n:natural),add n Zero=n.
  induction n.
  simpl;reflexivity.
  simpl; rewrite IHn;reflexivity.
Qed.
Lemma add_induc_r:forall (n m:natural),add n (Succ m)=Succ (add n m).
  induction n.
  simpl;reflexivity.
  intros;simpl.
  rewrite IHn;reflexivity.
Qed.

Lemma add_comm:forall (n m:natural),add n m=add m n.
  induction n.
  intros m.
  rewrite add_zero_l;rewrite add_zero_r;reflexivity.
  intros;simpl.
  rewrite add_induc_r.
  rewrite IHn.
  reflexivity.
Qed.
