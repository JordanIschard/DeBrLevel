From Coq Require Import Orders Streams Lia Bool.Bool Structures.EqualitiesFacts.
From DeBrLevel Require Import LevelInterface Level.

Module IsLvlStreamET (E : IsLvlETWL) <: IsLvlET.


(** *** Definition *)
Section definition.

Definition t := Stream E.t.

Definition eq (s s1 : t) := EqSt s s1.

Definition shift (lb k : Level.t) (t0 : t) : t := 
  map (E.shift lb k) t0.

Definition valid (lb : Level.t) (t : t) := 
  ForAll (fun st => E.valid lb (hd st)) t.

End definition.

(** *** Equality *)
Section equality.

Lemma eq_refl : Reflexive eq. 
Proof. 
  red; intros. apply EqSt_reflex.
Qed.

Lemma eq_sym  : Symmetric eq.
Proof. 
  red; intros. now apply sym_EqSt.
Qed.

Lemma eq_trans : Transitive eq.
Proof. 
  red; intros. eapply trans_EqSt; eauto.
Qed.

#[global]
Instance eq_equiv : Equivalence eq.
Proof. 
  split.
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans.
Qed.

#[export]
Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  repeat red; intros; subst; unfold eq, shift in *.
  apply ntheq_eqst. intro n.
  apply eqst_ntheq with (n := n) in H1.
  repeat rewrite Str_nth_map. now rewrite H1.
Qed.

Lemma shift_eq_iff : forall lb k t t1, 
  eq t t1 <-> eq (shift lb k t) (shift lb k t1).
Proof.
  split; intro Heq; destruct t0,t1; unfold eq in *;
  try (now inversion Heq).
  - unfold shift; simpl.
    apply ntheq_eqst. intro n.
    apply eqst_ntheq with (n := n) in Heq.
    repeat rewrite Str_nth_map. now rewrite Heq.
  - unfold shift in *; simpl in *.
    apply ntheq_eqst. intro n.
    apply eqst_ntheq with (n := n) in Heq.
    repeat rewrite Str_nth_map in *.
    apply E.eq_leibniz. 
    rewrite E.shift_eq_iff. now rewrite Heq.
Qed.

Lemma valid_eq_bis lb: forall s s',
  EqSt s s' -> valid lb s -> valid lb s'.
cofix valid_eq_bis.
  intros. unfold valid in *; simpl in *. destruct H.
  destruct H0,s,s'; split; simpl in *.
  - now rewrite <- H.
  - eapply valid_eq_bis; eauto.
Qed.

#[export]
Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  repeat red; intros; subst; split; unfold eq in *.
  - now apply valid_eq_bis.
  - apply valid_eq_bis. now symmetry.
Qed.

End equality.

(** *** Shift *)
Section shift.

Variable lb k k' k'' : Level.t.
Variable t : t.

Lemma shift_zero_refl : eq (shift lb 0 t) t.
Proof.
  unfold eq, shift. apply ntheq_eqst.
  intros. rewrite Str_nth_map.
  apply E.eq_leibniz.
  apply E.shift_zero_refl. 
Qed.

Lemma shift_trans : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof. 
  unfold eq, shift. apply ntheq_eqst.
  intros. repeat rewrite Str_nth_map.
  apply E.eq_leibniz.
  apply E.shift_trans.
Qed.

Lemma shift_permute : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof. 
  unfold eq, shift. apply ntheq_eqst.
  intros. repeat rewrite Str_nth_map.
  apply E.eq_leibniz.
  apply E.shift_permute.
Qed.

Lemma shift_unfold : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof. 
  unfold eq, shift. apply ntheq_eqst.
  intros. repeat rewrite Str_nth_map.
  apply E.eq_leibniz.
  apply E.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros Hlt Hlt'; 
  unfold eq, shift. apply ntheq_eqst.
  intros. repeat rewrite Str_nth_map.
  apply E.eq_leibniz.
  now apply E.shift_unfold_1.
Qed.

End shift.

(** *** Valid *)
Section valid.

Lemma valid_weakening : forall k k' (t : t), 
  (k <= k') -> valid k t -> valid k' t.
cofix valid_weakening.
  unfold valid in *; intros.
  destruct H0; split.
  - now apply E.valid_weakening with k.
  - destruct t0; simpl in *.
    now apply valid_weakening with k.
Qed.

Lemma shift_preserves_valid : forall k k' t, 
  valid k t -> valid (k + k') (shift k k' t).
Proof.
  unfold valid,shift in *; intros k k' t.
  rewrite <- ForAll_map. revert t. 
  cofix shift_preserves_valid; intros.
  constructor; destruct H; auto.
  now apply E.shift_preserves_valid.
Qed. 

Lemma shift_preserves_valid_1 : forall lb k k' t, 
  valid k t -> valid (k + k') (shift lb k' t).
Proof.
  unfold valid,shift in *; intros lb k k' t.
  rewrite <- ForAll_map. revert t. 
  cofix shift_preserves_valid; intros.
  constructor; destruct H; auto.
  now apply E.shift_preserves_valid_1.
Qed.

Lemma shift_preserves_valid_gen : forall lb lb' k k' t,  
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' ->
  k' - k = lb' - lb ->  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  unfold valid,shift in *; intros lb lb' k k' t Hle Hle' Hle1 Hle1' Heq.
  rewrite <- ForAll_map. revert t. 
  cofix shift_preserves_valid; intros.
  constructor; destruct H; auto.
  now apply E.shift_preserves_valid_gen with lb.
Qed.

Lemma shift_preserves_valid_2 : forall lb lb' t, 
  lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof.
  unfold valid,shift in *; intros lb lb' t Hle.
  rewrite <- ForAll_map. revert t. 
  cofix shift_preserves_valid; intros.
  constructor; destruct H; auto.
  now apply E.shift_preserves_valid_2.
Qed.

Lemma shift_preserves_valid_zero : forall k t,
  valid k t -> valid k (shift k 0 t).
Proof.
  intros; replace k with (k + 0); try lia; 
  now apply shift_preserves_valid_1.
Qed.

End valid.

End IsLvlStreamET.

Module IsBdlLvlStreamET (E : IsBdlLvlETWL) <: IsBdlLvlET.

Include IsLvlStreamET E.

Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
Proof.
  unfold eq,valid; intros lb k t HFA.
  apply ntheq_eqst; intro.
  apply ForAll_Str_nth_tl with (m := n) in HFA.
  revert  t HFA; induction n; intros.
  - unfold shift in *; destruct t0; simpl in *.
    unfold Str_nth; inversion HFA; simpl in *.
    apply E.eq_leibniz. 
    now apply E.shift_valid_refl.
  - unfold Str_nth; destruct t0; simpl in HFA.
    unfold shift. rewrite Str_nth_tl_map.
    simpl. apply IHn in HFA.
    unfold Str_nth in HFA. unfold shift in *.
    rewrite Str_nth_tl_map in HFA; now simpl in *.
Qed.
  
End IsBdlLvlStreamET.