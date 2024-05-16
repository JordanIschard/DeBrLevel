From Coq Require Import Orders Lia Bool.Bool Structures.EqualitiesFacts.
From DeBrLevel Require Import LevelInterface Level.

Module IsLvlOptET (E : IsLvlET) <: IsLvlET.


(** *** Definition *)
Section definition.

Definition t := option E.t.

Definition eq (ot1 ot2 : t) :=
  match (ot1,ot2) with
   | (Some t1,Some t2) => E.eq t1 t2
   | (None,None) => True
   | _ => False
  end.

Definition shift (lb k : Level.t) (t : t) := 
  option_map (E.shift lb k) t.

Definition valid (lb : Level.t) (t : t) := 
  match t with
   | Some t1 => E.valid lb t1
   | _ => True
  end.

End definition.

(** *** Equality *)
Section equality.

Lemma eq_refl : Reflexive eq. 
Proof. 
  red; intros; destruct x; unfold eq; auto.
  reflexivity.
Qed.

Lemma eq_sym  : Symmetric eq.
Proof. 
  red; intros; destruct x,y; unfold eq in *; auto.
  now symmetry.
Qed.

Lemma eq_trans : Transitive eq.
Proof. 
  red; intros; destruct x,y,z; unfold eq in *; auto.
  - transitivity t1; auto.
  - inversion H.
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
  repeat red; intros; subst; destruct x1,y1; unfold eq in *;
  try (now inversion H1).
  unfold shift; simpl. now apply E.shift_eq.
Qed.

Lemma shift_eq_iff : forall lb k t t1, 
  eq t t1 <-> eq (shift lb k t) (shift lb k t1).
Proof.
  split; intro Heq; destruct t0,t1; unfold eq in *;
  try (now inversion Heq).
  - unfold shift; simpl.
    now apply E.shift_eq_iff.
  - unfold shift in *; simpl in *.
    now rewrite <- E.shift_eq_iff in Heq.
Qed.

#[export]
Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  repeat red; intros; subst; destruct x0,y0;
  unfold eq in *; try now inversion H0.
  unfold valid; split; intros.
  - eapply E.valid_eq; eauto.
    -- reflexivity.
    -- now symmetry.
  - eapply E.valid_eq; eauto. reflexivity.
Qed.


End equality.

(** *** Shift *)
Section shift.

Variable lb k k' k'' : Level.t.
Variable t : t.

Lemma shift_refl : eq (shift lb 0 t) t.
Proof.
  destruct t; unfold shift,eq; simpl; auto.
  apply E.shift_refl. 
Qed.

Lemma shift_trans : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof. 
  destruct t; unfold eq, shift; simpl; auto.
  apply E.shift_trans.
Qed.

Lemma shift_permute : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof. 
  destruct t; unfold eq, shift; simpl; auto.
  apply E.shift_permute.
Qed.

Lemma shift_unfold : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof. 
  destruct t; unfold eq, shift; simpl; auto.
  apply E.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros Hlt Hlt'; 
  destruct t; unfold eq, shift; simpl; auto.
  now apply E.shift_unfold_1.
Qed.

End shift.

(** *** Valid *)
Section valid.

Lemma valid_weakening : forall k k' (t : t), 
  (k <= k') -> valid k t -> valid k' t.
Proof.
  intros k k' t Hle Hvt.
  destruct t; unfold valid in *; simpl in *; auto.
  apply (E.valid_weakening k k' _ Hle Hvt).
Qed.

Lemma shift_preserves_valid : forall k k' t, 
  valid k t -> valid (k + k') (shift k k' t).
Proof.
  intros k k' t Hvt.
  destruct t; unfold valid in *; simpl in *; auto.
  apply (E.shift_preserves_valid k k' _ Hvt).
Qed.

Lemma shift_preserves_valid_1 : forall lb k k' t, 
  valid k t -> valid (k + k') (shift lb k' t).
Proof.
  intros lb k k' t Hvt.
  destruct t; unfold valid in *; simpl in *; auto.
  apply (E.shift_preserves_valid_1 lb k k' _ Hvt).
Qed.

Lemma shift_preserves_valid_2 : forall lb lb' k k' t,  
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' ->
  k' - k = lb' - lb ->  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  intros lb lb' k k' t. intros.
  destruct t; unfold valid in *; simpl in *; auto.
  now apply (E.shift_preserves_valid_2 lb lb' k k').
Qed.

Lemma shift_preserves_valid_3 : forall lb lb' t, 
  lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof.  intros. eapply shift_preserves_valid_2; eauto. Qed.

Lemma shift_preserves_valid_4 : forall k t,
  valid k t -> valid k (shift k 0 t).
Proof. 
  intros; replace k with (k + 0); try lia; 
  now apply shift_preserves_valid_1.
Qed.

End valid.

End IsLvlOptET.

Module IsLvlOptETWL (E : IsLvlETWL) <: IsLvlETWL.

Include IsLvlOptET E.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; unfold eq in *; 
  try now inversion H.
  f_equal. now apply E.eq_leibniz.
Qed.

End IsLvlOptETWL.

Module IsLvlFullOptET (E : IsLvlFullET) <: IsLvlFullET.

Include IsLvlOptET E.

(** *** Definition *)
Section definition.

Definition validb (lb : Level.t) (t : t) := 
  match t with
   | Some t1 => E.validb lb t1
   | _ => true
  end.

End definition.

(** *** Equality *)
Section equality.

Lemma validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
Proof.
  repeat red; intros; destruct x0,y0; 
  unfold eq, validb in *; subst;
  try now inversion H0.
  now apply E.validb_eq.
Qed.

End equality.

(** *** Valid *)
Section valid.

Variable k : Level.t.
Variable t : t.

Lemma validb_valid : validb k t = true <-> valid k t.
Proof.
  destruct t; unfold validb,valid.
  - apply E.validb_valid.
  - split; now intros.
Qed.

Lemma validb_nvalid : validb k t = false <-> ~ valid k t.
Proof.
  intros; rewrite <- not_true_iff_false; split; intros; intro.
  - apply H; now rewrite validb_valid. 
  - apply H; now rewrite <- validb_valid.
Qed. 

End valid.
  
End IsLvlFullOptET.

Module IsLvlFullOptETWL (E : IsLvlFullETWL) <: IsLvlFullETWL.

Include IsLvlFullOptET E.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; unfold eq in *; 
  try now inversion H.
  f_equal. now apply E.eq_leibniz.
Qed.

End IsLvlFullOptETWL.

Module IsBdlLvlOptET (E : IsBdlLvlET) <: IsBdlLvlET.

Include IsLvlOptET E.

Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
Proof.
  intros lb k t Hvt; destruct t; unfold valid,eq; simpl in *; auto.
  now apply E.shift_valid_refl.
Qed.
  
End IsBdlLvlOptET.

Module IsBdlLvlOptETWL (E : IsBdlLvlETWL) <: IsBdlLvlETWL.

Include IsBdlLvlOptET E.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; unfold eq in *; 
  try now inversion H.
  f_equal. now apply E.eq_leibniz.
Qed.

End IsBdlLvlOptETWL.

Module IsBdlLvlFullOptET (E : IsBdlLvlFullET) <: IsBdlLvlFullET.

Include IsLvlFullOptET E.

Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
Proof.
  intros lb k t Hvt; destruct t; unfold valid,eq; simpl in *; auto.
  now apply E.shift_valid_refl.
Qed.

End IsBdlLvlFullOptET.


Module IsBdlLvlFullOptETWL (E : IsBdlLvlFullETWL) <: IsBdlLvlFullETWL.

Include IsBdlLvlFullOptET E.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; unfold eq in *; 
  try now inversion H.
  f_equal. now apply E.eq_leibniz.
Qed.

End IsBdlLvlFullOptETWL.