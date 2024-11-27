From Coq Require Import Orders Lia Bool.Bool Structures.EqualitiesFacts.
From DeBrLevel Require Import LevelInterface Level.

(** * Implementation - Option 

  Implementation of k leveled elements embedded in an optional type. We use the notation [ET] when elements satisfy [Equality Type] module, [WL] when the embedded type has an equivalent equality to the one from Coq, [FL] when the embbeded type has boolean version of [Wf] and finally [BD] when elements does not contains binders associated to levels.
*)

(** ** Leveled Option Implementation - [ET] *)
Module IsLvlOptET (E : IsLvlET) <: IsLvlET.


(** *** Definitions *)
Section definition.

Definition t := option E.t.

Definition eq (ot1 ot2 : t) :=
  match (ot1,ot2) with
   | (Some t1,Some t2) => E.eq t1 t2
   | (None,None) => True
   | _ => False
  end.

Definition shift (m n: Lvl.t) (t : t) := 
  option_map (E.shift m n) t.

Definition Wf (m : Level.t) (t : t) := 
  match t with
   | Some t1 => E.Wf m t1
   | _ => True
  end.

End definition.

(** *** Properties *)

(** **** [eq] properties *)

#[export] Instance eq_refl : Reflexive eq. 
Proof. 
  red; intros; destruct x; unfold eq; auto.
  reflexivity.
Qed.

#[export] Instance eq_sym  : Symmetric eq.
Proof. 
  red; intros; destruct x,y; unfold eq in *; auto.
  now symmetry.
Qed.

#[export] Instance eq_trans : Transitive eq.
Proof. 
  red; intros; destruct x,y,z; unfold eq in *; auto.
  - transitivity t1; auto.
  - inversion H.
Qed.

#[export] Program Instance eq_equiv : Equivalence eq.

(** **** [shift] properties *)
Section shift.

Variable m n k p : Level.t.
Variable t t1 : t.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  repeat red; intros; subst; destruct x1,y1; unfold eq in *;
  try (now inversion H1).
  unfold shift; simpl. now apply E.shift_eq.
Qed.

Lemma shift_eq_iff :
  eq t t1 <-> eq (shift m n t) (shift m n t1).
Proof.
  split; intro Heq; destruct t,t1; unfold eq in *;
  try (now inversion Heq).
  - unfold shift; simpl.
    now apply E.shift_eq_iff.
  - unfold shift in *; simpl in *.
    now rewrite <- E.shift_eq_iff in Heq.
Qed.

Lemma shift_zero_refl : eq (shift m 0 t) t.
Proof.
  destruct t; unfold shift,eq; simpl; auto.
  apply E.shift_zero_refl. 
Qed.

Lemma shift_trans : eq (shift m n (shift m k t)) (shift m (n + k) t).
Proof. 
  destruct t; unfold eq, shift; simpl; auto.
  apply E.shift_trans.
Qed.

Lemma shift_permute : eq (shift m n (shift m k t)) (shift m k (shift m n t)).
Proof. 
  destruct t; unfold eq, shift; simpl; auto.
  apply E.shift_permute.
Qed.

Lemma shift_unfold : eq (shift m (n + k) t) (shift (m + n) k (shift m n t)). 
Proof. 
  destruct t; unfold eq, shift; simpl; auto.
  apply E.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  n <= k -> k <= p -> 
  eq (shift k (p - k) (shift n  (k - n) t)) (shift n (p - n) t).
Proof.
  intros Hlt Hlt'; 
  destruct t; unfold eq, shift; simpl; auto.
  now apply E.shift_unfold_1.
Qed.

End shift.

(** **** [Wf] properties *)


#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf.
Proof.
  repeat red; intros; subst; destruct x0,y0;
  unfold eq in *; try now inversion H0.
  unfold Wf; split; intros.
  - eapply E.Wf_iff; eauto.
    -- reflexivity.
    -- now symmetry.
  - eapply E.Wf_iff; eauto. reflexivity.
Qed.

Lemma Wf_weakening (n k: Lvl.t) (t : t) : (n <= k) -> Wf n t -> Wf k t.
Proof.
  intros  Hle Hvt.
  destruct t; unfold Wf in *; simpl in *; auto.
  apply (E.Wf_weakening n k _ Hle Hvt).
Qed.

Lemma shift_preserves_wf (n k: Lvl.t) (t: t) : Wf n t -> Wf (n + k) (shift n k t).
Proof.
  intro Hvt.
  destruct t; unfold Wf in *; simpl in *; auto.
  apply (E.shift_preserves_wf n k _ Hvt).
Qed.

Lemma shift_preserves_wf_1 (m n k: Lvl.t) (t: t) : 
  Wf n t -> Wf (n + k) (shift m k t).
Proof.
  intro Hvt.
  destruct t; unfold Wf in *; simpl in *; auto.
  apply (E.shift_preserves_wf_1 m n k _ Hvt).
Qed.

Lemma shift_preserves_wf_gen (m p n k: Lvl.t) (t: t) :  
  n <= k -> m <= p -> n <= m -> k <= p ->
  k - n = p - m ->  Wf m t -> Wf p (shift n (k - n) t).
Proof.
  intros.
  destruct t; unfold Wf in *; simpl in *; auto.
  now apply (E.shift_preserves_wf_gen m p n k).
Qed.

Lemma shift_preserves_wf_2 (m p: Lvl.t) (t: t) : 
  m <= p -> Wf m t -> Wf p (shift m (p - m) t).
Proof.  intros. eapply shift_preserves_wf_gen; eauto. Qed.

Lemma shift_preserves_wf_zero (n: Lvl.t) (t: t) :
  Wf n t -> Wf n (shift n 0 t).
Proof. 
  intros; replace n with (n + 0); try lia; 
  now apply shift_preserves_wf_1.
Qed.

End IsLvlOptET.


(** ---- *)


(** ** Leveled Option Implementation - [ET] and [WL] *)
Module IsLvlOptETWL (E : IsLvlETWL) <: IsLvlETWL.

Include IsLvlOptET E.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; unfold eq in *; 
  try now inversion H.
  f_equal. now apply E.eq_leibniz.
Qed.

End IsLvlOptETWL.


(** ---- *)


(** ** Leveled Option Implementation - [ET] and [FL] *)
Module IsLvlFullOptET (E : IsLvlFullET) <: IsLvlFullET.

Include IsLvlOptET E.

(** *** Definition *)
Section definition.

Definition is_wf (m : Level.t) (t : t) := 
  match t with
   | Some t1 => E.is_wf m t1
   | _ => true
  end.

End definition.

(** *** [is_wf] properties *)
Section valid.

Variable n : Level.t.
Variable t : t.

#[export] Instance is_wf_eq : Proper (Logic.eq ==> eq ==> Logic.eq) is_wf.
Proof.
  repeat red; intros; destruct x0,y0; 
  unfold eq, is_wf in *; subst;
  try now inversion H0.
  now apply E.is_wf_eq.
Qed.

Lemma Wf_is_wf_true : Wf n t <-> is_wf n t = true.
Proof.
  destruct t; unfold is_wf,Wf.
  - apply E.Wf_is_wf_true.
  - split; now intros.
Qed.

Lemma notWf_is_wf_false :  ~ Wf n t <-> is_wf n t = false.
Proof.
  intros; rewrite <- not_true_iff_false; split; intros; intro.
  - apply H; now rewrite Wf_is_wf_true. 
  - apply H; now rewrite <- Wf_is_wf_true.
Qed. 

End valid.
  
End IsLvlFullOptET.


(** ---- *)


(** ** Leveled Option Implementation - [ET], [WL] and [FL] *)
Module IsLvlFullOptETWL (E : IsLvlFullETWL) <: IsLvlFullETWL.

Include IsLvlFullOptET E.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; unfold eq in *; 
  try now inversion H.
  f_equal. now apply E.eq_leibniz.
Qed.

End IsLvlFullOptETWL.


(** ---- *)


(** ** Leveled Option Implementation - [ET] and [BD] *)
Module IsBdlLvlOptET (E : IsBdlLvlET) <: IsBdlLvlET.

Include IsLvlOptET E.

Lemma shift_wf_refl : forall m n t, Wf m t -> eq (shift m n t) t.
Proof.
  intros m n t Hvt; destruct t; unfold Wf,eq; simpl in *; auto.
  now apply E.shift_wf_refl.
Qed.
  
End IsBdlLvlOptET.


(** ---- *)


(** ** Leveled Option Implementation - [ET], [BD] and [WL] *)
Module IsBdlLvlOptETWL (E : IsBdlLvlETWL) <: IsBdlLvlETWL.

Include IsBdlLvlOptET E.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; unfold eq in *; 
  try now inversion H.
  f_equal. now apply E.eq_leibniz.
Qed.

End IsBdlLvlOptETWL.


(** ---- *)


(** ** Leveled Option Implementation - [ET], [BD] and [FL] *)
Module IsBdlLvlFullOptET (E : IsBdlLvlFullET) <: IsBdlLvlFullET.

Include IsLvlFullOptET E.

Lemma shift_wf_refl : forall m n t, Wf m t -> eq (shift m n t) t.
Proof.
  intros m n t Hvt; destruct t; unfold Wf,eq; simpl in *; auto.
  now apply E.shift_wf_refl.
Qed.

End IsBdlLvlFullOptET.


(** ---- *)


(** ** Leveled Option Implementation - [ET], [BD], [FL] and [WL] *)
Module IsBdlLvlFullOptETWL (E : IsBdlLvlFullETWL) <: IsBdlLvlFullETWL.

Include IsBdlLvlFullOptET E.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; unfold eq in *; 
  try now inversion H.
  f_equal. now apply E.eq_leibniz.
Qed.

End IsBdlLvlFullOptETWL.