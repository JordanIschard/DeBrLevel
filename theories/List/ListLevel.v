From Coq Require Import Orders Lia RelationPairs Bool.Bool Structures.EqualitiesFacts.
From DeBrLevel Require Import LevelInterface Level.

Module IsLvlListETWL (E : IsLvlETWL) <: IsLvlETWL.


(** *** Definition *)
Section definition.

Definition t := list E.t.

Definition eq := @Logic.eq (list E.t).

Definition shift (lb k : Level.t) (t : t) := 
 List.map (E.shift lb k) t.

Definition valid (lb : Level.t) (t : t) := 
 forall x, List.In x t -> E.valid lb x.

End definition.

(** *** Equality *)
Section equality.

Lemma eq_refl : Reflexive eq. 
Proof.
  red; intros; unfold eq; reflexivity. 
Qed.

Lemma eq_sym  : Symmetric eq.
Proof. 
  red; intros; unfold eq in *. now symmetry.
Qed.

Lemma eq_trans : Transitive eq.
Proof. 
  red; intros; unfold eq in *; etransitivity; eauto.
Qed.

#[global]
Instance eq_equiv : Equivalence eq.
Proof. 
  split.
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans.
Qed.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. now unfold eq. Qed.

#[export]
Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  repeat red; intros; subst; unfold eq in *; now subst.
Qed.

Lemma shift_eq_iff : forall lb k t t1, 
  eq t t1 <-> eq (shift lb k t) (shift lb k t1).
Proof.
  split; unfold eq in *.
  - intros; now subst.
  - revert t1; induction t0.
    -- unfold shift; intros; simpl in *.
       destruct t1; auto. simpl in *.
       inversion H.
    -- intros; destruct t1; simpl in *.
       + inversion H.
       + inversion H. f_equal.
         ++ apply E.eq_leibniz. 
            rewrite E.shift_eq_iff; now rewrite H1.
         ++ now apply IHt0.
Qed.

#[export]
Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  repeat red; intros; unfold eq in *; now subst.
Qed.

End equality.

(** *** Shift *)
Section shift.

Variable lb k k' k'' : Level.t.
Variable t : t.

Lemma shift_refl : eq (shift lb 0 t) t.
Proof.
  unfold eq; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_refl. 
Qed.

Lemma shift_trans : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof. 
  unfold eq; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_trans. 
Qed.

Lemma shift_permute : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof. 
  unfold eq; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_permute. 
Qed.

Lemma shift_unfold : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof. 
  unfold eq; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  unfold eq; intros Hle Hle'; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_unfold_1. 
Qed.

End shift.

(** *** Valid *)
Section valid.

Lemma valid_weakening : forall k k' (t : t), 
  (k <= k') -> valid k t -> valid k' t.
Proof.
  intros. unfold valid in *. intros.
  apply H0 in H1. 
  eapply E.valid_weakening; eauto.
Qed.

Lemma shift_preserves_valid : forall k k' t, 
  valid k t -> valid (k + k') (shift k k' t).
Proof.
Admitted.

Lemma shift_preserves_valid_1 : forall lb k k' t, 
  valid k t -> valid (k + k') (shift lb k' t).
Proof. Admitted.

Lemma shift_preserves_valid_2 : forall lb lb' k k' t,  
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' ->
  k' - k = lb' - lb ->  valid lb t -> valid lb' (shift k (k' - k) t).
Proof. Admitted.

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

End IsLvlListETWL.


(** ** Pair implementation with minimal constraints with [validb] *)
Module IsLvlFullListETWL (E : IsLvlFullETWL) <: IsLvlFullETWL.

Include IsLvlListETWL E.

(** *** Definition *)
Section definition.

  Definition validb (lb : Level.t) (t : t) := 
    List.forallb (E.validb lb) t.

End definition.

(** *** Equality *)
Section equality.

  Lemma validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
  Proof.
    repeat red; intros. unfold eq in *; now subst.
  Qed.

End equality.

(** *** Valid *)
Section valid.

  Variable k : Level.t.
  Variable t : t.

  Lemma validb_valid : validb k t = true <-> valid k t.
  Proof. 
    split; intros; unfold valid,validb in *.
    - rewrite List.forallb_forall in H; intros.
      rewrite <- E.validb_valid.
      now apply H.
    - rewrite List.forallb_forall; intros.
      rewrite E.validb_valid.
      now apply H.
  Qed.

  Lemma validb_nvalid : validb k t = false <-> ~ valid k t.
  Proof.
    intros; rewrite <- not_true_iff_false; split; intros; intro.
    - apply H; now rewrite validb_valid. 
    - apply H; now rewrite <- validb_valid.
  Qed. 

End valid.
  
End IsLvlFullListETWL.


Module IsBdlLvlListETWL (E : IsBdlLvlETWL) <: IsBdlLvlETWL.

Include IsLvlListETWL E.

Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
Proof. Admitted.

End IsBdlLvlListETWL.

(** ** List implementation with fully constrained with [validb] *)
Module IsBdlLvlFullListETWL (E : IsBdlLvlFullETWL) <: IsBdlLvlFullET.

Include IsLvlFullListETWL E.

Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
Proof. Admitted.
  
End IsBdlLvlFullListETWL.