From Coq Require Import Orders Lia RelationPairs Bool.Bool Structures.EqualitiesFacts.
From DeBrLevel Require Import LevelInterface Level.

Module IsLvlPairET (O1 : IsLvlET) (O2 : IsLvlET) <: IsLvlET.


(** *** Definition *)
Section definition.
Definition t := (O1.t * O2.t)%type.

Definition eq := (O1.eq * O2.eq)%signature.

#[global]
Instance eq_equiv : Equivalence eq := _.

Definition shift (lb k : Level.t) (t : t) := 
  (O1.shift lb k (fst t),O2.shift lb k (snd t)).

Definition valid (lb : Level.t) (t : t) := 
  (O1.valid lb (fst t)) /\ ((O2.valid lb) (snd t)).

End definition.

(** *** Equality *)
Section equality.

Lemma eq_refl : Reflexive eq. 
Proof. 
  red; intros; destruct x; unfold eq; split;
  unfold RelationPairs.RelCompFun; simpl; reflexivity.
Qed.

Lemma eq_sym  : Symmetric eq.
Proof. 
  red; intros; destruct x,y; unfold eq in *; split; destruct H;
  unfold RelationPairs.RelCompFun in *; simpl in *; now symmetry.
Qed.

Lemma eq_trans   : Transitive eq.
Proof. 
  red; intros; destruct x,y,z; unfold eq in *; split; destruct H,H0;
  unfold RelationPairs.RelCompFun in *; simpl in *; etransitivity; eauto.
Qed.

Lemma shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  repeat red; intros; subst; destruct x1,y1.
  destruct H1; unfold RelationPairs.RelCompFun in *; simpl in *;
  split; try (now apply O1.shift_eq); now apply O2.shift_eq.
Qed.

Lemma shift_eq_iff : forall lb k t t1, 
  eq t t1 <-> eq (shift lb k t) (shift lb k t1).
Proof.
  split; intro Heq; destruct t0,t1,Heq; split;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  - now apply O1.shift_eq_iff.
  - now apply O2.shift_eq_iff.
  - rewrite O1.shift_eq_iff; eauto.
  - rewrite O2.shift_eq_iff; eauto.
Qed.

#[export]
Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  repeat red; intros; subst; destruct x0,y0,H0.
  unfold RelationPairs.RelCompFun in *; simpl in *.
  split; intros; destruct H1; split; simpl in *;
  try (eapply O1.valid_eq; eauto; now symmetry);
  eapply O2.valid_eq; eauto; now symmetry.
Qed.

End equality.

(** *** Shift *)
Section shift.

Variable lb k k' k'' : Level.t.
Variable t : t.

Lemma shift_refl : eq (shift lb 0 t) t.
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_refl); now apply O2.shift_refl.
Qed.

Lemma shift_trans : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_trans); now apply O2.shift_trans.
Qed.

Lemma shift_permute : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_permute); now apply O2.shift_permute.
Qed.

Lemma shift_unfold : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_unfold); now apply O2.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros Hlt Hlt'; destruct t; unfold eq,shift; simpl; split; 
  unfold RelationPairs.RelCompFun; simpl.
  - now apply O1.shift_unfold_1.
  - now apply O2.shift_unfold_1.
Qed.

End shift.

(** *** Valid *)
Section valid.

Lemma valid_weakening : forall k k' (t : t), 
  (k <= k') -> valid k t -> valid k' t.
Proof.
  intros. destruct H0,t0; split; simpl in *;
  try (eapply O1.valid_weakening; eauto); 
  eapply O2.valid_weakening; eauto.
Qed.

Lemma shift_preserves_valid : forall k k' t, 
  valid k t -> valid (k + k') (shift k k' t).
Proof.
  intros; destruct t0,H; split; simpl in *.
  - now apply O1.shift_preserves_valid.
  - now apply O2.shift_preserves_valid.
Qed.

Lemma shift_preserves_valid_1 : forall lb k k' t, 
  valid k t -> valid (k + k') (shift lb k' t).
Proof.
  intros; destruct t0,H; split; simpl in *.
  - now apply O1.shift_preserves_valid_1.
  - now apply O2.shift_preserves_valid_1.
Qed.

Lemma shift_preserves_valid_2 : forall lb lb' k k' t,  
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' ->
  k' - k = lb' - lb ->  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  intros; destruct t0,H4; split; simpl in *.
  - now apply O1.shift_preserves_valid_2 with lb.
  - now apply O2.shift_preserves_valid_2 with lb.
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

End IsLvlPairET.



(** ** Pair implementation with minimal constraints *)
Module IsLvlPairETWL (O1 : IsLvlETWL) (O2 : IsLvlETWL) <: IsLvlETWL.

Include IsLvlPairET O1 O2.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsLvlPairETWL.

(** ** Pair implementation with minimal constraints with [validb] *)
Module IsLvlFullPairET (O1 : IsLvlFullET) 
                                       (O2 : IsLvlFullET) 
                                                <: IsLvlFullET.

  Include IsLvlPairET O1 O2.

  (** *** Definition *)
  Section definition.

    Definition validb (lb : Level.t) (t : t) := 
      (O1.validb lb (fst t)) && ((O2.validb lb) (snd t)).

  End definition.

  (** *** Equality *)
  Section equality.

    Lemma validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
    Proof.
      repeat red; intros; destruct x0,y0,H0;
      unfold RelationPairs.RelCompFun,validb in *; simpl in *; f_equal.
      - eapply O1.validb_eq; eauto.
      - eapply O2.validb_eq; eauto.
    Qed.

  End equality.

  (** *** Valid *)
  Section valid.

    Variable k : Level.t.
    Variable t : t.

    Lemma validb_valid : validb k t = true <-> valid k t.
    Proof. 
      destruct t; split; unfold validb,valid; simpl;
      rewrite andb_true_iff; intros [H1 H2]; split;
      try (eapply O1.validb_valid; eauto);
      eapply O2.validb_valid; eauto.
    Qed.

    Lemma validb_nvalid : validb k t = false <-> ~ valid k t.
    Proof.
      intros; rewrite <- not_true_iff_false; split; intros; intro.
      - apply H; now rewrite validb_valid. 
      - apply H; now rewrite <- validb_valid.
    Qed. 

  End valid.
  
End IsLvlFullPairET.

(** ** Pair implementation with minimal constraints *)
Module IsLvlFullPairETWL (O1 : IsLvlFullETWL) 
                                   (O2 : IsLvlFullETWL) <: IsLvlFullETWL.

Include IsLvlFullPairET O1 O2.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsLvlFullPairETWL.

(** ** Pair implementation with fully constrained *)
Module IsBdlLvlPairET (O1 : IsBdlLvlET) 
                                         (O2 : IsBdlLvlET) 
                                                <: IsBdlLvlET.

  Include IsLvlPairET O1 O2.

  Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
  Proof.
    intros; destruct t0,H; split; unfold RelationPairs.RelCompFun;
    simpl in *; try (now apply O1.shift_valid_refl);
    now apply O2.shift_valid_refl.
  Qed.
  
End IsBdlLvlPairET.

Module IsBdlLvlPairETWL (O1 : IsBdlLvlETWL) 
                                   (O2 : IsBdlLvlETWL) <: IsBdlLvlETWL.

Include IsBdlLvlPairET O1 O2.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsBdlLvlPairETWL.

(** ** Pair implementation with fully constrained with [validb] *)
Module IsBdlLvlFullPairET (O1 : IsBdlLvlFullET) 
                                             (O2 : IsBdlLvlFullET) 
                                                    <: IsBdlLvlFullET.

  Include IsLvlFullPairET O1 O2.

  Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
  Proof.
    intros; destruct t0,H; split; unfold RelationPairs.RelCompFun;
    simpl in *; try (now apply O1.shift_valid_refl);
    now apply O2.shift_valid_refl.
  Qed.
  
End IsBdlLvlFullPairET.


Module IsBdlLvlFullPairETWL (O1 : IsBdlLvlFullETWL) 
                                   (O2 : IsBdlLvlFullETWL) <: IsBdlLvlFullETWL.

Include IsBdlLvlFullPairET O1 O2.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsBdlLvlFullPairETWL.


Module IsLvlPairOT (O1 : IsLvlOT) 
                                   (O2 : IsLvlOT) <: IsLvlOT.

Include OrdersEx.PairOrderedType O1 O2.

(** *** Definition *)
Section definition.

Definition shift (lb k : Level.t) (t : t) := 
  (O1.shift lb k (fst t),O2.shift lb k (snd t)).

Definition valid (lb : Level.t) (t : t) := 
  (O1.valid lb (fst t)) /\ ((O2.valid lb) (snd t)).

End definition.

(** *** Equality *)
Section equality.

Lemma shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  repeat red; intros; subst; destruct x1,y1.
  destruct H1; unfold RelationPairs.RelCompFun in *; simpl in *;
  split; try (now apply O1.shift_eq); now apply O2.shift_eq.
Qed.

Lemma shift_eq_iff : forall lb k t t1, 
  eq t t1 <-> eq (shift lb k t) (shift lb k t1).
Proof.
  split; intro Heq; destruct t0,t1,Heq; split;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  - now apply O1.shift_eq_iff.
  - now apply O2.shift_eq_iff.
  - rewrite O1.shift_eq_iff; eauto.
  - rewrite O2.shift_eq_iff; eauto.
Qed.

Lemma valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  repeat red; intros; subst; destruct x0,y0,H0.
  unfold RelationPairs.RelCompFun in *; simpl in *.
  split; intros; destruct H1; split; simpl in *;
  try (eapply O1.valid_eq; eauto; now symmetry);
  eapply O2.valid_eq; eauto; now symmetry.
Qed.

End equality.

(** *** Shift *)
Section shift.

Variable lb k k' k'' : Level.t.
Variable t : t.

Lemma shift_refl : eq (shift lb 0 t) t.
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_refl); now apply O2.shift_refl.
Qed.

Lemma shift_trans : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_trans); now apply O2.shift_trans.
Qed.

Lemma shift_permute : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_permute); now apply O2.shift_permute.
Qed.

Lemma shift_unfold : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_unfold); now apply O2.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros Hlt Hlt'; destruct t; unfold eq,shift; simpl; split; 
  unfold RelationPairs.RelCompFun; simpl.
  - now apply O1.shift_unfold_1.
  - now apply O2.shift_unfold_1.
Qed.

End shift.

(** *** Valid *)
Section valid.

Lemma valid_weakening : forall k k' (t : t), 
  (k <= k') -> valid k t -> valid k' t.
Proof.
  intros. destruct H0,t0; split; simpl in *;
  try (eapply O1.valid_weakening; eauto); 
  eapply O2.valid_weakening; eauto.
Qed.

Lemma shift_preserves_valid : forall k k' t, 
  valid k t -> valid (k + k') (shift k k' t).
Proof.
  intros; destruct t0,H; split; simpl in *.
  - now apply O1.shift_preserves_valid.
  - now apply O2.shift_preserves_valid.
Qed.

Lemma shift_preserves_valid_1 : forall lb k k' t, 
  valid k t -> valid (k + k') (shift lb k' t).
Proof.
  intros; destruct t0,H; split; simpl in *.
  - now apply O1.shift_preserves_valid_1.
  - now apply O2.shift_preserves_valid_1.
Qed.

Lemma shift_preserves_valid_2 : forall lb lb' k k' t,  
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' ->
  k' - k = lb' - lb ->  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  intros; destruct t0,H4; split; simpl in *.
  - now apply O1.shift_preserves_valid_2 with lb.
  - now apply O2.shift_preserves_valid_2 with lb.
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

End IsLvlPairOT.


(** ** Pair implementation with minimal constraints *)
Module IsLvlPairOTWL (O1 : IsLvlOTWL) 
                                   (O2 : IsLvlOTWL) <: IsLvlOTWL.

Include IsLvlPairOT O1 O2.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsLvlPairOTWL.

(** ** Pair implementation with minimal constraints with [validb] *)
Module IsLvlFullPairOT (O1 : IsLvlFullOT) 
                                       (O2 : IsLvlFullOT) 
                                                <: IsLvlFullOT.

  Include IsLvlPairOT O1 O2.

  (** *** Definition *)
  Section definition.

    Definition validb (lb : Level.t) (t : t) := 
      (O1.validb lb (fst t)) && ((O2.validb lb) (snd t)).

  End definition.

  (** *** Equality *)
  Section equality.

    Lemma validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
    Proof.
      repeat red; intros; destruct x0,y0,H0;
      unfold RelationPairs.RelCompFun,validb in *; simpl in *; f_equal.
      - eapply O1.validb_eq; eauto.
      - eapply O2.validb_eq; eauto.
    Qed.

  End equality.

  (** *** Valid *)
  Section valid.

    Variable k : Level.t.
    Variable t : t.

    Lemma validb_valid : validb k t = true <-> valid k t.
    Proof. 
      destruct t; split; unfold validb,valid; simpl;
      rewrite andb_true_iff; intros [H1 H2]; split;
      try (eapply O1.validb_valid; eauto);
      eapply O2.validb_valid; eauto.
    Qed.

    Lemma validb_nvalid : validb k t = false <-> ~ valid k t.
    Proof.
      intros; rewrite <- not_true_iff_false; split; intros; intro.
      - apply H; now rewrite validb_valid. 
      - apply H; now rewrite <- validb_valid.
    Qed. 

  End valid.
  
End IsLvlFullPairOT.

Module IsLvlFullPairOTWL (O1 : IsLvlFullOTWL) 
                                   (O2 : IsLvlFullOTWL) <: IsLvlFullOTWL.

Include IsLvlFullPairOT O1 O2.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsLvlFullPairOTWL.

(** ** Pair implementation with fully constrained *)
Module IsBdlLvlPairOT (O1 : IsBdlLvlOT) 
                                         (O2 : IsBdlLvlOT) 
                                                <: IsBdlLvlOT.

  Include IsLvlPairOT O1 O2.

  Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
  Proof.
    intros; destruct t0,H; split; unfold RelationPairs.RelCompFun;
    simpl in *; try (now apply O1.shift_valid_refl);
    now apply O2.shift_valid_refl.
  Qed.
  
End IsBdlLvlPairOT.

Module IsBdlLvlPairOTWL (O1 : IsBdlLvlOTWL) 
                                   (O2 : IsBdlLvlOTWL) <: IsBdlLvlOTWL.

Include IsBdlLvlPairOT O1 O2.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsBdlLvlPairOTWL.

(** ** Pair implementation with fully constrained with [validb] *)
Module IsBdlLvlFullPairOT (O1 : IsBdlLvlFullOT) 
                                             (O2 : IsBdlLvlFullOT) 
                                                    <: IsBdlLvlFullOT.

  Include IsLvlFullPairOT O1 O2.

  Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
  Proof.
    intros; destruct t0,H; split; unfold RelationPairs.RelCompFun;
    simpl in *; try (now apply O1.shift_valid_refl);
    now apply O2.shift_valid_refl.
  Qed.
  
End IsBdlLvlFullPairOT.

Module IsBdlLvlFullPairOTWL (O1 : IsBdlLvlFullOTWL) 
                                   (O2 : IsBdlLvlFullOTWL) <: IsBdlLvlFullOTWL.

Include IsBdlLvlFullPairOT O1 O2.

Lemma eq_leibniz : forall x y, eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsBdlLvlFullPairOTWL.