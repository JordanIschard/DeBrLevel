From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From DeBrLevel Require Import LevelInterface Level MapExtInterface MapExt MapLevelInterface.
From MMaps Require Import MMaps.

(** * Implementation - Map - [LvlK/LvlD] *)

(** ** Leveled Map Implementation *)
Module IsLvlMapKD  
  (Key : IsLvlOTWL) (Data : IsLvlETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsLvlMapKDInterface Key Data M MO.

Import MO OP.P.
Include MO.

(** *** Definition *)

Definition shift_func (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m : t) :=
  M.add (Key.shift lb k key) (Data.shift lb k v) m.

Definition valid_func (lb : Lvl.t) (key : Key.t) (v : Data.t) (P : Prop) :=
  (Key.valid lb key) /\ (Data.valid lb v) /\ P.

Definition shift (lb k : Lvl.t) (m : t) := M.fold (shift_func lb k) m M.empty.

Definition valid (lb : Lvl.t) (m : t) := M.fold (valid_func lb) m True.


(** *** Facts *)

#[export] Instance iff_equiv : Equivalence iff := _.
#[export] Instance logic_eq_equiv : forall A, Equivalence (@Logic.eq A) := _.

Fact valid_diamond (lb : Lvl.t) : Diamond iff (valid_func lb).
Proof.
  intros k k' v v' P P' P'' HneqK HvfP HvfP'.
  split; intros [HvK [HvD HvP]].
  - rewrite <- HvfP' in HvP.
    destruct HvP as [HvK' [HvD' HvP]].
    repeat split; auto.
    rewrite <- HvfP.
    now repeat split.
  - rewrite <- HvfP in HvP.
    destruct HvP as [HvK' [HvD' HvP]].
    repeat split; auto.
    rewrite <- HvfP'.
    now repeat split.
Qed.

#[export] Instance valid_proper : 
  Proper (Logic.eq ==> Key.eq ==> Logic.eq ==> iff ==> iff) valid_func.
Proof.
  intros lb' lb Heqlb k' k HeqK v' v HeqD P P' HeqP; subst.
  split; intros [Hvk [Hvd HvP]]. 
  - repeat split; auto.
    -- eapply Key.valid_eq; eauto. 
       + reflexivity.
       + now rewrite HeqK.
    -- now rewrite <- HeqP.
  - repeat split; auto.
    -- eapply Key.valid_eq; eauto; reflexivity. 
    -- now rewrite HeqP.
Qed.

#[export] Instance shift_proper :
  Proper (Logic.eq ==> Logic.eq ==> Key.eq ==> Logic.eq ==> eq ==> eq) shift_func.
Proof.
  intros lb' lb Heqlb k' k Heqk ke ke' HeqK v' v Heqv m m' Heqm; subst.
  unfold shift_func.
  rewrite Heqm.
  now apply Key.eq_leibniz in HeqK; subst. 
Qed.

Fact shift_diamond (lb k : Lvl.t) : Diamond eq (shift_func lb k).
Proof.
  intros ke ke' v v' P P' P'' HneqK Heq1 Heq2.
  unfold shift_func in *.
  rewrite <- Heq2; rewrite <- Heq1.
  rewrite add_add_2; try reflexivity.
  now rewrite <- Key.shift_eq_iff.
Qed.


(** *** extra [valid] property *)

#[local] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv valid_diamond valid_proper
shift_proper shift_diamond : core.

Lemma valid_Empty_spec (lb : Lvl.t) (m : t) : Empty m -> valid lb m.
Proof.
  intro HEmp; unfold valid.
  rewrite fold_Empty; auto.
Qed.

Lemma valid_Empty_iff (lb : Lvl.t) (m : t) : Empty m -> valid lb m <-> True.
Proof.
  intro HEmp; unfold valid.
  rewrite fold_Empty; auto; reflexivity.
Qed.

Lemma valid_empty_spec (lb : Lvl.t) : valid lb M.empty.
Proof.
  unfold valid; rewrite fold_Empty; auto.
  apply empty_1.
Qed.

Lemma valid_add_notin_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  ~ M.In x m -> 
  valid lb (M.add x v m) <-> Key.valid lb x /\ Data.valid lb v /\ valid lb m.
Proof.
  unfold valid in *; intro HnIn.
  rewrite fold_add; auto.
  - reflexivity.
  - now apply valid_proper.
Qed.

Lemma valid_Add_iff (lb : Lvl.t) (x : Key.t) (v : Data.t) (m m' : t) :
  ~ M.In x m -> Add x v m m' -> 
  Key.valid lb x /\ Data.valid lb v /\ valid lb m <-> valid lb m'.
Proof.
  unfold valid in *; split; intros.
  - rewrite fold_Add with (i := True); eauto.
    now apply valid_proper.
  - rewrite fold_Add with (i := True) in H1; eauto.
    now apply valid_proper.
Qed.

#[export] Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  intros lb' lb Heqlb m m' Heqm; subst.
  revert m' Heqm; induction m using map_induction; intros m' Heqm.
  - split; intro Hvm.
    -- apply valid_Empty_spec. 
       now rewrite <- Heqm.
    -- now apply valid_Empty_spec. 
  - split; intro Hvm.
    -- rewrite <- valid_Add_iff in Hvm; eauto.
       destruct Hvm as [Hvx [Hve Hvm]].
       rewrite <- valid_Add_iff; eauto.
       unfold Add in *; now rewrite H0 in *.
    -- rewrite <- valid_Add_iff with (v := e) in Hvm; eauto.
       + destruct Hvm as [Hvx [Hve Hvm]].
         rewrite <- valid_Add_iff; eauto.
       + unfold Add in *; now rewrite H0 in *.
Qed.

Lemma valid_add_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  Key.valid lb x /\ Data.valid lb v /\ valid lb m -> valid lb (M.add x v m).
Proof.
  induction m using map_induction; intros [HvK [HvD Hvm]].
  - rewrite valid_add_notin_spec; auto.
    rewrite Empty_eq_spec; auto.
    apply not_in_empty.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply valid_add_notin_spec in Hvm as [Hvx0 [Hve Hvm]]; auto.
    destruct (Key.eq_dec x x0) as [Heq | Hneq].
    -- rewrite Heq in *.
       rewrite add_shadow.
       now apply valid_add_notin_spec.
    -- rewrite add_add_2; auto.
       apply valid_add_notin_spec.
       + rewrite add_in_iff.
         intros [Heq | HIn]; auto.
       + repeat split; auto.
Qed.

Lemma valid_find_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  valid lb m -> M.find x m = Some v -> Key.valid lb x /\ Data.valid lb v.
Proof.
  induction m using map_induction; intros Hvm Hfm.
  - rewrite Empty_eq_spec in Hfm; auto.
    rewrite empty_o in Hfm.
    inversion Hfm.
  - unfold Add in *; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hvm as [Hvx0 [Hve Hvm]]; auto.
    destruct (Key.eq_dec x0 x) as [Heq | Hneq].
    -- rewrite add_eq_o in Hfm; auto.
       inversion Hfm; subst; clear Hfm.
       split; auto.
       eapply Key.valid_eq; eauto; try reflexivity.
       now symmetry.
    -- rewrite add_neq_o in Hfm; auto.
Qed. 

Lemma valid_in_spec (lb : Lvl.t) (x : Key.t) (m : t) :
  valid lb m -> M.In x m -> Key.valid lb x.
Proof.
  intros Hvm [v Hfm].
  apply find_1 in Hfm.
  now apply (valid_find_spec lb x v m Hvm) in Hfm as [Hvx _].
Qed. 

Lemma valid_add_in_spec (lb : Lvl.t) (x : Key.t) (m : t) :
  M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).
Proof.
  induction m using map_induction; intros HIn Hvm.
  - exfalso.
    rewrite Empty_eq_spec in HIn; auto.
    now apply not_in_empty in HIn.
  - rewrite <- valid_Add_iff in Hvm; eauto.
    destruct Hvm as [Hvx0 [Hve Hvm]].
    unfold Add in *; rewrite H0 in *.
    apply add_in_iff in HIn as [Heq | HIn].
    -- rewrite Heq in *.
       exists e.
       rewrite H0; rewrite add_shadow.
       apply valid_add_notin_spec; auto.
       repeat split; auto.
       eapply Key.valid_eq; eauto; try reflexivity.
       now symmetry.
    -- apply (IHm1 HIn) in Hvm as [v Hvm].
       destruct (Key.eq_dec x x0) as [Heq | Hneq].
       + rewrite Heq in *; contradiction.
       + exists v.
         rewrite H0.
         rewrite add_add_2; auto.
         apply valid_add_notin_spec; auto.
         rewrite add_in_iff; intros [Heq | HIn1]; contradiction.  
Qed.

Lemma valid_Add_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m m' : t) :
  Add x v m m' -> 
  Key.valid lb x /\ Data.valid lb v /\ valid lb m -> valid lb m'.
Proof.
  unfold Add; intros Heq Hv.
  rewrite Heq.
  now apply valid_add_spec.
Qed.


(** *** extra [shift] property *)


Lemma shift_Empty_spec (lb k : Lvl.t) (m : t) :
  Empty m -> eq (shift lb k m) m.
Proof.
  intro HEmp; unfold shift.
  rewrite fold_Empty with (eqA := eq); auto.
  symmetry. 
  now apply Empty_eq_spec. 
Qed.

Lemma shift_Add_spec_1 (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m m' : t) :
  ~ M.In key m -> Add key v m m' -> 
  eq (shift lb k m') (M.add (Key.shift lb k key) (Data.shift lb k v) (shift lb k m)).
Proof.
  intros HIn HAdd; unfold shift. 
  rewrite fold_Add with (eqA := eq) (i := M.empty); eauto.
  - reflexivity.
  - now apply shift_proper.
Qed.

Lemma shift_Empty_iff (lb k : Lvl.t) (m : t) :
  Empty m <-> Empty (shift lb k m).
Proof.
  split; intro HEmp.
  - now rewrite shift_Empty_spec.
  - revert HEmp; induction m using map_induction; intro HEmp; auto.
    rewrite shift_Add_spec_1 in HEmp; eauto.
    exfalso; apply (HEmp (Key.shift lb k x) (Data.shift lb k e)).
    now apply add_1.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  intros lb' lb Heqlb k' k Heqk m m' Heqm; subst.
  revert m' Heqm; induction m using map_induction; intros.
  - repeat rewrite shift_Empty_spec; auto.
    now rewrite <- Heqm.
  - rewrite shift_Add_spec_1; eauto.
    symmetry.
    rewrite shift_Add_spec_1; eauto; try reflexivity.
    unfold Add in *. 
    now rewrite <- Heqm.
Qed.

Lemma shift_add_notin_spec (lb k : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  ~ M.In x m ->  
  eq (shift lb k (M.add x v m)) 
      (M.add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Proof.
  intro HIn; unfold shift.
  rewrite fold_add with (eqA := eq) (i := M.empty); eauto; try reflexivity.
  now apply shift_proper.
Qed.

Lemma shift_Add_spec_2 (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m m' : t) :
  ~ M.In key m -> Add key v m m' ->
  Add (Key.shift lb k key) (Data.shift lb k v) (shift lb k m) (shift lb k m').
Proof.
  unfold Add; intros HnIn HAdd. 
  now rewrite shift_Add_spec_1; eauto.
Qed.

Lemma shift_add_spec (lb k : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  eq (shift lb k (M.add x v m)) 
      (M.add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Proof.
  destruct (In_dec m x) as [HIn | HnIn].
  - revert HIn; induction m using map_induction; intro.
    -- exfalso.
       rewrite Empty_eq_spec in *; auto.
       now apply not_in_empty in HIn.
    -- unfold Add in H0; rewrite H0 in *; clear H0.
       apply add_in_iff in HIn as [Heq | HIn].
       + rewrite Heq in *.
         rewrite add_shadow.
         repeat rewrite shift_add_notin_spec; auto.
         now rewrite add_shadow.
       + destruct (Key.eq_dec x x0) as [Heq | Hneq].
         ++ rewrite Heq in HIn. 
            contradiction.
         ++ rewrite add_add_2; auto.
            rewrite shift_add_notin_spec.
            * rewrite IHm1; auto.
              rewrite shift_add_notin_spec; auto.
              rewrite add_add_2; try reflexivity.
              rewrite <- Key.shift_eq_iff.
              intro Heq; symmetry in Heq.
              contradiction.
            * rewrite add_in_iff.
              intros [Heq | HIn0]; contradiction.
  - now apply shift_add_notin_spec.
Qed.

Lemma shift_Add_spec (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m m' : t) :
  Add key v m m' -> 
  eq (shift lb k m') (M.add (Key.shift lb k key) (Data.shift lb k v) (shift lb k m)).
Proof.
  unfold Add; intro Heq.
  rewrite Heq.
  now apply shift_add_spec. 
Qed.
  
Lemma shift_in_spec_1 (lb k : Lvl.t) (key : Key.t) (m : t) :
  M.In key m -> M.In (Key.shift lb k key) (shift lb k m).
Proof.
  induction m using map_induction; intro HIn.
  - rewrite Empty_eq_spec in HIn; auto.
    apply not_in_empty in HIn.
    now exfalso.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_spec.
    rewrite add_in_iff in *.
    destruct HIn as [Heq | HIn]; auto.
    left.
    now rewrite <- Key.shift_eq_iff.
Qed.

Lemma shift_in_spec_2 (lb k : Lvl.t) (key : Key.t) (m : t) :
  M.In (Key.shift lb k key) (shift lb k m) -> M.In key m.
Proof.
  induction m using map_induction; intro HIn.
  - rewrite shift_Empty_spec in HIn; auto.
    rewrite Empty_eq_spec in HIn; auto.
    apply not_in_empty in HIn.
    now exfalso.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_notin_spec in *; auto.
    rewrite add_in_iff in *.
    destruct HIn as [Heq | HIn]; auto.
    left.
    now rewrite <- Key.shift_eq_iff in Heq.
Qed.

Lemma shift_in_iff (lb k : Lvl.t) (key : Key.t) (m : t) : 
  M.In key m <-> M.In (Key.shift lb k key) (shift lb k m).
Proof. 
  split; intro HIn.
  - apply (shift_in_spec_1 _ _ _ _ HIn).
  - apply (shift_in_spec_2 lb k _ _ HIn).
Qed.

Lemma shift_notin_iff (lb k : Lvl.t) (key : Key.t) (m : t) : 
  ~ M.In key m <-> ~ M.In (Key.shift lb k key) (shift lb k m).
Proof.
  split; intros HnIn HIn; apply HnIn.
  - rewrite shift_in_iff; eauto.
  - now rewrite <- shift_in_iff.
Qed.

Lemma shift_find_spec_1 (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m : t) : 
  M.find key m = Some v -> 
  M.find (Key.shift lb k key) (shift lb k m) = Some (Data.shift lb k v).
Proof.
  induction m using map_induction; intro Hfm.
  - rewrite Empty_eq_spec in Hfm; auto. 
    rewrite empty_o in *.
    inversion Hfm.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add_spec.
    destruct (Key.eq_dec x key) as [Heq | Hneq].
    -- rewrite add_eq_o in *; auto.
       + now inversion Hfm.
       + now rewrite <- Key.shift_eq_iff.
    -- rewrite add_neq_o in *; auto.
       now rewrite <- Key.shift_eq_iff.
Qed.

Lemma shift_find_spec_2 (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m : t) : 
  M.find (Key.shift lb k key) (shift lb k m) = Some (Data.shift lb k v) -> 
  M.find key m = Some v.
Proof.
  induction m using map_induction; intro Hfm.
  - rewrite shift_Empty_spec in Hfm; auto.
    rewrite Empty_eq_spec in Hfm; auto.
    rewrite empty_o in Hfm.
    inversion Hfm.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_spec in Hfm.
    destruct (Key.eq_dec x key) as [Heq | Hneq].
    -- rewrite add_eq_o in *; auto.
       + inversion Hfm; f_equal. 
         apply Data.eq_leibniz. 
         eapply Data.shift_eq_iff. 
         now rewrite H1.
       + now rewrite <- Key.shift_eq_iff.
    -- rewrite add_neq_o in *; auto.
       now rewrite <- Key.shift_eq_iff.
Qed.

Lemma shift_find_iff (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m : t) : 
  M.find key m = Some v <-> 
  M.find (Key.shift lb k key) (shift lb k m) = Some (Data.shift lb k v).
Proof.
  split; intro Hfm.
  - apply (shift_find_spec_1 _ _ _ _ _ Hfm).
  - apply (shift_find_spec_2 lb k _ _ _ Hfm).
Qed.

Lemma shift_find_e_spec (lb k : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  M.find (Key.shift lb k x) (shift lb k m) = Some v -> 
  exists v', Data.eq v (Data.shift lb k v').
Proof.
  induction m using map_induction; intro Hfm.
  - rewrite shift_Empty_spec in Hfm; auto.
    rewrite Empty_eq_spec in Hfm; auto.
    rewrite empty_o in Hfm.
    inversion Hfm.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_spec in Hfm.
    destruct (Key.eq_dec (Key.shift lb k x0) (Key.shift lb k x)) as [Heq | Hneq].
    -- rewrite add_eq_o in Hfm; auto.
       inversion Hfm; subst.
       now exists e.
    -- rewrite add_neq_o in Hfm; auto.
Qed.     

Lemma shift_eq_iff (lb k : Lvl.t) (m m1 : t) : 
  eq m m1 <-> eq (shift lb k m) (shift lb k m1).
Proof.
  split; intro Heq.
  - now rewrite Heq.
  - intro y; destruct (In_dec m y) as [[v Hfm] | HnIn].
    -- apply find_1 in Hfm.
       rewrite Hfm.
       apply (shift_find_iff lb k) in Hfm.
       rewrite Heq in Hfm.
       apply shift_find_iff in Hfm.
       now symmetry.
    -- apply not_in_find in HnIn as Hneq.
       rewrite Hneq; clear Hneq.
       symmetry.
       rewrite shift_in_iff in HnIn.
       rewrite Heq in HnIn.
       rewrite <- shift_in_iff in HnIn.
       now apply not_in_find.
Qed.

Lemma shift_Add_iff (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m m' : t) :
  Add key v m m' <->
  Add (Key.shift lb k key) (Data.shift lb k v) (shift lb k m) (shift lb k m').
Proof.
  unfold Add; split; intro HAdd.
  - rewrite HAdd.
    now rewrite shift_add_spec.
  - rewrite <- shift_add_spec in HAdd.
    now rewrite <- shift_eq_iff in HAdd.
Qed.

Lemma shift_remove_spec (lb k : Lvl.t) (x : Key.t) (t : t) :
  eq (M.remove (Key.shift lb k x) (shift lb k t)) (shift lb k (M.remove x t)).
Proof.
  induction t using map_induction.
  - assert (HnIn : ~ M.In (Key.shift lb k x) (shift lb k t0)).
    { 
      apply shift_notin_iff.
      rewrite Empty_eq_spec; auto.
      now apply not_in_empty.
    }
    apply shift_notin_iff in HnIn as HnIn'.
    rewrite <- remove_id in *.
    now rewrite HnIn,HnIn'.
  - unfold Add in H0; rewrite H0; clear H0.
    destruct (Key.eq_dec x0 x) as [Heq | Hneq].
    -- symmetry.
       rewrite Heq at 1.
       rewrite shift_add_spec.
       rewrite (Key.shift_eq_iff lb k) in Heq.
       rewrite Heq.
       now repeat rewrite remove_add_1.
    -- rewrite remove_add_2; auto.
       repeat rewrite shift_add_spec; auto.
       rewrite remove_add_2.
       + now rewrite IHt1.
       + now rewrite <- Key.shift_eq_iff.
Qed.

Lemma shift_zero_refl (lb : Lvl.t) (t : t) : eq (shift lb 0 t) t.
Proof.
  induction t using map_induction.
  - now apply shift_Empty_spec.
  - unfold Add in *; rewrite H0; clear H0.
    rewrite shift_add_spec.
    rewrite IHt1.
    rewrite Key.shift_zero_refl.
    assert (Hzr : Data.shift lb 0 e = e). 
    { apply Data.eq_leibniz; apply Data.shift_zero_refl. }

    now rewrite Hzr.
Qed.

Lemma shift_trans (lb k k' : Lvl.t) (t : t) :
  eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof.
  induction t using map_induction. 
  - now repeat rewrite shift_Empty_spec; auto.
  - unfold Add in *; rewrite H0; clear H0.
    repeat rewrite shift_add_spec; auto.
    rewrite Key.shift_trans.
    rewrite IHt1.

    replace (Data.shift lb k (Data.shift lb k' e)) 
    with (Data.shift lb (k + k') e); try reflexivity.
    apply Data.eq_leibniz. 
    now rewrite Data.shift_trans.
Qed.

Lemma shift_permute (lb k k' : Lvl.t) (t : t) :
  eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof.
  induction t using map_induction.
  - now repeat rewrite shift_Empty_spec; auto.
  - unfold Add in *; rewrite H0; clear H0.
    repeat rewrite shift_add_spec; auto.
    rewrite Key.shift_permute.
    rewrite IHt1.

    replace (Data.shift lb k' (Data.shift lb k e)) 
    with (Data.shift lb k (Data.shift lb k' e)); try reflexivity.
    apply Data.eq_leibniz.
    now apply Data.shift_permute.
Qed.


Lemma shift_unfold (lb k k' : Lvl.t) (t : t) :
  eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof.
  induction t using map_induction. 
  - now repeat rewrite shift_Empty_spec; auto.
  - unfold Add in *; rewrite H0; clear H0.
    repeat rewrite shift_add_spec; auto.
    rewrite Key.shift_unfold.
    rewrite IHt1.

    replace (Data.shift (lb + k) k' (Data.shift lb k e)) 
    with (Data.shift lb (k + k') e); try reflexivity.
    apply Data.eq_leibniz. 
    now rewrite Data.shift_unfold.
Qed.

Lemma shift_unfold_1 (k k' k'' : Lvl.t) (t : t) :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros Hle Hle1; induction t using map_induction. 
  - now repeat rewrite shift_Empty_spec; auto.
  - unfold Add in *; rewrite H0; clear H0.
    repeat rewrite shift_add_spec; auto.
    rewrite Key.shift_unfold_1; auto.
    rewrite IHt1.

    replace (Data.shift k' (k'' - k') (Data.shift k (k' - k) e))
    with (Data.shift k (k'' - k) e); try reflexivity.
    apply Data.eq_leibniz. 
    now rewrite Data.shift_unfold_1.
Qed.


(** **** Interaction property between [valid] and [shift]  *)

Lemma valid_weakening (k k' : Lvl.t) (t : t) : (k <= k') -> valid k t -> valid k' t.
Proof.
  induction t using map_induction; intros Hle Hvt.
  - now apply valid_Empty_spec.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite valid_add_notin_spec in *; auto.
    destruct Hvt as [Hv [Hv' Hvt1]]. 
    repeat split; auto.
    -- now apply Key.valid_weakening with k. 
    -- now apply Data.valid_weakening with k.
Qed.

Lemma shift_preserves_valid_1 (lb k k' : Lvl.t) (t : t) : 
  valid k t -> valid (k + k') (shift lb k' t).
Proof.
  induction t using map_induction; intro Hvt.
  - rewrite shift_Empty_spec; auto.
    now rewrite valid_Empty_iff.
  - eapply valid_Add_iff in Hvt as [Hv [Hv' Hvt']]; eauto.
    rewrite shift_Add_spec; eauto.
    rewrite valid_add_notin_spec; auto.
    -- repeat split; auto.
       + now apply Key.shift_preserves_valid_1.
       + now apply Data.shift_preserves_valid_1.
    -- now apply shift_notin_iff.
Qed.

Lemma shift_preserves_valid_gen (lb lb' k k' : Lvl.t) (t : t) :
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  intros Hle Hle1 Hle2 Hle3 Heq; induction t using map_induction; intro Hvt.
  - rewrite shift_Empty_spec; auto.
    now apply valid_Empty_spec.
  - eapply valid_Add_iff in Hvt as [Hvx [Hve Hvt]]; eauto.
    rewrite shift_Add_spec; eauto.
    rewrite valid_add_notin_spec.
    -- repeat split; auto.
        + now apply Key.shift_preserves_valid_gen with (lb := lb).
        + now apply Data.shift_preserves_valid_gen with (lb := lb).
    -- now apply shift_notin_iff.
Qed.

Lemma shift_preserves_valid_2 (lb lb' : Lvl.t) (t : t) :
  lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof. 
  intros Hle Hvt. 
  apply (shift_preserves_valid_gen lb lb' lb lb'); auto.
Qed.

Lemma shift_preserves_valid (k k' : Lvl.t) (t : t) : valid k t -> valid (k + k') (shift k k' t).
Proof. intro Hvt; now apply shift_preserves_valid_1. Qed.

Lemma shift_preserves_valid_zero (k : Lvl.t) (t : t) : valid k t -> valid k (shift k 0 t).
Proof. 
  intro Hvt. 
  replace k with (k + 0) by lia. 
  now apply shift_preserves_valid_1. 
Qed.


End IsLvlMapKD.


(** ** Bindless Leveled Map Implementation *)
Module IsBdlLvlMapKD  
  (Key : IsBdlLvlOTWL) (Data : IsBdlLvlETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsBdlLvlMapKDInterface Key Data M MO.

Include IsLvlMapKD Key Data M MO.
Import MO OP.P.  

Lemma shift_valid_refl (lb k : Lvl.t) (t : t) : valid lb t -> eq (shift lb k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty_spec.
  - unfold Add in *; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hvt as [Hvx [Hve Hvt]]; auto.
    rewrite shift_add_spec.
    rewrite IHt1; auto.
    rewrite Key.shift_valid_refl; auto. 
    eapply Data.shift_valid_refl in Hve.
    apply Data.eq_leibniz in Hve. 
    now rewrite Hve.
Qed.

End IsBdlLvlMapKD.

(** ---- *)

(** * Make - Leveled Map [LvlK/LvlD] *)

Module MakeLvlMapKD (Key : IsLvlOTWL) (Data : IsLvlETWL) <: IsLvlET.
  
  Module Raw := MMaps.OrdList.Make Key.
  Module Ext := MapET Key Data Raw.
  Include IsLvlMapKD Key Data Raw Ext.
  Include OP.P.

End MakeLvlMapKD.

Module MakeBdlLvlMapKD  (Key : IsBdlLvlOTWL) (Data : IsBdlLvlETWL) <: IsBdlLvlET.
  
  Module Raw := MMaps.OrdList.Make Key.
  Module Ext := MapET Key Data Raw.
  Include IsBdlLvlMapKD Key Data Raw Ext.
  Include OP.P.

End MakeBdlLvlMapKD.