From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From DeBrLevel Require Import LevelInterface Level MapExtInterface MapExt MapLevelInterface.


(** * Implementation - Map - [OTK/LvlD] *)

(** ** Leveled Map Implementation *)

Module IsLvlMapD 
  (Key : OrderedTypeWithLeibniz) (Data : IsLvlETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsLvlMapDInterface Key Data M MO.

Import MO OP.P.
Include MO.            

(** *** Definition *)

Definition shift_func (lb k : Lvl.t) (key : M.key) (v : Data.t) (m : t) :=
  M.add key (Data.shift lb k v) m.

Definition valid_func (lb : Lvl.t) (k : M.key) (v : Data.t) (P : Prop) :=
  Data.valid lb v /\ P.

Definition shift (lb k : Lvl.t) (m : t) := M.fold (shift_func lb k) m M.empty.

Definition valid (lb : Lvl.t) (m : t) := M.fold (valid_func lb) m True.

(** *** Facts *)

#[export] Instance iff_equiv : Equivalence iff := _.
#[export] Instance logic_eq_equiv : forall A, Equivalence (@Logic.eq A) := _.

Fact valid_diamond (lb : Lvl.t) : Diamond iff (valid_func lb).
Proof.
  unfold Diamond; intros; split; intros [bn iu].
  -- rewrite <- H1 in iu; destruct iu; split; auto.
      rewrite <- H0; split; auto.
  -- rewrite <- H0 in iu; destruct iu; split; auto.
      rewrite <- H1; split; auto.
Qed.

#[export] Instance valid_proper :
  Proper (Logic.eq ==> Key.eq ==> Logic.eq ==> iff ==> iff) valid_func.
Proof. 
  intros lb' lb HeqLvl k k' _ v' v HeqData P' P HeqP; subst.
  split.
  - intros [Hv HP']; split; auto; now rewrite <- HeqP.
  - intros [Hv HP']; split; auto; now rewrite HeqP.
Qed.

#[export] Instance shift_proper :
  Proper (Logic.eq ==> Logic.eq ==> Key.eq ==> Logic.eq ==> eq ==> eq) shift_func.
Proof.
  intros lb' lb Heqlb k' k Heqk key key' HeqKey v' v HeqData m m' Heqm y; subst.
  unfold shift_func; rewrite Heqm.
  destruct (Key.eq_dec key y) as [Heqk | Hneqk].
  - repeat rewrite add_eq_o; auto.
    now rewrite <- HeqKey.
  - repeat rewrite add_neq_o; auto.
    now rewrite <- HeqKey.
Qed.

Fact shift_diamond (lb k : Lvl.t) : Diamond eq (shift_func lb k).
Proof.
  intros key key' v v' m m1 m2 HneqKey Heqm1 Heqm2. 
  rewrite <- Heqm1; rewrite <- Heqm2.
  unfold shift_func.
  now rewrite add_add_2.
Qed.


(** *** extra [valid] property *)

#[export] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv valid_diamond valid_proper
                       shift_proper shift_diamond : core.

Lemma valid_Empty_spec (lb : Lvl.t) (m : t) : Empty m -> valid lb m.
Proof.
  intro HEmpty; unfold valid.
  rewrite fold_Empty with (m := m); eauto.
Qed.

Lemma valid_Empty_iff (lb : Lvl.t) (m : t) : Empty m -> valid lb m <-> True.
Proof.
  intro HEmpty; unfold valid.
  rewrite fold_Empty with (m := m); eauto.
  reflexivity.
Qed.

Lemma valid_empty_spec (lb : Lvl.t) : valid lb M.empty.
Proof. apply valid_Empty_spec; apply empty_1. Qed.

Lemma valid_Add_iff (lb : Lvl.t) (x : Key.t) (v : Data.t) (m m' : t) :
  ~ M.In x m -> Add x v m m' -> 
  Data.valid lb v /\ valid lb m <-> valid lb m'.
Proof.
  unfold valid, valid_func; intros HnIn HAdd.
  symmetry.
  rewrite fold_Add with (i := True); eauto.
  - reflexivity.
  - now apply valid_proper.
  - now apply valid_diamond.
Qed.
  
#[export] Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  intros lb' lb Heqlb m m' Heqm; subst.
  revert m' Heqm; induction m using map_induction; intros m' Heqm.
  - repeat rewrite valid_Empty_iff; auto; try reflexivity.
    now rewrite <- Heqm.
  - rewrite <- valid_Add_iff; eauto.
    symmetry.
    rewrite <- valid_Add_iff with (v := e); eauto.
    -- reflexivity.
    -- unfold Add in *; now rewrite <- Heqm.
Qed.

Lemma valid_add_notin_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  ~ M.In x m -> valid lb (M.add x v m) <-> Data.valid lb v /\ valid lb m.
Proof.
  intros HnIn. 
  rewrite (valid_Add_iff lb x v m (M.add x v m) HnIn).
  - reflexivity.
  - unfold Add; reflexivity.
Qed.

Lemma valid_add_in_spec (k : Lvl.t) (x : Key.t) (m : t) :
  M.In x m -> valid k m -> exists v, valid k (M.add x v m).
Proof.
  revert x; induction m using map_induction; intros y HIn Hv.
  - exfalso.
    destruct HIn as [v HMp].
    now apply (H y v).
  - rewrite <- valid_Add_iff in Hv; eauto.
    destruct Hv as [Hve Hv].
    unfold Add in H0.
    destruct (Key.eq_dec y x) as [Heq | Hneq].
    -- exists e.
       rewrite H0 in *.
       rewrite Heq.
       rewrite add_add_1.
       rewrite valid_add_notin_spec; auto.
    -- rewrite H0 in HIn.
       apply add_in_iff in HIn as [Heq | HIn]. 
       + symmetry in Heq; contradiction.
       + apply (IHm1 y HIn) in Hv as [v' Hv].
         exists v'.
         rewrite H0; rewrite add_add_2; auto.
         apply valid_add_notin_spec; auto.
         rewrite add_in_iff. 
         intros [c | c]; auto.
Qed.

Lemma valid_add_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  Data.valid lb v /\ valid lb m -> valid lb (M.add x v m).
Proof.
  revert x v; induction m using map_induction; intros y v [Hv Hvm].
  - apply Empty_eq_spec in H; rewrite H.
    apply valid_add_notin_spec.
    -- apply not_in_empty.
    -- split; auto.
       apply valid_empty_spec.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hvm as [Hve Hvm]; auto.
    destruct (Key.eq_dec y x) as [Heq | Hneq].
    -- rewrite Heq.
       rewrite add_shadow.
       now apply valid_add_notin_spec.
    -- rewrite add_add_2; auto. 
       apply valid_add_notin_spec; auto.
       rewrite add_in_iff.
       intros [c | c]; auto.
Qed.

Lemma valid_Add_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m m' : t) :
  Add x v m m' -> 
  Data.valid lb v /\ valid lb m -> valid lb m'.
Proof. 
  intros HA Hv; unfold Add in HA.
  rewrite HA.
  now apply valid_add_spec.
Qed.

Lemma valid_find_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  valid lb m -> M.find x m = Some v -> Data.valid lb v.
Proof.
  induction m using map_induction; intros Hv Hfi.
  - exfalso.
    apply find_2 in Hfi.
    now apply (H x v).
  - unfold Add in *; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hv as [Hve Hvm1]; auto.
    rewrite add_o in Hfi.
    destruct (Key.eq_dec x0 x) as [Heq | Hneq]; auto.
    inversion Hfi; now subst.
Qed. 


(** *** extra [shift] property *)

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  intros lb' lb Heqlb k' k Heqk m; subst.
  induction m using map_induction; intros m' Heqm; unfold shift.
  - apply Empty_eq_spec in H as Heq.
    repeat rewrite fold_Empty with (eqA := eq); auto.
    -- reflexivity.
    -- rewrite <- Heqm; rewrite Heq.
       apply empty_1.
  - rewrite fold_Add with (eqA := eq); eauto; try now apply shift_proper.
    symmetry.
    rewrite fold_Add; eauto; try apply Equal_equiv.
    -- now apply shift_proper.
    -- unfold Add in H0; now rewrite <- Heqm.
Qed.

Lemma shift_Empty_spec (lb k : Lvl.t) (m : t) :
  Empty m -> eq (shift lb k m) m.
Proof. 
  intro HEmp; unfold shift.
  rewrite fold_Empty with (eqA := eq); eauto.
  symmetry; now apply Empty_eq_spec.
Qed.

Lemma shift_add_notin_spec (lb k : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  ~ M.In x m ->  
  eq (shift lb k (M.add x v m)) (M.add x (Data.shift lb k v) (shift lb k m)).
Proof.
  intro HnIn; unfold shift.
  rewrite fold_add with (eqA := eq) (i := M.empty); eauto.
  - reflexivity.
  - now apply shift_proper.
Qed.

Lemma shift_add_spec (lb k : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  eq (shift lb k (M.add x v m)) (M.add x (Data.shift lb k v) (shift lb k m)).
Proof.
  destruct (In_dec m x) as [HIn | HnIn].
  - revert HIn; induction m using map_induction; intro HIn.
    -- exfalso.
       destruct HIn as [v1 HMp].
       now apply (H x v1).
    -- unfold Add in H0; rewrite H0 in *; clear H0.
       apply add_in_iff in HIn as [Heq | HIn].
       + rewrite Heq in *; clear Heq.
         rewrite add_shadow.
         repeat rewrite shift_add_notin_spec; auto.
         now rewrite add_shadow.
       + destruct (Key.eq_dec x x0) as [Heq | Hneq].
         ++ rewrite Heq in *; clear Heq.
            contradiction.
         ++ apply IHm1 in HIn as Heq.
            rewrite add_add_2; auto.
            rewrite shift_add_notin_spec.
            * rewrite Heq.
              rewrite shift_add_notin_spec; auto.
              rewrite add_add_2.
              ** reflexivity.
              ** intro c; symmetry in c.
                 contradiction.
            * rewrite add_in_iff.
              intros [c | c]; auto.
  - now apply shift_add_notin_spec.
Qed.

Lemma shift_Add_spec (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m m' : t) :
  Add key v m m' -> 
  eq (shift lb k m') (M.add key (Data.shift lb k v) (shift lb k m)).
Proof.
  unfold Add; intro HAdd.
  rewrite HAdd.
  apply shift_add_spec.
Qed.
  
Lemma shift_in_spec_1 (lb k : Lvl.t) (key : Key.t) (m : t) :
  M.In key m -> M.In key (shift lb k m).
Proof.
  induction m using map_induction; intro HIn.
  - exfalso.
    destruct HIn as [v HMp].
    now apply (H key v).
  - apply shift_Add_spec with (lb := lb) (k := k) in H0 as H0'; auto.
    rewrite in_find in *. 
    rewrite H0',H0 in *. 
    rewrite <- in_find in *. 
    rewrite add_in_iff in *.
    destruct HIn; auto.
Qed.

Lemma shift_in_spec_2 (lb k : Lvl.t) (key : Key.t) (m : t) :
  M.In key (shift lb k m) -> M.In key m.
Proof.
  induction m using map_induction; intro HIn.
  - exfalso.
    rewrite shift_Empty_spec in HIn; auto.
    destruct HIn as [v HMp].
    now apply (H key v). 
  - rewrite shift_Add_spec in HIn; eauto.
    unfold Add in *; rewrite H0; clear H0.
    rewrite add_in_iff in *.
    destruct HIn as [Heq | HIn]; auto.
Qed.

Lemma shift_in_iff (lb k : Lvl.t) (key : Key.t) (m : t) : 
  M.In key m <-> M.In key (shift lb k m).
Proof.
  split; intro HIn.
  - apply shift_in_spec_1; auto.
  - eapply shift_in_spec_2; eauto. 
Qed.

Lemma shift_notin_iff (lb k : Lvl.t) (key : Key.t) (m : t) : 
  ~ M.In key m <-> ~ M.In key (shift lb k m).
Proof. now rewrite <- shift_in_iff. Qed.

Lemma shift_find_iff (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m : t) : 
  M.find key m = Some v <-> M.find key (shift lb k m) = Some (Data.shift lb k v).
Proof.
  induction m using map_induction.
  - split; intro Hfi.
    -- exfalso.
       apply (H key v).
       now apply find_2.
    -- exfalso.
       rewrite shift_Empty_spec in Hfi; auto.
       apply (H key (Data.shift lb k v)).
       now apply find_2.
  - rewrite shift_Add_spec with (lb := lb) (k := k); eauto.
    unfold Add in H0; rewrite H0.
    destruct (Key.eq_dec x key).
    -- repeat rewrite add_eq_o; auto. 
       split; intro Heq; inversion Heq; clear Heq; auto.
       f_equal.
       apply Data.eq_leibniz. 
       rewrite Data.shift_eq_iff. 
       now rewrite H2.
    -- split; intro Hfi.
       + rewrite add_neq_o in *; auto. 
         now rewrite <- IHm1.
       + rewrite add_neq_o in *; auto. 
         now rewrite IHm1.
Qed.

Lemma shift_Empty_iff (lb k : Lvl.t) (m : t) :
  Empty m <-> Empty (shift lb k m).
Proof.
  split; intro HEmp.
  - rewrite shift_Empty_spec; auto.
  - intros key v HMp.
    apply (HEmp key (Data.shift lb k v)).
    apply find_2.
    apply shift_find_iff.
    now apply find_1. 
Qed.

Lemma shift_eq_iff (lb k : Lvl.t) (m m1 : t) : 
  eq m m1 <-> eq (shift lb k m) (shift lb k m1).
Proof.
  split; intro Heq.
  - now rewrite Heq.
  - intro y; destruct (In_dec m y) as [[v HMp] | HnIn].
    -- apply find_1 in HMp.
       rewrite HMp; symmetry.
       rewrite shift_find_iff in HMp.
       rewrite Heq in HMp. 
       now rewrite <- shift_find_iff in HMp. 
    -- apply not_in_find in HnIn as Hnfi.
       rewrite Hnfi; symmetry; clear Hnfi. 
       rewrite shift_notin_iff in HnIn.
       apply not_in_find in HnIn as Hnfi. 
       rewrite Heq in *.
       destruct (In_dec m1 y) as [[v HMp] | HnIn1].
       + apply find_1 in HMp.
         rewrite shift_find_iff in HMp.
         rewrite Hnfi in HMp; inversion HMp.
       + now apply not_in_find.
Qed.

Lemma shift_Add_iff (lb k : Lvl.t) (key : Key.t) (v : Data.t) (m m' : t) :
  Add key v m m' <->
  Add key (Data.shift lb k v) (shift lb k m) (shift lb k m').
Proof.
  split.
  - apply shift_Add_spec.
  - unfold Add; intro HAdd.
    rewrite <- shift_add_spec in HAdd. 
    eapply shift_eq_iff; eauto.
Qed.

Lemma shift_remove_spec (lb k : Lvl.t) (x : Key.t) (t : t) :
  eq (M.remove x (shift lb k t)) (shift lb k (M.remove x t)).
Proof.
  induction t using map_induction.
  - repeat rewrite shift_Empty_spec; auto; try reflexivity.
    intros key v HMp.
    apply remove_3 in HMp.
    now apply (H key v).
  - unfold Add in H0; rewrite H0; clear H0. 
    rewrite shift_add_notin_spec; auto.
    destruct (Key.eq_dec x0 x) as [Heq | Hneq].
    -- rewrite <- Heq in *. 
       now repeat rewrite remove_add_1.
    -- repeat rewrite remove_add_2; auto.
       rewrite IHt1.
       rewrite shift_add_notin_spec; auto; try reflexivity.
       intros [v HMp].
       apply remove_3 in HMp.
       apply H; now exists v.
Qed.

Lemma shift_zero_refl (lb : Lvl.t) (t : t) : eq (shift lb 0 t) t.
Proof.
  induction t using map_induction.
  - now apply shift_Empty_spec.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add_notin_spec; auto.
    rewrite IHt1.
    assert (HeqD : (Data.shift lb 0 e) = e).
    { apply Data.eq_leibniz; now apply Data.shift_zero_refl. }
    now rewrite HeqD.
Qed.

Lemma shift_trans (lb k k' : Lvl.t) (t : t) :
  eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof.
  induction t using map_induction. 
  - repeat rewrite shift_Empty_spec; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_notin_spec; auto.
    -- replace (Data.shift lb (k + k') e) 
       with (Data.shift lb k (Data.shift lb k' e)).
       + now rewrite IHt1.
       + apply Data.eq_leibniz. 
         now apply Data.shift_trans.
    -- now rewrite <- shift_notin_iff.
Qed.

Lemma shift_permute (lb k k' : Lvl.t) (t : t) :
  eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof.
  induction t using map_induction.
  - repeat rewrite shift_Empty_spec; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_notin_spec; auto.
    -- replace (Data.shift lb k' (Data.shift lb k e)) 
       with (Data.shift lb k (Data.shift lb k' e)).
       + now rewrite IHt1.
       + apply Data.eq_leibniz; apply Data.shift_permute.
    -- now rewrite <- shift_notin_iff.
    -- now rewrite <- shift_notin_iff.
Qed.

Lemma shift_unfold (lb k k' : Lvl.t) (t : t) :
  eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof.
  induction t using map_induction.
  - repeat rewrite shift_Empty_spec; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_notin_spec; auto.
    -- replace (Data.shift (lb + k) k' (Data.shift lb k e)) 
       with (Data.shift lb (k + k') e).
       + now rewrite IHt1.
       + apply Data.eq_leibniz. apply Data.shift_unfold.
    -- now rewrite <- shift_notin_iff.  
Qed.

Lemma shift_unfold_1 (k k' k'' : Lvl.t) (t : t) :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros Hlt Hlt'; induction t using map_induction.
  - repeat rewrite shift_Empty_spec; auto; reflexivity. 
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_notin_spec; auto.
    -- replace (Data.shift k' (k'' - k') (Data.shift k (k' - k) e))
       with (Data.shift k (k'' - k) e).
       + now rewrite IHt1.
       + apply Data.eq_leibniz; now rewrite Data.shift_unfold_1.
    -- now rewrite <- shift_in_iff.
Qed.


(** *** Interaction property between [valid] and [shift]  *)


Lemma valid_weakening (k k' : Lvl.t) (t : t) : (k <= k') -> valid k t -> valid k' t.
Proof.
  induction t using map_induction; intros Hle Hvt.
  - apply (valid_Empty_spec k' t0 H).
  - rewrite <- valid_Add_iff; eauto.
    rewrite <- valid_Add_iff in Hvt; eauto.
    destruct Hvt as [Hv Hvt1]; split. 
    -- now apply Data.valid_weakening with k.
    -- now apply IHt1.
Qed.

Lemma shift_preserves_valid_1 (lb k k' : Lvl.t) (t : t) : 
  valid k t -> valid (k + k') (shift lb k' t).
Proof.
  induction t using map_induction; intro Hvt.
  - rewrite shift_Empty_spec; auto.
    apply (valid_Empty_spec _ t0 H).
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite shift_add_notin_spec; auto.
    rewrite valid_add_notin_spec in *; auto.
    -- destruct Hvt as [Hve Hvt1].
       split; auto.
       now apply Data.shift_preserves_valid_1.
    -- now apply shift_notin_iff.
Qed.

Lemma shift_preserves_valid_gen (lb lb' k k' : Lvl.t) (t : t) :
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  induction t using map_induction; intros Hle Hle1 Hle2 Hle3 Heq Hvt.
  - rewrite shift_Empty_spec; auto.
    apply (valid_Empty_spec _ _ H).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hvt as [Hve Hvt1]; auto.
    rewrite shift_add_notin_spec; auto.
    apply valid_add_notin_spec.
    -- now apply shift_notin_iff.
    -- split; auto.
       now apply Data.shift_preserves_valid_gen with (lb := lb).
Qed.

Lemma shift_preserves_valid_2 (lb lb' : Lvl.t) (t : t) :
lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof. intros; eapply shift_preserves_valid_gen; eauto. Qed.

Lemma shift_preserves_valid (k k' : Lvl.t) (t : t) : 
  valid k t -> valid (k + k') (shift k k' t).
Proof. intros; now apply shift_preserves_valid_1. Qed.

Lemma shift_preserves_valid_zero (k : Lvl.t) (t : t) : 
  valid k t -> valid k (shift k 0 t).
Proof. intros; replace k with (k + 0) by lia; now apply shift_preserves_valid_1. Qed.

End IsLvlMapD.


(** ** Bindless Leveled Map Implementation *)
Module IsBdlLvlMapD  
  (Key : OrderedTypeWithLeibniz) (Data : IsBdlLvlETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsBdlLvlMapDInterface Key Data M MO.

Include IsLvlMapD Key Data M MO.
Import MO OP.P.  

Lemma shift_valid_refl (lb k : Lvl.t) (t : t) : valid lb t -> eq (shift lb k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty_spec.
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite shift_add_notin_spec; auto. 
    apply valid_add_notin_spec in Hvt as [Hv Hv']; auto.
    eapply Data.shift_valid_refl in Hv; auto. 
    apply Data.eq_leibniz in Hv. 
    rewrite Hv.
    now rewrite IHt1.
Qed.

End IsBdlLvlMapD.

(** ---- *)

(** * Make - Leveled Map [OTK/LvlD] *)

Module MakeLvlMapD 
  (Key : OrderedTypeWithLeibniz) (Data : IsLvlETWL) <: IsLvlET.
  
  Module Raw := MMaps.OrdList.Make Key.
  Module Ext := MapET Key Data Raw.
  Include IsLvlMapD Key Data Raw Ext.
  Include OP.P.

End MakeLvlMapD.

Module MakeBdlLvlMapD 
  (Key : OrderedTypeWithLeibniz) (Data : IsBdlLvlETWL) <: IsBdlLvlET.
  
  Module Raw := MMaps.OrdList.Make Key.
  Module Ext := MapET Key Data Raw.
  Include IsBdlLvlMapD Key Data Raw Ext.
  Include OP.P.

End MakeBdlLvlMapD.