From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From DeBrLevel Require Import LevelInterface Level MapExtInterface MapExt MapLevelInterface.
From MMaps Require Import MMaps.

(** * Implementation - Map - [LvlK/ETD] *)

(** ** Leveled Map Implementation *)

Module IsLvlMapK  (Key : IsLvlOTWL)
                       (Data : EqualityType) 
                       (M : Interface.S Key)
                       (MO : MapInterface Key Data M) <: IsLvlMapKInterface Key Data M MO.

Import MO OP.P.
Include MO.

(** *** Definition *)

Definition shift_func (lb : Lvl.t) (k : Lvl.t) (key : M.key) (v : Data.t) (m : t) :=
  M.add (Key.shift lb k key) v m.

Definition valid_func (lb : Lvl.t) (k : M.key) (_v : Data.t) (P : Prop) :=
  Key.valid lb k /\ P.

Definition shift (lb : Lvl.t) (k : Lvl.t) (m : t) := M.fold (shift_func lb k) m M.empty.

Definition valid (lb : Lvl.t) (m : t) := M.fold (valid_func lb) m True.

(** *** Facts *)

#[export] Instance iff_equiv : Equivalence iff := _.
#[export] Instance logic_eq_equiv : forall A, Equivalence (@Logic.eq A) := _.

Fact valid_diamond : forall lb, Diamond iff (valid_func lb).
Proof.
  unfold Diamond, valid_func. 
  intros lb k k' _ _ a b b' Hneq Hiff1 Hiff2.
  now rewrite <- Hiff1; rewrite <- Hiff2.
Qed.

#[export] Instance valid_proper : 
  Proper (Logic.eq ==> Key.eq ==> Logic.eq ==> iff ==> iff) valid_func.
Proof.
  intros lb' lb Heq k k' HeqKey v' v _ P P' HeqP; subst.
  unfold valid_func.
  rewrite HeqP; split.
  - intros [Hk HP']; split; auto.
    eapply Key.valid_eq; eauto; try reflexivity.
    now symmetry.
  - intros [Hk HP']; split; auto.
    eapply Key.valid_eq; eauto; reflexivity.
Qed.

#[export] Instance shift_proper :
  Proper (Logic.eq ==> Logic.eq ==> Key.eq ==> Logic.eq ==> eq ==> eq) shift_func.
Proof.
  intros lb' lb Heqlb k' k Heqk key key' HeqKey v' v HeqData m m' Heqm y; subst.
  unfold shift_func; rewrite Heqm.
  destruct (Key.eq_dec (Key.shift lb k key) y) as [Heq | Hneq].
  - rewrite Heq at 1.
    rewrite Key.shift_eq in Heq; eauto; try reflexivity.
    rewrite Heq.
    now repeat rewrite add_eq_o.
  - rewrite add_neq_o; auto.
    rewrite Key.shift_eq in Hneq; eauto; try reflexivity.
    now rewrite add_neq_o; auto.
Qed.

Fact shift_diamond (lb k : Lvl.t) : Diamond eq (shift_func lb k). 
Proof.
  intros key key' v v' m m1 m2 Hneq Heqm1 Heqm2.
  rewrite <- Heqm1; rewrite <- Heqm2.
  unfold shift_func.
  rewrite add_add_2; try reflexivity.
  now rewrite <- Key.shift_eq_iff.
Qed.

(** *** extra [valid] property *)

#[export] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv  valid_diamond valid_proper
shift_proper shift_diamond Key.valid_eq : core.

Lemma valid_Empty_spec (lb : Lvl.t) (m : t) : Empty m -> valid lb m.
Proof.
  intro HEmp; unfold valid.
  rewrite fold_Empty; auto. 
Qed.

Lemma valid_Empty_iff (lb : Lvl.t) (m : t) : Empty m -> valid lb m <-> True.
Proof.
  intro HEmpty; unfold valid.
  rewrite fold_Empty with (m := m); eauto.
  reflexivity.
Qed.

Lemma valid_empty_spec (lb : Lvl.t) : valid lb M.empty.
Proof. apply valid_Empty_spec; apply empty_1. Qed.

Lemma valid_Add_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m m' : t) :
  ~ M.In x m -> Add x v m m' -> 
  Key.valid lb x /\ valid lb m <-> valid lb m'.
Proof.
  unfold valid, valid_func; intros HnIn HAdd.
  symmetry.
  rewrite fold_Add with (i := True); eauto.
  - reflexivity.
  - now apply valid_proper.
  - now apply valid_diamond.
Qed.
  
Lemma valid_add_notin_spec (lb : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  ~ M.In x m -> valid lb (M.add x v m) <-> Key.valid lb x /\ valid lb m.
Proof.
  intro HnIn.
  rewrite (valid_Add_spec _ _ v m (M.add x v m)); eauto.
  - reflexivity.
  - unfold Add; reflexivity.
Qed.

#[export] Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  intros lb' lb Heqlb m; subst.
  induction m using map_induction; intros m' Heqm.
  - repeat rewrite valid_Empty_iff; auto; try reflexivity.
    now rewrite <- Heqm.
  - rewrite  <- valid_Add_spec; eauto.
    symmetry.
    rewrite <- valid_Add_spec with (v := e); eauto.
    -- reflexivity.
    -- unfold Add in *.
       now rewrite <- Heqm.
Qed.

Lemma valid_add_in_spec  (lb : Lvl.t) (x : Key.t) (m : t) :
  M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).
Proof.
  revert x; induction m using map_induction; intros y HIn Hvm.
  - exfalso.
    destruct HIn as [z HM]. 
    now apply (H y z).
  - rewrite <- valid_Add_spec in Hvm; eauto.
    destruct Hvm as [Hvx Hvm].
    unfold Add in *.
    destruct (Key.eq_dec y x) as [Heq | Hneq].
    -- exists e. 
       rewrite H0; rewrite Heq in *.
       rewrite add_add_1.
       rewrite valid_add_notin_spec; auto. 
    -- rewrite H0 in *.
       apply add_in_iff in HIn as [Heq | HIn].
       + symmetry in Heq; contradiction.
       + apply IHm1 with (x := y) in Hvm as [v Hvm]; auto.
         exists v.
         rewrite H0; rewrite add_add_2; auto.
         rewrite valid_add_notin_spec; auto.
         rewrite add_in_iff; intros [C | C]; auto.
Qed.

Lemma valid_add_iff  (lb : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  Key.valid lb x /\ valid lb m <-> valid lb (M.add x v m).
Proof.
  induction m using map_induction.
  - rewrite valid_add_notin_spec; try reflexivity.
    apply Empty_eq_spec in H.
    rewrite H. 
    apply not_in_empty.
  - unfold Add in *; rewrite H0.
    rewrite valid_add_notin_spec; auto.
    destruct (Key.eq_dec x x0) as [Heq | Hneq].
    -- split.
       + intros [Hvx [_ Hvm]].
         rewrite <- Heq in *.
         rewrite add_shadow.
         now apply valid_add_notin_spec.
       + intro Hvm.
         rewrite Heq in *.
         rewrite add_shadow in Hvm.
         apply valid_add_notin_spec in Hvm as [Hvx Hm1]; auto.
         repeat split; auto.
         eapply Key.valid_eq; eauto; reflexivity.
    -- split.
       + intros [Hvx [Hvx0 Hvm]].
         rewrite add_add_2; auto.
         apply valid_add_notin_spec.
         ++ rewrite add_in_iff.
            intros [c | c]; contradiction.
         ++ split; auto.
            rewrite <- IHm1; auto.
       + intro Hvm.
         rewrite add_add_2 in Hvm; auto.
         apply valid_add_notin_spec in Hvm as [Hvx0 Hvm].
         ++ rewrite <- IHm1 in Hvm.
            destruct Hvm as [Hvx Hvm].
            split; auto.
         ++ rewrite add_in_iff.
            intros [c | c]; contradiction.
Qed.

Lemma valid_Add_iff  (lb : Lvl.t) (x : Key.t) (v : Data.t) (m m' : t) :
  Add x v m m' -> Key.valid lb x /\ valid lb m <-> valid lb m'.
Proof.
  unfold Add; intro HAdd.
  rewrite HAdd.
  apply valid_add_iff.
Qed.

Lemma valid_in_spec  (lb : Lvl.t) (x : Key.t) (m : t) :
  valid lb m -> M.In x m -> Key.valid lb x.
Proof.
  induction m using map_induction; intros Hvm HIn.
  - exfalso.
    apply Empty_eq_spec in H; rewrite H in *.
    apply not_in_empty in HIn; assumption.
  - unfold Add in H0; rewrite H0 in *. 
    apply valid_add_iff in Hvm as [Hvx0 Hvm1].
    apply add_in_iff in HIn as [Heq | HIn].
    -- eapply Key.valid_eq; eauto; try reflexivity.
       now symmetry.
    -- now apply IHm1.
Qed. 


(** *** extra [shift] property *)

Lemma shift_Empty_spec (lb k : Lvl.t) (m : t) :
  Empty m -> eq (shift lb k m) m.
Proof. 
  unfold shift, shift_func; intro HEmp. 
  rewrite fold_Empty with (eqA := eq) (i := M.empty); auto.
  symmetry; now apply Empty_eq_spec.
Qed.

Lemma shift_Empty_iff (lb k : Lvl.t) (m : t) :
  Empty m <-> Empty (shift lb k m).
Proof.
  split; intro HEmp.
  - now rewrite shift_Empty_spec.
  - induction m using map_induction; auto.
    exfalso. 
    apply (HEmp (Key.shift lb k x) e); apply find_2.
    unfold shift. 
    rewrite fold_Add with (eqA := eq) (i := M.empty); eauto.
    -- unfold shift_func. now rewrite add_eq_o; auto.
    -- now apply shift_proper.  
Qed.

Lemma shift_Add_spec_1 (lb k : Lvl.t) (key : M.key) (v : Data.t) (m m' : t) :
  ~ M.In key m -> Add key v m m' -> 
  eq (shift lb k m') (M.add (Key.shift lb k key) v (shift lb k m)).
Proof.
  intros HIn HAdd; unfold shift, shift_func. 
  rewrite fold_Add with (eqA := eq) (i := M.empty); eauto.
  - reflexivity.
  - now apply shift_proper.
  - now apply shift_diamond.
Qed.

Lemma shift_Add_spec_2 (lb k : Lvl.t) (key : M.key) (v : Data.t) (m m' : t) :
  ~ M.In key m -> Add key v m m' ->
  Add (Key.shift lb k key) v (shift lb k m) (shift lb k m').
Proof.
  intros HnIn HAdd. 
  apply shift_Add_spec_1 with (lb := lb) (k := k) in HAdd; auto.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  intros lb' lb Heqlb k' k Heqk m; subst.
  induction m using map_induction; intros m' Heqm.
  - repeat rewrite shift_Empty_spec; auto.
    now rewrite <- Heqm.
  - rewrite shift_Add_spec_1; eauto.
    symmetry.
    rewrite shift_Add_spec_1 with (v := e); eauto; try reflexivity.
    unfold Add in *; now rewrite <- Heqm.
Qed.

Lemma shift_add_notin_spec (lb k : Lvl.t) (x : M.key) (v : Data.t) (m : t) :
  ~ M.In x m ->  
  eq (shift lb k (M.add x v m)) (M.add (Key.shift lb k x) v (shift lb k m)).
Proof.
  intro HnIn.
  apply shift_Add_spec_1; auto.
  unfold Add; reflexivity.
Qed.

Lemma shift_add_spec (lb k : Lvl.t) (x : M.key) (v : Data.t) (m : t) :
  eq (shift lb k (M.add x v m)) 
      (M.add (Key.shift lb k x) v (shift lb k m)).
Proof.
  destruct (In_dec m x) as [HIn | HnIn].
  - revert HIn; induction m using map_induction; intro HIn.
    -- exfalso.
       apply Empty_eq_spec in H. 
       rewrite H in *.
       now apply not_in_empty in HIn.
    -- unfold Add in *; rewrite H0 in *; clear H0.
       apply add_in_iff in HIn as [Heq | HIn].
       + rewrite Heq in *.
         rewrite add_shadow.
         rewrite shift_add_notin_spec; auto.
         symmetry.
         rewrite shift_add_notin_spec; auto.
         now rewrite add_shadow.
       + destruct (Key.eq_dec x x0) as [Heq | Hneq].
         ++ exfalso; apply H.
            now rewrite <- Heq.
         ++ rewrite add_add_2; auto.
            rewrite shift_add_notin_spec.
            * rewrite IHm1; auto.
              symmetry.
              rewrite shift_add_notin_spec; auto.
              rewrite add_add_2; try reflexivity.
              now rewrite <- Key.shift_eq_iff.
            * rewrite add_in_iff; intros [c | c]; auto.
  - now apply shift_add_notin_spec.
Qed.

Lemma shift_Add_spec (lb k : Lvl.t) (key : M.key) (v : Data.t) (m m' : t) :
  Add key v m m' -> 
  eq (shift lb k m') (M.add (Key.shift lb k key) v (shift lb k m)).
Proof.
  unfold Add; intros HAdd.
  rewrite HAdd.
  apply shift_add_spec.
Qed.

Lemma shift_find_spec (lb k : Lvl.t) (key : M.key)  (m : t) : 
  M.find key m = M.find (Key.shift lb k key) (shift lb k m).
Proof.
  induction m using map_induction.
  - rewrite shift_Empty_spec; auto.
    apply Empty_eq_spec in H.
    rewrite H.
    now repeat rewrite empty_o.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add_spec; eauto.
    destruct (Key.eq_dec x key) as [Heq | Hneq].
    -- repeat rewrite add_eq_o; auto. 
       now rewrite <- Key.shift_eq_iff.
    -- repeat rewrite add_neq_o; auto. 
       now rewrite <- Key.shift_eq_iff.
Qed.

Lemma shift_in_spec_1 (lb k : Lvl.t) (key : M.key) (m : t) :
  M.In key m -> M.In (Key.shift lb k key) (shift lb k m).
Proof.
  induction m using map_induction; intro HIn.
  - exfalso.
    apply Empty_eq_spec in H.
    rewrite H in *.
    now apply not_in_empty in HIn.
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite shift_add_spec.
    rewrite add_in_iff in *.
    destruct HIn as [Heq | HIn].
    -- left. 
       now rewrite <- Key.shift_eq_iff.
    -- right; auto.
Qed.

Lemma shift_in_spec_2 (lb k : Lvl.t) (key : M.key) (m : t) :
  M.In (Key.shift lb k key) (shift lb k m) -> M.In key m.
Proof.
  induction m using map_induction; intro HIn.
  - exfalso. 
    apply shift_Empty_iff with (lb := lb) (k := k) in H.
    apply Empty_eq_spec in H.
    rewrite H in *.
    now apply not_in_empty in HIn.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_spec in *.
    rewrite add_in_iff in *.
    destruct HIn as [Heq | HIn].
    -- left. 
       now rewrite <- Key.shift_eq_iff in Heq.
    -- right; auto.
Qed.

Lemma shift_in_iff (lb k : Lvl.t) (key : M.key) (m : t) : 
  M.In key m <-> M.In (Key.shift lb k key) (shift lb k m).
Proof. 
  split; intro HIn. 
  - now apply shift_in_spec_1.
  - now apply shift_in_spec_2 in HIn.
Qed.

Lemma shift_notin_iff (lb k : Lvl.t) (key : M.key) (m : t) : 
  ~ M.In key m <-> ~ M.In (Key.shift lb k key) (shift lb k m).
Proof.
  split; intros HnIn HIn; apply HnIn.
  - rewrite shift_in_iff; eauto.
  - now rewrite <- shift_in_iff.
Qed.

Lemma shift_eq_iff (lb k : Lvl.t) (m m1 : t) : 
  eq m m1 <-> eq (shift lb k m) (shift lb k m1).
Proof.
  split; intro Heq.
  - now rewrite Heq.
  - intro y. 
    destruct (In_dec m y) as [HIn | HnIn].
    -- destruct HIn as [v HMp].
       apply find_1 in HMp. 
       rewrite HMp; symmetry.
       rewrite (shift_find_spec lb k) in *.
       now rewrite <- Heq.
    -- apply not_in_find in HnIn as n''; rewrite n''; clear n''. 
       symmetry.
       apply not_in_find. 
       rewrite shift_notin_iff in *.
       rewrite <- Heq; eauto.
Qed.

Lemma shift_Add_iff (lb k : Lvl.t) (key : M.key) (v : Data.t) (m m' : t) :
  Add key v m m' <->
  Add (Key.shift lb k key) v (shift lb k m) (shift lb k m').
Proof.
  unfold Add; split; intro HAdd.
  - rewrite HAdd. 
    now rewrite shift_add_spec.
  - rewrite <- shift_add_spec in HAdd.
    now rewrite <- shift_eq_iff in HAdd.
Qed.

Lemma shift_remove_spec (lb k : Lvl.t) (x : M.key) (t : t) :
  eq (M.remove (Key.shift lb k x) (shift lb k t)) (shift lb k (M.remove x t)).
Proof.
  induction t using map_induction.
  - assert (~ M.In (Key.shift lb k x) (shift lb k t0)).
    { 
      rewrite shift_Empty_spec; auto.
      apply Empty_eq_spec in H.
      rewrite H. 
      apply not_in_empty.
    }
    apply shift_notin_iff  in H0 as H0'.
    rewrite <- remove_id in H0; rewrite H0; clear H0.
    rewrite <- remove_id in H0'; now rewrite H0'.
  - unfold Add in H0; rewrite H0. 
    destruct (Key.eq_dec x0 x) as [Heq | Hneq].
    -- rewrite Heq. 
       rewrite shift_add_spec. 
       now repeat rewrite remove_add_1.
    -- rewrite remove_add_2; auto.
       repeat rewrite shift_add_spec.
       rewrite remove_add_2; auto.
       + now rewrite IHt1.
       + now rewrite <- Key.shift_eq_iff.
Qed.

Lemma shift_zero_refl (lb : Lvl.t) (t : t) : eq (shift lb 0 t) t.
Proof.
  induction t using map_induction.
  - now apply shift_Empty_spec.
  - rewrite shift_Add_spec; eauto. 
    rewrite IHt1.
    rewrite Key.shift_zero_refl.
    now unfold Add in *.
Qed.

Lemma shift_trans (lb k k' : Lvl.t) (t : t) :
  eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof.
  induction t using map_induction. 
  - repeat rewrite shift_Empty_spec; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_spec.
    rewrite Key.shift_trans.
    now rewrite IHt1.
Qed.

Lemma shift_permute (lb k k' : Lvl.t) (t : t) :
  eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof.
  induction t using map_induction. 
  - repeat rewrite shift_Empty_spec; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_spec.
    rewrite Key.shift_permute.
    now rewrite IHt1.
Qed.

Lemma shift_unfold (lb k k' : Lvl.t) (t : t) :
  eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof.
  induction t using map_induction. 
  - repeat rewrite shift_Empty_spec; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_spec.
    rewrite Key.shift_unfold.
    now rewrite IHt1.
Qed.

Lemma shift_unfold_1 (k k' k'' : Lvl.t) (t : t) :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros Hle Hle1.
  induction t using map_induction. 
  - repeat rewrite shift_Empty_spec; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_spec.
    rewrite Key.shift_unfold_1; auto.
    now rewrite IHt1.
Qed.

(** *** Interaction property between [valid] and [shift]  *)

Lemma valid_weakening (k k' : Lvl.t) (t : t) : (k <= k') -> valid k t -> valid k' t.
Proof.
  induction t using map_induction; intros Hle Hvt.
  - now apply valid_Empty_spec.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite <- valid_add_iff in *.
    destruct Hvt as [Hvx Hvt].
    split; auto.
    now apply Key.valid_weakening with k. 
Qed.

Lemma shift_preserves_valid_1 (lb k k' : Lvl.t) (t : t) : 
  valid k t -> valid (k + k') (shift lb k' t).
Proof.
  induction t using map_induction; intros Hvt.
  - rewrite shift_Empty_spec; auto. 
    now apply valid_Empty_spec.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_spec.
    rewrite <- valid_add_iff in *.
    destruct Hvt as [Hvx Hvt].
    split; auto.
    now apply Key.shift_preserves_valid_1. 
Qed.

Lemma shift_preserves_valid_gen (lb lb' k k' : Lvl.t) (t : t) :
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  intros Hle Hle1 Hle2 Hle3 Heq. 
  induction t using map_induction; intro Hvt.
  - rewrite shift_Empty_spec; auto.
    rewrite valid_Empty_iff; auto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    rewrite shift_add_spec.
    rewrite <- valid_add_iff in *.
    destruct Hvt as [Hvx Hvt].
    split; auto.
    apply Key.shift_preserves_valid_gen with (lb := lb); assumption.
Qed.

Lemma shift_preserves_valid_2 (lb lb' : Lvl.t) (t : t) :
  lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof. 
  intro Hle. 
  eapply shift_preserves_valid_gen; eauto.
Qed.

Lemma shift_preserves_valid (k k' : Lvl.t) (t : t) : 
  valid k t -> valid (k + k') (shift k k' t).
Proof. 
  intro Hvt. 
  now apply shift_preserves_valid_1. 
Qed.

Lemma shift_preserves_valid_zero (k : Lvl.t) (t : t) : 
  valid k t -> valid k (shift k 0 t).
Proof. 
  intro Hvt. 
  replace k with (k + 0) by lia. 
  now apply shift_preserves_valid_1. 
Qed.

End IsLvlMapK.

(** ** Bindless Leveled Map Implementation *)

Module IsBdlLvlMapK  (Key : IsBdlLvlOTWL)
                            (Data : EqualityType) 
                            (M : Interface.S Key) 
                            (MO : MapInterface Key Data M) 
                               <: IsBdlLvlMapKInterface Key Data M MO.

Include IsLvlMapK Key Data M MO.
Import MO OP.P.  

Lemma shift_valid_refl (lb k : Lvl.t) (t : t) : valid lb t -> eq (shift lb k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty_spec.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add_spec.
    rewrite <- valid_add_iff in Hvt.
    destruct Hvt as [Hvx Hvt].
    rewrite IHt1; auto. 
    now rewrite Key.shift_valid_refl; auto.
Qed.

End IsBdlLvlMapK.


(** ---- *)

(** * Make - Leveled Map [LvlK/ETD] *)


Module MakeLvlMapK (Key : IsLvlOTWL) (Data : EqualityType) <: IsLvlET.
  
  Module Raw := MMaps.OrdList.Make Key.
  Module Ext := MapET Key Data Raw.
  Include IsLvlMapK Key Data Raw Ext.
  Include OP.P.

End MakeLvlMapK.


Module MakeBdlLvlMapK (Key : IsBdlLvlOTWL) 
                                 (Data : EqualityType) <: IsBdlLvlET.
  
  Module Raw := MMaps.OrdList.Make Key.
  Module Ext := MapET Key Data Raw.
  Include IsBdlLvlMapK Key Data Raw Ext.
  Include OP.P.

End MakeBdlLvlMapK.
