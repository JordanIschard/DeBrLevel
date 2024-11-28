From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From DeBrLevel Require Import LevelInterface Level MapExtInterface MapExt MapLevelInterface.


(** * Implementation - Map - [OTK/LvlD] *)

(** ** Leveled Map Implementation *)
Module IsLvlMapD (Key : OrderedTypeWithLeibniz) (Data : IsLvlETWL) (M : Interface.S Key) 
                 (MO : MapInterface Key Data M) <: IsLvlMapDInterface Key Data M MO.

Import MO OP.P.
Include MO.            

(** *** Definitions *)

Definition shift_func (n k: Lvl.t) (key: M.key) (v: Data.t) (m: t) :=
  M.add key (Data.shift n k v) m.

Definition Wf_func (n: Lvl.t) (k: M.key) (v: Data.t) (P: Prop) := Data.Wf n v /\ P.

Definition shift (n k: Lvl.t) (m: t) := M.fold (shift_func n k) m M.empty.

Definition Wf (n : Lvl.t) (m : t) := M.fold (Wf_func n) m True.

(** *** Facts *)

#[export] Instance iff_equiv : Equivalence iff := _.

#[export] Instance logic_eq_equiv : forall A, Equivalence (@Logic.eq A) := _.

Fact Wf_func_diamond (n : Lvl.t) : Diamond iff (Wf_func n).
Proof.
  unfold Diamond; intros; split; intros [bn iu].
  -- rewrite <- H1 in iu; destruct iu; split; auto.
      rewrite <- H0; split; auto.
  -- rewrite <- H0 in iu; destruct iu; split; auto.
      rewrite <- H1; split; auto.
Qed.

#[export] Instance Wf_func_iff : Proper (Logic.eq ==> Key.eq ==> Logic.eq ==> iff ==> iff) Wf_func.
Proof. 
  intros n' n HeqLvl k k' _ v' v HeqData P' P HeqP; subst.
  split.
  - intros [Hv HP']; split; auto; now rewrite <- HeqP.
  - intros [Hv HP']; split; auto; now rewrite HeqP.
Qed.

#[export] Instance shift_proper :
  Proper (Logic.eq ==> Logic.eq ==> Key.eq ==> Logic.eq ==> eq ==> eq) shift_func.
Proof.
  intros n' n Heqlb k' k Heqk key key' HeqKey v' v HeqData m m' Heqm y; subst.
  unfold shift_func; rewrite Heqm.
  destruct (Key.eq_dec key y) as [Heqk | Hneqk].
  - repeat rewrite add_eq_o; auto.
    now rewrite <- HeqKey.
  - repeat rewrite add_neq_o; auto.
    now rewrite <- HeqKey.
Qed.

Fact shift_diamond (n k : Lvl.t) : Diamond eq (shift_func n k).
Proof.
  intros key key' v v' m m1 m2 HneqKey Heqm1 Heqm2. 
  rewrite <- Heqm1; rewrite <- Heqm2.
  unfold shift_func.
  now rewrite add_add_2.
Qed.

#[export] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv Wf_func_diamond Wf_func_iff
                       shift_proper shift_diamond : core.

(** *** Properties *)

(** **** [Wf] properties *)

Lemma Wf_Empty (n : Lvl.t) (m : t) : Empty m -> Wf n m.
Proof.
  intro HEmpty; unfold Wf.
  rewrite fold_Empty with (m := m); eauto.
Qed.

Lemma Wf_Empty_iff (n : Lvl.t) (m : t) : Empty m -> Wf n m <-> True.
Proof.
  intro HEmpty; unfold Wf.
  rewrite fold_Empty with (m := m); eauto.
  reflexivity.
Qed.

Lemma Wf_empty (n : Lvl.t) : Wf n M.empty.
Proof. apply Wf_Empty; apply empty_1. Qed.

Lemma Wf_Add_iff (n : Lvl.t) (x : Key.t) (v : Data.t) (m m' : t) :
  ~ M.In x m -> Add x v m m' -> Data.Wf n v /\ Wf n m <-> Wf n m'.
Proof.
  unfold Wf, Wf_func; intros HnIn HAdd.
  symmetry.
  rewrite fold_Add with (i := True); eauto.
  - reflexivity.
  - now apply Wf_func_iff.
  - now apply Wf_func_diamond.
Qed.
  
#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf.
Proof.
  intros n' n Heqlb m m' Heqm; subst.
  revert m' Heqm; induction m using map_induction; intros m' Heqm.
  - repeat rewrite Wf_Empty_iff; auto; try reflexivity.
    now rewrite <- Heqm.
  - rewrite <- Wf_Add_iff; eauto.
    symmetry.
    rewrite <- Wf_Add_iff with (v := e); eauto.
    -- reflexivity.
    -- unfold Add in *; now rewrite <- Heqm.
Qed.

Lemma Wf_add_notin (n : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  ~ M.In x m -> Wf n (M.add x v m) <-> Data.Wf n v /\ Wf n m.
Proof.
  intros HnIn. 
  rewrite (Wf_Add_iff n x v m (M.add x v m) HnIn).
  - reflexivity.
  - unfold Add; reflexivity.
Qed.

Lemma Wf_add_in (k : Lvl.t) (x : Key.t) (m : t) :
  M.In x m -> Wf k m -> exists v, Wf k (M.add x v m).
Proof.
  revert x; induction m using map_induction; intros y HIn Hv.
  - exfalso.
    destruct HIn as [v HMp].
    now apply (H y v).
  - rewrite <- Wf_Add_iff in Hv; eauto.
    destruct Hv as [Hve Hv].
    unfold Add in H0.
    destruct (Key.eq_dec y x) as [Heq | Hneq].
    -- exists e.
       rewrite H0 in *.
       rewrite Heq.
       rewrite add_add_1.
       rewrite Wf_add_notin; auto.
    -- rewrite H0 in HIn.
       apply add_in_iff in HIn as [Heq | HIn]. 
       + symmetry in Heq; contradiction.
       + apply (IHm1 y HIn) in Hv as [v' Hv].
         exists v'.
         rewrite H0; rewrite add_add_2; auto.
         apply Wf_add_notin; auto.
         rewrite add_in_iff. 
         intros [c | c]; auto.
Qed.

Lemma Wf_add (n : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  Data.Wf n v /\ Wf n m -> Wf n (M.add x v m).
Proof.
  revert x v; induction m using map_induction; intros y v [Hv Hvm].
  - apply Empty_eq in H; rewrite H.
    apply Wf_add_notin.
    -- apply not_in_empty.
    -- split; auto.
       apply Wf_empty.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hvm as [Hve Hvm]; auto.
    destruct (Key.eq_dec y x) as [Heq | Hneq].
    -- rewrite Heq.
       rewrite add_shadow.
       now apply Wf_add_notin.
    -- rewrite add_add_2; auto. 
       apply Wf_add_notin; auto.
       rewrite add_in_iff.
       intros [c | c]; auto.
Qed.

Lemma Wf_Add (n : Lvl.t) (x : Key.t) (v : Data.t) (m m' : t) :
  Add x v m m' -> 
  Data.Wf n v /\ Wf n m -> Wf n m'.
Proof. 
  intros HA Hv; unfold Add in HA.
  rewrite HA.
  now apply Wf_add.
Qed.

Lemma Wf_find (n : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  Wf n m -> M.find x m = Some v -> Data.Wf n v.
Proof.
  induction m using map_induction; intros Hv Hfi.
  - exfalso.
    apply find_2 in Hfi.
    now apply (H x v).
  - unfold Add in *; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hv as [Hve Hvm1]; auto.
    rewrite add_o in Hfi.
    destruct (Key.eq_dec x0 x) as [Heq | Hneq]; auto.
    inversion Hfi; now subst.
Qed. 

Lemma Wf_update (n : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  M.In x m -> Wf n m -> Data.Wf n v -> Wf n (M.add x v m).
Proof.
  revert x v; induction m using map_induction; intros y v HIn Hvo Hvd.
  - apply Empty_eq in H; rewrite H in *.
    inversion HIn.
    apply empty_mapsto_iff in H0; contradiction.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hvo as [Hve Hvo1]; auto.
    apply add_in_iff in HIn as [Heq | HIn]; subst.
    -- rewrite Heq in *. 
       rewrite add_shadow.
       rewrite Wf_add_notin; auto.
    -- destruct (Key.eq_dec y x) as [Heq| Hneq].
       + rewrite Heq in *. contradiction.
       + rewrite add_add_2; auto.
         eapply IHm1 in Hvo1; eauto.
         rewrite Wf_add_notin; auto.
         rewrite add_in_iff; intros [Hc | Hc]; subst; contradiction.
Qed.

(** **** [shift] properties *)

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  intros n' n Heqlb k' k Heqk m; subst.
  induction m using map_induction; intros m' Heqm; unfold shift.
  - apply Empty_eq in H as Heq.
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

Lemma shift_Empty (n k : Lvl.t) (m : t) :
  Empty m -> eq (shift n k m) m.
Proof. 
  intro HEmp; unfold shift.
  rewrite fold_Empty with (eqA := eq); eauto.
  symmetry; now apply Empty_eq.
Qed.

Lemma shift_add_notin (n k : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  ~ M.In x m ->  
  eq (shift n k (M.add x v m)) (M.add x (Data.shift n k v) (shift n k m)).
Proof.
  intro HnIn; unfold shift.
  rewrite fold_add with (eqA := eq) (i := M.empty); eauto.
  - reflexivity.
  - now apply shift_proper.
Qed.

Lemma shift_add (n k : Lvl.t) (x : Key.t) (v : Data.t) (m : t) :
  eq (shift n k (M.add x v m)) (M.add x (Data.shift n k v) (shift n k m)).
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
         repeat rewrite shift_add_notin; auto.
         now rewrite add_shadow.
       + destruct (Key.eq_dec x x0) as [Heq | Hneq].
         ++ rewrite Heq in *; clear Heq.
            contradiction.
         ++ apply IHm1 in HIn as Heq.
            rewrite add_add_2; auto.
            rewrite shift_add_notin.
            * rewrite Heq.
              rewrite shift_add_notin; auto.
              rewrite add_add_2.
              ** reflexivity.
              ** intro c; symmetry in c.
                 contradiction.
            * rewrite add_in_iff.
              intros [c | c]; auto.
  - now apply shift_add_notin.
Qed.

Lemma shift_Add (n k : Lvl.t) (key : Key.t) (v : Data.t) (m m' : t) :
  Add key v m m' -> 
  eq (shift n k m') (M.add key (Data.shift n k v) (shift n k m)).
Proof.
  unfold Add; intro HAdd.
  rewrite HAdd.
  apply shift_add.
Qed.
  
Lemma shift_in_1 (n k : Lvl.t) (key : Key.t) (m : t) :
  M.In key m -> M.In key (shift n k m).
Proof.
  induction m using map_induction; intro HIn.
  - exfalso.
    destruct HIn as [v HMp].
    now apply (H key v).
  - apply shift_Add with (n := n) (k := k) in H0 as H0'; auto.
    rewrite in_find in *. 
    rewrite H0',H0 in *. 
    rewrite <- in_find in *. 
    rewrite add_in_iff in *.
    destruct HIn; auto.
Qed.

Lemma shift_in_2 (n k : Lvl.t) (key : Key.t) (m : t) :
  M.In key (shift n k m) -> M.In key m.
Proof.
  induction m using map_induction; intro HIn.
  - exfalso.
    rewrite shift_Empty in HIn; auto.
    destruct HIn as [v HMp].
    now apply (H key v). 
  - rewrite shift_Add in HIn; eauto.
    unfold Add in *; rewrite H0; clear H0.
    rewrite add_in_iff in *.
    destruct HIn as [Heq | HIn]; auto.
Qed.

Lemma shift_in_iff (n k : Lvl.t) (key : Key.t) (m : t) : 
  M.In key m <-> M.In key (shift n k m).
Proof.
  split; intro HIn.
  - apply shift_in_1; auto.
  - eapply shift_in_2; eauto. 
Qed.

Lemma shift_notin_iff (n k : Lvl.t) (key : Key.t) (m : t) : 
  ~ M.In key m <-> ~ M.In key (shift n k m).
Proof. now rewrite <- shift_in_iff. Qed.

Lemma shift_find_iff (n k : Lvl.t) (key : Key.t) (v : Data.t) (m : t) : 
  M.find key m = Some v <-> M.find key (shift n k m) = Some (Data.shift n k v).
Proof.
  induction m using map_induction.
  - split; intro Hfi.
    -- exfalso.
       apply (H key v).
       now apply find_2.
    -- exfalso.
       rewrite shift_Empty in Hfi; auto.
       apply (H key (Data.shift n k v)).
       now apply find_2.
  - rewrite shift_Add with (n := n) (k := k); eauto.
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

Lemma shift_Empty_iff (n k : Lvl.t) (m : t) :
  Empty m <-> Empty (shift n k m).
Proof.
  split; intro HEmp.
  - rewrite shift_Empty; auto.
  - intros key v HMp.
    apply (HEmp key (Data.shift n k v)).
    apply find_2.
    apply shift_find_iff.
    now apply find_1. 
Qed.

Lemma shift_eq_iff (n k : Lvl.t) (m m1 : t) : 
  eq m m1 <-> eq (shift n k m) (shift n k m1).
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

Lemma shift_Add_iff (n k : Lvl.t) (key : Key.t) (v : Data.t) (m m' : t) :
  Add key v m m' <->
  Add key (Data.shift n k v) (shift n k m) (shift n k m').
Proof.
  split.
  - apply shift_Add.
  - unfold Add; intro HAdd.
    rewrite <- shift_add in HAdd. 
    eapply shift_eq_iff; eauto.
Qed.

Lemma shift_remove (n k : Lvl.t) (x : Key.t) (t : t) :
  eq (M.remove x (shift n k t)) (shift n k (M.remove x t)).
Proof.
  induction t using map_induction.
  - repeat rewrite shift_Empty; auto; try reflexivity.
    intros key v HMp.
    apply remove_3 in HMp.
    now apply (H key v).
  - unfold Add in H0; rewrite H0; clear H0. 
    rewrite shift_add_notin; auto.
    destruct (Key.eq_dec x0 x) as [Heq | Hneq].
    -- rewrite <- Heq in *. 
       now repeat rewrite remove_add_1.
    -- repeat rewrite remove_add_2; auto.
       rewrite IHt1.
       rewrite shift_add_notin; auto; try reflexivity.
       intros [v HMp].
       apply remove_3 in HMp.
       apply H; now exists v.
Qed.

Lemma shift_zero_refl (n : Lvl.t) (t : t) : eq (shift n 0 t) t.
Proof.
  induction t using map_induction.
  - now apply shift_Empty.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add_notin; auto.
    rewrite IHt1.
    assert (HeqD : (Data.shift n 0 e) = e).
    { apply Data.eq_leibniz; now apply Data.shift_zero_refl. }
    now rewrite HeqD.
Qed.

Lemma shift_trans (n k k' : Lvl.t) (t : t) :
  eq (shift n k (shift n k' t)) (shift n (k + k') t).
Proof.
  induction t using map_induction. 
  - repeat rewrite shift_Empty; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_notin; auto.
    -- replace (Data.shift n (k + k') e) 
       with (Data.shift n k (Data.shift n k' e)).
       + now rewrite IHt1.
       + apply Data.eq_leibniz. 
         now apply Data.shift_trans.
    -- now rewrite <- shift_notin_iff.
Qed.

Lemma shift_permute (n k k' : Lvl.t) (t : t) :
  eq (shift n k (shift n k' t)) (shift n k' (shift n k t)).
Proof.
  induction t using map_induction.
  - repeat rewrite shift_Empty; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_notin; auto.
    -- replace (Data.shift n k' (Data.shift n k e)) 
       with (Data.shift n k (Data.shift n k' e)).
       + now rewrite IHt1.
       + apply Data.eq_leibniz; apply Data.shift_permute.
    -- now rewrite <- shift_notin_iff.
    -- now rewrite <- shift_notin_iff.
Qed.

Lemma shift_unfold (n k k' : Lvl.t) (t : t) :
  eq (shift n (k + k') t) (shift (n + k) k' (shift n k t)). 
Proof.
  induction t using map_induction.
  - repeat rewrite shift_Empty; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_notin; auto.
    -- replace (Data.shift (n + k) k' (Data.shift n k e)) 
       with (Data.shift n (k + k') e).
       + now rewrite IHt1.
       + apply Data.eq_leibniz. apply Data.shift_unfold.
    -- now rewrite <- shift_notin_iff.  
Qed.

Lemma shift_unfold_1 (k k' k'' : Lvl.t) (t : t) :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros Hlt Hlt'; induction t using map_induction.
  - repeat rewrite shift_Empty; auto; reflexivity. 
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add_notin; auto.
    -- replace (Data.shift k' (k'' - k') (Data.shift k (k' - k) e))
       with (Data.shift k (k'' - k) e).
       + now rewrite IHt1.
       + apply Data.eq_leibniz; now rewrite Data.shift_unfold_1.
    -- now rewrite <- shift_in_iff.
Qed.

(** **** Interaction properties between [Wf] and [shift] *)

Lemma Wf_weakening (k k' : Lvl.t) (t : t) : (k <= k') -> Wf k t -> Wf k' t.
Proof.
  induction t using map_induction; intros Hle Hvt.
  - apply (Wf_Empty k' t0 H).
  - rewrite <- Wf_Add_iff; eauto.
    rewrite <- Wf_Add_iff in Hvt; eauto.
    destruct Hvt as [Hv Hvt1]; split. 
    -- now apply Data.Wf_weakening with k.
    -- now apply IHt1.
Qed.

Lemma shift_preserves_wf_1 (n k k' : Lvl.t) (t : t) : 
  Wf k t -> Wf (k + k') (shift n k' t).
Proof.
  induction t using map_induction; intro Hvt.
  - rewrite shift_Empty; auto.
    apply (Wf_Empty _ t0 H).
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite shift_add_notin; auto.
    rewrite Wf_add_notin in *; auto.
    -- destruct Hvt as [Hve Hvt1].
       split; auto.
       now apply Data.shift_preserves_wf_1.
    -- now apply shift_notin_iff.
Qed.

Lemma shift_preserves_wf_gen (n p k m : Lvl.t) (t : t) :
  k <= m -> n <= p -> k <= n -> m <= p -> m - k = p - n -> 
  Wf n t -> Wf p (shift k (m - k) t).
Proof.
  induction t using map_induction; intros Hle Hle1 Hle2 Hle3 Heq Hvt.
  - rewrite shift_Empty; auto.
    apply (Wf_Empty _ _ H).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hvt as [Hve Hvt1]; auto.
    rewrite shift_add_notin; auto.
    apply Wf_add_notin.
    -- now apply shift_notin_iff.
    -- split; auto.
       now apply Data.shift_preserves_wf_gen with (m := n).
Qed.

Lemma shift_preserves_wf_2 (n p : Lvl.t) (t : t) :
n <= p -> Wf n t -> Wf p (shift n (p - n) t).
Proof. intros; eapply shift_preserves_wf_gen; eauto. Qed.

Lemma shift_preserves_wf (k m : Lvl.t) (t : t) : 
  Wf k t -> Wf (k + m) (shift k m t).
Proof. intros; now apply shift_preserves_wf_1. Qed.

Lemma shift_preserves_wf_zero (k : Lvl.t) (t : t) : 
  Wf k t -> Wf k (shift k 0 t).
Proof. intros; replace k with (k + 0) by lia; now apply shift_preserves_wf_1. Qed.

End IsLvlMapD.


(** ---- *)


(** ** Bindless Leveled Map Implementation *)
Module IsBdlLvlMapD (Key : OrderedTypeWithLeibniz) (Data : IsBdlLvlETWL) (M : Interface.S Key) 
                    (MO : MapInterface Key Data M) <: IsBdlLvlMapDInterface Key Data M MO.

Include IsLvlMapD Key Data M MO.
Import MO OP.P.  

Lemma shift_wf_refl (n k : Lvl.t) (t : t) : Wf n t -> eq (shift n k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty.
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite shift_add_notin; auto. 
    apply Wf_add_notin in Hvt as [Hv Hv']; auto.
    eapply Data.shift_wf_refl in Hv; auto. 
    apply Data.eq_leibniz in Hv. 
    rewrite Hv.
    now rewrite IHt1.
Qed.

End IsBdlLvlMapD.


(** ---- *)


(** * Make - Leveled Map [OTK/LvlD] *)
Module MakeLvlMapD (Key : OrderedTypeWithLeibniz) (Data : IsLvlETWL) <: IsLvlET.
  
Module Raw := MMaps.OrdList.Make Key.
Module Ext := MapET Key Data Raw.
Include IsLvlMapD Key Data Raw Ext.
Include OP.P.

End MakeLvlMapD.

Module MakeBdlLvlMapD (Key : OrderedTypeWithLeibniz) (Data : IsBdlLvlETWL) <: IsBdlLvlET.

Module Raw := MMaps.OrdList.Make Key.
Module Ext := MapET Key Data Raw.
Include IsBdlLvlMapD Key Data Raw Ext.
Include OP.P.

End MakeBdlLvlMapD.