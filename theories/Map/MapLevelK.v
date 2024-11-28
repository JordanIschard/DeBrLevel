From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From DeBrLevel Require Import LevelInterface Level MapExtInterface MapExt MapLevelInterface.
From MMaps Require Import MMaps.

(** * Implementation - Map - [LvlK/ETD] *)

(** ** Leveled Map Implementation *)

Module IsLvlMapK (Key : IsLvlOTWL) (Data : EqualityType) (M : Interface.S Key)
                 (MO : MapInterface Key Data M) <: IsLvlMapKInterface Key Data M MO.

Import MO OP.P.
Include MO.

(** *** Definitions *)

Definition shift_func (n: Lvl.t) (k: Lvl.t) (key: M.key) (v: Data.t) (m: t) :=
  M.add (Key.shift n k key) v m.

Definition Wf_func (n: Lvl.t) (k: M.key) (_v: Data.t) (P : Prop) := Key.Wf n k /\ P.

Definition shift (n k: Lvl.t) (m: t) := M.fold (shift_func n k) m M.empty.

Definition Wf (n: Lvl.t) (m: t) := M.fold (Wf_func n) m True.

(** *** Facts *)

#[export] Instance iff_equiv : Equivalence iff := _.

#[export] Instance logic_eq_equiv : forall A, Equivalence (@Logic.eq A) := _.

Fact Wf_func_diamond : forall n, Diamond iff (Wf_func n).
Proof.
  unfold Diamond, Wf_func. 
  intros n k p _ _ a b b' Hneq Hiff1 Hiff2.
  now rewrite <- Hiff1; rewrite <- Hiff2.
Qed.

#[export] Instance WF_func_iff : Proper (Logic.eq ==> Key.eq ==> Logic.eq ==> iff ==> iff) Wf_func.
Proof.
  intros m n Heq k p HeqKey v' v _ P n' HeqP; subst.
  unfold Wf_func.
  rewrite HeqP; split.
  - intros [Hk Hn]; split; auto.
    eapply Key.Wf_iff; eauto; try reflexivity.
    now symmetry.
  - intros [Hk Hn]; split; auto.
    eapply Key.Wf_iff; eauto; reflexivity.
Qed.

#[export] Instance shift_proper :
  Proper (Logic.eq ==> Logic.eq ==> Key.eq ==> Logic.eq ==> eq ==> eq) shift_func.
Proof.
  intros n' n Heqlb p k Heqk key key' HeqKey v' v HeqData m m' Heqm y; subst.
  unfold shift_func; rewrite Heqm.
  destruct (Key.eq_dec (Key.shift n k key) y) as [Heq | Hneq].
  - rewrite Heq at 1.
    rewrite Key.shift_eq in Heq; eauto; try reflexivity.
    rewrite Heq.
    now repeat rewrite add_eq_o.
  - rewrite add_neq_o; auto.
    rewrite Key.shift_eq in Hneq; eauto; try reflexivity.
    now rewrite add_neq_o; auto.
Qed.

Fact shift_diamond (n k: Lvl.t) : Diamond eq (shift_func n k). 
Proof.
  intros key key' v v' m m1 m2 Hneq Heqm1 Heqm2.
  rewrite <- Heqm1; rewrite <- Heqm2.
  unfold shift_func.
  rewrite add_add_2; try reflexivity.
  now rewrite <- Key.shift_eq_iff.
Qed.


#[export] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv  Wf_func_diamond WF_func_iff
                       shift_proper shift_diamond Key.Wf_iff : core.

(** *** Properties *)

(** **** [Wf] properties *)

Lemma Wf_Empty (n: Lvl.t) (m: t) : Empty m -> Wf n m.
Proof.
  intro HEmp; unfold Wf.
  rewrite fold_Empty; auto. 
Qed.

Lemma Wf_Empty_iff (n: Lvl.t) (m: t) : Empty m -> Wf n m <-> True.
Proof.
  intro HEmpty; unfold Wf.
  rewrite fold_Empty with (m := m); eauto.
  reflexivity.
Qed.

Lemma Wf_empty (n: Lvl.t) : Wf n M.empty.
Proof. apply Wf_Empty; apply empty_1. Qed.

Lemma Wf_Add (n: Lvl.t) (x: Key.t) (v: Data.t) (m m': t) :
  ~ M.In x m -> Add x v m m' -> Key.Wf n x /\ Wf n m <-> Wf n m'.
Proof.
  unfold Wf, Wf_func; intros HnIn HAdd.
  symmetry.
  rewrite fold_Add with (i := True); eauto.
  - reflexivity.
  - now apply WF_func_iff.
  - now apply Wf_func_diamond.
Qed.
  
Lemma Wf_add_notin (n: Lvl.t) (x: Key.t) (v: Data.t) (m: t) :
  ~ M.In x m -> Wf n (M.add x v m) <-> Key.Wf n x /\ Wf n m.
Proof.
  intro HnIn.
  rewrite (Wf_Add _ _ v m (M.add x v m)); eauto.
  - reflexivity.
  - unfold Add; reflexivity.
Qed.

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf.
Proof.
  intros n' n Heqlb m; subst.
  induction m using map_induction; intros m' Heqm.
  - repeat rewrite Wf_Empty_iff; auto; try reflexivity.
    now rewrite <- Heqm.
  - rewrite  <- Wf_Add; eauto.
    symmetry.
    rewrite <- Wf_Add with (v := e); eauto.
    -- reflexivity.
    -- unfold Add in *.
       now rewrite <- Heqm.
Qed.

Lemma Wf_add_in  (n: Lvl.t) (x: Key.t) (m: t) : M.In x m -> Wf n m -> exists v, Wf n (M.add x v m).
Proof.
  revert x; induction m using map_induction; intros y HIn Hvm.
  - exfalso.
    destruct HIn as [z HM]. 
    now apply (H y z).
  - rewrite <- Wf_Add in Hvm; eauto.
    destruct Hvm as [Hvx Hvm].
    unfold Add in *.
    destruct (Key.eq_dec y x) as [Heq | Hneq].
    -- exists e. 
       rewrite H0; rewrite Heq in *.
       rewrite add_add_1.
       rewrite Wf_add_notin; auto. 
    -- rewrite H0 in *.
       apply add_in_iff in HIn as [Heq | HIn].
       + symmetry in Heq; contradiction.
       + apply IHm1 with (x := y) in Hvm as [v Hvm]; auto.
         exists v.
         rewrite H0; rewrite add_add_2; auto.
         rewrite Wf_add_notin; auto.
         rewrite add_in_iff; intros [C | C]; auto.
Qed.

Lemma Wf_add_iff  (n: Lvl.t) (x: Key.t) (v: Data.t) (m: t) :
  Key.Wf n x /\ Wf n m <-> Wf n (M.add x v m).
Proof.
  induction m using map_induction.
  - rewrite Wf_add_notin; try reflexivity.
    apply Empty_eq in H.
    rewrite H. 
    apply not_in_empty.
  - unfold Add in *; rewrite H0.
    rewrite Wf_add_notin; auto.
    destruct (Key.eq_dec x x0) as [Heq | Hneq].
    -- split.
       + intros [Hvx [_ Hvm]].
         rewrite <- Heq in *.
         rewrite add_shadow.
         now apply Wf_add_notin.
       + intro Hvm.
         rewrite Heq in *.
         rewrite add_shadow in Hvm.
         apply Wf_add_notin in Hvm as [Hvx Hm1]; auto.
         repeat split; auto.
         eapply Key.Wf_iff; eauto; reflexivity.
    -- split.
       + intros [Hvx [Hvx0 Hvm]].
         rewrite add_add_2; auto.
         apply Wf_add_notin.
         ++ rewrite add_in_iff.
            intros [c | c]; contradiction.
         ++ split; auto.
            rewrite <- IHm1; auto.
       + intro Hvm.
         rewrite add_add_2 in Hvm; auto.
         apply Wf_add_notin in Hvm as [Hvx0 Hvm].
         ++ rewrite <- IHm1 in Hvm.
            destruct Hvm as [Hvx Hvm].
            split; auto.
         ++ rewrite add_in_iff.
            intros [c | c]; contradiction.
Qed.

Lemma Wf_Add_iff  (n: Lvl.t) (x: Key.t) (v: Data.t) (m m': t) :
  Add x v m m' -> Key.Wf n x /\ Wf n m <-> Wf n m'.
Proof.
  unfold Add; intro HAdd.
  rewrite HAdd.
  apply Wf_add_iff.
Qed.

Lemma Wf_in  (n: Lvl.t) (x: Key.t) (m: t) : Wf n m -> M.In x m -> Key.Wf n x.
Proof.
  induction m using map_induction; intros Hvm HIn.
  - exfalso.
    apply Empty_eq in H; rewrite H in *.
    apply not_in_empty in HIn; assumption.
  - unfold Add in H0; rewrite H0 in *. 
    apply Wf_add_iff in Hvm as [Hvx0 Hvm1].
    apply add_in_iff in HIn as [Heq | HIn].
    -- eapply Key.Wf_iff; eauto; try reflexivity.
       now symmetry.
    -- now apply IHm1.
Qed. 


(** **** extra [shift] properties *)

Lemma shift_Empty (n k: Lvl.t) (m: t) : Empty m -> eq (shift n k m) m.
Proof. 
  unfold shift, shift_func; intro HEmp. 
  rewrite fold_Empty with (eqA := eq) (i := M.empty); auto.
  symmetry; now apply Empty_eq.
Qed.

Lemma shift_Empty_iff (n k: Lvl.t) (m: t) :
  Empty m <-> Empty (shift n k m).
Proof.
  split; intro HEmp.
  - now rewrite shift_Empty.
  - induction m using map_induction; auto.
    exfalso. 
    apply (HEmp (Key.shift n k x) e); apply find_2.
    unfold shift. 
    rewrite fold_Add with (eqA := eq) (i := M.empty); eauto.
    -- unfold shift_func. now rewrite add_eq_o; auto.
    -- now apply shift_proper.  
Qed.

Lemma shift_Add_1 (n k: Lvl.t) (key : M.key) (v: Data.t) (m m': t) :
  ~ M.In key m -> Add key v m m' -> 
  eq (shift n k m') (M.add (Key.shift n k key) v (shift n k m)).
Proof.
  intros HIn HAdd; unfold shift, shift_func. 
  rewrite fold_Add with (eqA := eq) (i := M.empty); eauto.
  - reflexivity.
  - now apply shift_proper.
  - now apply shift_diamond.
Qed.

Lemma shift_Add_2 (n k: Lvl.t) (key : M.key) (v: Data.t) (m m': t) :
  ~ M.In key m -> Add key v m m' ->
  Add (Key.shift n k key) v (shift n k m) (shift n k m').
Proof.
  intros HnIn HAdd. 
  apply shift_Add_1 with (n := n) (k := k) in HAdd; auto.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  intros n' n Heqlb p k Heqk m; subst.
  induction m using map_induction; intros m' Heqm.
  - repeat rewrite shift_Empty; auto.
    now rewrite <- Heqm.
  - rewrite shift_Add_1; eauto.
    symmetry.
    rewrite shift_Add_1 with (v := e); eauto; try reflexivity.
    unfold Add in *; now rewrite <- Heqm.
Qed.

Lemma shift_add_notin (n k: Lvl.t) (x : M.key) (v: Data.t) (m: t) :
  ~ M.In x m ->  
  eq (shift n k (M.add x v m)) (M.add (Key.shift n k x) v (shift n k m)).
Proof.
  intro HnIn.
  apply shift_Add_1; auto.
  unfold Add; reflexivity.
Qed.

Lemma shift_add (n k: Lvl.t) (x : M.key) (v: Data.t) (m: t) :
  eq (shift n k (M.add x v m)) (M.add (Key.shift n k x) v (shift n k m)).
Proof.
  destruct (In_dec m x) as [HIn | HnIn].
  - revert HIn; induction m using map_induction; intro HIn.
    -- exfalso.
       apply Empty_eq in H. 
       rewrite H in *.
       now apply not_in_empty in HIn.
    -- unfold Add in *; rewrite H0 in *; clear H0.
       apply add_in_iff in HIn as [Heq | HIn].
       + rewrite Heq in *.
         rewrite add_shadow.
         rewrite shift_add_notin; auto.
         symmetry.
         rewrite shift_add_notin; auto.
         now rewrite add_shadow.
       + destruct (Key.eq_dec x x0) as [Heq | Hneq].
         ++ exfalso; apply H.
            now rewrite <- Heq.
         ++ rewrite add_add_2; auto.
            rewrite shift_add_notin.
            * rewrite IHm1; auto.
              symmetry.
              rewrite shift_add_notin; auto.
              rewrite add_add_2; try reflexivity.
              now rewrite <- Key.shift_eq_iff.
            * rewrite add_in_iff; intros [c | c]; auto.
  - now apply shift_add_notin.
Qed.

Lemma shift_Add (n k: Lvl.t) (key : M.key) (v: Data.t) (m m': t) :
  Add key v m m' -> eq (shift n k m') (M.add (Key.shift n k key) v (shift n k m)).
Proof.
  unfold Add; intros HAdd.
  rewrite HAdd.
  apply shift_add.
Qed.

Lemma shift_find (n k: Lvl.t) (key : M.key)  (m: t) : 
  M.find key m = M.find (Key.shift n k key) (shift n k m).
Proof.
  induction m using map_induction.
  - rewrite shift_Empty; auto.
    apply Empty_eq in H.
    rewrite H.
    now repeat rewrite empty_o.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add; eauto.
    destruct (Key.eq_dec x key) as [Heq | Hneq].
    -- repeat rewrite add_eq_o; auto. 
       now rewrite <- Key.shift_eq_iff.
    -- repeat rewrite add_neq_o; auto. 
       now rewrite <- Key.shift_eq_iff.
Qed.

Lemma shift_in_1 (n k: Lvl.t) (key : M.key) (m: t) :
  M.In key m -> M.In (Key.shift n k key) (shift n k m).
Proof.
  induction m using map_induction; intro HIn.
  - exfalso.
    apply Empty_eq in H.
    rewrite H in *.
    now apply not_in_empty in HIn.
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite shift_add.
    rewrite add_in_iff in *.
    destruct HIn as [Heq | HIn].
    -- left. 
       now rewrite <- Key.shift_eq_iff.
    -- right; auto.
Qed.

Lemma shift_in_2 (n k: Lvl.t) (key : M.key) (m: t) :
  M.In (Key.shift n k key) (shift n k m) -> M.In key m.
Proof.
  induction m using map_induction; intro HIn.
  - exfalso. 
    apply shift_Empty_iff with (n := n) (k := k) in H.
    apply Empty_eq in H.
    rewrite H in *.
    now apply not_in_empty in HIn.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add in *.
    rewrite add_in_iff in *.
    destruct HIn as [Heq | HIn].
    -- left. 
       now rewrite <- Key.shift_eq_iff in Heq.
    -- right; auto.
Qed.

Lemma shift_in_iff (n k: Lvl.t) (key : M.key) (m: t) : 
  M.In key m <-> M.In (Key.shift n k key) (shift n k m).
Proof. 
  split; intro HIn. 
  - now apply shift_in_1.
  - now apply shift_in_2 in HIn.
Qed.

Lemma shift_notin_iff (n k: Lvl.t) (key : M.key) (m: t) : 
  ~ M.In key m <-> ~ M.In (Key.shift n k key) (shift n k m).
Proof.
  split; intros HnIn HIn; apply HnIn.
  - rewrite shift_in_iff; eauto.
  - now rewrite <- shift_in_iff.
Qed.

Lemma shift_in_e (n k: Lvl.t) (x : M.key) (m: t) : 
  M.In x (shift n k m) -> exists (x' : M.key), x = Key.shift n k x'.
Proof.
  revert x; induction m using map_induction; intros y HIn.
  - rewrite shift_Empty in HIn; auto.
    exfalso; destruct HIn as [v HM]; now apply (H y v).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add in HIn.
    apply add_in_iff in HIn as [Heq | Hneq]; auto.
    exists x. 
    apply Key.eq_leibniz in Heq.  
    now rewrite Heq.
Qed.

Lemma shift_eq_iff (n k: Lvl.t) (m m1: t) : 
  eq m m1 <-> eq (shift n k m) (shift n k m1).
Proof.
  split; intro Heq.
  - now rewrite Heq.
  - intro y. 
    destruct (In_dec m y) as [HIn | HnIn].
    -- destruct HIn as [v HMp].
       apply find_1 in HMp. 
       rewrite HMp; symmetry.
       rewrite (shift_find n k) in *.
       now rewrite <- Heq.
    -- apply not_in_find in HnIn as m'; rewrite m'; clear m'. 
       symmetry.
       apply not_in_find. 
       rewrite shift_notin_iff in *.
       rewrite <- Heq; eauto.
Qed.

Lemma shift_Add_iff (n k: Lvl.t) (key : M.key) (v: Data.t) (m m': t) :
  Add key v m m' <->
  Add (Key.shift n k key) v (shift n k m) (shift n k m').
Proof.
  unfold Add; split; intro HAdd.
  - rewrite HAdd. 
    now rewrite shift_add.
  - rewrite <- shift_add in HAdd.
    now rewrite <- shift_eq_iff in HAdd.
Qed.

Lemma shift_remove (n k: Lvl.t) (x : M.key) (t: t) :
  eq (M.remove (Key.shift n k x) (shift n k t)) (shift n k (M.remove x t)).
Proof.
  induction t using map_induction.
  - assert (~ M.In (Key.shift n k x) (shift n k t0)).
    { 
      rewrite shift_Empty; auto.
      apply Empty_eq in H.
      rewrite H. 
      apply not_in_empty.
    }
    apply shift_notin_iff  in H0 as H0'.
    rewrite <- remove_id in H0; rewrite H0; clear H0.
    rewrite <- remove_id in H0'; now rewrite H0'.
  - unfold Add in H0; rewrite H0. 
    destruct (Key.eq_dec x0 x) as [Heq | Hneq].
    -- rewrite Heq. 
       rewrite shift_add. 
       now repeat rewrite remove_add_1.
    -- rewrite remove_add_2; auto.
       repeat rewrite shift_add.
       rewrite remove_add_2; auto.
       + now rewrite IHt1.
       + now rewrite <- Key.shift_eq_iff.
Qed.

Lemma shift_zero_refl (n: Lvl.t) (t: t) : eq (shift n 0 t) t.
Proof.
  induction t using map_induction.
  - now apply shift_Empty.
  - rewrite shift_Add; eauto. 
    rewrite IHt1.
    rewrite Key.shift_zero_refl.
    now unfold Add in *.
Qed.

Lemma shift_trans (n k p: Lvl.t) (t: t) :
  eq (shift n k (shift n p t)) (shift n (k + p) t).
Proof.
  induction t using map_induction. 
  - repeat rewrite shift_Empty; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add.
    rewrite Key.shift_trans.
    now rewrite IHt1.
Qed.

Lemma shift_permute (n k p: Lvl.t) (t: t) :
  eq (shift n k (shift n p t)) (shift n p (shift n k t)).
Proof.
  induction t using map_induction. 
  - repeat rewrite shift_Empty; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add.
    rewrite Key.shift_permute.
    now rewrite IHt1.
Qed.

Lemma shift_unfold (n k p: Lvl.t) (t: t) :
  eq (shift n (k + p) t) (shift (n + k) p (shift n k t)). 
Proof.
  induction t using map_induction. 
  - repeat rewrite shift_Empty; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add.
    rewrite Key.shift_unfold.
    now rewrite IHt1.
Qed.

Lemma shift_unfold_1 (k p n: Lvl.t) (t: t) :
  k <= p -> p <= n -> 
  eq (shift p (n - p) (shift k  (p - k) t)) (shift k (n - k) t).
Proof.
  intros Hle Hle1.
  induction t using map_induction. 
  - repeat rewrite shift_Empty; auto; reflexivity.
  - unfold Add in H0; rewrite H0; clear H0.
    repeat rewrite shift_add.
    rewrite Key.shift_unfold_1; auto.
    now rewrite IHt1.
Qed.

(** *** Interaction property between [Wf] and [shiesft]  *)

Lemma Wf_weakening (k p: Lvl.t) (t: t) : (k <= p) -> Wf k t -> Wf p t.
Proof.
  induction t using map_induction; intros Hle Hvt.
  - now apply Wf_Empty.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite <- Wf_add_iff in *.
    destruct Hvt as [Hvx Hvt].
    split; auto.
    now apply Key.Wf_weakening with k. 
Qed.

Lemma shift_preserves_wf_1 (n k p: Lvl.t) (t: t) : 
  Wf k t -> Wf (k + p) (shift n p t).
Proof.
  induction t using map_induction; intros Hvt.
  - rewrite shift_Empty; auto. 
    now apply Wf_Empty.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add.
    rewrite <- Wf_add_iff in *.
    destruct Hvt as [Hvx Hvt].
    split; auto.
    now apply Key.shift_preserves_wf_1. 
Qed.

Lemma shift_preserves_wf_gen (n m k p : Lvl.t) (t: t) :
  k <= p -> n <= m -> k <= n -> p <= m -> p - k = m - n -> 
  Wf n t -> Wf m (shift k (p - k) t).
Proof.
  intros Hle Hle1 Hle2 Hle3 Heq. 
  induction t using map_induction; intro Hvt.
  - rewrite shift_Empty; auto.
    rewrite Wf_Empty_iff; auto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    rewrite shift_add.
    rewrite <- Wf_add_iff in *.
    destruct Hvt as [Hvx Hvt].
    split; auto.
    apply Key.shift_preserves_wf_gen with (m := n); assumption.
Qed.

Lemma shift_preserves_wf_2 (n m : Lvl.t) (t: t) :
  n <= m -> Wf n t -> Wf m (shift n (m - n) t).
Proof. 
  intro Hle. 
  eapply shift_preserves_wf_gen; eauto.
Qed.

Lemma shift_preserves_wf (k p : Lvl.t) (t: t) : 
  Wf k t -> Wf (k + p) (shift k p t).
Proof. 
  intro Hvt. 
  now apply shift_preserves_wf_1. 
Qed.

Lemma shift_preserves_wf_zero (k : Lvl.t) (t: t) : 
  Wf k t -> Wf k (shift k 0 t).
Proof. 
  intro Hvt. 
  replace k with (k + 0) by lia. 
  now apply shift_preserves_wf_1. 
Qed.

End IsLvlMapK.

(** ** Bindless Leveled Map Implementation *)

Module IsBdlLvlMapK (Key : IsBdlLvlOTWL) (Data : EqualityType) (M : Interface.S Key) 
                    (MO : MapInterface Key Data M) <: IsBdlLvlMapKInterface Key Data M MO.

Include IsLvlMapK Key Data M MO.
Import MO OP.P.  

Lemma Wf_in_iff (m n: Lvl.t) (x: M.key) (t: t) :
  Wf m t -> M.In x (shift m n t) <-> M.In x t.
Proof.
  revert x; induction t using map_induction; intros y Hvo; split; intro HIn.
  - rewrite shift_Empty in HIn; auto.
  - rewrite shift_Empty; auto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply Wf_add_notin in Hvo as [Hvk Hv]; auto.
    rewrite shift_add_notin in HIn; auto.
    rewrite add_in_iff in *; destruct HIn as [Heq | HIn]; subst.
    -- left; rewrite <- Heq. 
       now rewrite Key.shift_wf_refl; auto.
    -- right. rewrite <- IHt1; eauto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply Wf_add_notin in Hvo as [Hvk Hv]; auto.
    rewrite shift_add_notin; auto.
    rewrite add_in_iff in *; destruct HIn as [Heq | HIn]; subst.
    -- left; rewrite <- Heq. 
       now rewrite Key.shift_wf_refl; auto.
    -- right. rewrite IHt1; eauto.
Qed.

Lemma shift_wf_refl (n k: Lvl.t) (t: t) : Wf n t -> eq (shift n k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add.
    rewrite <- Wf_add_iff in Hvt.
    destruct Hvt as [Hvx Hvt].
    rewrite IHt1; auto. 
    now rewrite Key.shift_wf_refl; auto.
Qed.

Lemma shift_find_Wf (n k: Lvl.t) (x: M.key) (m m': t) :
  Key.Wf n x -> M.In x m ->
  M.find x m = M.find x m' -> M.find x (shift n k m) = M.find x (shift n k m').
Proof.
  intros Hvk HIn Hfi. 
  destruct HIn as [v HfV]; apply find_1 in HfV.
  rewrite <- (Key.shift_wf_refl n k x); auto.
  now do 2 rewrite <- (shift_find n k).
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


Module MakeBdlLvlMapK (Key : IsBdlLvlOTWL) (Data : EqualityType) <: IsBdlLvlET.
  
Module Raw := MMaps.OrdList.Make Key.
Module Ext := MapET Key Data Raw.
Include IsBdlLvlMapK Key Data Raw Ext.
Include OP.P.

End MakeBdlLvlMapK.
