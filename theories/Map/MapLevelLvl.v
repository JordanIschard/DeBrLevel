From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From DeBrLevel Require Import LevelInterface Level MapExtInterface 
                              MapExt MapLevelInterface MapLevelK.

(** * Implementation - Map - [LevelK/ETD] *)

(** ** Leveled Map Implementation *)

Module IsLvlMapLVL 
  (Data : EqualityType) (M : Interface.S Level) 
  (MO : MapLVLInterface Data M)  <: IsLvlMapLVLInterface Data M MO.

Include IsLvlMapK Level Data M MO.
Import MO OP.P.

Lemma shift_new_notin (lb k : Lvl.t) (t : t) : lb >= (new_key t) -> ~ M.In lb (shift lb k t).
Proof.
  induction t using map_induction; intros Hgeq.
  - rewrite shift_Empty; auto.
    rewrite Empty_eq; auto. 
    apply not_in_empty.
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite shift_add.
    rewrite new_key_add_max in Hgeq.
    rewrite add_in_iff. 
    intros [Heq | HIn]; subst.
    -- unfold Level.shift in Heq.
       destruct (Lvl.leb_spec0 lb x) as [Hle | Hnle]; lia.
    -- apply IHt1; auto; lia.
Qed.

Lemma shift_max_refl (lb k : Lvl.t) (t : t) :
  lb >= (new_key t) -> max_key (shift lb k t) = max_key t.
Proof.
  induction t using map_induction; intro Hleb.
  - rewrite shift_Empty; auto.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite new_key_add_max in *.
    rewrite shift_add.
    assert (Hle1: lb >= new_key t1) by lia.
    apply IHt1 in Hle1.
    do 2 rewrite max_key_add_max.
    rewrite Hle1; f_equal.
    rewrite Level.shift_wf_refl; auto. 
    unfold Level.Wf.
    assert (HIn : M.In x (M.add x e t1)).
    { rewrite add_in_iff; now left. }
    apply new_key_in in HIn; lia.
Qed.

Lemma shift_new_refl (lb k : Lvl.t) (t : t) :
  lb >= (new_key t) -> new_key (shift lb k t) = new_key t.
Proof.
  intro Hge; repeat rewrite new_key_unfold.
  destruct (M.is_empty t) eqn:HEmp.
  - rewrite shift_Empty.
    -- now rewrite HEmp.
    -- now apply is_empty_2.
  - destruct (M.is_empty (shift lb k t)) eqn:HEmp'.
    -- rewrite shift_Empty in HEmp'.
       + now rewrite HEmp in *.
       + apply is_empty_2 in HEmp'. 
         now rewrite <- shift_Empty_iff in HEmp'.
    -- f_equal; now apply shift_max_refl.
Qed.  

Lemma shift_max_key_gt_iff (m n x : Lvl.t) (o : t) :
  max_key o > x <-> max_key (shift m n o) > (Level.shift m n x).
Proof.
  revert x; induction o using map_induction; intro y.
  - split; intro Hmax.
    -- rewrite max_key_Empty in Hmax; auto; lia.
    -- rewrite shift_Empty in Hmax; auto.
       rewrite max_key_Empty in Hmax; auto; lia.
  - split; intro Hmax;
    unfold Add in H0; rewrite H0 in *; clear H0.
    -- rewrite shift_add. 
       rewrite max_key_add_max.
       destruct (Lvl.leb_spec0 (max_key o1) x) as [Hle | Hgt].
       + rewrite max_key_add_l in Hmax; auto.
         apply (Level.shift_gt_iff m n) in Hmax; lia.
       + rewrite max_key_add_r in Hmax by lia.
         apply IHo1 in Hmax; lia.
    -- rewrite shift_add in Hmax. 
       rewrite max_key_add_max.
       destruct (Lvl.leb_spec0 (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
       + rewrite max_key_add_l in Hmax; auto.
         apply (Level.shift_gt_iff m n) in Hmax; lia.
       + rewrite max_key_add_r in Hmax by lia.
         apply IHo1 in Hmax; lia.
Qed. 

Lemma shift_max_key_le (m n : Lvl.t) (o : t) :
  max_key o <= max_key (shift m n o).
Proof.
  induction o using map_induction.
  - now rewrite shift_Empty.
  - unfold Add in H0; rewrite H0; clear H0. 
    rewrite shift_add.
    do 2 rewrite max_key_add_max.
    assert (x <= (Level.shift m n x)) by apply Level.shift_le.
    lia.
Qed.
       
Lemma shift_new_key_le (m n : Lvl.t) (o : t) :
  new_key o <= new_key (shift m n o).
Proof.
  repeat rewrite new_key_unfold.
  destruct (M.is_empty o) eqn:Hemp; try lia.
  destruct (M.is_empty (shift m n o)) eqn:Hemp'.
  - apply is_empty_2 in Hemp'. 
    rewrite <- (shift_Empty_iff m n) in Hemp'.
    apply is_empty_1 in Hemp'.
    rewrite Hemp in Hemp'; now inversion Hemp'.
  - assert (max_key o <= max_key (shift m n o)); try lia.
    apply shift_max_key_le.
Qed.

Lemma Wf_in_iff (m n : Lvl.t) (x : M.key) (t : t) :
  Wf m t -> M.In x (shift m n t) <-> M.In x t.
Proof.
  revert x; induction t using map_induction; intros y Hvo; split; intro HIn.
  - rewrite shift_Empty in HIn; auto.
  - rewrite shift_Empty; auto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply Wf_add_notin in Hvo as [Hvk Hv]; auto.
    rewrite shift_add_notin in HIn; auto.
    rewrite add_in_iff in *; destruct HIn as [Heq | HIn]; subst.
    -- left; now rewrite Level.shift_wf_refl; auto.
    -- right. rewrite <- IHt1; eauto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply Wf_add_notin in Hvo as [Hvk Hv]; auto.
    rewrite shift_add_notin; auto.
    rewrite add_in_iff in *; destruct HIn as [Heq | HIn]; subst.
    -- left; now rewrite Level.shift_wf_refl; auto.
    -- right. rewrite IHt1; eauto.
Qed.

Lemma shift_find_Wf (lb k : Lvl.t) (x : M.key) (m m' : t) :
  Level.Wf lb x -> M.In x m ->
  M.find x m = M.find x m' -> M.find x (shift lb k m) = M.find x (shift lb k m').
Proof.
  intros Hvk HIn Hfi. 
  destruct HIn as [v HfV]; apply find_1 in HfV.
  rewrite <- (Level.shift_wf_refl lb k x); auto.
  now do 2 rewrite <- (shift_find lb k).
Qed.

Lemma shift_in_new_key (n : Lvl.t) (x : M.key) (t : t) :
  M.In x (shift (new_key t) n t) <-> M.In x t.
Proof.
  split; intro HIn.
  - apply shift_in_e in HIn as H.
    destruct H as [y Heq]; subst.
    rewrite <- shift_in_iff in HIn.
    apply new_key_in in HIn as Hlt.
    rewrite Level.shift_wf_refl; auto.
  - apply new_key_in in HIn as Hlt.
    rewrite <- (Level.shift_wf_refl (new_key t) n x); auto.
    now rewrite <- shift_in_iff.
Qed.

End IsLvlMapLVL.

(** ** Bindless Leveled Map Implementation *)
Module IsBdlLvlMapLVL 
  (Data : EqualityType) (M : Interface.S Level) 
  (MO : MapLVLInterface Data M) <: IsBdlLvlMapLVLInterface Data M MO.

Include IsLvlMapLVL Data M MO.
Import MO OP.P.

Lemma shift_wf_refl (lb k : Lvl.t) (t : t) : Wf lb t -> eq (shift lb k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite <- Wf_add_iff in Hvt. 
    destruct Hvt as [Hvx Hvt].
    rewrite shift_add.
    rewrite IHt1; auto.
    now rewrite Level.shift_wf_refl; auto.
Qed.
    
End IsBdlLvlMapLVL.

(** ---- *)

(** * Make - Leveled Map [LevelK/ETD] *)

Module MakeLvlMapLVL (Data : EqualityType) <: IsLvlET.
  
Module Raw := MMaps.OrdList.Make Level.
Module Ext := MapETLVL Data Raw.
Include IsLvlMapLVL Data Raw Ext.
Include OP.P.

End MakeLvlMapLVL.


Module MakeBdlLvlMapLVL (Data : EqualityType) <: IsBdlLvlET.
  
Module Raw := MMaps.OrdList.Make Level.
Module Ext := MapETLVL Data Raw.
Include IsBdlLvlMapLVL Data Raw Ext.
Include OP.P.

End MakeBdlLvlMapLVL.