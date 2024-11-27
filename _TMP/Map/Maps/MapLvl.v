From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From DeBrLevel Require Import LevelInterface Level MapExtInterface MapExt MapLevelInterface MapK.

(** * Implementation - Map - [LevelK/ETD] *)

(** ** Leveled Map Implementation *)

Module IsLvlMapLVL 
  (Data : EqualityType) (M : Interface.S Level) 
  (MO : MapLVLInterface Data M)  <: IsLvlMapLVLInterface Data M MO.

Include IsLvlMapK Level Data M MO.
Import MO OP.P.

Lemma shift_new_notin_spec (lb k : Lvl.t) (t : t) :
  lb >= (new_key t) -> ~ M.In lb (shift lb k t).
Proof.
  induction t using map_induction; intros Hgeq.
  - rewrite shift_Empty_spec; auto.
    rewrite Empty_eq_spec; auto. 
    apply not_in_empty.
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite shift_add_spec.
    rewrite add_in_iff. 
    intros [Heq | HIn]; subst.
    -- unfold Level.shift in Heq. 
       destruct (Nat.leb_spec0 lb x) as [Hle | Hnle].
       + assert (HIn: M.In x (M.add x e t1)).
         { now rewrite add_in_iff; left. }
         assert (HnIn: ~ M.In x (M.add x e t1)).
         { apply new_key_notin_spec; lia. }
         contradiction.
       + subst; lia.
    -- apply IHt1; auto.
       apply new_key_add_spec with (v := e) in H; auto.
       destruct H as [[Heq Hleb] | [Heq Hgt]]; lia.
Qed.

Lemma shift_max_refl_spec (lb k : Lvl.t) (t : t) :
  lb >= (new_key t) -> max_key (shift lb k t) = max_key t.
Proof.
  induction t using map_induction; intro Hleb.
  - rewrite shift_Empty_spec; auto.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add_spec. 
    assert (Hle1: lb >= new_key t1).
    {
      apply new_key_add_spec with (v := e) in H; auto.
      destruct H as [[Heq Hleb'] | [Heq Hgt]]; lia.
    }
    apply IHt1 in Hle1.
    assert (Heq : (Level.shift lb k x) = x).
    { 
      rewrite Level.shift_valid_refl; auto. 
      unfold Level.valid.
      assert (HIn : M.In x (M.add x e t1)).
      { rewrite add_in_iff; now left. }
      apply new_key_in_spec in HIn; lia.
    }
    rewrite Heq.
    eapply max_key_add_spec_1; eauto.
    rewrite <- Heq.
    now apply shift_notin_iff.
Qed.

Lemma shift_new_refl_spec (lb k : Lvl.t) (t : t) :
  lb >= (new_key t) -> new_key (shift lb k t) = new_key t.
Proof.
  intro Hge; repeat rewrite new_key_unfold.
  destruct (M.is_empty t) eqn:HEmp.
  - rewrite shift_Empty_spec.
    -- now rewrite HEmp.
    -- now apply is_empty_2.
  - destruct (M.is_empty (shift lb k t)) eqn:HEmp'.
    -- rewrite shift_Empty_spec in HEmp'.
       + now rewrite HEmp in *.
       + apply is_empty_2 in HEmp'. 
         now rewrite <- shift_Empty_iff in HEmp'.
    -- f_equal; now apply shift_max_refl_spec.
Qed.  

Lemma shift_max_key_gt_iff (m n x : Lvl.t) (o : t) :
  max_key o > x <-> max_key (shift m n o) > (Level.shift m n x).
Proof.
  revert x; induction o using map_induction; intro y.
  - split; intro Hmax.
    -- rewrite max_key_Empty_spec in Hmax; auto; lia.
    -- rewrite shift_Empty_spec in Hmax; auto.
       rewrite max_key_Empty_spec in Hmax; auto; lia.
  - split; intro Hmax;
    unfold Add in H0; rewrite H0 in *; clear H0.
    -- destruct (Level.leb_spec (max_key o1) x) as [Hle | Hgt].
       + rewrite max_key_add_ge_spec in Hmax; auto; try lia.
         rewrite shift_add_spec.
         rewrite (shift_in_iff m n) in H.
         destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
         ++ rewrite max_key_add_ge_spec; auto; try lia.
            now apply Level.shift_gt_iff.
         ++ rewrite max_key_add_lt_spec; auto; try lia.
            assert (max_key o1 > x) by (rewrite IHo1; lia); lia.
       + rewrite max_key_add_lt_spec in Hmax; auto; try lia.
         rewrite shift_add_spec.
         rewrite (shift_in_iff m n) in H.
         destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
         ++ rewrite IHo1 in Hmax.
            rewrite max_key_add_ge_spec; auto; lia.
         ++ rewrite max_key_add_lt_spec; auto; try lia.
            now rewrite <- IHo1.
    -- rewrite shift_add_spec in Hmax.
       rewrite (shift_in_iff m n) in H.
       destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle | Hgt].
       + rewrite max_key_add_ge_spec in Hmax; auto; try lia.
         rewrite <- (shift_in_iff m n) in H.
         destruct (Level.leb_spec (max_key o1) x) as [Hle' | Hgt'].
         ++ rewrite max_key_add_ge_spec; auto; try lia.
            now apply Level.shift_gt_iff in Hmax.
         ++ rewrite max_key_add_lt_spec; auto; try lia.
            rewrite <- Level.shift_gt_iff in Hmax; lia.
       + rewrite max_key_add_lt_spec in Hmax; auto; try lia.
         rewrite <- (shift_in_iff m n) in H.
         destruct (Level.leb_spec (max_key o1) x) as [Hle' | Hgt'].
         ++ rewrite max_key_add_ge_spec; auto; try lia.
            rewrite <- IHo1 in Hmax; lia.
         ++ rewrite max_key_add_lt_spec; auto; try lia.
            rewrite <- IHo1 in Hmax; lia.
Qed. 

Lemma shift_max_key_le_spec (m n : Lvl.t) (o : t) :
  max_key o <= max_key (shift m n o).
Proof.
  induction o using map_induction.
  - now rewrite shift_Empty_spec.
  - unfold Add in H0; rewrite H0; clear H0. 
    rewrite shift_add_spec.
    destruct (Level.leb_spec (max_key o1) x) as [Hle | Hgt].
    -- rewrite max_key_add_ge_spec; auto; try lia.
       rewrite (shift_in_iff m n) in H.
       destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
       + rewrite max_key_add_ge_spec; auto; try lia.
         apply Level.shift_le_spec.
       + rewrite max_key_add_lt_spec; auto; try lia.
         assert (Hgt : max_key (shift m n o1) > Level.shift m n x) by lia.
         rewrite <- shift_max_key_gt_iff in Hgt; lia.
    -- rewrite max_key_add_lt_spec; auto; try lia.
       rewrite (shift_in_iff m n) in H.
       destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
       + rewrite max_key_add_ge_spec; auto; lia.
       + rewrite max_key_add_lt_spec; auto; lia.
Qed.
       
Lemma shift_new_key_le_spec (m n : Lvl.t) (o : t) :
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
    apply shift_max_key_le_spec.
Qed.

Lemma valid_in_iff (m n : Lvl.t) (x : M.key) (t : t) :
  valid m t -> M.In x (shift m n t) <-> M.In x t.
Proof.
  revert x; induction t using map_induction; intros y Hvo; split; intro HIn.
  - rewrite shift_Empty_spec in HIn; auto.
  - rewrite shift_Empty_spec; auto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply valid_add_notin_spec in Hvo as [Hvk Hv]; auto.
    rewrite shift_add_notin_spec in HIn; auto.
    rewrite add_in_iff in *; destruct HIn as [Heq | HIn]; subst.
    -- left; now rewrite Level.shift_valid_refl; auto.
    -- right. rewrite <- IHt1; eauto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply valid_add_notin_spec in Hvo as [Hvk Hv]; auto.
    rewrite shift_add_notin_spec; auto.
    rewrite add_in_iff in *; destruct HIn as [Heq | HIn]; subst.
    -- left; now rewrite Level.shift_valid_refl; auto.
    -- right. rewrite IHt1; eauto.
Qed.

Lemma shift_find_valid_spec (lb k : Lvl.t) (x : M.key) (m m' : t) :
  Level.valid lb x -> M.In x m ->
  M.find x m = M.find x m' -> M.find x (shift lb k m) = M.find x (shift lb k m').
Proof.
  intros Hvk HIn Hfi. 
  destruct HIn as [v HfV]; apply find_1 in HfV.
  rewrite <- (Level.shift_valid_refl lb k x); auto.
  now do 2 rewrite <- (shift_find_spec lb k).
Qed.

Lemma shift_in_new_key (n : Lvl.t) (x : M.key) (t : t) :
  M.In x (shift (new_key t) n t) <-> M.In x t.
Proof.
  split; intro HIn.
  - apply shift_in_e_spec in HIn as H.
    destruct H as [y Heq]; subst.
    rewrite <- shift_in_iff in HIn.
    apply new_key_in_spec in HIn as Hlt.
    rewrite Level.shift_valid_refl; auto.
  - apply new_key_in_spec in HIn as Hlt.
    rewrite <- (Level.shift_valid_refl (new_key t) n x); auto.
    now rewrite <- shift_in_iff.
Qed.

End IsLvlMapLVL.

(** ** Bindless Leveled Map Implementation *)
Module IsBdlLvlMapLVL 
  (Data : EqualityType) (M : Interface.S Level) 
  (MO : MapLVLInterface Data M) <: IsBdlLvlMapLVLInterface Data M MO.

Include IsLvlMapLVL Data M MO.
Import MO OP.P.

Lemma shift_valid_refl (lb k : Lvl.t) (t : t) : valid lb t -> eq (shift lb k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty_spec.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite <- valid_add_iff in Hvt. 
    destruct Hvt as [Hvx Hvt].
    rewrite shift_add_spec.
    rewrite IHt1; auto.
    now rewrite Level.shift_valid_refl; auto.
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