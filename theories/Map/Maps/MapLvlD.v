From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From DeBrLevel Require Import Level LevelInterface MapExtInterface MapExt MapLevelInterface MapKD.

(** * Implementation - Map - [LevelK/LvlD] *)

(** ** Leveled Map Implementation *)

Module IsLvlMapLVLD
  (Data : IsLvlETWL) (M : Interface.S Level) 
  (MO : MapLVLInterface Data M) <: IsLvlMapLVLDInterface Data M MO.

Include IsLvlMapKD Level Data M MO.
Import MO OP.P.

Lemma shift_new_notin_spec (lb k : Lvl.t) (t : t) :
  lb >= (new_key t) -> ~ M.In lb (shift lb k t).
Proof.
  induction t using map_induction; intros Hgeq.
  - rewrite shift_Empty_spec; auto.
    rewrite Empty_eq_spec; auto.
    apply not_in_empty.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_notin_spec; auto. 
    rewrite add_in_iff.
    intros [Heq | HIn].
    -- unfold Level.shift in Heq. 
       destruct (Nat.leb_spec0 lb x) as [Hle | Hnle].
       + assert (HIn : M.In x (M.add x e t1)).
         { exists e. now apply add_1. }
         assert (HnIn : ~ M.In x (M.add x e t1)). 
         { apply new_key_notin_spec; lia. }
         contradiction.
        + subst; lia.
    -- revert HIn; apply IHt1. 
       apply new_key_add_spec with (v := e) in H; auto.
       destruct H as [[Heq Hleb] | [Heq Hgt]]; try lia.
Qed.

Lemma shift_max_spec (lb k : Lvl.t) (t : t) :
  lb >= (new_key t) -> max_key (shift lb k t) = max_key t.
Proof.
  induction t using map_induction; intros Hle.
  - rewrite shift_Empty_spec; auto.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_spec.
    apply max_key_add_spec with (v := e) in H as HI. 
    assert (Hge : lb >= new_key t1).
    {
        apply new_key_add_spec with (v := e) in H; auto.
        destruct H as [[Heq Hleb'] | [Heq Hgt]]; lia.
    }

    destruct HI as [[Heq Hleb] | [Heq Hgt]].
    -- rewrite new_key_add_ge_spec in Hle; auto.
       + rewrite Heq.
         rewrite max_key_add_ge_spec; auto.
         * apply Level.shift_valid_refl.
           unfold Level.valid; lia.
         * now rewrite <- shift_notin_iff.
         * rewrite IHt1; try lia.
           rewrite Level.shift_valid_refl; auto.
       + rewrite new_key_unfold.
         destruct (M.is_empty t1); lia.
    -- assert (Hlt : x < lb).
       {
         transitivity (max_key t1); try lia.
         rewrite <- Heq.
         rewrite new_key_unfold in Hle.
         destruct (M.is_empty (M.add x e t1)) eqn:Hemp; try lia.
         apply is_empty_2 in Hemp.
         exfalso.
         apply (Hemp x e).
         now apply add_1.
       } 
       rewrite new_key_add_lt_spec in Hle; auto.
       + rewrite Heq.
         rewrite max_key_add_lt_spec; auto.
         * now rewrite <- shift_notin_iff.
         * rewrite IHt1; auto.
           rewrite Level.shift_valid_refl; auto.
       + rewrite new_key_unfold.
         destruct (M.is_empty t1) eqn:Hemp; try lia.
         rewrite max_key_Empty_spec in Hgt; try lia.
         now apply is_empty_2.
Qed.

Lemma shift_new_spec (lb k : Lvl.t) (t : t) :
  lb >= (new_key t) -> new_key (shift lb k t) = new_key t.
Proof.
  repeat rewrite new_key_unfold; intro Hge.
  destruct (M.is_empty t) eqn:Hemp.
  - apply is_empty_2 in Hemp as HEmp.
    rewrite (shift_Empty_iff lb k) in HEmp.
    apply is_empty_1 in HEmp.
    now rewrite HEmp.
  - destruct (M.is_empty (shift lb k t)) eqn:Hemp'.
    -- apply is_empty_2 in Hemp'. 
       rewrite <- shift_Empty_iff in Hemp'.
       apply is_empty_1 in Hemp'. 
       rewrite Hemp in *; inversion Hemp'.
    -- f_equal; apply shift_max_spec.
       rewrite new_key_unfold.
       now rewrite Hemp.
Qed.  

End IsLvlMapLVLD.

(** ** Bindless Leveled Map Implementation *)
Module IsBdlLvlMapLVLD 
  (Data : IsBdlLvlETWL) (M : Interface.S Level) 
  (MO : MapLVLInterface Data M) <: IsBdlLvlMapLVLDInterface Data M MO.

Include IsLvlMapLVLD Data M MO.
Import MO OP.P.

Lemma shift_valid_refl (lb k : Lvl.t) (t : t) : valid lb t -> eq (shift lb k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty_spec.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hvt as [Hvx [Hve Hvt]]; auto. 
    rewrite shift_add_spec.
    rewrite IHt1; auto.
    rewrite Level.shift_valid_refl; auto.

    replace (Data.shift lb k e) with e; try reflexivity.
    apply Data.eq_leibniz.
    now rewrite Data.shift_valid_refl; auto.
Qed.
    
End IsBdlLvlMapLVLD.


(** *** Map Make *)

Module MakeLvlMapLVLD (Data : IsLvlETWL) <: IsLvlET.
  
  Module Raw := MMaps.OrdList.Make Level.
  Module Ext := MapETLVL Data Raw.
  Include IsLvlMapLVLD Data Raw Ext.
  Include OP.P.

End MakeLvlMapLVLD.


Module MakeBdlLvlMapLVLD (Data : IsBdlLvlETWL) <: IsBdlLvlET.
  
  Module Raw := MMaps.OrdList.Make Level.
  Module Ext := MapETLVL Data Raw.
  Include IsBdlLvlMapLVLD Data Raw Ext.
  Include OP.P.

End MakeBdlLvlMapLVLD.