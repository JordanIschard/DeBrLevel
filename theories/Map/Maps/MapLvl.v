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

Lemma shift_max_spec (lb k : Lvl.t) (t : t) :
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

Lemma shift_new_spec (lb k : Lvl.t) (t : t) :
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
    -- f_equal; now apply shift_max_spec.
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