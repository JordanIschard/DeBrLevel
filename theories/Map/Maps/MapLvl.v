From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From DeBrLevel Require Import LevelInterface Level MapExtInterface MapExt MapLevelInterface MapK.

(** * Implementation -- Map *)

(** ** Map with basic datas and levels as keys *)

(** *** Map implementation with minimal constraints *)

Module IsLvlMapLVL (Data : EqualityType) 
                          (M : Interface.S Level)
                          (MO : MapLVLInterface Data M) 
                          <: IsLvlMapLVLInterface Data M MO.

Include IsLvlMap Level Data M MO.
Import MO OP.P.

Lemma shift_new_notin_spec : forall lb k t,
  lb >= (new_key t) -> ~ M.In lb (shift lb k t).
Proof.
  intros lb k t; revert lb k;
  induction t using map_induction; intros lb k Hgeq.
  - rewrite shift_Empty_spec; auto.
    unfold Empty in *. intro HIn. destruct HIn. now apply (H lb x).
  - unfold Add in H0; rewrite H0 in *. rewrite shift_add_notin_spec; auto. intro Hin.
    rewrite add_in_iff in Hin; destruct Hin.
    -- unfold Level.shift in H1. destruct (Nat.leb_spec0 lb x).
        + assert (M.In x t2).
          { exists e. apply find_2; rewrite H0. now apply add_eq_o. }
          assert (~ M.In x t2). { apply new_key_notin_spec; lia. }
          contradiction.
        + rewrite H1 in *; apply n. lia.
    --  revert H1. apply IHt1. apply new_key_Add_spec in H0; auto.
        destruct H0 as [[Heq Hleb] | [Heq Hgt]]; lia.
Qed.

Lemma shift_max_spec : forall lb k t,
  lb >= (new_key t) -> max_key (shift lb k t) = max_key t.
Proof.
  intros lb k t; revert lb k; induction t using map_induction; intros lb k Hleb.
  - eapply shift_Empty_spec in H as H'; apply max_key_eq; eauto.
  - eapply shift_Add_spec in H0 as H0'; auto.
    apply max_key_eq in H0'; rewrite H0'. clear H0'.
    unfold Add in H0. apply max_key_eq in H0 as H0'; rewrite H0'; clear H0'.
    assert (lb >= new_key t1).
    {
        apply new_key_Add_spec in H0; auto.
        destruct H0 as [[Heq Hleb'] | [Heq Hgt]]; lia.
    }
    apply IHt1 with (k := k) in H1.
    assert ((Level.shift lb k x) = x).
    { 
      rewrite Level.shift_valid_refl; auto. 
      unfold Level.valid.
      assert (M.In x t2).
      { exists e. apply find_2; rewrite H0. now apply add_eq_o. }
      apply new_key_in_spec in H2; lia.
    }
    rewrite H2. eapply max_key_add_spec_4; auto.
    rewrite <- H2; now apply shift_notin_spec.
Qed.

Lemma shift_new_spec : forall lb k t,
  lb >= (new_key t) -> new_key (shift lb k t) = new_key t.
Proof.
  intros; repeat rewrite new_key_unfold.
  destruct (M.is_empty t0) eqn:HEmp.
  - apply is_empty_2 in HEmp as HEmp'.
    eapply shift_Empty_iff in HEmp'. apply is_empty_1 in HEmp'.
    now rewrite HEmp'.
  - destruct (M.is_empty (shift lb k t0)) eqn:HEmp'.
    -- apply is_empty_2 in HEmp'. rewrite <- shift_Empty_iff in HEmp'.
        apply is_empty_1 in HEmp'; rewrite HEmp in *; inversion HEmp'.
    -- f_equal; now apply shift_max_spec.
Qed.  

End IsLvlMapLVL.

(** *** Map implementation fully constrained *)
Module IsBdlLvlMapLVL (Data : EqualityType) 
                                (M : Interface.S Level) 
                                (MO : MapLVLInterface Data M) 
                                   <: IsBdlLvlMapLVLInterface Data M MO.

Include IsLvlMapLVL Data M MO.
Import MO OP.P.

Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
Proof.
  intros; induction t0 using map_induction.
  - now apply shift_Empty_spec.
  - unfold Add in H1; rewrite H1 in *.
    rewrite valid_add_notin_spec in H; auto; destruct H.
    rewrite shift_add_notin_spec; auto. rewrite IHt0_1; auto.
    rewrite Level.shift_valid_refl; auto; reflexivity.
Qed.
    
End IsBdlLvlMapLVL.


(** *** Map Make *)

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