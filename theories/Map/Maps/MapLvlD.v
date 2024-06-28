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

Lemma shift_new_notin_spec : forall lb k t,
  lb >= (new_key t) -> ~ M.In lb (shift lb k t).
Proof.
  intros lb k t; revert lb k;
  induction t using map_induction; intros lb k Hgeq.
  - eapply shift_Empty_spec in H as H'; rewrite H'.
    unfold Empty in *. intro HIn. destruct HIn. now apply (H lb x).
  - unfold Add in *; rewrite H0; intro HIn.
    rewrite shift_add_notin_spec in HIn; auto. 
    apply add_in_iff in HIn; destruct HIn.
    -- unfold Level.shift in H1. destruct (Nat.leb_spec0 lb x).
        + assert (M.In x t2).
          { exists e. apply find_2; rewrite H0. now apply add_eq_o. }
          assert (~ M.In x t2). { apply new_key_notin_spec; lia. }
          contradiction.
        + rewrite H1 in *; apply n. lia.
    -- revert H1. apply IHt1. apply new_key_Add_spec in H0; auto.
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
    rewrite <- H2; now apply shift_notin_iff.
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

End IsLvlMapLVLD.

(** ** Bindless Leveled Map Implementation *)
Module IsBdlLvlMapLVLD 
  (Data : IsBdlLvlETWL) (M : Interface.S Level) 
  (MO : MapLVLInterface Data M) <: IsBdlLvlMapLVLDInterface Data M MO.

Include IsLvlMapLVLD Data M MO.
Import MO OP.P.

Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
Proof.
  intros; induction t0 using map_induction.
  - now apply shift_Empty_spec.
  - apply shift_Add_spec with (lb := lb) (k := k) in H1 as H1'; auto.
    unfold Add in *.
    rewrite H1'. rewrite <- valid_Add_iff in H; eauto.
    destruct H as [Hvr [Hve Hvt]]. apply IHt0_1 in Hvt. rewrite H1.
    rewrite Hvt. 
    apply Level.shift_valid_refl with (k := k) in Hvr; rewrite Hvr.
    apply Data.shift_valid_refl with (k := k) in Hve; apply Data.eq_leibniz in Hve.
    now rewrite Hve.
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