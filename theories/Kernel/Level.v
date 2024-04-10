From Coq Require Import Structures.OrdersEx Classes.Morphisms Arith.PeanoNat Lia.
Require Import LevelInterface.


(** * Implementation -- Level 

  A level in our library is a [nat]. it has to satisfied all constraints.
*)
Module Level <: StrongShiftValidFullOTWithLeibniz.

  Include Lvl.

  (** *** Definition *)
  Section definition.

    Definition shift (lb : Lvl.t) (k : Lvl.t) (v : t) := 
      if (lb <=? v)%nat then v + k else v.

    Definition valid (lb : Lvl.t) (v : t) := Lvl.lt v lb.

    Definition validb (lb : Lvl.t) (v : t) := Lvl.ltb v lb.

  End definition.
  
  (** *** Equality *)
  Section equality.
    
    Lemma eq_leibniz : forall x y, eq x y -> x = y. 
    Proof. auto. Qed.

  End equality.

  (** *** Strict order between levels *)
  Section lt.

    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y. 
    Proof. intros; lia. Qed.

    Lemma gt_neq_nlt : forall x y, ~ eq x y -> ~ lt x y -> lt y x.
    Proof. intros; lia. Qed.
    
  End lt.

  (** *** Shift *)
  Section shift.

    Variable lb lb' k k' : Lvl.t.
    Variable t t1 : t.

    #[global]
    Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
    Proof. repeat red; intros; subst; now rewrite H1. Qed.

    Lemma shift_neq :
      t <> t1 -> (shift lb k t) <> (shift lb k t1).
    Proof.
      intros; unfold shift. destruct (Nat.leb_spec0 lb t); destruct (Nat.leb_spec0 lb t1); lia.
    Qed.

    Lemma shift_neq_1 :
      (shift lb k t) <> (shift lb k t1) -> t <> t1.
    Proof.
      intros; unfold shift in H. destruct (Nat.leb_spec0 lb t); 
      destruct (Nat.leb_spec0 lb t1); lia.
    Qed.

    Lemma shift_eq_iff :
      t = t1 <-> (shift lb k t) = (shift lb k t1).
    Proof.
      split; subst; auto. intros; unfold shift in H. 
      destruct (Nat.leb_spec0 lb t); destruct (Nat.leb_spec0 lb t1); lia.
    Qed.

    Lemma shift_refl : shift lb 0 t = t.
    Proof.
      unfold shift; destruct (Nat.leb_spec0 lb t); auto.
    Qed.

    Lemma shift_valid_refl : valid lb t -> shift lb k t = t.
    Proof. 
      unfold shift,valid; intros Hvt. destruct (Nat.leb_spec0 lb t); auto.
      lia.
    Qed.

    Lemma shift_trans : shift lb k (shift lb k' t) = shift lb (k + k') t.
    Proof.
      unfold shift; destruct (Nat.leb_spec0 lb t); auto.
      - assert (lb <= (t + k'))%nat; try lia.
        rewrite <- Nat.leb_le in H; rewrite H; lia.
      - rewrite <- Nat.leb_nle in n; rewrite n; reflexivity. 
    Qed.

    Lemma shift_permute :
      shift lb k (shift lb k' t) = shift lb k' (shift lb k t).
    Proof.
      unfold shift; destruct (Nat.leb_spec0 lb t).
      - destruct (Nat.leb_spec0 lb (t + k')); 
        destruct (Nat.leb_spec0 lb (t + k)); lia.
      - rewrite <- Nat.leb_nle in n; now rewrite n.
    Qed.

    Lemma shift_permute_1 : 
      (shift lb k (shift lb k' t)) = (shift (lb + k) k' (shift lb k t)).
    Proof.
      unfold shift; destruct (Nat.leb_spec0 lb t).
      - replace (lb <=? t + k') with true; replace (lb + k <=? t + k) with true.
        -- lia.
        -- symmetry; rewrite Nat.leb_le; lia.
        -- symmetry; rewrite Nat.leb_le; lia.
        -- symmetry; rewrite Nat.leb_le; lia.
      - replace (lb <=? t) with false; replace (lb + k <=? t) with false; try reflexivity;
        symmetry; rewrite Nat.leb_nle; lia.
    Qed.

    Lemma shift_permute_2 : 
      lb <= lb' -> (shift lb k (shift lb' k' t)) = (shift (lb' + k) k' (shift lb k t)).
    Proof.
      unfold shift; intros; destruct (Nat.leb_spec0 lb' t); destruct (Nat.leb_spec0 lb t).
      - replace (lb <=? t + k') with true; replace (lb' + k <=? t + k) with true; try lia;
        symmetry; rewrite Nat.leb_le; lia.
      - replace (lb <=? t + k') with false; replace (lb' + k <=? t) with true; try reflexivity;
        symmetry; try (rewrite Nat.leb_le; lia); rewrite Nat.leb_nle; lia.
      - replace (lb' + k <=? t + k) with false; try reflexivity; symmetry; 
        rewrite Nat.leb_nle; lia.
      - replace (lb' + k <=? t) with false; try reflexivity; symmetry; rewrite Nat.leb_nle; lia.
    Qed.

    Lemma shift_unfold : (shift lb (k + k') t) = (shift (lb + k) k' (shift lb k t)). 
    Proof.
      unfold shift; destruct (lb <=? t) eqn:Hleb.
      - replace (lb + k <=? t + k) with true; try lia. symmetry; rewrite Nat.leb_le in *; lia.
      - apply Nat.leb_nle in Hleb. destruct (Nat.leb_spec0 (lb + k) t); lia.
    Qed.

    Lemma shift_unfold_1 : forall k k1 k2 r,
      k <= k1 -> k1 <= k2 ->
      (shift k1 (k2 - k1) (shift k  (k1 - k) r)) = shift k (k2 - k) r.
    Proof.
      unfold shift; intros; destruct (Nat.leb_spec0 k0 r).
      -- destruct (Nat.leb_spec0 k1 (r + (k1 - k0))); lia.
      -- destruct (Nat.leb_spec0 k1 r); auto; assert (r < k0) by lia; lia.
    Qed.
    
  End shift.

  (** *** Valid *)
  Section valid.
    
    Lemma validb_valid : forall k t, validb k t = true <-> valid k t. 
    Proof.
      split; intros; unfold valid,validb in *; now apply Nat.ltb_lt.
    Qed.

    Lemma validb_nvalid : forall k t, validb k t = false <-> ~ valid k t.
    Proof.
      split; intros; unfold valid,validb in *; now apply Nat.ltb_nlt.
    Qed. 

    #[global]
    Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
    Proof. repeat red; intros; subst; rewrite H0; split; auto. Qed.

    Lemma validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
    Proof. repeat red; intros; subst; rewrite H0; split; auto. Qed.

    Lemma valid_weakening : forall k k' t, (k <= k') -> valid k t -> valid k' t.
    Proof. unfold valid; intros k k' t Hleb Hvt; lia. Qed.

    Lemma shift_preserves_valid : forall k k' t, valid k t -> valid (k + k') (shift k k' t).
    Proof.
      unfold valid,shift; intros k k' t Hvt; destruct (Nat.leb_spec0 k t); try lia.
    Qed.

    Lemma shift_preserves_valid_1 : forall lb k k' t, 
      valid k t -> valid (k + k') (shift lb k' t).
    Proof.
      unfold valid,shift; intros lb k k' t Hvt; destruct (Nat.leb_spec0 lb t); lia.
    Qed.

    Lemma shift_preserves_valid_2 : forall lb lb' k k' t,
      k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> 
      k' - k = lb' - lb -> 
      valid lb t -> valid lb' (shift k (k' - k) t).
    Proof.
      intros lb lb' k; revert lb lb'; induction k; simpl; intros.
      - unfold valid, shift in *. destruct t0; simpl; lia.
      - unfold valid, shift in *; destruct t0; simpl; try lia.
        destruct lb; try lia; destruct k'; try lia.
        destruct lb'; try lia; simpl in *. apply le_S_n in H0,H,H1,H2.
        apply IHk with (t := t0) in H3; auto; try lia.
        destruct (Nat.leb_spec0 k t0); simpl in *; lia.
    Qed.

    Lemma shift_preserves_valid_3 : forall lb lb' t,
      lb <= lb' -> valid lb t -> 
      valid lb' (shift lb (lb' - lb) t).
    Proof. intros. eapply shift_preserves_valid_2; eauto. Qed. 

    Lemma shift_preserves_valid_4 : forall k t, valid k t -> valid k (shift k 0 t).
    Proof. 
      intros; replace k with (k + 0); try lia;
      now apply shift_preserves_valid_1. 
    Qed. 
  
  End valid.

End Level.