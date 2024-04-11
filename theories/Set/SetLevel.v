From Coq Require Import MSets Lia.
Require Import Kernel.Level Kernel.LevelInterface.
Require Import SetLevelInterface SetOTwL SetOTwLInterface.

(** * Implementation -- Set of leveled elements *)

(** ** Set implementation with minimal constraints *)
Module ShiftValidSetOTWL (T : ShiftValidOTWithLeibniz) 
                                    <: (ShiftValidSetOTWLInterface T).

  Include SetOTWithLeibniz T.

  (** *** Definition *)
  Section definition.

    Definition shift (lb : nat) (k : nat) (s : t) : t := map (T.shift lb k) s.

    Definition valid (k : nat) (s : t) := (For_all (T.valid k) s).

  End definition.

  (** *** Valid *)
  Section valid.

    Variable lb : nat.
    Variable v : elt.
    Variable s s' : t.

    Lemma valid_unfold : valid lb s <-> (For_all (T.valid lb) s).
    Proof. unfold valid; split; auto. Qed.

    Lemma valid_add_spec : valid lb (add v s) -> T.valid lb v /\ valid lb s.
    Proof.
      intros; unfold valid,For_all in *; split.
      - apply H; apply add_spec; now left.
      - intros. apply H; apply add_spec; now right.
    Qed.

    Lemma valid_empty_spec : valid lb empty.
    Proof. intros; unfold valid,For_all; intros; inversion H. Qed.

    Lemma valid_union_spec : valid lb (union s s') <-> valid lb s /\ valid lb s'.
    Proof.
      split; intros; unfold valid,For_all in *.
      - split; intros; apply H; rewrite union_spec; auto.
      - intros; destruct H; rewrite union_spec in *; destruct H0; auto.
    Qed.

    Lemma valid_singleton_spec : valid lb (singleton v) <-> T.valid lb v.
    Proof.
      split; intros; unfold valid,For_all in *.
      - apply H; now rewrite singleton_spec.
      - intros; rewrite singleton_spec in H0. apply T.eq_leibniz in H0; now subst.
    Qed.

    Lemma valid_in_spec : valid lb s -> In v s -> T.valid lb v.
    Proof.
      unfold valid,For_all in *; intros; now apply H.
    Qed.

  End valid.

  (** *** Shift *)
  Section shift.

    Variable lb k : nat.
    Variable v : elt.
    Variable s : t.

    #[local] Hint Resolve eq_equiv transpose_1 proper_1 : core.


    Lemma shift_union_spec : forall s', 
      shift lb k (union s s') = union (shift lb k s) (shift lb k s').
    Proof. intros; unfold shift; now rewrite map_union_spec. Qed.

    Lemma shift_Empty_spec : Empty s -> shift lb k s = empty.
    Proof. intros; unfold shift; now apply map_Empty_spec. Qed.

    Lemma shift_empty_spec : shift lb k empty = empty.
    Proof. intros; unfold shift; now apply map_empty_spec. Qed.

    Lemma shift_singleton_spec : shift lb k (singleton v) = singleton (T.shift lb k v).
    Proof. intros; unfold shift; now apply map_singleton_spec. Qed.

    Lemma shift_add_notin_spec :
      ~ In v s -> shift lb k (add v s) = add (T.shift lb k v) (shift lb k s).
    Proof. intros; unfold shift; now apply map_add_notin_spec. Qed.

    Lemma shift_add_in_spec :
      In v s -> shift lb k (add v s) = (shift lb k s).
    Proof. intros; unfold shift; now apply map_add_in_spec. Qed.

    Lemma shift_in_spec :
      In v s <-> In (T.shift lb k v) (shift lb k s).
    Proof.
      unfold shift; induction s using set_induction.
      - split; intro HIn; rewrite map_Empty_spec in *; auto; apply empty_is_empty_1 in H; 
        apply eq_leibniz in H; subst; inversion HIn. 
      - apply Add_inv in H0; subst; split; intro HIn; rewrite map_add_notin_spec in *; auto;
        rewrite add_spec in *; destruct HIn.
        -- apply T.eq_leibniz in H0; subst; left; reflexivity.
        -- rewrite <- IHt0_1; now right. 
        -- apply T.shift_eq_iff in H0; now left.
        -- rewrite <- IHt0_1 in H0; now right.
    Qed.

    Lemma shift_add_spec :
      shift lb k (add v s) = add (T.shift lb k v) (shift lb k s).
    Proof.
      intros; destruct (In_dec v s).
      - rewrite shift_add_in_spec; auto. apply eq_leibniz; rewrite add_equal.
        -- reflexivity.
        -- now apply shift_in_spec.
      - now  apply shift_add_notin_spec.
    Qed.

    Lemma shift_in_e_spec :
      In v (shift lb k s) -> 
      exists v', v = (T.shift lb k v') /\  In (T.shift lb k v') (shift lb k s).
    Proof.
      induction s using set_induction; intro HI; unfold shift in *.
      - rewrite map_Empty_spec in HI; auto; inversion HI.
      - apply Add_inv in H0; subst; rewrite map_add_notin_spec in HI; auto.
        rewrite add_spec in *; destruct HI.
        -- apply T.eq_leibniz in H0; rewrite H0; exists x; split; auto.
          rewrite map_add_notin_spec; auto; apply add_spec; now left.
        -- apply IHt0_1 in H0; destruct H0 as [r' [Heq HIn]]; subst.
          exists r'; split; auto. rewrite map_add_notin_spec; auto; rewrite add_spec; now right.
    Qed. 

    Lemma shift_notin_spec : ~ In v s <-> ~ In (T.shift lb k v) (shift lb k s).
    Proof.
      intros; split; unfold not; intros; apply H.
      - now rewrite <- shift_in_spec in H0.
      - now rewrite <- shift_in_spec.
    Qed.

  End shift.

  (** *** Shift continued *)
  Section shift_1.

    Lemma shift_remove_spec : forall lb k v s,
      shift lb k (remove v s) = remove (T.shift lb k v)(shift lb k s).
    Proof.
      intros lb k v s; revert lb k v;
      induction s using set_induction; intros.
      - symmetry; rewrite shift_Empty_spec; auto. 
        apply empty_is_empty_1 in H. eapply Equal_remove in H; apply eq_leibniz in H; rewrite H.
        apply eq_leibniz. split; intros.
        -- rewrite remove_spec in H0; destruct H0. inversion H0.
        -- apply shift_in_e_spec in H0.
           destruct H0. destruct H0.
           apply shift_in_spec in H1. rewrite remove_spec in H1; destruct H1; inversion H1.
      
      - apply Add_inv in H0; subst. apply eq_leibniz; split; intros.
        -- apply shift_in_e_spec in H0. destruct H0; destruct H0.
           apply shift_in_spec in H1. apply remove_spec in H1 as [H1 H1'].
           rewrite remove_spec; split; subst.
           + now apply shift_in_spec.
           + intro; apply H1'. eapply T.shift_eq_iff; eauto.
        -- apply remove_spec in H0 as [H0 H0']. rewrite shift_add_notin_spec in H0; auto.
           apply add_spec in H0; destruct H0; subst.
           + apply T.eq_leibniz in H0; subst; apply shift_in_spec. apply remove_spec; split.
             ++ apply add_spec; now left.
             ++ intro; apply H0'; subst; auto; apply T.eq_leibniz in H0;
                subst; reflexivity.
           + apply shift_in_e_spec in H0; destruct H0 as [y [Heq HIn]]; subst.
             apply shift_in_spec. rewrite remove_spec; split.
             ++ apply add_spec; right; now apply shift_in_spec in HIn.
             ++ intro; apply H0'; apply T.eq_leibniz in H0; now subst.
    Qed.

    Lemma shift_eq_iff : forall lb k s s',
      eq s s' <-> eq (shift lb k s) (shift lb k s').
    Proof.
      split.
      - intro Heq; apply eq_leibniz in Heq; now subst.
      - revert lb k s'; induction s using set_induction; intros lb k s'' Heq.
        -- apply empty_is_empty_1 in H as H'.
           apply eq_leibniz in H'; subst. eapply shift_Empty_spec in H; rewrite H in *.
           symmetry in Heq. clear H. symmetry. revert lb k Heq.
           induction s'' using set_induction; intros.
           * apply empty_is_empty_1 in H; now rewrite H.
           * apply Add_inv in H0; subst. rewrite shift_add_notin_spec in Heq; auto.

             assert (eq (add (T.shift lb k x) (shift lb k s''1)) empty).
             { now rewrite Heq. }

             apply empty_is_empty_2 in H0; unfold Empty in H0; exfalso.
             apply (H0 (T.shift lb k x)). rewrite add_spec; now left.
        -- apply Add_inv in H0; subst.

           assert (forall s s' v, (add v s) = s' -> In v s').
           { intros; subst; apply add_spec; now left. }

           rewrite shift_add_notin_spec in Heq; auto. apply eq_leibniz in Heq.
           apply H0 in Heq as Heq'. apply add_remove in Heq' as Htmp.
           apply eq_leibniz in Htmp. rewrite <- Htmp in Heq; clear Htmp.
           rewrite <- shift_in_spec in Heq'. apply add_remove in Heq' as Htmp.
           apply eq_leibniz in Htmp. rewrite <- Htmp; clear Htmp.

           assert (((add x s1) = (add x (remove x s''))) -> 
                   (eq (add x s1) (add x (remove x s'')))) by (intro Hc; now rewrite Hc).
           
           apply H1; clear H1. f_equal. apply eq_leibniz; eapply IHs1.
           rewrite <- add_eq_leibniz in Heq; eauto.
           * rewrite Heq. now rewrite shift_remove_spec.
           * now apply shift_notin_spec.
           * rewrite remove_spec; intro. destruct H1; auto.
             apply H2; reflexivity.
    Qed.

    Lemma shift_inter_spec : forall lb k s s', 
      shift lb k (inter s s') = inter (shift lb k s) (shift lb k s').
    Proof.
      intros lb k s; induction s using set_induction; intros.
      - apply empty_inter_1 with (s' := s') in H as H'.
        unfold shift; rewrite map_Empty_spec; auto.
        symmetry; rewrite map_Empty_spec; auto. apply eq_leibniz; split; intros.
        -- rewrite inter_spec in H0; destruct H0; assumption.
        -- inversion H0.

      - apply Add_inv in H0; subst; unfold shift.
        destruct (In_dec x s').
        -- rewrite inter_in_add_spec; auto. rewrite map_add_notin_spec.
          + symmetry; rewrite map_add_notin_spec; auto.
            rewrite (shift_in_spec lb k) in i.
            rewrite inter_in_add_spec; auto.
            unfold shift in *. now rewrite IHs1.
          + unfold not; intros; rewrite inter_spec in H0; destruct H0; contradiction.

        -- rewrite inter_notin_add_spec; auto. rewrite map_add_notin_spec; auto.
          rewrite (shift_notin_spec lb k) in n.
          rewrite inter_notin_add_spec; auto.
          unfold shift in *. now rewrite IHs1.
    Qed.

    Lemma shift_diff_spec : forall lb k s s',
      shift lb k (diff s s') = (diff (shift lb k s) (shift lb k s')).
    Proof.
      intros lb k s; induction s using set_induction; intros.

      - apply eq_leibniz; split; unfold shift; intros.
        -- apply empty_diff_1 with (s' := s') in H; rewrite map_Empty_spec in H0; auto.
          inversion H0.

        -- rewrite diff_spec in H0; destruct H0; rewrite map_Empty_spec in H0; auto;
          inversion H0.
      
      - apply eq_leibniz; split; intros.
        
        -- apply Add_inv in H0; subst; destruct (In_dec x s').
          + rewrite diff_in_add_spec in H1; auto. rewrite IHs1 in H1.
            rewrite diff_spec in *; destruct H1; split; auto.
            unfold shift in *.
            rewrite map_add_notin_spec; auto; rewrite add_spec; auto.

          + rewrite diff_notin_add_spec in H1; auto. rewrite diff_spec in *.
            replace (shift lb k (add x (diff s1 s')))
            with ( add (T.shift lb k x) (shift lb k (diff s1 s'))) in H1.
            ++ rewrite add_spec in H1; destruct H1.
                * rewrite H0; split.
                  ** unfold shift; rewrite map_add_notin_spec; auto.
                    rewrite add_spec; left; reflexivity.
                  ** now apply shift_notin_spec.

                * rewrite IHs1 in *; rewrite diff_spec in H0; destruct H0.
                  split; auto. unfold shift; rewrite map_add_notin_spec; auto.
                  rewrite add_spec; right; apply H0.

            ++ unfold shift; apply eq_leibniz; split; intros.
                * rewrite add_spec in H0; destruct H0.
                  ** rewrite H0; apply map_in_spec. rewrite add_spec; now left.
                  ** unfold shift in *; rewrite IHs1 in H0; rewrite diff_spec in *.
                    destruct H0. rewrite map_add_notin_spec.
                    { rewrite add_spec; right; rewrite IHs1; rewrite diff_spec; auto. }
                    { rewrite diff_notin_spec; auto. }

                * rewrite map_add_notin_spec in H0.
                  ** rewrite add_spec in *; auto.
                  ** rewrite diff_notin_spec; auto.

        -- apply Add_inv in H0; subst; destruct (In_dec x s').
          + rewrite diff_in_add_spec; auto; rewrite IHs1. rewrite diff_spec in *; 
            destruct H1; split; auto.
            unfold shift in *. rewrite map_add_notin_spec in H0; auto.
            rewrite add_spec in H0; destruct H0; auto; rewrite H0 in *.
            unfold not in *; exfalso; apply H1; now apply map_in_spec.
          + rewrite diff_notin_add_spec; auto. rewrite diff_spec in H1. 
            destruct H1; unfold shift in *. rewrite map_add_notin_spec in H0; auto.
            rewrite add_spec in H0; destruct H0.
            ++ rewrite H0 in *; rewrite map_add_notin_spec.
                * rewrite add_spec; left; reflexivity.
                * apply diff_notin_spec; auto.
            ++ rewrite map_add_notin_spec.
                * rewrite add_spec; right; rewrite IHs1; rewrite diff_spec; split; auto.
                * apply diff_notin_spec; auto.
    Qed.
  
    Lemma shift_refl : forall lb s,
      eq (shift lb 0 s) s.
    Proof.
      unfold shift; intros. induction s using set_induction.
      - apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.  
        now rewrite map_empty_spec.
      - apply Add_inv in H0; subst; rewrite map_add_notin_spec; auto.
        apply eq_leibniz in IHs1; rewrite IHs1; rewrite T.shift_refl; reflexivity.
    Qed.

    Lemma shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
    Proof. 
      red; red; red; red; intros; subst. apply eq_leibniz in H1; now subst.
    Qed.

    Lemma shift_trans : forall lb k k' s,
      eq (shift lb k (shift lb k' s)) (shift lb (k + k') s).
    Proof.
      intros lb k k' s; induction s using set_induction; unfold shift.
      - repeat rewrite map_Empty_spec; auto; reflexivity.
      - apply Add_inv in H0; subst. repeat rewrite map_add_notin_spec; auto.
        -- split; intros HI; rewrite add_spec in *; destruct HI.
          + left; rewrite H0; now rewrite T.shift_trans.
          + right; unfold shift in IHs1. now rewrite <- IHs1.
          + left; rewrite H0; now rewrite T.shift_trans.
          + right. unfold shift in IHs1. now rewrite IHs1.
        -- rewrite shift_notin_spec in H; eauto.
    Qed.

    Lemma shift_permute : forall lb k k' s,
      eq (shift lb k (shift lb k' s)) (shift lb k' (shift lb k s)).
    Proof.
      intros lb k k' s; induction s using set_induction; unfold shift.
      - repeat rewrite map_Empty_spec; auto; reflexivity.
      - apply Add_inv in H0; subst; repeat rewrite map_add_notin_spec; auto;
        try (rewrite shift_notin_spec in H; now eauto).
        split; intros; rewrite add_spec in *; destruct H0.
        -- left; rewrite H0; apply T.shift_permute.
        -- right; unfold shift in *; now rewrite <- IHs1.
        -- left; rewrite H0; apply T.shift_permute.
        -- right; unfold shift in *; now rewrite IHs1.
    Qed.

    Lemma shift_unfold : forall lb k k' t,
      eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
    Proof.
      intros lb k k' t; induction t using set_induction.
      - unfold shift; repeat rewrite map_Empty_spec; auto. reflexivity.
      - apply Add_inv in H0; subst. repeat rewrite shift_add_notin_spec; eauto.
        -- rewrite T.shift_unfold; rewrite IHt1; reflexivity.
        -- now apply shift_notin_spec.
    Qed.

    Lemma shift_unfold_1 : forall k k' k'' t,
      k <= k' -> k' <= k'' -> 
      eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
    Proof.
      intros k k' k'' t; induction t using set_induction; intros.
      - unfold shift; repeat rewrite map_Empty_spec; auto. reflexivity.
      - apply Add_inv in H0; subst. repeat rewrite shift_add_notin_spec; eauto.
        -- rewrite T.shift_unfold_1; auto; rewrite IHt1; auto; reflexivity.
        -- now apply shift_notin_spec.
    Qed.

  End shift_1.

  (** *** Valid continued *)
  Section valid_1.

    Lemma valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
    Proof.
      repeat red; intros; apply eq_leibniz in H0; subst; split; auto.
    Qed.

    Lemma valid_weakening: forall k k' s,
      (k <= k') -> valid k s -> valid k' s.
    Proof. 
      intros; unfold valid,For_all in *; intros; apply H0 in H1. 
      eapply T.valid_weakening; eauto.
    Qed.

    Theorem shift_preserves_valid_1 : forall lb k k' s,
      valid k s -> valid (k + k') (shift lb k' s).
    Proof.
      unfold valid,For_all in *; intros.
      apply shift_in_e_spec in H0; destruct H0 as [y [Heq HIn]]; subst.
      apply T.shift_preserves_valid_1; apply H; now rewrite <- shift_in_spec in HIn.
    Qed.

    Theorem shift_preserves_valid : forall k k' s,
      valid k s -> valid (k + k') (shift k k' s).
    Proof. intros; now apply shift_preserves_valid_1. Qed.

    Lemma shift_preserves_valid_4 : forall k t, valid k t -> valid k (shift k 0 t).
    Proof. intros; replace k with (k + 0); try lia; now apply shift_preserves_valid_1. Qed.

    Lemma shift_preserves_valid_2 : forall lb lb' k k' t,
      k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
      valid lb t -> valid lb' (shift k (k' - k) t).
    Proof.
      unfold valid,For_all in *; intros. apply shift_in_e_spec in H5. 
      destruct H5 as [y [Heq HIn]]; subst.
      apply T.shift_preserves_valid_2 with (lb := lb); auto.
      apply H4. now rewrite <- shift_in_spec in HIn.
    Qed.

    Lemma shift_preserves_valid_3 : forall lb lb' t,
      lb <= lb' -> valid lb t -> 
      valid lb' (shift lb (lb' - lb) t).
    Proof. intros. eapply shift_preserves_valid_2; eauto. Qed.


  End valid_1.

End ShiftValidSetOTWL.

(** ** Set implementation with fully constrained *)
Module StrongShiftValidSetOTWL (T : StrongShiftValidOTWithLeibniz) 
                                            <: StrongShiftValidSetOTWLInterface T.

  Include ShiftValidSetOTWL T.

    Lemma shift_valid_refl : forall lb k s,
      valid lb s -> eq (shift lb k s) s.
    Proof.
      intros lb k s; induction s using set_induction; intros.
      - apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.
        now rewrite shift_empty_spec.
      
      - apply Add_inv in H0; subst.
        rewrite shift_add_notin_spec; try assumption.
        apply valid_add_spec in H1; destruct H1; f_equal.
        rewrite T.shift_valid_refl; auto.
        apply IHs1 in H1; now rewrite H1.
    Qed.

End StrongShiftValidSetOTWL.

(** ** Set implementation with minimal constraints with [validb] *)
Module ShiftValidFullSetOTWL (T : ShiftValidFullOTWithLeibniz) 
                                            <: ShiftValidFullSetOTWLInterface T.

  Include ShiftValidSetOTWL T.

  (** *** Definition *)
  Section definition.

    Definition validb (k : nat) (s : t) := (for_all (fun v => T.validb k v) s).

  End definition.

  (** *** Valid *)
  Section valid.

    Fact proper_valid : forall k, Proper (T.eq ==> Logic.eq) (fun (v : elt) => T.validb k v).
    Proof. repeat red; intros; subst; apply T.eq_leibniz in H; now subst. Qed.

    #[local] Hint Resolve proper_valid : core.

    Lemma validb_valid : forall k t, validb k t = true <-> valid k t. 
    Proof.
      unfold valid,validb; split; intros; rewrite for_all_spec in *; unfold For_all in *;
      try (repeat red; intros; now subst); auto.
      - intros; rewrite <- T.validb_valid; auto.
      - intros; rewrite T.validb_valid; auto.
    Qed.

    Lemma validb_nvalid : forall k t, validb k t = false <-> ~ valid k t.
    Proof.
      intros; rewrite <- not_true_iff_false; split; intros; intro.
      - apply H; now rewrite validb_valid. 
      - apply H; now rewrite <- validb_valid.
    Qed.

    Lemma validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
    Proof. repeat red; intros; subst; apply eq_leibniz in H0; now subst. Qed.

  End valid.

End ShiftValidFullSetOTWL.

(** ** Set implementation with fully constrained with [validb] *)
Module StrongShiftValidFullSetOTWL (T : StrongShiftValidFullOTWithLeibniz) 
                                                <: StrongShiftValidFullSetOTWLInterface T.

  Include StrongShiftValidSetOTWL T.

  (** *** Definition *)
  Section definition.

    Definition validb (k : nat) (s : t) := (for_all (fun v => T.validb k v) s).

  End definition.

  (** *** Valid *)
  Section valid.

    Fact proper_valid : forall k, Proper (T.eq ==> Logic.eq) (fun (v : elt) => T.validb k v).
    Proof. repeat red; intros; subst; apply T.eq_leibniz in H; now subst. Qed.

    #[local] Hint Resolve proper_valid : core.

    Lemma validb_valid : forall k t, validb k t = true <-> valid k t. 
    Proof.
      unfold valid,validb; split; intros; rewrite for_all_spec in *; unfold For_all in *;
      try (repeat red; intros; now subst); auto.
      - intros; rewrite <- T.validb_valid; auto.
      - intros; rewrite T.validb_valid; auto.
    Qed.

    Lemma validb_nvalid : forall k t, validb k t = false <-> ~ valid k t.
    Proof.
      intros; rewrite <- not_true_iff_false; split; intros; intro.
      - apply H; now rewrite validb_valid. 
      - apply H; now rewrite <- validb_valid.
    Qed.

    Lemma validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
    Proof. repeat red; intros; subst; apply eq_leibniz in H0; now subst. Qed.

  End valid.

End StrongShiftValidFullSetOTWL.
