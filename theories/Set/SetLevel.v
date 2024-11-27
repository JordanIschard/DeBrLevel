From Coq Require Import MSets Lia.
From DeBrLevel Require Import Level LevelInterface SetLevelInterface SetOTwL SetOTwLInterface.

(** * Implementation - Leveled Set 

We use the notation [OT] when elements satisfy [Ordered Type] module, [WL] when the embedded type has an equivalent equality to the one from Coq, [FL] when the embbeded type has boolean version of [Wf] and finally [BD] when elements does not contains binders associated to levels.
*)

(** ** Leveled Set Implementation - [OT] and [WL] *)
Module IsLvlSet (T : IsLvlOTWL) (Import St : SetOTWithLeibnizInterface T) <: IsLvlSetInterface T St.


(** *** Definitions *)

Definition t := t.

Definition eq := eq.
Definition eq_equiv := eq_equiv.
Definition eq_dec := eq_dec.
Definition eq_leibniz := eq_leibniz.

Definition lt := lt.
Definition lt_strorder := lt_strorder.
Definition lt_compat := lt_compat.

Definition compare := compare.
Definition compare_spec := compare_spec.

Definition shift (m k: Lvl.t) (s: t) : t := map (T.shift m k) s.
Definition Wf (k: Lvl.t) (s: t) := (For_all (T.Wf k) s).

(** *** Properties *)

(** **** [Wf] properties *)
Section specs.

Variable m n k : Lvl.t.
Variable v : elt.
Variable s s' : t.


#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf.
Proof.
  repeat red; intros; apply eq_leibniz in H0; subst; split; auto.
Qed.

Lemma Wf_unfold : Wf m s <-> (For_all (T.Wf m) s).
Proof. unfold Wf; split; auto. Qed.

Lemma Wf_add_iff : Wf m (add v s) <-> T.Wf m v /\ Wf m s.
Proof.
  split.
  - intros; unfold Wf,For_all in *; split.
    -- apply H; apply add_spec; now left.
    -- intros. apply H; apply add_spec; now right.
  - intros [Hwfv HWfs].
    unfold Wf, For_all in *.
    intros x HIn.
    apply add_spec in HIn as [Heq | HIn].
    -- now apply T.eq_leibniz in Heq; subst.
    -- now apply HWfs.
Qed.

Lemma Wf_empty : Wf m empty.
Proof. intros; unfold Wf,For_all; intros; inversion H. Qed.

Lemma Wf_union_iff : Wf m (union s s') <-> Wf m s /\ Wf m s'.
Proof.
  split; intros; unfold Wf,For_all in *.
  - split; intros; apply H; rewrite union_spec; auto.
  - intros; destruct H; rewrite union_spec in *; destruct H0; auto.
Qed.

Lemma Wf_singleton_iff : Wf m (singleton v) <-> T.Wf m v.
Proof.
  split; intros; unfold Wf,For_all in *.
  - apply H; now rewrite singleton_spec.
  - intros; rewrite singleton_spec in H0. apply T.eq_leibniz in H0; now subst.
Qed.

Lemma Wf_in : Wf m s -> In v s -> T.Wf m v.
Proof.
  unfold Wf,For_all in *; intros; now apply H.
Qed.

Lemma Wf_weakening : (m <= n) -> Wf m s -> Wf n s.
Proof. 
  intros; unfold Wf,For_all in *; intros; apply H0 in H1. 
  eapply T.Wf_weakening; eauto.
Qed.

(** **** [shift] properties *)

#[local] Hint Resolve eq_equiv transpose_1 proper_1 : core.

Lemma shift_union :
  shift m k (union s s') = union (shift m k s) (shift m k s').
Proof. intros; unfold shift; now rewrite map_union_spec. Qed.

Lemma shift_Empty : Empty s -> shift m k s = empty.
Proof. intros; unfold shift; now apply map_Empty_spec. Qed.

Lemma shift_empty : shift m k empty = empty.
Proof. intros; unfold shift; now apply map_empty_spec. Qed.

Lemma shift_singleton : shift m k (singleton v) = singleton (T.shift m k v).
Proof. intros; unfold shift; now apply map_singleton_spec. Qed.

Lemma shift_add_notin :
  ~ In v s -> shift m k (add v s) = add (T.shift m k v) (shift m k s).
Proof. intros; unfold shift; now apply map_add_notin_spec. Qed.

Lemma shift_add_in :
  In v s -> shift m k (add v s) = (shift m k s).
Proof. intros; unfold shift; now apply map_add_in_spec. Qed.

Lemma shift_in_iff :
  In v s <-> In (T.shift m k v) (shift m k s).
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

Lemma shift_add :
  shift m k (add v s) = add (T.shift m k v) (shift m k s).
Proof.
  intros; destruct (In_dec v s).
  - rewrite shift_add_in; auto. apply eq_leibniz; rewrite add_equal.
    -- reflexivity.
    -- now apply shift_in_iff.
  - now  apply shift_add_notin.
Qed.

Lemma shift_in_e :
  In v (shift m k s) -> 
  exists v', v = (T.shift m k v') /\  In (T.shift m k v') (shift m k s).
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

Lemma shift_notin_iff : ~ In v s <-> ~ In (T.shift m k v) (shift m k s).
Proof.
  intros; split; unfold not; intros; apply H.
  - now rewrite <- shift_in_iff in H0.
  - now rewrite <- shift_in_iff.
Qed.

End specs.

Lemma shift_remove (m k: Lvl.t) (v: elt) (s: t) :
  shift m k (remove v s) = remove (T.shift m k v)(shift m k s).
Proof.
  revert m k v;
  induction s using set_induction; intros.
  - symmetry; rewrite shift_Empty; auto. 
    apply empty_is_empty_1 in H. eapply Equal_remove in H; apply eq_leibniz in H; rewrite H.
    apply eq_leibniz. split; intros.
    -- rewrite remove_spec in H0; destruct H0. inversion H0.
    -- apply shift_in_e in H0.
        destruct H0. destruct H0.
        apply shift_in_iff in H1. rewrite remove_spec in H1; destruct H1; inversion H1.
  
  - apply Add_inv in H0; subst. apply eq_leibniz; split; intros.
    -- apply shift_in_e in H0. destruct H0; destruct H0.
        apply shift_in_iff in H1. apply remove_spec in H1 as [H1 H1'].
        rewrite remove_spec; split; subst.
        + now apply shift_in_iff.
        + intro; apply H1'. eapply T.shift_eq_iff; eauto.
    -- apply remove_spec in H0 as [H0 H0']. rewrite shift_add_notin in H0; auto.
        apply add_spec in H0; destruct H0; subst.
        + apply T.eq_leibniz in H0; subst; apply shift_in_iff. apply remove_spec; split.
          ++ apply add_spec; now left.
          ++ intro; apply H0'; subst; auto; apply T.eq_leibniz in H0;
            subst; reflexivity.
        + apply shift_in_e in H0; destruct H0 as [y [Heq HIn]]; subst.
          apply shift_in_iff. rewrite remove_spec; split.
          ++ apply add_spec; right; now apply shift_in_iff in HIn.
          ++ intro; apply H0'; apply T.eq_leibniz in H0; now subst.
Qed.

Lemma shift_eq_iff (m k: Lvl.t) (s s': t) :
  eq s s' <-> eq (shift m k s) (shift m k s').
Proof.
  split.
  - intro Heq; apply eq_leibniz in Heq; now subst.
  - revert m k s'; induction s using set_induction; intros m k s'' Heq.
    -- apply empty_is_empty_1 in H as H'.
        apply eq_leibniz in H'; subst. eapply shift_Empty in H; rewrite H in *.
        symmetry in Heq. clear H. symmetry. revert m k Heq.
        induction s'' using set_induction; intros.
        * apply empty_is_empty_1 in H; now rewrite H.
        * apply Add_inv in H0; subst. rewrite shift_add_notin in Heq; auto.

          assert (eq (add (T.shift m k x) (shift m k s''1)) empty).
          { now rewrite Heq. }

          apply empty_is_empty_2 in H0; unfold Empty in H0; exfalso.
          apply (H0 (T.shift m k x)). rewrite add_spec; now left.
    -- apply Add_inv in H0; subst.

        assert (forall s s' v, (add v s) = s' -> In v s').
        { intros; subst; apply add_spec; now left. }

        rewrite shift_add_notin in Heq; auto. apply eq_leibniz in Heq.
        apply H0 in Heq as Heq'. apply add_remove in Heq' as Htmp.
        apply eq_leibniz in Htmp. rewrite <- Htmp in Heq; clear Htmp.
        rewrite <- shift_in_iff in Heq'. apply add_remove in Heq' as Htmp.
        apply eq_leibniz in Htmp. rewrite <- Htmp; clear Htmp.

        assert (((add x s1) = (add x (remove x s''))) -> 
                (eq (add x s1) (add x (remove x s'')))) by (intro Hc; now rewrite Hc).
        
        apply H1; clear H1. f_equal. apply eq_leibniz; eapply IHs1.
        rewrite <- add_eq_leibniz in Heq; eauto.
        * rewrite Heq. now rewrite shift_remove.
        * now apply shift_notin_iff.
        * rewrite remove_spec; intro. destruct H1; auto.
          apply H2; reflexivity.
Qed.

Lemma shift_inter (m k: Lvl.t) (s s': t) : 
  shift m k (inter s s') = inter (shift m k s) (shift m k s').
Proof.
  revert s'; induction s using set_induction; intros.
  - apply empty_inter_1 with (s' := s') in H as H'.
    unfold shift; rewrite map_Empty_spec; auto.
    symmetry; rewrite map_Empty_spec; auto. apply eq_leibniz; split; intros.
    -- rewrite inter_spec in H0; destruct H0; assumption.
    -- inversion H0.

  - apply Add_inv in H0; subst; unfold shift.
    destruct (In_dec x s').
    -- rewrite inter_in_add_spec; auto. rewrite map_add_notin_spec.
      + symmetry; rewrite map_add_notin_spec; auto.
        rewrite (shift_in_iff m k) in i.
        rewrite inter_in_add_spec; auto.
        unfold shift in *. now rewrite IHs1.
      + unfold not; intros; rewrite inter_spec in H0; destruct H0; contradiction.

    -- rewrite inter_notin_add_spec; auto. rewrite map_add_notin_spec; auto.
      rewrite (shift_notin_iff m k) in n.
      rewrite inter_notin_add_spec; auto.
      unfold shift in *. now rewrite IHs1.
Qed.

Lemma shift_diff (m k: Lvl.t) (s s': t) :
  shift m k (diff s s') = (diff (shift m k s) (shift m k s')).
Proof.
  revert s'; induction s using set_induction; intros.

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
        replace (shift m k (add x (diff s1 s')))
        with ( add (T.shift m k x) (shift m k (diff s1 s'))) in H1.
        ++ rewrite add_spec in H1; destruct H1.
            * rewrite H0; split.
              ** unfold shift; rewrite map_add_notin_spec; auto.
                rewrite add_spec; left; reflexivity.
              ** now apply shift_notin_iff.

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

Lemma shift_zero_refl (m: Lvl.t) (s: t) :
  eq (shift m 0 s) s.
Proof.
  unfold shift; intros. induction s using set_induction.
  - apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.  
    now rewrite map_empty_spec.
  - apply Add_inv in H0; subst; rewrite map_add_notin_spec; auto.
    apply eq_leibniz in IHs1; rewrite IHs1; rewrite T.shift_zero_refl; reflexivity.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof. 
  red; red; red; red; intros; subst. 
  apply eq_leibniz in H1; now subst.
Qed.

Lemma shift_trans (m n k: Lvl.t) (s: t) :
  eq (shift m n (shift m k s)) (shift m (n + k) s).
Proof.
  induction s using set_induction; unfold shift.
  - repeat rewrite map_Empty_spec; auto; reflexivity.
  - apply Add_inv in H0; subst. repeat rewrite map_add_notin_spec; auto.
    -- split; intros HI; rewrite add_spec in *; destruct HI.
      + left; rewrite H0; now rewrite T.shift_trans.
      + right; unfold shift in IHs1. now rewrite <- IHs1.
      + left; rewrite H0; now rewrite T.shift_trans.
      + right. unfold shift in IHs1. now rewrite IHs1.
    -- rewrite shift_notin_iff in H; eauto.
Qed.

Lemma shift_permute (m n k: Lvl.t) (s: t) :
  eq (shift m n (shift m k s)) (shift m k (shift m n s)).
Proof.
  induction s using set_induction; unfold shift.
  - repeat rewrite map_Empty_spec; auto; reflexivity.
  - apply Add_inv in H0; subst; repeat rewrite map_add_notin_spec; auto;
    try (rewrite shift_notin_iff in H; now eauto).
    split; intros; rewrite add_spec in *; destruct H0.
    -- left; rewrite H0; apply T.shift_permute.
    -- right; unfold shift in *; now rewrite <- IHs1.
    -- left; rewrite H0; apply T.shift_permute.
    -- right; unfold shift in *; now rewrite IHs1.
Qed.

Lemma shift_unfold (m n k: Lvl.t) (t: t) :
  eq (shift m (n + k) t) (shift (m + n) k (shift m n t)). 
Proof.
  induction t using set_induction.
  - unfold shift; repeat rewrite map_Empty_spec; auto. reflexivity.
  - apply Add_inv in H0; subst. repeat rewrite shift_add_notin; eauto.
    -- rewrite T.shift_unfold; rewrite IHt1; reflexivity.
    -- now apply shift_notin_iff.
Qed.

Lemma shift_unfold_1 (m n p: Lvl.t) (t: t) :
  m <= n -> n <= p -> 
  eq (shift n (p - n) (shift m  (n - m) t)) (shift m (p - m) t).
Proof.
  induction t using set_induction; intros.
  - unfold shift; repeat rewrite map_Empty_spec; auto. reflexivity.
  - apply Add_inv in H0; subst. repeat rewrite shift_add_notin; eauto.
    -- rewrite T.shift_unfold_1; auto; rewrite IHt1; auto; reflexivity.
    -- now apply shift_notin_iff.
Qed.

(** **** Interaction properties between [Wf] and [shift] *)

Theorem shift_preserves_wf_1 (m n k: Lvl.t) (s: t) :
  Wf n s -> Wf (n + k) (shift m k s).
Proof.
  unfold Wf,For_all in *; intros.
  apply shift_in_e in H0; destruct H0 as [y [Heq HIn]]; subst.
  apply T.shift_preserves_wf_1; apply H; now rewrite <- shift_in_iff in HIn.
Qed.

Theorem shift_preserves_wf (m n: Lvl.t) (s: t) :
  Wf m s -> Wf (m + n) (shift m n s).
Proof. intros; now apply shift_preserves_wf_1. Qed.

Lemma shift_preserves_wf_zero (m: Lvl.t) (s: t) : Wf m s -> Wf m (shift m 0 s).
Proof. intros; replace m with (m + 0); try lia; now apply shift_preserves_wf_1. Qed.

Lemma shift_preserves_wf_gen (m m' n k: Lvl.t) (s: t) :
  n <= k -> m <= m' -> n <= m -> k <= m' -> k - n = m' - m -> 
  Wf m s -> Wf m' (shift n (k - n) s).
Proof.
  unfold Wf,For_all in *; intros. apply shift_in_e in H5. 
  destruct H5 as [y [Heq HIn]]; subst.
  apply T.shift_preserves_wf_gen with (m := m); auto.
  apply H4. now rewrite <- shift_in_iff in HIn.
Qed.

Lemma shift_preserves_wf_2 (m n: Lvl.t) (s: t) :
  m <= n -> Wf m s -> 
  Wf n (shift m (n - m) s).
Proof. intros. eapply shift_preserves_wf_gen; eauto. Qed.

End IsLvlSet.


(** ---- *)


(** ** Leveled Set Implementation - [OT], [BD] and [WL] *)
Module IsBdlLvlSet (T : IsBdlLvlOTWL) (Import Se : SetOTWithLeibnizInterface T) <: IsBdlLvlOTWL.

Include IsLvlSet T Se.

Lemma shift_wf_refl (m n: Lvl.t) (s: t) :
  Wf m s -> eq (shift m n s) s.
Proof.
  induction s using set_induction; intros.
  - apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.
    now rewrite shift_empty.
  
  - apply Add_inv in H0; subst.
    rewrite shift_add_notin; try assumption.
    apply Wf_add_iff in H1; destruct H1; f_equal.
    rewrite T.shift_wf_refl; auto.
    apply IHs1 in H1; now rewrite H1.
Qed.

Lemma Wf_in_iff (m n : Lvl.t) (r : elt) (s : t):
  Wf m s -> In r (shift m n s) <-> In r s.
Proof.
  induction s using set_induction; intro Hv; split.
  - intro HIn; rewrite shift_Empty in *; auto; inversion HIn.
  - intro HIn; unfold Empty in *; exfalso; now apply (H r).
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin in *; auto.
    apply Wf_add_iff in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite H0. rewrite T.shift_wf_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite <- IHs1; eauto.
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin in *; auto.
    apply Wf_add_iff in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite H0. rewrite T.shift_wf_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite IHs1; eauto.
Qed.

End IsBdlLvlSet.


(** ---- *)


(** ** Leveled Set Implementation - [OT], [FL] and [WL] *)
Module IsLvlFullSet 
  (T : IsLvlFullOTWL) (Import Se : SetOTWithLeibnizInterface T) <: IsLvlFullSetInterface T Se.

Include IsLvlSet T Se.

Definition is_wf (n : Lvl.t) (s : t) := (for_all (fun v => T.is_wf n v) s).

Lemma Wf_is_wf_true (m: Lvl.t) (s: t) : Wf m s <-> is_wf m s = true. 
Proof.
  unfold Wf,is_wf; split; intros; rewrite for_all_spec in *; unfold For_all in *;
  try (repeat red; intros; now subst); auto.
  - intros; rewrite <- T.Wf_is_wf_true; auto.
  - repeat red; intros; subst. apply T.eq_leibniz in H0; now subst.
  - intros; rewrite T.Wf_is_wf_true; auto.
  - repeat red; intros; subst. apply T.eq_leibniz in H0; now subst.
Qed.

Lemma notWf_is_wf_false (m: Lvl.t) (s: t) : ~ Wf m s <-> is_wf m s = false.
Proof.
  intros; rewrite <- not_true_iff_false; split; intros; intro.
  - apply H; now rewrite Wf_is_wf_true. 
  - apply H; now rewrite <- Wf_is_wf_true.
Qed.

#[export] Instance is_wf_eq : Proper (Logic.eq ==> eq ==> Logic.eq) is_wf.
Proof. repeat red; intros; subst; apply eq_leibniz in H0; now subst. Qed.

End IsLvlFullSet.


(** ---- *)


(** ** Leveled Set Implementation - [OT], [FL], [BD] and [WL] *)
Module IsBdlLvlFullSet (T : IsBdlLvlFullOTWL) 
                       (Import Se : SetOTWithLeibnizInterface T) <: IsBdlLvlFullSetInterface T Se.

Include IsLvlFullSet T Se.

Lemma shift_wf_refl (m n: Lvl.t) (s: t) :
  Wf m s -> eq (shift m n s) s.
Proof.
  induction s using set_induction; intros.
  - apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.
    now rewrite shift_empty.
  
  - apply Add_inv in H0; subst.
    rewrite shift_add_notin; try assumption.
    apply Wf_add_iff in H1; destruct H1; f_equal.
    rewrite T.shift_wf_refl; auto.
    apply IHs1 in H1; now rewrite H1.
Qed.

Lemma Wf_in_iff (m k: Lvl.t) (r: elt) (s: t) :
  Wf m s -> In r (shift m k s) <-> In r s.
Proof.
  induction s using set_induction; intro Hv; split.
  - intro HIn; rewrite shift_Empty in *; auto; inversion HIn.
  - intro HIn; unfold Empty in *; exfalso; now apply (H r).
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin in *; auto.
    apply Wf_add_iff in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite H0. rewrite T.shift_wf_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite <- IHs1; eauto.
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin in *; auto.
    apply Wf_add_iff in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite H0. rewrite T.shift_wf_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite IHs1; eauto.
Qed.

End IsBdlLvlFullSet.


(** ---- *)


(** * Make - Leveled Set *)

Module MakeLvlSet (T : IsLvlOTWL) <: IsLvlOTWL.

Module St := SetOTWithLeibniz T.
Include IsLvlSet T St.
Import St.

End MakeLvlSet.


Module MakeBdlLvlSet (T : IsBdlLvlOTWL) <: IsBdlLvlOTWL.

Module St := SetOTWithLeibniz T.
Include IsBdlLvlSet T St.
Import St.

End MakeBdlLvlSet.


Module MakeLvlFullSet (T : IsLvlFullOTWL) <: IsLvlFullOTWL.

Module St := SetOTWithLeibniz T.
Include IsLvlFullSet T St.
Import St.

End MakeLvlFullSet.


Module MakeBdlLvlFullSet (T : IsBdlLvlFullOTWL) <: IsBdlLvlFullOTWL.

Module St := SetOTWithLeibniz T.
Include IsBdlLvlFullSet T St.
Import St.

End MakeBdlLvlFullSet.