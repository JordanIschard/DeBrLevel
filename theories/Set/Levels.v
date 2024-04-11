From Coq Require Import MSets Lia.
Require Import Kernel.LevelInterface Kernel.Level.
Require Import SetLevelInterface SetLevel.

(** * Implementation -- Level Set

  When the set of leveled elements is directly a set of levels, we can
  prove more lemmas because of the correspondence between the levels
  used by shift and the leveled element.
*)
Module Levels <: StrongShiftValidFullSetOTWLInterface Level.

  Include StrongShiftValidFullSetOTWLInterface Level.

  Lemma shift_permute_1 : forall (t : t) lb k k',
    eq (shift lb k (shift lb k' t)) (shift (lb + k) k' (shift lb k t)).
  Proof.
    intro t; induction t using set_induction; intros.
    - repeat rewrite shift_Empty_spec; eauto. reflexivity.
    - apply Add_inv in H0; subst. repeat rewrite shift_add_notin_spec; auto.
      -- split; intros; rewrite add_spec in *; destruct H0;
          try (left; rewrite H0; now rewrite Level.shift_permute_1);
          right; now rewrite IHt1 in *.
      -- rewrite shift_notin_spec in H; eauto.
      -- rewrite shift_notin_spec in H; eauto.
  Qed.

  Lemma shift_permute_2 : forall (t : t) lb lb' k k',
    lb <= lb' -> eq (shift lb k (shift lb' k' t)) (shift (lb' + k) k' (shift lb k t)).
  Proof.
    intro t. induction t using set_induction; intros.
    - repeat rewrite shift_Empty_spec; eauto; reflexivity.
    - apply Add_inv in H0; subst. repeat rewrite shift_add_notin_spec; auto.
      -- split; intros; rewrite add_spec in *; destruct H0.
          + subst; left; now apply Level.shift_permute_2.
          + right. rewrite IHt1 in H0; auto.
          + subst; left; symmetry; now apply Level.shift_permute_2.
          + right. rewrite <- IHt1 in H0; auto.
      -- rewrite shift_notin_spec in H; eauto.
      -- rewrite shift_notin_spec in H; eauto.
  Qed.

End Levels.