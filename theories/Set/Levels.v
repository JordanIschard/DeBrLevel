From Coq Require Import MSets Lia.
From DeBrLevel Require Import LevelInterface Level SetLevelInterface SetLevel SetOTwL SetOTwLInterface.

(** * Implementation - Set of levels

  A level set has extra permutation properties because of elements of the set can
  interact with [shift] parameters. We also define [new_key] function as done for maps.
*)
Module Levels (Import Se : SetOTWithLeibnizInterface Level) <: IsLvlSetLVLInterface Se.

Include IsBdlLvlFullSet Level Se.

(** *** Definitions *)

Definition max_key (s: t) := fold (Nat.max) s 0.
Definition new_key (s: t) := if is_empty s then 0 else S (max_key s).

(** *** Properties *)

(** **** [max_key] properties *)

#[export] Instance max_eq : Proper (Logic.eq ==> Logic.eq ==> Logic.eq) max := _.
#[export] Instance logic_eq : Equivalence Logic.eq := _.

Lemma max_transpose : transpose Logic.eq max.
Proof.
 intros x y z; lia.
Qed.

#[export] Hint Resolve max_eq max_transpose logic_eq : core.

#[export] Instance max_key_eq : Proper (eq ==> Logic.eq) max_key.
Proof.
  intros s s' Heq.
  apply eq_leibniz in Heq; now subst.
Qed. 

Lemma max_key_Empty (s: t) : Empty s -> max_key s = 0.
Proof.
  unfold max_key; intro HEmp.
  apply empty_is_empty_1 in HEmp.
  apply eq_leibniz in HEmp; subst.
  now rewrite fold_empty.
Qed.

Lemma max_key_empty : max_key empty = 0.
Proof. unfold max_key; now rewrite fold_empty. Qed.

Lemma max_key_add_max (v: elt) (s: t) : max_key (add v s) = max v (max_key s).
Proof.
  unfold max_key.
  destruct (In_dec v s).
  - assert (s = add v (remove v s)).
    -- apply eq_leibniz.
       rewrite add_remove; auto; reflexivity.
    -- assert (s = add v s).
       + apply eq_leibniz.
         rewrite add_equal; auto; reflexivity.
       + rewrite <- H0.
         rewrite H.
         rewrite fold_add; auto; try lia.
         rewrite remove_spec; intros [HIn Hc]; contradiction.
  - rewrite fold_add; auto.
Qed.

Lemma max_key_Add_max (v: elt) (s s': t) : Add v s s' -> max_key s' = max v (max_key s).
Proof.
  intro HA.
  apply Add_inv in HA; subst.
  apply max_key_add_max.
Qed.

(** **** [new_key] properties *)

#[export] Instance new_key_eq : Proper (eq ==> Logic.eq) new_key.
Proof.
  intros s s' Heq; unfold new_key.
  rewrite Heq.
  erewrite max_key_eq; eauto. 
Qed.

Lemma new_key_Empty (s: t) : Empty s -> new_key s = 0.
Proof.
  unfold new_key; intro HEmp.
  rewrite <- is_empty_spec in HEmp.
  now rewrite HEmp.
Qed.

Lemma new_key_empty : new_key empty = 0.
Proof.
  apply new_key_Empty.
  apply empty_spec.
Qed.

Lemma new_key_add_max (v: elt) (s: t) : new_key (add v s) = max (S v) (new_key s).
Proof.
  unfold new_key.
  destruct (is_empty s) eqn:Hemp.
  - destruct (is_empty (add v s)) eqn:Hemp'.
    -- apply is_empty_spec in Hemp'.
       exfalso; apply (Hemp' v).
       rewrite add_spec; auto.
    -- rewrite max_key_add_max.
       rewrite max_key_Empty.
       + lia.
       + now apply is_empty_spec.
  - destruct (is_empty (add v s)) eqn:Hemp'.
    -- apply is_empty_spec in Hemp'.
       exfalso; apply (Hemp' v).
       rewrite add_spec; auto.
    -- rewrite max_key_add_max; lia.
Qed.

Lemma new_key_Add_max (v: elt) (s s': t) : Add v s s' -> new_key s' = max (S v) (new_key s).
Proof.
  intro HA.
  apply Add_inv in HA; subst.
  apply new_key_add_max.
Qed.

Lemma new_key_in_spec (v: elt) (s: t) : In v s -> (v < new_key s)%nat.
Proof.
  revert v.
  induction s using set_induction; intros b HIn.
  - exfalso.
    apply (H b HIn).
  - apply Add_inv in H0; subst.
    apply add_spec in HIn as [Heq | HIn]; subst.
    -- rewrite new_key_add_max; lia.
    -- rewrite new_key_add_max.
       apply IHs1 in HIn; lia.
Qed.

(** **** [shift] properties *)

Lemma shift_permute_1 (m n k: Lvl.t) (s: t) :
  eq (shift m n (shift m k s)) (shift (m + n) k (shift m n s)).
Proof.
  induction s using set_induction; intros.
  - repeat rewrite shift_Empty; eauto. reflexivity.
  - apply Add_inv in H0; subst. repeat rewrite shift_add_notin; auto.
    -- split; intros; rewrite add_spec in *; destruct H0;
        try (left; rewrite H0; now rewrite Level.shift_permute_1);
        right; now rewrite IHs1 in *.
    -- rewrite shift_notin_iff in H; eauto.
    -- rewrite shift_notin_iff in H; eauto.
Qed.

Lemma shift_permute_2 (m n k p: Lvl.t) (s: t) :
  m <= n -> eq (shift m k (shift n p s)) (shift (n + k) p (shift m k s)).
Proof.
  induction s using set_induction; intros.
  - repeat rewrite shift_Empty; eauto; reflexivity.
  - apply Add_inv in H0; subst. repeat rewrite shift_add_notin; auto.
    -- split; intros; rewrite add_spec in *; destruct H0.
        + subst; left; now apply Level.shift_permute_2.
        + right. rewrite IHs1 in H0; auto.
        + subst; left; symmetry; now apply Level.shift_permute_2.
        + right. rewrite <- IHs1 in H0; auto.
    -- rewrite shift_notin_iff in H; eauto.
    -- rewrite shift_notin_iff in H; eauto.
Qed.

End Levels.


(** ---- *)


(** * Make - Set of levels *)

Module MakeLVL <: IsBdlLvlFullOTWL.

Module St := SetOTWithLeibniz Level.
Include Levels St.
Import St.

End MakeLVL.