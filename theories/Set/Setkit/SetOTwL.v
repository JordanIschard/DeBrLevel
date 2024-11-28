From Coq Require Import MSets Classical_Prop.
From DeBrLevel Require Import SetOTwLInterface.

(** * Implementation - [MSet] extension *)

(** ** Extension of [MSet] *)
Module SetOTWithLeibniz (Elt : MSetList.OrderedTypeWithLeibniz) <: (SetOTWithLeibnizInterface Elt).

Include MSetList.MakeWithLeibniz Elt.
Include MSetProperties.WPropertiesOn Elt.

(** *** Definitions *)

Definition ltb (s s' : t) : bool :=
  match compare s s' with
    | Lt => true
    | _  => false
  end
.

Definition map (f : elt -> elt) (s : t) : t := fold (fun r acc => add (f r) acc) s empty.

(** *** Properties *)

(** **** Some facts *)

Fact Add_inv (x: elt) (s s': t) : Add x s s' -> add x s = s'.
Proof. 
  intros; apply Add_Equal in H; apply eq_leibniz in H; now subst.
Qed.

#[export] Instance proper_1 (f: elt -> elt) :
  Proper (Elt.eq ==> eq ==> eq) (fun (r0 : elt) (acc : t) => add (f r0) acc).
Proof. 
  repeat red; intros; rewrite H0; apply Elt.eq_leibniz in H.
  now rewrite H. 
Qed.

Fact transpose_1 (f: elt -> elt) :
  transpose eq (fun (r0 : elt) (acc : t) => add (f r0) acc).
Proof.
  repeat red; intros; split; repeat rewrite add_spec; intros [|[|]]; auto.
Qed.

Section props.

Variable x y: elt.
Variable s s': t.

(** **** [eq] and [lt] properties *)

Lemma eqb_refl : equal s s = true.
Proof. intros; rewrite equal_spec; reflexivity. Qed.

Lemma add_eq_leibniz :
  ~ In x s -> ~ In x s' -> s = s' <-> (add x s) = (add x s').
Proof.
  split.
  - intros; subst; auto.
  - intros. assert (eq (add x s) (add x s')) by now rewrite H1.
    apply eq_leibniz; split; intros.
    -- destruct (H2 a). destruct (Elt.eq_dec a x); subst.
        + apply Elt.eq_leibniz in e; subst; contradiction.
        + assert (In a (add x s') -> In a s').
          { intros. apply add_spec in H6. destruct H6; subst; try contradiction; auto. }
          apply H6. apply H4. apply add_spec; now right.
    -- destruct (H2 a). destruct (Elt.eq_dec a x); subst.
        + apply Elt.eq_leibniz in e; subst; contradiction.
        + assert (In a (add x s) -> In a s).
          { intros. apply add_spec in H6. destruct H6; subst; try contradiction; auto. }
          apply H6. apply H5. apply add_spec; now right.
Qed.

Lemma ltb_lt : ltb s s' = true <-> lt s s'.
Proof.
  split; intros.
  - unfold ltb in *; destruct (compare s s') eqn:Heq; try now inversion H.
    clear H. assert (CompSpec eq lt s s' (compare s s')) by apply compare_spec.
    rewrite Heq in H; now inversion H.
  - assert (StrictOrder lt) by apply lt_strorder;
    assert (CompSpec eq lt s s' (compare s s')) by apply compare_spec; unfold ltb; 
    destruct (compare s s') eqn:Heq; auto.
    -- unfold CompSpec in H1; inversion H1; apply eq_leibniz in H2; subst.
        inversion H0. repeat red in StrictOrder_Irreflexive; exfalso; apply (StrictOrder_Irreflexive s' H).
    -- exfalso. inversion H0. repeat red in StrictOrder_Irreflexive,StrictOrder_Transitive.
      inversion H1. apply (StrictOrder_Transitive s s' s) in H2; auto.
      apply StrictOrder_Irreflexive in H2; inversion H2.
Qed.

Lemma gt_neq_nlt : ~ eq s s' -> ~ lt s s' -> lt s' s.
Proof.
  intros. assert (CompSpec eq lt s s' (compare s s')) by apply compare_spec.
  destruct (compare s s'); inversion H1; auto; contradiction.
Qed.

(** **** [In] properties *)

Lemma diff_in_add_spec : In x s' -> (diff (add x s) s') = (diff s s').
Proof.
  intros; apply eq_leibniz; split; intros; rewrite diff_spec in *; destruct H0; split; auto.
  - rewrite add_spec in H0; destruct H0; auto; rewrite H0 in *; contradiction.
  - rewrite add_spec; auto.
Qed.

Lemma union_add_spec : (union (add x s) s') =  add x (union s s').
Proof.
  intros; apply eq_leibniz; split; rewrite union_spec; rewrite add_spec; intros.
  - destruct H as [[|]|]; rewrite add_spec; auto;
    rewrite union_spec; auto.
  - rewrite union_spec in H; destruct H as [|[|]];
    rewrite add_spec; auto.
Qed.

Lemma inter_in_add_spec : In x s' -> (inter (add x s) s') = add x (inter s s').
Proof.
  intros; apply eq_leibniz; split; rewrite inter_spec; rewrite add_spec; intros.
  - destruct H0 as [[|] ].
    -- rewrite add_spec; auto.
    -- rewrite add_spec; rewrite inter_spec; auto.
  - rewrite inter_spec in H0; destruct H0.
    -- rewrite H0 in *; split; auto; rewrite add_spec; left; reflexivity.
    -- destruct H0; split; auto; rewrite add_spec; auto.
Qed.

Lemma diff_notin_add_spec : ~ In x s' -> (diff (add x s) s') = add x (diff s s').
Proof.
  intros; apply eq_leibniz; split; intros.
  - rewrite diff_spec in *; destruct H0; rewrite add_spec in *;
    destruct H0; auto. right; rewrite diff_spec; split; assumption.
  - rewrite diff_spec; rewrite add_spec in *; destruct H0.
    -- rewrite H0 in *; split; auto; apply Elt.eq_leibniz in H0; subst;
        auto; now left.
    --  rewrite diff_spec in H0; destruct H0; split; auto.
Qed.

Lemma inter_notin_add_spec : ~ In x s' -> (inter (add x s) s') =  (inter s s').
Proof.
  intros; apply eq_leibniz; split; rewrite inter_spec; intros.
  - rewrite add_spec in H0; destruct H0; destruct H0.
    -- rewrite H0 in *; contradiction.
    -- rewrite inter_spec; split; assumption.
  - rewrite inter_spec; destruct H0; split; auto.
    rewrite add_spec; right; assumption.
Qed.

Lemma add_notin_spec : ~ In x (add y s) <-> x <> y /\ ~ In x s.
Proof.
  split; intros.
  - split; unfold not in *; intros; 
    apply H; apply add_spec; auto; subst;
    now left.
  - destruct H; unfold not in *; intros.
    rewrite add_spec in H1; destruct H1; auto.
    apply Elt.eq_leibniz in H1; subst; now apply H.
Qed. 

Lemma union_notin_spec : ~ In x (union s s') <-> ~ In x s /\ ~ In x s'.
Proof. 
  split; unfold not; intros.
  - split; intro; apply H; apply union_spec; auto.
  - destruct H; apply union_spec in H0 as [H0 | H0]; auto. 
Qed.

Lemma diff_notin_spec : ~ In x (diff s s') <-> ~ In x s \/ In x s'.
Proof.
  unfold not; split; intros.
  - apply NNPP; unfold not; intros. apply H. apply diff_spec; split.
    -- apply NNPP; unfold not; intros. apply H0; left; auto.
    -- unfold not; intros; apply H0. now right.
  - apply diff_spec in H0 as [H0 H0']. destruct H; auto.
Qed.

Lemma singleton_notin_spec : ~ In x (singleton  y) <-> x <> y.
Proof.
  split; unfold not; intros.
  - apply H; apply singleton_spec; subst; reflexivity.
  - apply H; apply singleton_spec in H0; now apply Elt.eq_leibniz in H0.
Qed.
  

End props.

#[local] Hint Resolve eq_equiv transpose_1 proper_1 : core.

(** **** [map] properties *)

Lemma map_Empty_spec (s: t) (f: elt -> elt) : Empty s -> map f s = empty.
Proof.
  intros; unfold map; apply empty_is_empty_1 in H. 
  apply eq_leibniz in H; subst; now rewrite fold_empty.
Qed.

Lemma map_empty_spec (f: elt -> elt) : map f empty = empty.
Proof.
  intros; unfold map; now rewrite fold_empty. 
Qed.

Lemma map_singleton_spec (x: elt) (f: elt -> elt) : map f (singleton x) = singleton (f x).
Proof.
  intros; unfold map. 
  replace (singleton x) with (add x empty).
  - apply eq_leibniz; rewrite fold_add; auto.
    -- rewrite fold_empty; symmetry; apply singleton_equal_add.
    -- unfold not; intros H; inversion H.
  - apply eq_leibniz; apply singleton_equal_add.
Qed.

Lemma map_in_spec (x: elt) (s: t) (f: elt -> elt) : In x s -> In (f x) (map f s).
Proof.
  induction s using set_induction; intro HI.
  - apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.
    inversion HI.

  - intros; apply Add_inv in H0; subst; unfold map in *; rewrite add_spec in *.
    rewrite fold_add; auto; rewrite add_spec. destruct HI; auto. 
    apply Elt.eq_leibniz in H0; subst; now left.
Qed.

Lemma map_add_notin_spec (x: elt) (s: t) (f: elt -> elt) : 
  ~ In x s -> map f (add x s) = add (f x) (map f s).
Proof.
  intros; apply eq_leibniz; unfold map; rewrite fold_add; now auto.
Qed.

Lemma map_add_in_spec (x: elt) (s: t) (f: elt -> elt) : In x s -> map f (add x s) = (map f s).
Proof.
  intros; apply eq_leibniz; unfold map; rewrite add_fold; now auto.
Qed.

Fact union_sym_leibniz (s s': t) : union s s' = union s' s.
Proof.
  apply eq_leibniz.
  now rewrite union_sym.
Qed.

Fact add_shadow_leibniz (x: elt) (s: t) : add x (add x s) = add x s.
Proof.
  apply eq_leibniz.
  rewrite add_equal.
  - reflexivity.
  - rewrite add_spec; now left.
Qed. 

Lemma map_union_spec (s s': t) (f: elt -> elt) : 
  (map f (union s s')) = union (map f s) (map f s').
Proof.
  apply eq_leibniz.
  revert s f s'; clear; intro s. 
  induction s using set_induction; intros f s'.
  -  assert (HUn: union s s' = s').
    -- apply eq_leibniz. 
       rewrite empty_union_1; auto; reflexivity.
    -- rewrite HUn.
       rewrite (map_Empty_spec s); auto.
       rewrite empty_union_1; auto.
       reflexivity.
  - apply Add_inv in H0; subst.
    rewrite (map_add_notin_spec _ s1); auto.
    do 2 rewrite union_add_spec.
    destruct (In_dec x s') as [HIn | HnIn].
    -- rewrite union_sym_leibniz; symmetry;
       rewrite union_sym_leibniz; symmetry. 
       apply add_remove in HIn as Heq.
       apply eq_leibniz in Heq; rewrite <- Heq; clear Heq.
       rewrite union_add_spec.
       rewrite add_shadow_leibniz.
       rewrite map_add_notin_spec.
       + rewrite union_sym_leibniz. 
         rewrite IHs1.
         rewrite union_sym_leibniz.
         symmetry.
         rewrite map_add_notin_spec.
         ++ rewrite union_add_spec.
            now rewrite add_shadow_leibniz.
         ++ rewrite remove_spec; intros []. 
            apply H1; reflexivity.
       + rewrite union_notin_spec; split; auto.
         rewrite remove_spec; intros [].
         apply H1; reflexivity.
    -- rewrite map_add_notin_spec.
       + now rewrite IHs1.
       + rewrite union_notin_spec; split; assumption.
Qed.

End SetOTWithLeibniz.