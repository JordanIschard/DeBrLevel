From Coq Require Import MSets Classical_Prop.
From DeBrLevel Require Import SetOTwLInterface.

Module SetOTWithLeibniz (Elt : MSetList.OrderedTypeWithLeibniz) <: (SetOTWithLeibnizInterface Elt).


  Include MSetList.MakeWithLeibniz Elt.
  Include MSetProperties.WPropertiesOn Elt.

  Section definition.


    Definition ltb (s s' : t) : bool :=
      match compare s s' with
        | Lt => true
        | _  => false
      end
    .

    Definition map (f : elt -> elt) (s : t) : t :=
      fold (fun r acc => add (f r) acc) s empty
    .


  End definition.

  Section fact.


    Lemma Add_inv : forall x s s', Add x s s' -> add x s = s'.
    Proof. 
      intros; apply Add_Equal in H; apply eq_leibniz in H; now subst.
    Qed.

    #[global] 
    Instance proper_1 : forall f,
      Proper (Elt.eq ==> eq ==> eq) (fun (r0 : elt) (acc : t) => add (f r0) acc).
    Proof. 
      repeat red; intros; rewrite H0; apply Elt.eq_leibniz in H.
       now rewrite H. Qed.

    Lemma transpose_1 : forall f,
      transpose eq (fun (r0 : elt) (acc : t) => add (f r0) acc).
    Proof.
      repeat red; intros; split; repeat rewrite add_spec; intros [|[|]]; auto.
    Qed.


  End fact.

  Section equality.


    Lemma eqb_refl : forall s, equal s s = true.
    Proof. intros; rewrite equal_spec; reflexivity. Qed.

    Lemma add_eq_leibniz : forall s s' v,
      ~ In v s -> ~ In v s' -> s = s' <-> (add v s) = (add v s').
    Proof.
      split.
      - intros; subst; auto.
      - intros. assert (eq (add v s) (add v s')) by now rewrite H1.
        apply eq_leibniz; split; intros.
        -- destruct (H2 a). destruct (Elt.eq_dec a v); subst.
           + apply Elt.eq_leibniz in e; subst; contradiction.
           + assert (In a (add v s') -> In a s').
             { intros. apply add_spec in H6. destruct H6; subst; try contradiction; auto. }
             apply H6. apply H4. apply add_spec; now right.
        -- destruct (H2 a). destruct (Elt.eq_dec a v); subst.
           + apply Elt.eq_leibniz in e; subst; contradiction.
           + assert (In a (add v s) -> In a s).
             { intros. apply add_spec in H6. destruct H6; subst; try contradiction; auto. }
             apply H6. apply H5. apply add_spec; now right.
    Qed.


  End equality.

  Section lt.


    Lemma ltb_lt : forall s s', ltb s s' = true <-> lt s s'.
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

    Lemma gt_neq_nlt : forall s s', ~ eq s s' -> ~ lt s s' -> lt s' s.
    Proof.
      intros. assert (CompSpec eq lt s s' (compare s s')) by apply compare_spec.
      destruct (compare s s'); inversion H1; auto; contradiction.
    Qed.


  End lt.

  Section in_set.


    Variable x : elt.
    Variable s s' : t.

    Lemma diff_in_add_spec :
      In x s' -> (diff (add x s) s') = (diff s s').
    Proof.
      intros; apply eq_leibniz; split; intros; rewrite diff_spec in *; destruct H0; split; auto.
      - rewrite add_spec in H0; destruct H0; auto; rewrite H0 in *; contradiction.
      - rewrite add_spec; auto.
    Qed.

    Lemma union_add_spec :
      (union (add x s) s') =  add x (union s s').
    Proof.
      intros; apply eq_leibniz; split; rewrite union_spec; rewrite add_spec; intros.
      - destruct H as [[|]|]; rewrite add_spec; auto;
        rewrite union_spec; auto.
      - rewrite union_spec in H; destruct H as [|[|]];
        rewrite add_spec; auto.
    Qed.

    Lemma inter_in_add_spec :
      In x s' -> (inter (add x s) s') = add x (inter s s').
    Proof.
      intros; apply eq_leibniz; split; rewrite inter_spec; rewrite add_spec; intros.
      - destruct H0 as [[|] ].
        -- rewrite add_spec; auto.
        -- rewrite add_spec; rewrite inter_spec; auto.
      - rewrite inter_spec in H0; destruct H0.
        -- rewrite H0 in *; split; auto; rewrite add_spec; left; reflexivity.
        -- destruct H0; split; auto; rewrite add_spec; auto.
    Qed.


  End in_set.

  Section notin_set.

    Variable x r r' : elt.
    Variable s s' s1 s2 : t.

    Lemma diff_notin_add_spec :
      ~ In x s' -> (diff (add x s) s') = add x (diff s s').
    Proof.
      intros; apply eq_leibniz; split; intros.
      - rewrite diff_spec in *; destruct H0; rewrite add_spec in *;
        destruct H0; auto. right; rewrite diff_spec; split; assumption.
      - rewrite diff_spec; rewrite add_spec in *; destruct H0.
        -- rewrite H0 in *; split; auto; apply Elt.eq_leibniz in H0; subst;
           auto; now left.
        --  rewrite diff_spec in H0; destruct H0; split; auto.
    Qed.

    Lemma inter_notin_add_spec :
      ~ In x s' -> (inter (add x s) s') =  (inter s s').
    Proof.
      intros; apply eq_leibniz; split; rewrite inter_spec; intros.
      - rewrite add_spec in H0; destruct H0; destruct H0.
        -- rewrite H0 in *; contradiction.
        -- rewrite inter_spec; split; assumption.
      - rewrite inter_spec; destruct H0; split; auto.
        rewrite add_spec; right; assumption.
    Qed.

    Lemma add_notin_spec :
      ~ In r (add r' s) <-> r <> r' /\ ~ In r s.
    Proof.
      split; intros.
      - split; unfold not in *; intros; 
        apply H; apply add_spec; auto; subst;
        now left.
      - destruct H; unfold not in *; intros.
        rewrite add_spec in H1; destruct H1; auto.
        apply Elt.eq_leibniz in H1; subst; now apply H.
    Qed. 

    Lemma union_notin_spec :
      ~ In r (union s1 s2) <-> ~ In r s1 /\ ~ In r s2.
    Proof. 
      split; unfold not; intros.
      - split; intro; apply H; apply union_spec; auto.
      - destruct H; apply union_spec in H0 as [H0 | H0]; auto. 
    Qed.

    Lemma diff_notin_spec :
      ~ In r (diff s1 s2) <-> ~ In r s1 \/ In r s2.
    Proof.
      unfold not; split; intros.
      - apply NNPP; unfold not; intros. apply H. apply diff_spec; split.
        -- apply NNPP; unfold not; intros. apply H0; left; auto.
        -- unfold not; intros; apply H0. now right.
      - apply diff_spec in H0 as [H0 H0']. destruct H; auto.
    Qed.

    Lemma singleton_notin_spec :
      ~ In r (singleton  r') <-> r <> r'.
    Proof.
      split; unfold not; intros.
      - apply H; apply singleton_spec; subst; reflexivity.
      - apply H; apply singleton_spec in H0; now apply Elt.eq_leibniz in H0.
    Qed.


  End notin_set.

  Section map.


    #[local] Hint Resolve eq_equiv transpose_1 proper_1 : core.

    Lemma map_Empty_spec : forall f s,
      Empty s -> map f s = empty.
    Proof.
      intros; unfold map; apply empty_is_empty_1 in H. 
      apply eq_leibniz in H; subst; now rewrite fold_empty.
    Qed.

    Lemma map_empty_spec : forall f,
      map f empty = empty.
    Proof.
      intros; unfold map; now rewrite fold_empty. 
    Qed.

    Lemma map_singleton_spec : forall f re,
      map f (singleton re) = singleton (f re).
    Proof.
      intros; unfold map. 
      replace (singleton re) with (add re empty).
      - apply eq_leibniz; rewrite fold_add; auto.
        -- rewrite fold_empty; symmetry; apply singleton_equal_add.
        -- unfold not; intros H; inversion H.
      - apply eq_leibniz; apply singleton_equal_add.
    Qed.

    Lemma map_in_spec : forall s f re,
      In re s -> In (f re) (map f s).
    Proof.
      intros s; induction s using set_induction; intros f re HI.
      - apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.
        inversion HI.

      - intros; apply Add_inv in H0; subst; unfold map in *; rewrite add_spec in *.
        rewrite fold_add; auto; rewrite add_spec. destruct HI; auto. 
        apply Elt.eq_leibniz in H0; subst; now left.
    Qed.

    Lemma map_add_notin_spec : forall f re s,
      ~ In re s -> map f (add re s) = add (f re) (map f s).
    Proof.
      intros; apply eq_leibniz; unfold map; rewrite fold_add; now auto.
    Qed.

    Lemma map_add_in_spec : forall f re s,
      In re s -> map f (add re s) = (map f s).
    Proof.
      intros; apply eq_leibniz; unfold map; rewrite add_fold; now auto.
    Qed.

    Lemma map_union_spec : forall s s' f,
      (map f (union s s')) = union (map f s) (map f s').
    Proof.
      intros; apply eq_leibniz; generalize s' f; clear s' f.
      induction s using set_induction; intros s' f.
      - split; intros.
        -- apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.
          replace (union empty s') with s' in H0; unfold map in *. rewrite fold_empty.
          + apply union_spec; auto.
          + apply eq_leibniz; rewrite empty_union_1; eauto; reflexivity.

        -- unfold map in *. apply empty_is_empty_1 in H; apply eq_leibniz in H; subst.
          apply union_spec in H0 as [|].
          + rewrite fold_empty in H; inversion H.
          + replace (union empty s') with s'; auto.
              apply eq_leibniz; rewrite empty_union_1; eauto; reflexivity.

      - split; intros.
        -- apply Add_inv in H0; subst; rewrite union_add_spec in H1; destruct (In_dec x s').
          + rewrite map_add_in_spec in H1.
            ++ apply IHs1 in H1. rewrite union_spec in *; destruct H1; auto.
                left; rewrite map_add_notin_spec; auto. rewrite add_spec; auto.
            ++ apply union_spec; now right.
            + rewrite map_add_notin_spec in H1.
              ++ rewrite add_spec in H1; rewrite union_spec; destruct H1.
                * rewrite H0 in *; left; rewrite map_add_notin_spec; auto.
                  rewrite add_spec; left; reflexivity.
                * apply IHs1 in H0; rewrite union_spec in H0; destruct H0; auto.
                  left; rewrite map_add_notin_spec; auto; rewrite add_spec; auto.
              ++ rewrite union_notin_spec; split; assumption.
        -- apply Add_inv in H0; subst; rewrite union_add_spec; rewrite union_spec in *; 
          destruct (In_dec x s').
          + rewrite map_add_in_spec.
            ++ destruct H1.
                * rewrite map_add_notin_spec in H0; auto; rewrite add_spec in H0; destruct H0.
                  ** rewrite H0 in *; rewrite IHs1; rewrite union_spec; right.
                    now apply map_in_spec.
                  ** rewrite IHs1; rewrite union_spec; now left.
                * rewrite IHs1; rewrite union_spec; now right.
            ++ apply union_spec; auto.
          + rewrite map_add_notin_spec.
            ++ destruct H1.
                * rewrite map_add_notin_spec in H0; auto; rewrite add_spec in *.
                  destruct H0; auto; right; apply IHs1; rewrite union_spec; auto.
                * rewrite add_spec; right; apply IHs1; rewrite union_spec; auto.
            ++ apply union_notin_spec; split; assumption.
    Qed.


  End map.

End SetOTWithLeibniz.