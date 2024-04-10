From Coq Require Import Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From Kernel Require Import LevelInterface Level.
From MapExt Require Import MapExtInterface MapExt MapLevelInterface.


(** * Implementation -- Map *)

(** ** Map with leveled datas and leveled keys *)

(** *** Map implementation with minimal constraints *)

Module ShiftValidMapD (Key : OrderedTypeWithLeibniz)
                        (Data : ShiftValidETWithLeibniz) 
                        (M : Interface.S Key)
                        (MO : MapInterface Key Data M) <: ShiftValidMapDInterface Key Data M MO.

Import MO OP.P.
Include MO.            

(** **** Definition *)
Section definition.

Definition shift (lb : Lvl.t) (k : Lvl.t) (m : t) :=
  M.fold (fun (key : M.key) (v : Data.t) (acc : t) => 
              M.add key (Data.shift lb k v) acc) m M.empty.

Definition valid (lb : Lvl.t) (m : t) :=
  M.fold (fun (key : M.key) (v : Data.t) (acc : Prop) => 
              Data.valid lb v /\ acc) m True.

End definition.

(** **** Some facts *)

Instance iff_equiv : Equivalence iff := _.
Instance logic_eq_equiv : forall A, Equivalence (@Logic.eq A) := _.

Fact valid_diamond : forall lb, Diamond iff
  (fun (key0 : Key.t) (v0 : Data.t) 
        (acc : Prop) => Data.valid lb v0 /\ acc).
Proof.
  unfold Diamond; intros; split; intros [bn iu].
  -- rewrite <- H1 in iu; destruct iu; split; auto.
      rewrite <- H0; split; auto.
  -- rewrite <- H0 in iu; destruct iu; split; auto.
      rewrite <- H1; split; auto.
Qed.

#[local]
Instance valid_proper : forall lb, Proper (Key.eq ==> Logic.eq ==> iff ==> iff)
  (fun (key0 : Key.t) (v0 : Data.t) 
        (acc : Prop) => Data.valid lb v0 /\ acc).
Proof. 
  split; intros [a b]; apply Key.eq_leibniz in H; subst; split; auto; 
  now rewrite <- H1 in *.
Qed.

#[local]
Instance shift_proper : forall lb k,
  Proper (Key.eq ==> Logic.eq ==> eq ==> eq)
  (fun (key0 : Key.t) (v0 : Data.t) 
        (acc : t) => M.add key0 (Data.shift lb k v0) acc).
Proof. 
  repeat red; intros; rewrite H1; apply Key.eq_leibniz in H; now subst.
Qed.

Fact shift_diamond : forall lb k,
  Diamond eq (fun (key0 : Key.t) (v0 : Data.t) (acc : t) 
    => M.add key0 (Data.shift lb k v0) acc).
Proof.
  unfold Diamond; intros. rewrite <- H0; rewrite <- H1.
  rewrite add_add_2; try reflexivity; assumption.
Qed.

(** **** Valid *)

#[export] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv  valid_diamond valid_proper
shift_proper shift_diamond : core.

Lemma valid_Empty_spec : forall lb m,
  Empty m -> valid lb m.
Proof.
  intros; unfold valid; eapply fold_Empty in H; auto. now rewrite H.
Qed.

Lemma valid_empty_spec : forall lb, valid lb M.empty.
Proof. intros. apply valid_Empty_spec. apply empty_1. Qed.

Lemma valid_add_notin_spec : forall lb x v m,
  ~ M.In x m -> valid lb (M.add x v m) <-> Data.valid lb v /\ valid lb m.
Proof.
  unfold valid in *; split; intros.
  - rewrite fold_add with (i := True) in H0; eauto.
  - destruct H0. rewrite fold_add with (i := True); eauto.
Qed.

Lemma valid_Add_spec : forall lb x v m m',
  ~ M.In x m -> Add x v m m' -> 
  Data.valid lb v /\ valid lb m <-> valid lb m'.
Proof.
  unfold valid in *; split; intros.
  - rewrite fold_Add with (i := True); eauto.
  - rewrite fold_Add with (i := True) in H1; eauto.
Qed.

Lemma valid_find_spec : forall lb x v m,
  valid lb m -> M.find x m = Some v -> Data.valid lb v.
Proof.
  intros lb x v m; induction m using map_induction; intros.
  - exfalso; unfold Empty in H; apply (H x v); now apply find_2.
  - apply (valid_Add_spec lb x0 e m1 m2) in H1 as [Hvr Hvm1]; auto.
    unfold Add in *; rewrite H0 in *. rewrite add_o in H2. destruct (Key.eq_dec x0 x);
    auto; inversion H2; now subst.
Qed. 
  
#[global]
Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  repeat red; split; subst; revert y y0 H0; rename x0 into m;
  induction m using map_induction; intros.
  - apply valid_Empty_spec. rewrite Empty_eq_spec; eauto; now symmetry.
  - rewrite <- valid_Add_spec in H2; eauto.
    rewrite Add_eq_spec in H0; eauto. rewrite <- valid_Add_spec; eauto.
  
  - now apply valid_Empty_spec.
  - rewrite <- valid_Add_spec; eauto.
    rewrite Add_eq_spec in H0; eauto. rewrite <- valid_Add_spec in H2; eauto.
Qed.

Lemma valid_add_in_spec : forall k x m,
  M.In x m -> valid k m -> exists v, valid k (M.add x v m).
Proof.
  intros k x m; revert k x; induction m using map_induction; intros k y HIn Hvm.
  - unfold Empty in *; exfalso.
    destruct HIn as [z HM]; now apply (H y z).
  - rewrite <- valid_Add_spec in Hvm; eauto; destruct Hvm as [Hvx Hvm].
    destruct (Key.eq_dec x y); subst.
    -- exists e. unfold Add in H0; rewrite H0.
       rewrite e0 in *. rewrite add_add_1.
       rewrite valid_add_notin_spec; auto; split; auto.
    -- apply IHm1 with (x := y) in Hvm as [v Hvm].
        + exists v. unfold Add in H0; rewrite H0.
          rewrite add_add_2.
          ++ rewrite valid_add_notin_spec; auto. intro c.
             rewrite add_in_iff in c; destruct c as [c | c].
             * symmetry in c; contradiction.
             * contradiction.
          ++ intro c; symmetry in c; contradiction. 
        + destruct HIn as [v' Hfm2]. apply find_1 in Hfm2.
          rewrite H0 in Hfm2. rewrite add_neq_o in Hfm2; auto.
          exists v'; now apply find_2.
Qed.

Lemma valid_add_spec : forall m x (v : Data.t) lb,
  Data.valid lb v /\ valid lb m -> valid lb (M.add x v m).
Proof.
  intro m; induction m using map_induction.
  - intros x v lb []. rewrite valid_add_notin_spec; try now split.
    intro i; unfold Empty in H; destruct i; exfalso; now apply (H x x0).
  - intros y v lb []. rewrite <- valid_Add_spec in H2; eauto; destruct H2.
    unfold Add in H0; rewrite H0. destruct (Key.eq_dec y x).
    -- apply Key.eq_leibniz in e0; subst. rewrite add_shadow. 
       apply IHm1; now split.
    -- rewrite add_add_2; auto. rewrite valid_add_notin_spec.
       + split; auto.
       + intro. rewrite add_in_iff in H4; destruct H4; try contradiction.
Qed.


(** **** Shift *)

Lemma shift_Empty_spec : forall lb k m,
  Empty m -> eq (shift lb k m) m.
Proof. 
  intros; unfold shift. eapply fold_Empty with (eqA := eq) (i := M.empty) in H as H'; 
  eauto. rewrite H'; clear H'; apply is_empty_1 in H as H'. symmetry; 
  now apply Empty_eq_spec_1.
Qed.

Lemma shift_Empty_spec_1 : forall lb k m,
  Empty m -> Empty (shift lb k m).
Proof.
  intros; unfold shift. eapply fold_Empty with (i := M.empty) (eqA := eq) in H; eauto.
  rewrite Empty_eq_spec; eauto; apply empty_1.
Qed.

Lemma shift_add_notin_spec : forall lb k x v  (m : t),
  ~ M.In x m ->  
  eq (shift lb k (M.add x v m)) 
      (M.add x (Data.shift lb k v) (shift lb k m)).
Proof.
  intros lb k x v m HIn; unfold shift.
  rewrite fold_add with (eqA := eq) (i := M.empty); now eauto.
Qed.

Lemma shift_Add_spec : forall lb k key v (m m' : t),
  ~ M.In key m -> Add key v m m' -> 
  eq (shift lb k m') (M.add key (Data.shift lb k v) (shift lb k m)).
Proof.
  intros lb k key v m m' HIn HAdd; unfold shift; 
  rewrite fold_Add with (eqA := eq) (i := M.empty); now eauto.
Qed.

Lemma shift_Add_spec_1 : forall lb k key v (m m' : t),
  ~ M.In key m -> Add key v m m' ->
  Add key (Data.shift lb k v) (shift lb k m) (shift lb k m').
Proof.
  intros. apply shift_Add_spec with (lb := lb) (k := k) in H0; auto.
Qed.
  
Lemma shift_in_spec_1 : forall lb k key (m : t),
  M.In key m -> M.In key (shift lb k m).
Proof.
  intros lb k key m; induction m using map_induction; intros.
  - exfalso; unfold Empty,not in *; destruct H0.
    now apply (H key x).
  - apply shift_Add_spec with (lb := lb) (k := k) in H0 as H0'; auto.
    rewrite in_find in *. 
    rewrite H0',H0 in *. rewrite <- in_find in *. rewrite add_in_iff in *.
    destruct H1; auto.
Qed.

Lemma shift_in_spec_2 : forall lb k key (m : t),
  M.In key (shift lb k m) -> M.In key m.
Proof.
  intros lb k key m; induction m using map_induction; intros.
  - exfalso. eapply fold_Empty with (i := M.empty) (eqA := eq) in H; eauto.
    unfold shift in H0. rewrite H in *. destruct H0.
    apply empty_mapsto_iff in H0. contradiction.
  - apply shift_Add_spec with (lb := lb) (k := k) in H0 as H0'; auto.
    rewrite in_find in *. 
    rewrite H0',H0 in *. rewrite <- in_find in *. rewrite add_in_iff in *.
    destruct H1; auto.
Qed.

Lemma shift_in_spec : forall lb k key (m : t), 
  M.In key m <-> M.In key (shift lb k m).
Proof. split; intros. eapply shift_in_spec_1; eauto. eapply shift_in_spec_2; eauto. Qed.

Lemma shift_notin_spec : forall lb k key (m : t), 
  ~ M.In key m <-> ~ M.In key (shift lb k m).
Proof.
  unfold not; split; intros; apply H.
  - rewrite shift_in_spec; eauto.
  - now rewrite <- shift_in_spec.
Qed.

Lemma shift_find_spec : forall lb k key v (m : t), 
  M.find key m = Some v <-> M.find key (shift lb k m) = Some (Data.shift lb k v).
Proof.
  intros lb k key v m; induction m using map_induction.
  - split; intros.
    -- exfalso. apply (H key v); now apply find_2.
    -- unfold shift in H0. eapply fold_Empty with (i := M.empty) (eqA := eq) in H; eauto.
       rewrite H in *. apply find_2 in H0. apply empty_mapsto_iff in H0.
       contradiction.
  - apply shift_Add_spec_1 with (lb := lb) (k := k) in H0 as H0'; auto.
    unfold Add in *; rewrite H0,H0'. destruct (Key.eq_dec x key); subst.
    -- repeat rewrite add_eq_o; auto; split.
       + intro Heq; inversion Heq; now subst.
       + intro Heq; inversion Heq. f_equal.
         apply Data.eq_leibniz. rewrite Data.shift_eq_iff; now rewrite H2.
    -- split.
       + intro Hfi. rewrite add_neq_o in *; auto. now rewrite <- IHm1.
       + intro Hfi. rewrite add_neq_o in *; auto. now rewrite IHm1.
Qed.

Lemma shift_find_e_spec : forall lb k x v m,
  M.find x (shift lb k m) = Some v -> 
  exists v', Data.eq v (Data.shift lb k v').
Proof.
  intros lb k x v m; revert lb k x v; induction m using map_induction;
  intros.
  - eapply shift_Empty_spec in H as H'. unfold Empty in H.
    exfalso; apply (H x v); apply find_2; eauto.
  
  - eapply shift_Add_spec in H0; eauto. rewrite H0 in H1.
    destruct (Key.eq_dec x x0); subst.
    -- rewrite add_eq_o in H1; auto. inversion H1; subst. exists e.
       reflexivity.
    -- rewrite add_neq_o in H1; auto. apply IHm1 in H1; auto.
Qed.     


Lemma shift_refl : forall lb t, eq (shift lb 0 t) t.
Proof.
  intros; induction t0 using map_induction.
  - now apply shift_Empty_spec.
  - apply shift_Add_spec with (lb := lb) (k := 0) in H0 as H0'; auto.
    unfold Add in *. intro y. rewrite H0,H0'.
    destruct (Key.eq_dec y x); subst.
    -- repeat rewrite add_eq_o; auto; try now symmetry. f_equal.
       apply Data.eq_leibniz. rewrite Data.shift_refl; try reflexivity.
    -- repeat rewrite add_neq_o; auto; intro Heq; symmetry in Heq;
       contradiction.
Qed.

#[global]
Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  red; red; red; red; intros; subst; revert y y0 y1 H1; rename x1 into m.
  induction m using map_induction; intros.
  - unfold shift; rewrite fold_Empty; auto.
    -- rewrite fold_Empty; auto; try reflexivity; try apply Equal_equiv.
      unfold Empty in *; intros; intro. apply find_1 in H0.
      apply (H x e). apply find_2; now rewrite H1.
    -- apply Equal_equiv.
  - unfold shift; intros. rewrite fold_Add; eauto; try (apply Equal_equiv).
    rewrite Add_eq_spec in H0; eauto.
    rewrite fold_Add; eauto; try (apply Equal_equiv). 
Qed.

Lemma shift_eq_iff : forall lb k m m1, 
  eq m m1 <-> eq (shift lb k m) (shift lb k m1).
Proof.
  split; intros.
  - now rewrite H.
  - intro y. destruct (In_dec m y).
    -- destruct i; apply find_1 in H0. rewrite H0; symmetry.
        erewrite shift_find_spec in H0; rewrite H in H0. 
        now rewrite <- shift_find_spec in H0.
    -- apply not_in_find in n as n''; rewrite n''; clear n''. 
       rewrite shift_notin_spec in n.
       apply not_in_find in n as n'. rewrite H in n'.
       symmetry; destruct (In_dec m1 y).
       + destruct i. apply find_1 in H0.
         rewrite shift_find_spec in H0; rewrite n' in H0; inversion H0.
       + now apply not_in_find.
Qed.

Lemma shift_trans : forall lb k k' t,
  eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof.
  intros lb k k' t; induction t using map_induction; intros. 
  - rewrite shift_Empty_spec with (lb := lb) (k := (k + k')); auto.
    apply shift_Empty_spec_1 with (lb := lb) (k := k') in H as H'.
    rewrite shift_Empty_spec with (lb := lb) (k := k); auto.
    now apply shift_Empty_spec with (lb := lb) (k := k').

  - unfold Add in H0; rewrite H0.
    rewrite shift_add_notin_spec with (lb := lb) (k := k + k'); auto.
    rewrite shift_add_notin_spec with (lb := lb) (k := k'); auto.
    rewrite shift_add_notin_spec with (lb := lb) (k := k).
    -- replace (Data.shift lb (k + k') e) with (Data.shift lb k (Data.shift lb k' e)).
       + now rewrite IHt1.
       + apply Data.eq_leibniz; now apply Data.shift_trans.
    -- now rewrite <- shift_notin_spec.
Qed.

Lemma shift_permute : forall lb k k' t,
eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof.
intros lb k k' t; induction t using map_induction; intros.
- apply shift_Empty_spec with (lb := lb) (k := k) in H as H'.
  apply shift_Empty_spec with (lb := lb) (k := k') in H as H''.
  apply shift_Empty_spec_1 with (lb := lb) (k := k') in H as H1.
  apply shift_Empty_spec_1 with (lb := lb) (k := k) in H as H1'.
  apply shift_Empty_spec with (lb := lb) (k := k) in H1.
  apply shift_Empty_spec with (lb := lb) (k := k') in H1'.
  now rewrite H1,H1',H',H''.
- apply shift_Add_spec_1 with (lb := lb) (k := k) in H0 as H1; auto.
  apply shift_Add_spec_1 with (lb := lb) (k := k') in H0 as H1'; auto.
  apply shift_Add_spec with (lb := lb) (k := k') in H1;
  apply shift_Add_spec with (lb := lb) (k := k) in H1';
  try (now rewrite <- shift_notin_spec).
  rewrite H1,H1'.
  replace (Data.shift lb k' (Data.shift lb k e)) with (Data.shift lb k (Data.shift lb k' e)).
  -- now rewrite IHt1.
  -- apply Data.eq_leibniz; apply Data.shift_permute.
Qed.


Lemma shift_unfold : forall lb k k' t,
eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof.
intros lb k k' t; induction t using map_induction.
- repeat rewrite shift_Empty_spec; auto; try reflexivity.
- rewrite shift_Add_spec; eauto. symmetry.
  eapply shift_Add_spec_1 with (lb := lb) (k := k) in H0 as H0'; auto.
  eapply shift_Add_spec with (lb := lb + k) (k := k') in H0' as H0''.
  -- rewrite H0''. 
     replace (Data.shift (lb + k) k' (Data.shift lb k e)) with (Data.shift lb (k + k') e).
     + now rewrite IHt1.
     + apply Data.eq_leibniz. apply Data.shift_unfold. 
  -- now rewrite <- shift_notin_spec.
Qed.

Lemma shift_unfold_1 : forall k k' k'' t,
k <= k' -> k' <= k'' -> 
eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
intros k k' k'' t Hlt Hlt'; induction t using map_induction.
- repeat rewrite shift_Empty_spec; auto; try reflexivity. 
- eapply shift_Add_spec_1 with (lb := k) (k := (k' - k)) in H0 as H0'; auto.
  eapply shift_Add_spec with (lb := k') (k := (k'' - k')) in H0' as H0''.
  -- rewrite H0''. symmetry; rewrite shift_Add_spec; eauto; symmetry.
     replace (Data.shift k' (k'' - k') (Data.shift k (k' - k) e))
     with (Data.shift k (k'' - k) e).
     + now rewrite IHt1.
     + apply Data.eq_leibniz; now rewrite Data.shift_unfold_1.
  -- now rewrite <- shift_notin_spec.
Qed.

Lemma shift_remove_spec : forall lb k x t,
eq (M.remove x (shift lb k t)) (shift lb k (M.remove x t)).
Proof.
intros lb k x t; induction t using map_induction.
- assert (~ M.In x (shift lb k t0)).
  { 
    apply shift_notin_spec; intro; unfold Empty in *.
    destruct H0. now apply (H x x0).  
  }
  apply shift_notin_spec in H0 as H0'.
  rewrite <- remove_id in H0; rewrite H0; clear H0.
  rewrite <- remove_id in H0'; now rewrite H0'.

- unfold Add in H0; rewrite H0. destruct (Key.eq_dec x x0).
  -- apply Key.eq_leibniz in e0; subst. rewrite remove_add_1.
     rewrite shift_add_notin_spec; auto. now rewrite remove_add_1.
  -- rewrite remove_add_2; try (intro c; symmetry in c; contradiction).
     repeat rewrite shift_add_notin_spec; auto.
     + rewrite remove_add_2; 
       try (rewrite <- Data.shift_eq_iff; intro c; symmetry in c; contradiction).
       now rewrite IHt1. intro. symmetry in H1; contradiction.
     + intro c; rewrite remove_in_iff in c; destruct c; contradiction.
Qed.

Lemma shift_eq_1 : forall lb k t t1, eq (shift lb k t) (shift lb k t1) -> eq t t1.
Proof.
intros lb k t; induction t using map_induction; intros t' Heq.
- rewrite shift_Empty_spec in Heq; auto.
  assert (Empty (shift lb k t')). { rewrite Empty_eq_spec in H; eauto. }
  rewrite shift_Empty_spec in Heq; auto.
  unfold Empty in *. intros; intro Hfi. apply find_1 in Hfi.
  rewrite shift_find_spec with (lb := lb) (k := k) in Hfi.
  apply (H0 x (Data.shift lb k e)); now apply find_2.
- unfold Add in H0; rewrite H0 in *. 
  rewrite shift_add_notin_spec in Heq; auto.
  assert (M.find x t' = Some e). 
  { erewrite shift_find_spec; rewrite <- Heq. now apply add_eq_o. }
  assert (M.find x (shift lb k t') = Some (Data.shift lb k e)).
  { now rewrite <- shift_find_spec. }
  apply add_remove_spec in H1,H2. rewrite H1; rewrite H2 in Heq. clear H1 H2.
  assert (eq t1 (M.remove x t')).
  { 
    apply IHt1; intro y. 
    assert (~ M.In x (M.remove x t')). { now apply remove_1. }
    destruct (Key.eq_dec y x).
    -- apply Key.eq_leibniz in e0; subst; 
      rewrite shift_notin_spec in H. apply not_in_find in H; rewrite H.
      rewrite shift_notin_spec in H1. apply not_in_find in H1; now rewrite H1.
    -- rewrite <- add_neq_o with (e := (Data.shift lb k e)) (x := x); eauto.
      + symmetry. 
        rewrite <- add_neq_o with (e := (Data.shift lb k e)) (x := x); eauto.
        ++ rewrite Heq. rewrite add_neq_o; auto.
            * symmetry. rewrite add_neq_o; auto.
              ** now rewrite shift_remove_spec.
              ** intro Heq'; symmetry in Heq'; contradiction.
            * intro Heq'; symmetry in Heq'; contradiction.
        ++ intro Heq'; symmetry in Heq'; contradiction.
      + intro Heq'; symmetry in Heq'; contradiction.     
  }
  now rewrite H1.
Qed.


Lemma shift_add_spec : forall lb k x v  (m : t),
  eq (shift lb k (M.add x v m)) 
      (M.add x (Data.shift lb k v) (shift lb k m)).
Proof.
  intros lb k x v m. destruct (In_dec m x).
  - revert lb k x v i; induction m using map_induction.
    -- intros; exfalso; unfold Empty in *; destruct i.
       now apply (H x x0).
    -- intros. unfold Add in H0. rewrite H0 in *.
       rewrite add_in_iff in i. destruct i.
       + rewrite H1 in *. unfold eq,M.Equal; intros. rewrite add_shadow.
         repeat rewrite shift_add_notin_spec; auto.
         destruct (Key.eq_dec y x0).
         ++ rewrite e0. repeat rewrite add_eq_o; auto; reflexivity.
         ++ repeat rewrite add_neq_o; auto; intro c; symmetry in c; contradiction.
       + destruct (Key.eq_dec x0 x).
         ++ rewrite e0 in *. contradiction.
         ++ rewrite add_add_2; auto. symmetry; rewrite shift_add_notin_spec; auto.
            symmetry; rewrite shift_add_notin_spec.
            * rewrite add_add_2; auto. rewrite IHm1; now auto.
            * intro. apply add_in_iff in H2; destruct H2; auto.
  - now apply shift_add_notin_spec.
Qed.

(** **** Valid continued *)


Lemma valid_weakening : forall k k' t, (k <= k') -> valid k t -> valid k' t.
Proof.
intros k k' t; revert k k'; induction t using map_induction; intros k k' Hle Hvt.
- now apply valid_Empty_spec.
- rewrite <- valid_Add_spec with (lb := k) in Hvt; eauto.
  rewrite <- valid_Add_spec with (lb := k'); eauto.
  destruct Hvt as [Hv Hvt1]; split. 
  -- now apply Data.valid_weakening with k.
  -- now apply IHt1 with k.
Qed.

Lemma shift_preserves_valid_1 : forall lb k k' t, valid k t -> valid (k + k') (shift lb k' t).
Proof.
intros lb k k' t; revert lb k k'; induction t using map_induction; 
intros lb k k' Hvt.
- apply shift_Empty_spec with (lb := lb) (k := k') in H as H'.
  rewrite H' in *.
  now apply valid_Empty_spec with (lb := k + k') in H.
- eapply valid_Add_spec in Hvt; eauto; destruct Hvt as [Hv Hvt'].
  apply IHt1 with (lb := lb) (k := k) (k' := k') in Hvt'.
  apply Data.shift_preserves_valid_1 with (lb := lb) (k' := k') in Hv.

  apply shift_Add_spec_1 with (lb := lb) (k := k') in H0; auto.
  rewrite <- valid_Add_spec; eauto. now apply shift_notin_spec.
Qed.

Lemma shift_preserves_valid_2 : forall lb lb' k k' t,
k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
intros lb lb' k k' t; induction t using map_induction; intros.
- apply shift_Empty_spec with (lb := k) (k := (k' - k)) in H as H'.
  rewrite H'; now apply valid_Empty_spec.
- eapply valid_Add_spec in H6; eauto; destruct H6 as [HvData Hvt].
  eapply IHt1 in Hvt; eauto.
  apply shift_Add_spec_1 with (lb := k) (k := k' - k) in H0; auto.
  rewrite <- valid_Add_spec with (m := (shift k (k' - k) t1)); eauto.
  -- split; auto.
     apply Data.shift_preserves_valid_2 with (lb := lb); assumption.
  -- now apply shift_notin_spec.
Qed.

Lemma shift_preserves_valid_3 : forall lb lb' t,
lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof. intros; eapply shift_preserves_valid_2; eauto. Qed.

Lemma shift_preserves_valid : forall k k' t, valid k t -> valid (k + k') (shift k k' t).
Proof. intros; now apply shift_preserves_valid_1. Qed.

Lemma shift_preserves_valid_4 : forall k t, valid k t -> valid k (shift k 0 t).
Proof. intros; replace k with (k + 0) by lia; now apply shift_preserves_valid_1. Qed.

End ShiftValidMapD.


(** *** Map implementation fully constrained *)
Module StrongShiftValidMapD  (Key : OrderedTypeWithLeibniz)
                            (Data : StrongShiftValidETWithLeibniz) 
                            (M : Interface.S Key) 
                            (MO : MapInterface Key Data M) 
                               <: StrongShiftValidMapDInterface Key Data M MO.

Include ShiftValidMapD Key Data M MO.
Import M OP.P.  

Lemma shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.
Proof.
  intros; induction t0 using map_induction.
  - now apply shift_Empty_spec.
  - unfold Add in H1; rewrite H1 in *. 
    rewrite shift_add_notin_spec; auto. apply valid_add_notin_spec in H as [Hv Hv']; auto.
    eapply Data.shift_valid_refl in Hv; auto. apply Data.eq_leibniz in Hv. rewrite Hv.
    now rewrite IHt0_1.
Qed.

End StrongShiftValidMapD.


(** *** Map Make *)

Module MakeShiftValidMapD (Key : OrderedTypeWithLeibniz) 
                            (Data : ShiftValidETWithLeibniz) <: ShiftValidET.
  
  Module Raw := MMaps.OrdList.Make Key.
  Module Ext := MapET Key Data Raw.
  Include ShiftValidMapD Key Data Raw Ext.

End MakeShiftValidMapD.

Module MakeStrongShiftValidMapD (Key : OrderedTypeWithLeibniz) 
                                  (Data : StrongShiftValidETWithLeibniz) <: StrongShiftValidET.
  
  Module Raw := MMaps.OrdList.Make Key.
  Module Ext := MapET Key Data Raw.
  Include StrongShiftValidMapD Key Data Raw Ext.
  Include OP.P.

End MakeStrongShiftValidMapD.