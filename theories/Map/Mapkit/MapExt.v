From Coq Require Import MSets Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From Kernel Require Import Level.
From MapExt Require Import MapExtInterface.

Module MapET (Key : OrderedTypeWithLeibniz) (Data : EqualityType) 
                                            (M : Interface.S Key) <:  MapInterface Key Data M.

Module OP := Facts.OrdProperties Key M.
Import OP.P.


Definition t : Type := M.t Data.t.
Definition eq := @M.Equal Data.t.

Definition Submap (m m' : t) :=
  (forall y, M.In y m -> M.In y m') /\
  (forall k e e', M.MapsTo k e m -> M.MapsTo k e' m' -> e = e')
.

#[global]
Instance eq_equiv : Equivalence eq. Proof. apply Equal_equiv. Qed.
 

Fact iff_equiv : Equivalence iff.
Proof.
  split. 
  -- unfold Reflexive; intros; reflexivity.
  -- unfold Symmetric; intros; now symmetry.
  -- unfold Transitive; intros; now transitivity y.
Qed.

Fact logic_eq_equiv : forall A, Equivalence (@Logic.eq A).
Proof. intros; split; auto; unfold Transitive; intros; subst; auto. Qed.


#[local] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv : core.

Lemma Empty_eq_spec : forall (m m' : t), 
  m == m' -> Empty m <-> Empty m'.
Proof. 
  split; intro HE; eapply Empty_m in HE; eauto;
  apply Equal_Eqdom in H; auto; now symmetry.
Qed.

Lemma Empty_eq_spec_1 : forall (m : t), 
  Empty m -> m == M.empty.
Proof.
  intros. intro. destruct (In_dec m y).
  -- exfalso; destruct i as [x Hm]; unfold Empty in *;
     now apply (H y x Hm).
  -- rewrite not_mem_in_iff in n. rewrite not_mem_find in n.
     rewrite n; symmetry. rewrite <- not_mem_find. 
     rewrite <- not_mem_in_iff. apply not_in_empty.
Qed.

Lemma notEmpty_Add_spec : forall (m m' : t) x e,
  Add x e m m' -> ~ Empty m'.
Proof.
  intros; unfold Add in *. rewrite H.
  unfold Empty,not in *; intros; apply (H0 x e); now apply add_1.
Qed.

Lemma notEmpty_find_spec : forall (m : t) x e,
  Empty m -> ~ (M.find x m = Some e).
Proof.
  intros; intro. unfold Empty in H; apply (H x e).
  now apply find_2.
Qed. 

Lemma is_empty_Add_spec : forall (m m' : t) x e,
  Add x e m m' -> M.is_empty m' = false.
Proof.
  intros. apply notEmpty_Add_spec in H. destruct (M.is_empty m') eqn:Heq; auto.
  apply is_empty_iff in Heq; contradiction.
Qed.

Lemma is_empty_add_spec : forall (m : t) x e,
  M.is_empty (M.add x e m) = false.
Proof.
  intros. destruct (M.is_empty (M.add x e m)) eqn:Heq; auto.
  apply is_empty_iff in Heq; unfold Empty,not in *; exfalso.
  apply (Heq x e). apply add_mapsto_iff; left; now split.
Qed.

Lemma Add_eq_spec : forall (n m m' : t) x v, 
  m == m' -> Add x v n m <-> Add x v n m'.
Proof.
  unfold Add; split; intros; rewrite <- H0; auto; now symmetry.
Qed.

(* Pas pertinent *)
(* Lemma add_eq_spec : forall (m m' : t) x v, 
  eq m m' -> eq (M.add x v m) (M.add x v m').
Proof. intros. now rewrite H. Qed. *)

Lemma add_remove_spec : forall (m : t) x v, 
  M.find x m = Some v -> m == (M.add x v (M.remove x m)).
Proof. 
  intros m x v Hfin; intro y. destruct (Key.eq_dec x y).
  - apply Key.eq_leibniz in e; subst. rewrite add_eq_o; auto; reflexivity.
  - rewrite add_neq_o; auto. now rewrite remove_neq_o.
Qed.

Lemma add_shadow : forall m x v v', 
  eq (M.add x v (M.add x v' m)) (M.add x v m). 
Proof. 
  unfold eq,M.Equal; intros. destruct (Key.eq_dec x y).
  - rewrite e. repeat rewrite add_eq_o; auto; reflexivity.
  - repeat rewrite add_neq_o; auto.
Qed.

(** *** Submap *)

Lemma Submap_Empty_spec : forall (m m' : t),
  Empty m -> Submap m m'.
Proof.
  intros; unfold Empty,Submap in *; split.
  - intros; exfalso; destruct H0; apply H in H0; contradiction.
  - intros; exfalso; apply H in H0; contradiction.
Qed.

Lemma Submap_Empty_spec_1 : forall (m m' : t),
  Submap m m' -> Empty m' -> Empty m.
Proof.
  intros; unfold Empty,Submap in *; destruct H; intros.
  intro. assert (M.In x m) by now exists e.
  apply H in H3. destruct H3. apply (H0 x x0) in H3; contradiction.
Qed.

Lemma Submap_empty_spec : forall (m : t),
  Submap M.empty m.
Proof.
  intro; unfold Submap; split; intros.
  - apply empty_in_iff in H; contradiction.
  - apply empty_mapsto_iff in H; contradiction.
Qed.

Lemma Submap_Add_spec : forall (m1 m m' : t) x v,
  Submap m' m1 -> ~ M.In x m -> Add x v m m' ->
  Submap m m1.
Proof.
  intros; unfold Add,Submap in *; destruct H; split; intros.
  - apply H; rewrite H1; now apply in_add.
  - eapply H2; eauto; rewrite H1. rewrite add_mapsto_new; auto.
Qed.

Lemma Submap_Add_spec_1 : forall (m1 m m' : t) x v,
  Submap m' m1 -> ~ M.In x m -> Add x v m m' ->
  M.In x m1.
Proof.
  intros. unfold Submap,Add in *; destruct H.
  apply H; rewrite H1; rewrite add_in_iff; now left.
Qed.

Lemma Submap_Add_spec_1' : forall (m1 m m' : t) x v,
  Submap m' m1 -> ~ M.In x m -> Add x v m m' ->
  M.find x m1 = Some v.
Proof.
  intros. unfold Submap,Add in *; destruct H.
  assert (M.In x m'). { rewrite H1; rewrite add_in_iff; now left. }
  apply H in H3 as H'. destruct H3,H'. apply find_1 in H3 as H3'; rewrite H1 in *.
  rewrite add_eq_o in H3'; auto; inversion H3'; subst; clear H3'.
  apply find_1 in H3; rewrite <- H1 in H3; apply find_2 in H3.
  eapply H2 in H3; eauto; subst; now apply find_1. reflexivity.
Qed.

Lemma Submap_Add_spec_2 : forall (m1 m m' : t) x v,
  Submap m m1 -> ~ M.In x m -> M.find x m1 = Some v -> Add x v m m' ->
  Submap m' m1.
Proof.
  intros. unfold Submap,Add in *; destruct H; split; intros.
  - rewrite H2 in *; rewrite add_in_iff in H4; destruct H4; subst; auto.
    apply Key.eq_leibniz in H4; subst; exists v; now apply find_2.
  - rewrite H2 in *; rewrite add_mapsto_new in H4; auto. destruct H4.
    -- destruct H4; subst. apply Key.eq_leibniz in H4; subst; auto. 
       apply find_1 in H5; rewrite H1 in H5. inversion H5; auto.
    -- eapply H3; eauto.
Qed.

Lemma Submap_add_spec : forall (m m' : t) x v,
  Submap m m' -> Submap (M.add x v m) (M.add x v m').
Proof.
  intros; unfold Submap in *; destruct H; split.
  - intros. rewrite add_in_iff in *; destruct H1; subst; auto.
  - intros. rewrite add_mapsto_iff in *; destruct H1,H2; destruct H1,H2; subst; auto.
    -- now contradiction H2.
    -- now contradiction H1.
    -- eapply H0; eauto.
Qed.

Lemma Submap_add_spec_1 : forall (m m' : t) x v,
  ~ M.In x m' -> Submap m m' -> Submap m (M.add x v m').
Proof.
  intros; unfold Submap in *; destruct H0; split.
  - intros. rewrite add_in_iff in *; right; auto.
  - intros. rewrite add_mapsto_new in *; auto. destruct H3.
    -- destruct H3; subst. apply Key.eq_leibniz in H3; subst;
       exfalso; apply H; apply H0; now exists e.
    -- eapply H1; eauto.
Qed.

Lemma Submap_in_spec :  forall (m m' : t) x,
  Submap m m' -> M.In x m -> M.In x m'.
Proof.
  intros. unfold Submap in *; destruct H; auto.
Qed.

Lemma Submap_notin_spec : forall (m m' : t) x,
  Submap m m' -> ~M.In x m' -> ~M.In x m.
Proof.
  unfold not,Submap; intros; apply H0; destruct H; auto.
Qed.

Lemma Submap_find_spec : forall (m m' : t) x v,
  Submap m m' -> M.find x m = Some v -> M.find x m' = Some v.
Proof.
  intro m; induction m using map_induction; intros m' y v Hsub Hfind.
  - unfold Empty in *; exfalso; apply (H y v). now apply find_2.
  - unfold Add in H0; rewrite H0 in *. destruct (Key.eq_dec x y); subst.
    -- rewrite add_eq_o in *; auto; inversion Hfind; subst; clear Hfind.
      unfold Submap in Hsub. destruct Hsub.
      assert (M.In y m2). { rewrite H0. rewrite add_in_iff. now left. }
      apply H1 in H3.
      assert (M.MapsTo y v m2). { rewrite H0. rewrite add_mapsto_iff; now left. }
      destruct H3. apply H2 with (e' := x0) in H4; auto; subst. now apply find_1.
    -- rewrite add_neq_o in *; auto; eapply Submap_Add_spec in Hsub; eauto.
Qed.

Lemma Submap_refl : Reflexive Submap.
Proof. 
  intros; unfold Submap; split; intros; auto.
  eapply mapsto_fun; eauto.
Qed.

Lemma Submap_eq_left_spec : forall (m m' m1 : t), 
  m == m' -> Submap m m1 <-> Submap m' m1.
Proof.
  split; intros.
  - split; destruct H0; intros.
    -- apply H0; now rewrite H.
    -- assert (M.MapsTo k e m). { apply find_2; rewrite H. now apply find_1. }
      apply (H1 k e e' H4 H3).
  - split; destruct H0; intros.
    -- apply H0; now rewrite <- H.
    -- assert (M.MapsTo k e m'). { apply find_2; rewrite <- H. now apply find_1. }
      apply (H1 k e e' H4 H3).
Qed.

Lemma Submap_eq_right_spec : forall (m m' m1 : t), 
  m == m' -> Submap m1 m <-> Submap m1 m'.
Proof.
  split; intros.
  - split; destruct H0; intros.
    -- apply H0 in H2. now rewrite H in *.
    -- assert (M.MapsTo k e' m). { apply find_2; rewrite H. now apply find_1. }
        apply (H1 k e e' H2 H4).
  - split; destruct H0; intros.
    -- apply H0 in H2; now rewrite <- H in *.
    -- assert (M.MapsTo k e' m'). { apply find_2; rewrite <- H. now apply find_1. }
      apply (H1 k e e' H2 H4).
Qed.

Lemma Submap_trans : Transitive Submap.
Proof.
  unfold Transitive; intro x; induction x using map_induction.
  - intros y z HSxy HSyz; now apply Submap_Empty_spec.
  - intros y z HSxy HSyz.
    assert (M.find x3 y = Some e).
    {
      unfold Submap in HSxy; destruct HSxy.
      assert (M.In x3 x2).
      { exists e; apply find_2; rewrite H0. now apply add_eq_o. }
      apply H1 in H3 as H3'. destruct H3,H3'. eapply H2 in H4 as H4'; eauto.
      apply find_1  in H3; rewrite H0 in *; rewrite add_eq_o in *; auto; inversion H3; subst.
      now apply find_1. reflexivity.
    }
    assert (M.find x3 z = Some e).
    {
      unfold Submap in HSyz; destruct HSyz.
      assert (M.In x3 y). { exists e; now apply find_2. }
      apply H2 in H4 as H4'. destruct H4,H4'. eapply H3 in H5 as H5'; eauto.
      apply find_1 in H4; rewrite H1 in *; inversion H4; subst.
      now apply find_1.
    }
    apply Submap_Add_spec_2 with (m := x1) (x := x3) (v := e); auto.
    apply IHx1 with (y := y); auto.
    eapply Submap_Add_spec; eauto.
Qed.

#[export] Instance Submap_po : PreOrder Submap.
Proof. split; try apply Submap_refl; apply Submap_trans. Qed.

End MapET.

Module MapETLVL (Data : EqualityType) (M : Interface.S Level) <:  MapLVLInterface Data M.

Include MapET Level Data M.
Import OP.P.

(** *** Definition *)

Definition max_key (m : t) : nat :=
  foldkeys (fun x acc => Nat.max x acc) m 0.

Definition new_key (m : t) : nat := 
  if M.is_empty m then 0 else S (max_key m).

(** *** Max *)

Fact max_key_proper : 
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq) 
    (fun (x0 : M.key) (acc : nat) => Nat.max x0 acc).
Proof. repeat red; intros; now subst. Qed.

Fact max_key_proper_forall : forall x,
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq) (fun (k : M.key) (_ : Data.t) => k <? x).
Proof. repeat red; intro; auto. Qed.

Fact max_key_diamond :
  Diamond Logic.eq (fun (k : M.key) (_ : Data.t) (acc : nat) => Nat.max k acc).
Proof. unfold Diamond; intros; subst; lia. Qed.

#[local] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv max_key_proper 
max_key_diamond max_key_proper_forall : core.

#[export]
Instance max_key_eq : Proper (eq ==> Logic.eq) max_key.
Proof.
  repeat red; intro m. induction m using map_induction; intros m' Heq; unfold max_key.
  - repeat rewrite foldkeys_Empty; eauto. now rewrite Empty_eq_spec.
  - rewrite foldkeys_Add; eauto.
    symmetry; rewrite foldkeys_Add; eauto; now rewrite Add_eq_spec.
Qed.

Lemma max_key_Empty_spec : forall (m : t), 
  Empty m -> max_key m = 0.
Proof.
  intros; unfold max_key; rewrite foldkeys_Empty; eauto.
Qed.

Lemma max_key_empty_spec : max_key M.empty = 0.
Proof.
  intros; unfold max_key; rewrite foldkeys_Empty; eauto. apply empty_1.
Qed.

Lemma max_key_Add_spec : forall (m m' : t) x v,
  ~M.In x m -> Add x v m m' ->
    (max_key m' = x /\ max_key m <= x) \/ (max_key m' = max_key m /\ max_key m > x).
Proof.
  intros; eapply foldkeys_Add in H; eauto; unfold max_key.
  rewrite H. 
  destruct (Nat.leb_spec0 (foldkeys (fun (x0 : M.key) (acc : nat) => Nat.max x0 acc) m 0) x).
  - apply max_l in l as l'. left; rewrite l' in *; split; auto.
  - rewrite max_r; try lia.
Qed.

Lemma max_key_Add_spec_1 : forall (m m' : t) x v,
  ~M.In x m -> Add x v m m' ->  max_key m <= x -> max_key m' = x.
Proof.
  intros; eapply foldkeys_Add in H; eauto; unfold max_key.
  rewrite H. now apply max_l.
Qed.

Lemma max_key_Add_spec_2 : forall (m m' : t) x v,
  ~M.In x m -> Add x v m m' ->  max_key m > x -> max_key m' = max_key m.
Proof.
  intros; eapply foldkeys_Add in H; eauto; unfold max_key.
  rewrite H. apply max_r. unfold max_key in *; lia.
Qed.

Lemma max_key_add_spec : forall (m : t) x v,
  ~M.In x m -> (max_key (M.add x v m) = x /\ max_key m <= x) \/ 
                (max_key (M.add x v m) = max_key m /\ max_key m > x).
Proof.
  intros; destruct (Nat.leb_spec0 (max_key m) x).
  - left; split; auto; unfold max_key,foldkeys; rewrite fold_add; auto.
    -- now rewrite max_l.
    -- repeat red; intros; now subst.
  - right; split; try lia; unfold max_key,foldkeys; rewrite fold_add; auto.
    -- rewrite max_r; auto. assert (x <= max_key m) by lia. 
      now unfold max_key,foldkeys in H0.
    -- repeat red; intros; now subst.
Qed.

Lemma max_key_add_spec_1 : forall (m : t) x v,
  ~M.In x m -> max_key m <= x -> max_key (M.add x v m) = x.
Proof.
  intros; apply max_key_add_spec with (v := v) in H; destruct H.
  - now destruct H.
  - destruct H; lia.
Qed.

Lemma max_key_add_spec_2 : forall (m : t) x v,
  ~M.In x m -> max_key m > x -> max_key (M.add x v m) = max_key m.
Proof.
  intros; apply max_key_add_spec with (v := v) in H; destruct H.
  - destruct H; lia.
  - now destruct H.
Qed.

Lemma max_key_add_spec_4 : forall (m m' : t) x v v',
  ~M.In x m -> ~M.In x m' ->
  max_key m = max_key m' -> max_key (M.add x v m) = max_key (M.add x v' m').
Proof.
  intros. 
  apply max_key_add_spec with (v := v) in H as H'. 
  apply max_key_add_spec with (v := v') in H0 as H0'.
  destruct H' as [[Heq1 Hleb1] | [Heq1 Hgt1]];
  destruct H0' as [[Heq2 Hleb2] | [Heq2 Hgt2]]; subst; try lia.
Qed.


Lemma max_key_ub_spec : forall (m : t) x, x > max_key m -> for_all_dom (fun y => y <? x) m = true.
Proof.
  intro m; induction m using map_induction; intros.
  - unfold for_all_dom; apply for_all_iff; auto.
    intros. unfold Empty in H; exfalso; apply (H x0 e H1).
  - unfold for_all_dom; apply for_all_iff; auto.
    intros. apply max_key_Add_spec in H0 as H'; auto. destruct H'; destruct H3.
    -- subst. unfold Add in H0. apply find_1 in H2. rewrite H0 in H2.
      rewrite add_o in H2; destruct (Level.eq_dec (max_key m2) x1); subst.
      + apply Nat.ltb_lt; lia.
      + apply find_2 in H2. assert (x0 > max_key m1) by lia.
        apply IHm1 in H3. unfold for_all_dom in *; rewrite for_all_iff in H3; auto.
        apply (H3 x1 e0 H2).
    -- apply find_1 in H2; rewrite H0 in H2. rewrite add_o in H2.
      destruct (Level.eq_dec x x1); subst.
      + inversion H2; subst; clear H2. rewrite H3 in *; clear H3.
        apply Nat.ltb_lt; lia.
      + apply find_2 in H2; rewrite H3 in *. apply IHm1 in H1.
        unfold for_all_dom in *; rewrite for_all_iff in H1; auto. apply (H1 x1 e0 H2).
Qed.

Lemma max_key_notin_spec : forall (m : t) x, x > max_key m -> ~ M.In x m.
Proof.
  intros; apply max_key_ub_spec in H as H'; unfold for_all_dom in *; 
  rewrite for_all_iff in *; auto. intro c; destruct c. 
  apply H' in H0; apply Nat.ltb_lt in H0; lia.
Qed.

Lemma max_key_wh_spec : forall (m : t) v v',
  max_key (M.add (S (S (max_key m))) v (M.add (S (max_key m)) v' m)) = S (S (max_key m)).
Proof.
  intros. assert (~M.In (S (max_key m)) m) by (apply max_key_notin_spec; lia).
  assert (~M.In (S (S (max_key m))) (M.add (S (max_key m)) v' m)).
  - apply max_key_notin_spec. rewrite max_key_add_spec_1; auto; lia.
  - rewrite max_key_add_spec_1; auto. rewrite max_key_add_spec_1; auto.
Qed.

Lemma max_key_add_max_key_spec : forall (m : t) v,
  max_key (M.add (S (max_key m)) v m) = S (max_key m).
Proof.
  intros; rewrite max_key_add_spec_1; auto.
  apply max_key_notin_spec; lia.
Qed.

Lemma max_key_Submap_spec : forall (m m' : t),
  Submap m m' -> max_key m <= max_key m'.
Proof.
  intro m; induction m using map_induction; intros.
  - rewrite max_key_Empty_spec; auto; lia.
  - apply max_key_Add_spec in H0 as H'; auto.
    destruct H'.
    -- destruct H2; subst. eapply Submap_Add_spec_1 in H1 as H'; eauto.
      eapply Submap_Add_spec in H1; eauto.
      apply IHm1 in H1. destruct (Nat.leb_spec0 (max_key m2) (max_key m')); try lia.
      assert ((max_key m2) > (max_key m')) by lia. clear n. apply max_key_notin_spec in H2.
      contradiction.
    -- destruct H2; rewrite H2 in *. eapply Submap_Add_spec in H1; eauto.
Qed.

Lemma max_key_in_spec : forall (m : t) (x : M.key),
  M.In x m -> x <= (max_key m).
Proof.
  intro m; induction m using map_induction; intros x' Hin.
  - exfalso; destruct Hin as [y Hin]; now apply (H x' y).
  - unfold Add in *; rewrite H0 in *.
    rewrite add_in_iff in Hin; destruct Hin; subst.
    -- destruct (Nat.leb_spec0 (max_key m1) x').
       + eapply max_key_add_spec_1 in l; eauto; rewrite l; lia.
       + assert (x' < max_key m1) by lia.
          eapply max_key_add_spec_2 in H1; eauto; rewrite H1; lia.
    -- apply IHm1 in H1. destruct (Nat.leb_spec0 (max_key m1) x).
       + eapply max_key_add_spec_1 in l as l'; eauto; rewrite l'; lia.
       + assert (x < max_key m1) by lia.
            eapply max_key_add_spec_2 in H2; eauto; now rewrite H2.
Qed.

Lemma max_key_add_spec_3 : forall (m: t) (x : M.key) v,
  M.In x m -> (max_key (M.add x v m)) = (max_key m).
Proof.
  intros m x v Hin. apply Eqdom_in_add with (e := v) in Hin.
  unfold max_key. rewrite foldkeys_Proper; eauto. now symmetry.
Qed.
  
(** *** New *)

Lemma new_key_unfold : forall (m : t), 
  new_key m = if M.is_empty m then 0 else S (max_key m).
Proof. intros; auto. Qed.

#[export]
Instance new_key_eq : Proper (eq ==> Logic.eq) new_key.
Proof. 
  intros m; induction m using map_induction; intros m' Heq; unfold new_key.
  - assert (Empty m'). { rewrite <- Empty_eq_spec; eauto. }
    apply is_empty_1 in H,H0; now rewrite H,H0.
  - assert (Add x e m1 m'). { rewrite <- Add_eq_spec; eauto. }
    apply is_empty_Add_spec in H0 as H0';
    apply is_empty_Add_spec in H1 as H1'. rewrite H0',H1'; clear H0' H1'; f_equal.
    now rewrite Heq.
Qed.

Lemma new_key_Empty_spec : forall (m : t), 
  Empty m -> new_key m = 0.
Proof.
  intros; unfold new_key; apply is_empty_1 in H; now rewrite H.
Qed.

Lemma new_key_empty_spec : new_key M.empty = 0.
Proof.
  assert (@Empty Data.t M.empty) by apply empty_1.
  intros; unfold new_key; apply is_empty_1 in H; now rewrite H.
Qed.

Lemma new_key_geq_max_key : forall (m : t), new_key m >= max_key m.
Proof.
  intro m; unfold new_key; destruct (M.is_empty m) eqn:HEmp; try lia.
  apply is_empty_2 in HEmp; rewrite max_key_Empty_spec; auto.
Qed. 

Lemma new_key_add_spec : forall (m : t) x v,
  ~M.In x m -> (new_key (M.add x v m) = S x /\ new_key m <= S x) \/ 
                (new_key (M.add x v m) = new_key m /\ new_key m > S x).
Proof.
  intros; unfold new_key; rewrite is_empty_add_spec. 
  destruct (Nat.leb_spec0 (new_key m) (S x)); unfold new_key in *; 
  destruct (M.is_empty m) eqn:Heq.
  - left; split; auto; f_equal. apply max_key_add_spec_1; auto.
    apply is_empty_iff in Heq; rewrite max_key_Empty_spec; auto; lia.
  - left; split; auto; f_equal; apply max_key_add_spec_1; auto; lia.
  - lia.
  - right; split; try lia; f_equal; apply max_key_add_spec_2; auto; lia.
Qed.

Lemma new_key_add_spec_2 : forall (m : t) x v,
  ~M.In x m -> new_key m > S x -> new_key (M.add x v m) = new_key m.
Proof.
  intros; apply new_key_add_spec with (v := v) in H; destruct H.
  - destruct H; lia.
  - now destruct H.
Qed.

Lemma new_key_add_spec_1 : forall (m : t) x v,
  ~M.In x m -> new_key m <= S x -> new_key (M.add x v m) = S x.
Proof.
  intros; apply new_key_add_spec with (v := v) in H; destruct H.
  - now destruct H.
  - destruct H; lia.
Qed.

Lemma new_key_add_spec_3 : forall (m: t) (x : M.key) v,
  M.In x m -> (new_key (M.add x v m)) = (new_key m).
Proof.
  intros m x v Hin. unfold new_key.
  destruct (M.is_empty m) eqn:Heq.
  - apply is_empty_2 in Heq; exfalso.
    destruct Hin. now apply (Heq x x0).
  - replace (M.is_empty (M.add x v m)) with false.
    -- f_equal; now apply max_key_add_spec_3.
    -- symmetry. destruct (M.is_empty (M.add x v m)) eqn:HEmp; auto.
        apply is_empty_2 in HEmp; exfalso; unfold Empty in *.
        apply (HEmp x v). apply add_mapsto_iff; left; now split.
Qed.

Lemma new_key_Add_spec : forall (m m' : t) x v,
  ~M.In x m -> Add x v m m' ->
    (new_key m' = S x /\ new_key m <= S x) \/ (new_key m' = new_key m /\ new_key m > S x).
Proof.
  intros; apply max_key_Add_spec in H0 as H0'; auto.
  destruct H0' as [[Heq Hleb] | [Heq Hgt]]; subst.
  - unfold new_key; apply is_empty_Add_spec in H0 as H0'.
    rewrite H0'; left; split; auto; destruct (M.is_empty m); lia.
  - unfold new_key; apply is_empty_Add_spec in H0 as H0'.
    rewrite H0'; right. destruct (M.is_empty m) eqn:HEmp.
    -- apply is_empty_2 in HEmp. apply max_key_Empty_spec in HEmp; rewrite HEmp in *.
        lia.
    -- split; lia.
Qed. 

Lemma new_key_notin_spec : forall (m : t) x, x >= new_key m -> ~ M.In x m.
Proof.
  intros; unfold new_key in *; destruct (M.is_empty m) eqn:Heq.
  - unfold not; intros; apply is_empty_iff in Heq;
    intros. destruct H0; now apply (Heq x x0).
  - apply max_key_notin_spec; lia.
Qed.

Lemma new_key_in_spec : forall (m : t) x, M.In x m -> x < new_key m.
Proof.
  intro m; induction m using map_induction; intros y HIn.
  - exfalso; destruct HIn; now apply (H y x).
  - unfold Add in H0; rewrite H0 in HIn.
    apply add_in_iff in HIn as [Heq | HIn]; subst.
    -- unfold new_key. apply is_empty_Add_spec in H0 as H0'.
        rewrite H0'. apply max_key_Add_spec in H0; auto.
        destruct H0 as [[Heq Hleb] | [Heq Hgt]]; subst; try lia.
    -- apply IHm1 in HIn. apply new_key_Add_spec in H0; auto.
        destruct H0 as [[Heq Hleb] | [Heq Hgt]]; subst; try lia.
Qed.

Lemma new_key_Submap_spec : forall (m' m : t),
  Submap m m' -> new_key m <= new_key m'.
Proof.
  intros; unfold new_key; destruct (M.is_empty m') eqn:Heq.
  - rewrite <- is_empty_iff in Heq;
    apply Submap_Empty_spec_1 in H; auto.
    rewrite is_empty_iff in *; now rewrite H.
  - destruct (M.is_empty m) eqn:Heq'; try lia.
    apply le_n_S. now apply max_key_Submap_spec.
Qed.

Lemma new_key_Submap_spec_1 : forall (m' m : t) v v',
  Submap m m' -> Submap m (M.add (S (new_key m')) v (M.add (new_key m') v' m')).
Proof.
  intros. repeat apply Submap_add_spec_1; auto.
  - intro; apply add_in_iff in H0; destruct H0; try lia.
    assert (S (new_key m') >= (new_key m')) by lia.
    apply new_key_notin_spec in H1; contradiction.
  - apply new_key_notin_spec; auto.
Qed.

Lemma new_key_add_new_key_spec : forall (m : t) v,
  new_key (M.add (new_key m) v m) = S (new_key m).
Proof.
  intros; unfold new_key; rewrite is_empty_add_spec; destruct (M.is_empty m) eqn:Heq.
  - rewrite max_key_add_spec_1; auto.
    -- apply is_empty_2 in Heq; intro; destruct H. now apply (Heq 0 x).
    -- apply is_empty_2 in Heq; rewrite max_key_Empty_spec; auto.
  - f_equal. apply max_key_add_max_key_spec.
Qed.

#[export] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv max_key_proper 
max_key_diamond max_key_proper_forall : core.

End MapETLVL.