From Coq Require Import MSets Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From DeBrLevel Require Import Level MapExtInterface.

(** * Implementation - [MMaps] extension *)

(** ** Extension of [MMaps] with new functions [Submap] and [For_all] *)
Module MapET (Key : OrderedTypeWithLeibniz) (Data : EqualityType) 
                                            (M : Interface.S Key) <:  MapInterface Key Data M.

Module OP := Facts.OrdProperties Key M.
Import OP.P.

(** *** Definitions *)

Definition t : Type := M.t Data.t.

Definition eq := @M.Equal Data.t.

Definition Submap (m m': t) :=
  (forall y, M.In y m -> M.In y m') /\
  (forall k e e', M.MapsTo k e m -> M.MapsTo k e' m' -> e = e').

(** MMaps does not provide a function that check if all elements in the environment satisfy a property [P]. Consequently we define it. *)
Definition For_all (P: Key.t -> Data.t -> Prop) (m: t) := 
  forall k d, M.find k m = Some d -> P k d.

(** *** Properties *)

(** **** [eq] properties *)

#[export] Instance eq_equiv : Equivalence eq := _.

#[export] Instance iff_equiv : Equivalence iff := _.

#[export] Instance logic_eq_equiv : forall A, Equivalence (@Logic.eq A) := _.

#[local] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv : core.

(** **** [Empty] properties *)

#[export] Instance Empty_eq_iff : Proper (eq ==> iff) Empty.
Proof. do 2 red; intros m m' Heq; now rewrite Heq. Qed.

Lemma Empty_eq (m : t) : Empty m -> m == M.empty.
Proof. intro HEmp; apply eq_empty; now apply is_empty_1. Qed.

Lemma notEmpty_Add (x: M.key) (e: Data.t) (m m': t) : Add x e m m' -> ~ Empty m'.
Proof.
  intro HAdd; intro HEmp.
  unfold Add in *. rewrite HAdd in HEmp.
  apply (HEmp x e).
  now apply add_1.
Qed.

Lemma notEmpty_find (x: M.key) (e: Data.t) (m: t) : Empty m -> ~ (M.find x m = Some e).
Proof.
  intro HEmp; intro Hfi.
  apply (HEmp x e).
  now apply find_2.
Qed. 

(** **** [is_empty] properties *)

Lemma is_empty_Add (x: M.key) (e: Data.t) (m m': t) : Add x e m m' -> M.is_empty m' = false.
Proof.
  intro HEmp. 
  apply notEmpty_Add in HEmp.
  apply not_true_is_false.
  intro Hemp; apply HEmp.
  now apply is_empty_iff.
Qed.

Lemma is_empty_add (x: M.key) (e: Data.t) (m : t) : M.is_empty (M.add x e m) = false.
Proof.
  apply not_true_is_false; intro Hemp.
  apply is_empty_iff in Hemp.
  apply (Hemp x e).
  apply add_mapsto_iff; now left.
Qed.

(** **** [Add] properties *)

#[export] Instance Add_eq_iff : forall (e: Data.t),
  Proper (Key.eq ==> eq ==> eq ==> iff) (fun (k : Key.t) => Add k e).
Proof.
  do 5 red. intros e k k' HKeq m m' Heqm n n' Heqn.
  split; unfold Add; intro HAdd.
  - now rewrite HKeq in *; rewrite <- Heqm; rewrite <- Heqn.
  - now rewrite <- HKeq in *; rewrite Heqm; rewrite Heqn.
Qed.

(** **** [add] properties *)

Lemma add_remove (x: M.key) (v: Data.t) (m: t) :
  M.find x m = Some v -> m == (M.add x v (M.remove x m)).
Proof. intro Hfi; rewrite add_remove_1; symmetry; now rewrite add_id. Qed.

Lemma add_shadow (x: M.key) (v v': Data.t) (m: t) : 
  eq (M.add x v (M.add x v' m)) (M.add x v m). 
Proof.
  intro y; destruct (Key.eq_dec x y).
  - rewrite e.
    repeat rewrite add_eq_o; auto; reflexivity.
  - repeat rewrite add_neq_o; auto.
Qed.

(** **** [Submap] properties *)

Lemma Submap_Empty_bot (m m': t) : Empty m -> Submap m m'.
Proof.
  intro HEmp; apply Empty_eq in HEmp.
  unfold Submap in *; split.
  - intros y HIn; rewrite HEmp in HIn.
    now apply not_in_empty in HIn. 
  - intros k e e' HMp; rewrite HEmp in HMp.
    now apply empty_mapsto_iff in HMp.
Qed.

Lemma Submap_Empty (m m': t) :
  Submap m m' -> Empty m' -> Empty m.
Proof.
  intros [HIn _] HEmp k e HM.
  assert (HInm : M.In k m) by now exists e.
  apply HIn in HInm as [e' HM'].
  now apply (HEmp k e').
Qed.

Lemma Submap_empty_bot (m: t) : Submap M.empty m.
Proof.
  split.
  - intros y HIn.
    apply empty_in_iff in HIn; contradiction.
  - intros k e e' HMp HMp'. 
    apply empty_mapsto_iff in HMp; contradiction.
Qed.

Lemma Submap_Add (x: M.key) (v: Data.t) (m m' m1: t) :
  Submap m' m1 -> ~ M.In x m -> Add x v m m' -> Submap m m1.
Proof.
  intros [HIn' HMp'] HIn HAdd; unfold Add in *; split.
  - intros k HIn1.
    apply HIn'; rewrite HAdd.
    now apply in_add.
  - intros k e e' HMp HMp1.
    apply (HMp' k); auto.
    rewrite HAdd.
    now apply add_mapsto_new; auto.
Qed.

Lemma Submap_Add_in (x: M.key) (v: Data.t) (m m' m1: t) :
  Submap m' m1 -> ~ M.In x m -> Add x v m m' -> M.In x m1.
Proof.
  unfold Add; intros [HIn _] HnIn Heq.
  apply HIn; rewrite Heq.
  apply add_in_iff; now left.
Qed.

Lemma Submap_Add_find (x: M.key) (v: Data.t) (m m' m1: t) :
  Submap m' m1 -> ~ M.In x m -> Add x v m m' -> M.find x m1 = Some v.
Proof.
  unfold Add; intros [HIn HMp] HnIn Heq.
  assert (HIn' : M.In x m'). 
  - rewrite Heq; apply add_in_iff; now left.
  - apply HIn in HIn' as HIn1; rewrite Heq in *.
    destruct HIn' as [e HMp']; destruct HIn1 as [e1 HMp1].
    rewrite <- Heq in HMp'. 
    apply (HMp x e e1) in HMp' as Heq1; auto; subst.
    rewrite Heq in *.
    apply find_1 in HMp1; rewrite HMp1; clear HMp1.
    apply find_1 in HMp'; rewrite add_eq_o in HMp'; auto.
    reflexivity.
Qed.

Lemma Submap_Add_1 (x: M.key) (v: Data.t) (m m' m1: t) :
  Submap m m1 -> 
  ~ M.In x m -> M.find x m1 = Some v -> Add x v m m' ->
  Submap m' m1.
Proof.
  unfold Add in *; intros [HIn HMp] HnIn Hfi Heq; split.
  - intros k HIn'; rewrite Heq in *.
    apply add_in_iff in HIn' as [Heq1 | HIn1]; auto.
    rewrite <- Heq1; exists v.
    now apply find_2.
  - intros k e e1 HMp' HMp1.
    rewrite Heq in *. 
    apply add_mapsto_new in HMp' as [[HKeq HDeq] | HMp2]; auto; subst.
    -- rewrite HKeq in *.
       apply find_1 in HMp1; rewrite Hfi in *.
       now inversion HMp1.
    -- apply (HMp k e e1) in HMp1 as Heq1; auto.
Qed.

Lemma Submap_add (x: M.key) (v: Data.t) (m m': t) :
  Submap m m' -> Submap (M.add x v m) (M.add x v m').
Proof.
  intros [HIn HMp]; split.
  - intros k HIn1. rewrite add_in_iff in *.
    destruct HIn1; auto.
  - intros k e e1 HMp1 HMp1'. 
    rewrite add_mapsto_iff in *.
    destruct HMp1 as [[Heq Heq'] | [Hneq HMp1]];
    destruct HMp1' as [[Heq1 Heq1'] | [Hneq1 HMp1']]; 
    subst; auto; (try now contradiction).
    apply (HMp k); auto.
Qed.

Lemma Submap_add_1 (x: M.key) (v: Data.t) (m m': t) :
  ~ M.In x m' -> Submap m m' -> Submap m (M.add x v m').
Proof.
  intros HnIn [HIn HMp]; split.
  - intros k HIn'. rewrite add_in_iff in *; right; auto.
  - intros k e e' HMp1 HMp1'. 
    apply add_mapsto_iff in HMp1' as [[HKeq HDeq] | [_ HMp1']].
    -- subst; rewrite HKeq in *.
       exfalso; apply HnIn.
       apply HIn; now exists e.
    -- now apply (HMp k).
Qed.

Lemma Submap_add_2 (x: M.key) (v: Data.t) (m m': t) : 
  ~ M.In x m -> Submap (M.add x v m) m' -> Submap m m'.
Proof.
  intros HIn HSub.
  eapply Submap_Add; eauto.
  eapply Add_add.
Qed.

Lemma Submap_in (x: M.key) (m m': t) : Submap m m' -> M.In x m -> M.In x m'.
Proof. intros [HIn _]; auto. Qed.

Lemma Submap_notin (x: M.key) (m m': t) : Submap m m' -> ~M.In x m' -> ~M.In x m.
Proof. intros [HIn _] HIn' HIn1; apply HIn'; auto. Qed.

Lemma Submap_find (x: M.key) (v: Data.t) (m m': t) :
  Submap m m' -> M.find x m = Some v -> M.find x m' = Some v.
Proof.
  induction m using map_induction; intros Hsub Hfind.
  - exfalso; apply (H x v); now apply find_2.
  - unfold Add in H0; rewrite H0 in *.
    destruct (Key.eq_dec x x0).
    -- rewrite e0 in *. 
       rewrite add_eq_o in *; auto; inversion Hfind; subst; clear Hfind.
       unfold Submap in Hsub. destruct Hsub.
       assert (M.In x0 m2). { rewrite H0. rewrite add_in_iff. now left. }
       apply H1 in H3.
       assert (M.MapsTo x0 v m2). { rewrite H0. rewrite add_mapsto_iff; now left. }
       destruct H3. apply H2 with (e' := x1) in H4; auto; subst. now apply find_1.
       reflexivity.
    -- rewrite add_neq_o in *; auto; eapply Submap_Add in Hsub; eauto.
       intro; apply n; now symmetry.
Qed.

#[export] Instance Submap_refl : Reflexive Submap.
Proof. 
  intros; unfold Submap; split; intros; auto.
  eapply mapsto_fun; eauto.
Qed.

#[export] Instance Submap_eq : Proper (eq ==> eq ==> iff) Submap.
Proof.
  do 4 red; intros m m' Heq m1 m1' Heq1. 
  split; intros [HIn HMp]; split.
  - intros y HIn'. 
    rewrite <- Heq1.
    apply HIn; now rewrite Heq.
  - intros k e e' HMp1 HMp1'.
    rewrite <- Heq1 in *.
    rewrite <- Heq in *.
    now apply (HMp k e e').
  - intros y HIn'. 
    rewrite Heq1.
    apply HIn; now rewrite <- Heq.
  - intros k e e' HMp1 HMp1'.
    rewrite Heq1 in *.
    rewrite Heq in *.
    now apply (HMp k e e').
Qed.

#[export] Instance Submap_trans : Transitive Submap.
Proof.
  red; intros x y z [HInx HMpx] [HIny HMpy]; split.
  - clear HMpx HMpy; intros k HIn.
    apply (HIny k).
    now apply (HInx k).
  - intros k e e' HMp HMp'.
    assert (HIn : M.In k x) by now exists e.
    apply (HInx k) in HIn as [e1 HMp1].
    apply (HMpx k e e1) in HMp1 as Heq; auto; subst.
    now apply (HMpy k e1 e').
Qed.

#[export] Instance Submap_po : PreOrder Submap.
Proof. split; try apply Submap_refl; apply Submap_trans. Qed.

(** **** [For_all] properties *)

#[export] Instance For_all_proper (P: Key.t -> Data.t -> Prop) : 
  Proper (eq ==> iff) (For_all P).
Proof.
  intros o o' Heqo; unfold For_all; split; intros HFa k d Hfi.
  - rewrite <- Heqo in Hfi; auto.
  - rewrite Heqo in Hfi; auto.
Qed.

Lemma For_all_empty (P: Key.t -> Data.t -> Prop) : For_all P M.empty.
Proof. 
  intros k d Hfi.
  apply find_2 in Hfi.
  apply empty_mapsto_iff in Hfi; contradiction.
Qed.

Lemma For_all_Empty (o: t) (P: Key.t -> Data.t -> Prop) :
  Empty o -> For_all P o.
Proof.
  intros HEmp k d Hfi; apply Empty_eq in HEmp.
  rewrite HEmp in Hfi.
  apply find_2 in Hfi.
  apply empty_mapsto_iff in Hfi; contradiction.
Qed.

Lemma For_all_add (k : Key.t) (d : Data.t) (o : t) (P : Key.t -> Data.t -> Prop) :
 P k d /\ For_all P o -> For_all P (M.add k d o).
Proof.
  intros [HP HFa] k' d' Hfi.
  destruct (Key.eq_dec k k') as [Heq | Hneq]; subst.
  - rewrite add_eq_o in Hfi; auto.
    inversion Hfi; subst.
    apply Key.eq_leibniz in Heq; now subst.
  - rewrite add_neq_o in Hfi; auto.
Qed.

Lemma For_all_add_notin 
  (k : Key.t) (d : Data.t) (o : t) (P : Key.t -> Data.t -> Prop) :
  ~ M.In k o ->
 ((P k d /\ For_all P o) <-> For_all P (M.add k d o)).
Proof.
  intro HnIn; split.
  - apply For_all_add.
  - intro HFa; split.
    -- apply HFa.
       now rewrite add_eq_o.
    -- intros k' d' Hfi. 
       destruct (Key.eq_dec k k') as [Heq | Hneq]; subst.
       + exfalso; apply HnIn.
         rewrite Heq.
         exists d'; now apply find_2.
       + apply HFa.
         now rewrite add_neq_o.
Qed.

End MapET.


(** ---- *)


(** ** Extension of [MMaps] with functions [max_key] and [new_key] *)
Module MapETLVL (Data : EqualityType) (M : Interface.S Level) <:  MapLVLInterface Data M.

Include MapET Level Data M.
Import OP.P.

(** *** Definitions *)

Definition max_key (m : t) : nat :=
  foldkeys Nat.max m 0.

Definition new_key (m : t) : nat := 
  if M.is_empty m then 0 else S (max_key m).

(** *** Properties *)

(** **** [max_key] properties *)

#[export] Instance max_key_proper : 
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq) Nat.max := _.

#[export] Instance max_key_proper_forall : forall x,
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq) (fun (k : M.key) (_ : Data.t) => k <? x) := _.

Fact max_key_diamond :
  Diamond Logic.eq (fun (k : M.key) (_ : Data.t) (acc : nat) => Nat.max k acc).
Proof. unfold Diamond; intros; subst; lia. Qed.

#[local] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv max_key_proper 
                      max_key_diamond max_key_proper_forall : core.

#[export] Instance max_key_eq : Proper (eq ==> Logic.eq) max_key.
Proof.
  repeat red; unfold max_key; intros.
  apply foldkeys_Proper; auto.
  now apply Equal_Eqdom.
Qed.

Lemma max_key_Empty (m : t) : Empty m -> max_key m = 0.
Proof. intro HEmp; unfold max_key; rewrite foldkeys_Empty; auto. Qed.

Lemma max_key_empty : max_key M.empty = 0.
Proof. unfold max_key; rewrite foldkeys_Empty; auto; apply empty_1. Qed.

Lemma max_key_Add_max (x: M.key) (v: Data.t) (m m': t) : 
  Add x v m m' -> max_key m' = max x (max_key m).
Proof.
  intro HA.
  destruct (In_dec m x).
  - unfold Add in HA; rewrite HA; clear HA.
    destruct i as [v' HM].
    apply find_1 in HM.
    apply add_id in HM.
    rewrite <- HM.
    rewrite add_shadow.
    rewrite <- add_remove_1.
    symmetry.
    rewrite <- add_remove_1.
    symmetry.
    unfold max_key.
    rewrite foldkeys_Add 
    with (m1 := (M.remove x m)) (k := x) (e := v); auto.
    -- symmetry. 
       rewrite foldkeys_Add
       with (m1 := (M.remove x m)) (k := x) (e := v'); auto.
       + lia.
       + rewrite remove_in_iff; intros []; auto.
       + apply Add_add.
    -- rewrite remove_in_iff; intros []; auto.
    -- apply Add_add.
  - unfold max_key. 
    rewrite foldkeys_Add; eauto.
Qed.

(* begin hide *)
(* 
Lemma max_key_Add_spec (x: M.key) (v: Data.t) (m m': t) :
  Add x v m m' ->
  (max_key m' = x /\ max_key m <= x) \/ (max_key m' = max_key m /\ max_key m > x).
Proof.
  intro HA.
  rewrite (max_key_Add_max x v m m' HA); lia.
Qed.
*)
(* end hide *)

Lemma max_key_Add_l (x: M.key) (v: Data.t) (m m': t) :
  Add x v m m' ->  max_key m <= x -> max_key m' = x.
Proof.
  intro HA.
  rewrite (max_key_Add_max x v m m' HA); lia.
Qed.

Lemma max_key_Add_r (x: M.key) (v: Data.t) (m m': t) :
  Add x v m m' ->  max_key m > x -> max_key m' = max_key m.
Proof.
  intro HA.
  rewrite (max_key_Add_max x v m m' HA); lia.
Qed. 

Lemma max_key_add_max (x: M.key) (v: Data.t) (m: t) : 
  max_key (M.add x v m) = max x (max_key m).
Proof.
  apply max_key_Add_max with (v := v).
  apply Add_add.
Qed.

(* begin hide *)
(* 
Lemma max_key_add_spec (x: M.key) (v: Data.t) (m: t) :
  (max_key (M.add x v m) = x /\ max_key m <= x) \/ 
               (max_key (M.add x v m) = max_key m /\ max_key m > x).
Proof.
  rewrite (max_key_add_max x v m); lia.
Qed.
*)
(* end hide *)

Lemma max_key_add_l (x: M.key) (v: Data.t) (m: t) :
  max_key m <= x -> max_key (M.add x v m) = x.
Proof.
  rewrite (max_key_add_max x v m); lia.
Qed.

Lemma max_key_add_r (x: M.key) (v: Data.t) (m: t) :
  max_key m > x -> max_key (M.add x v m) = max_key m.
Proof.
  rewrite (max_key_add_max x v m); lia.
Qed.

Lemma max_key_add_iff (x: M.key) (v v': Data.t) (m m' : t) :
  max_key m = max_key m' -> max_key (M.add x v m) = max_key (M.add x v' m').
Proof.
  intro Heq.
  do 2 rewrite max_key_add_max.
  now rewrite Heq. 
Qed.

Lemma max_key_ub (x: M.key) (m : t) : 
  x > max_key m -> for_all_dom (fun y => y <? x) m = true.
Proof.
  revert x.
  induction m using map_induction; intros y Hgt.
  - unfold for_all_dom.
    apply for_all_iff; auto.
    intros x v HM.
    exfalso; apply (H x v HM).
  - apply for_all_iff; auto.
    intros z v HM. 
    unfold Add in H0; rewrite H0 in *; clear H0.
    apply add_mapsto_iff in HM as [[Heq Heq'] | [Hneq HM]]; subst.
    -- destruct (Level.leb_spec0 (max_key m1) z).
       + rewrite max_key_add_l in Hgt; try lia.
         apply Level.ltb_lt; lia.
       + apply Level.ltb_lt. 
         rewrite max_key_add_r in Hgt; lia.
    -- assert (y > max_key m1).
       + rewrite max_key_add_max in Hgt; lia.
       + apply IHm1 in H0. 
         unfold for_all_dom in *.
         rewrite for_all_iff in H0; auto.
         apply (H0 z v HM).
Qed.

Lemma max_key_notin (x: M.key) (m : t) : x > max_key m -> ~ M.In x m.
Proof.
  intros Hgt [v HMp]. 
  apply max_key_ub in Hgt as Hfa. 
  unfold for_all_dom in *; rewrite for_all_iff in *; auto.
  apply Hfa in HMp.
  apply Nat.ltb_lt in HMp; lia.
Qed.

Lemma max_key_add_max_key (v: Data.t) (m : t) :
  max_key (M.add (S (max_key m)) v m) = S (max_key m).
Proof.
  rewrite max_key_add_max; lia.
Qed.

Lemma max_key_in (x : M.key) (m : t) :
  M.In x m -> x <= (max_key m).
Proof.
  intros [v Hfi].
  apply find_1 in Hfi.
  apply add_id in Hfi.
  rewrite <- Hfi.
  rewrite max_key_add_max; lia.
Qed.

Lemma max_key_Submap (m m' : t) : Submap m m' -> max_key m <= max_key m'.
Proof.
  revert m'; induction m using map_induction; intros m' Hsub.
  - rewrite max_key_Empty; auto; lia.
  - unfold Add in H0; rewrite H0 in *.
    assert (HIn: M.In x (M.add x e m1)) by (rewrite add_in_iff; auto).
    apply Submap_in with (m' := m') in HIn; auto.
    destruct HIn as [v Hfi].
    apply find_1 in Hfi.
    apply add_id in Hfi.
    rewrite <- Hfi.
    apply Submap_add_2 in Hsub; auto.
    apply IHm1 in Hsub.
    do 2 rewrite max_key_add_max; lia.
Qed.

Lemma max_key_add_in (x : M.key) (v: Data.t) (m: t) :
  M.In x m -> (max_key (M.add x v m)) = (max_key m).
Proof.
  intros [v' Hfi].
  apply find_1 in Hfi.
  apply add_id in Hfi.
  rewrite <- Hfi at 2.
  now do 2 rewrite max_key_add_max.
Qed.
  
(** **** [new_key] properties *)

Lemma new_key_unfold (m : t) : 
  new_key m = if M.is_empty m then 0 else S (max_key m).
Proof. intros; auto. Qed.

#[export] Instance new_key_eq : Proper (eq ==> Logic.eq) new_key.
Proof.
  repeat red; intros m m' Heq.
  repeat rewrite new_key_unfold.
  destruct (M.is_empty m) eqn:Hemp.
  - rewrite Heq in Hemp.
    now rewrite Hemp.
  - rewrite Heq in Hemp.
    rewrite Hemp; f_equal.
    now rewrite Heq. 
Qed.

Lemma new_key_Empty (m : t) : Empty m -> new_key m = 0.
Proof.
  intro HEmp; unfold new_key; apply is_empty_1 in HEmp; now rewrite HEmp.
Qed.

Lemma new_key_empty : new_key M.empty = 0.
Proof.
  assert (@Empty Data.t M.empty) by apply empty_1.
  intros; unfold new_key; apply is_empty_1 in H; now rewrite H.
Qed.

Lemma new_key_Add_max (x: M.key) (v: Data.t) (m m': t) : 
  Add x v m m' -> new_key m' = max (S x) (new_key m).
Proof.
  intro HA.
  unfold new_key.
  destruct (M.is_empty m) eqn:Hemp.
  - destruct (M.is_empty m') eqn:Hemp'.
    -- apply is_empty_2 in Hemp'.
       exfalso.
       apply (Hemp' x v).
       unfold Add in HA; rewrite HA; clear HA.
       apply add_mapsto_iff; auto.
    -- unfold Add in HA; rewrite HA; clear HA. 
       rewrite max_key_add_max.
       apply is_empty_2 in Hemp.
       rewrite max_key_Empty; auto; lia.
  - destruct (M.is_empty m') eqn:Hemp'.
    -- apply is_empty_2 in Hemp'.
       exfalso.
       apply (Hemp' x v).
       unfold Add in HA; rewrite HA; clear HA.
       apply add_mapsto_iff; auto.
    -- unfold Add in HA; rewrite HA; clear HA.
       rewrite max_key_add_max; lia.
Qed. 

Lemma new_key_add_max (x: M.key) (v: Data.t) (m: t) : 
  new_key (M.add x v m) = max (S x) (new_key m).
Proof.
  apply (new_key_Add_max x v m).
  apply Add_add.
Qed. 

Lemma new_key_geq_max_key (m : t) : new_key m >= max_key m.
Proof.
  rewrite new_key_unfold.
  destruct (M.is_empty m) eqn:HEmp; try lia.
  apply is_empty_2 in HEmp; rewrite max_key_Empty; auto.
Qed. 

(* begin hide *)
(*
Lemma new_key_add_spec (x: M.key) (v: Data.t) (m: t) :
  (new_key (M.add x v m) = S x /\ new_key m <= S x) \/ 
               (new_key (M.add x v m) = new_key m /\ new_key m > S x).
Proof.
  rewrite new_key_add_max; lia.
Qed.
*)
(* end hide *)

Lemma new_key_add_l (x: M.key) (v: Data.t) (m: t) :
  new_key m <= S x -> new_key (M.add x v m) = S x.
Proof.
  rewrite new_key_add_max; lia.
Qed.

Lemma new_key_add_r (x: M.key) (v: Data.t) (m: t) :
  new_key m > S x -> new_key (M.add x v m) = new_key m.
Proof.
  rewrite new_key_add_max; lia.
Qed.

Lemma new_key_add_in (x : M.key) (v: Data.t) (m: t) :
  M.In x m -> (new_key (M.add x v m)) = (new_key m).
Proof.
  intros [v' Hfi].
  apply find_1 in Hfi.
  apply add_id in Hfi.
  rewrite <- Hfi at 2.
  now do 2 rewrite new_key_add_max.
Qed.

(* begin hide *)
(* 
Lemma new_key_Add_spec (x: M.key) (v: Data.t) (m m': t) :
  Add x v m m' ->
    (new_key m' = S x /\ new_key m <= S x) \/ (new_key m' = new_key m /\ new_key m > S x).
Proof.
  intro HA.
  rewrite (new_key_Add_max x v m m' HA); lia.
Qed. 
*)
(* end hide *)

Lemma  new_key_Add_l (x: M.key) (v: Data.t) (m m': t) :
  Add x v m m' ->  new_key m <= S x -> new_key m' = S x.
Proof.
  intro HA.
  rewrite (new_key_Add_max x v m m' HA); lia.
Qed.

Lemma new_key_Add_r (x: M.key) (v: Data.t) (m m': t) :
  Add x v m m' ->  new_key m > S x -> new_key m' = new_key m.
Proof.
  intro HA.
  rewrite (new_key_Add_max x v m m' HA); lia.
Qed.

Lemma new_key_add_new_key (v: Data.t) (m: t) :
  new_key (M.add (new_key m) v m) = S (new_key m).
Proof.
  rewrite new_key_add_max; lia.
Qed. 

Lemma new_key_notin (x: M.key) (m: t) : x >= new_key m -> ~ M.In x m.
Proof.
  unfold new_key; intro ge.
  destruct (M.is_empty m) eqn:Heq.
  - intro HIn. 
    apply is_empty_iff in Heq.
    destruct HIn as [v HMp].
    now apply (Heq x v).
  - apply max_key_notin; lia.
Qed.

Lemma new_key_in (x: M.key) (m : t) : M.In x m -> x < new_key m.
Proof.
  intro HIn; unfold new_key.
  apply max_key_in in HIn as Hle.
  destruct (M.is_empty m) eqn:Hemp; try lia.
  apply is_empty_iff in Hemp.
  exfalso; destruct HIn as [v HMp].
  now apply (Hemp x v).
Qed.

Lemma new_key_Submap (m m' : t) :
  Submap m m' -> new_key m <= new_key m'.
Proof.
  intro Hsub; unfold new_key.
  destruct (M.is_empty m') eqn:Heq.
  - apply is_empty_iff in Heq.
    apply Submap_Empty in Hsub; auto.
    apply is_empty_iff in Hsub.
    now rewrite Hsub.
  - destruct (M.is_empty m) eqn:Heq'; try lia.
    apply le_n_S. 
    now apply max_key_Submap.
Qed.

Lemma new_key_Submap_add (v v': Data.t) (m m' : t) :
  Submap m m' -> Submap m (M.add (S (new_key m')) v (M.add (new_key m') v' m')).
Proof.
  intros Hsub. 
  repeat apply Submap_add_1; auto.
  - intro HIn. 
    apply add_in_iff in HIn as [Heq | HIn]; try lia.
    apply new_key_notin in HIn; auto.
  - apply new_key_notin; auto.
Qed.

#[export] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv max_key_proper 
max_key_diamond max_key_proper_forall : core.

End MapETLVL.