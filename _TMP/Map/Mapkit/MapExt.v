From Coq Require Import MSets Lia Arith.PeanoNat Classical_Prop Classes.RelationClasses.
From MMaps Require Import MMaps.
From DeBrLevel Require Import Level MapExtInterface.

Module MapET (Key : OrderedTypeWithLeibniz) (Data : EqualityType) 
                                            (M : Interface.S Key) <:  MapInterface Key Data M.

Module OP := Facts.OrdProperties Key M.
Import OP.P.

(** ** Definition *)

Definition t : Type := M.t Data.t.
Definition eq := @M.Equal Data.t.

Definition Submap (m m' : t) :=
  (forall y, M.In y m -> M.In y m') /\
  (forall k e e', M.MapsTo k e m -> M.MapsTo k e' m' -> e = e').

(** **** ForAll property

  MMaps does not provide a function that check if all elements in the environment satisfy a property [P]. Consequently we define it.
*)
Definition For_all (P : Key.t -> Data.t -> Prop) (m : t) := 
  forall k d, M.find k m = Some d -> P k d.


(** ** [Equivalence] property *)

#[export] Instance eq_equiv : Equivalence eq := _.
#[export] Instance iff_equiv : Equivalence iff := _.
#[export] Instance logic_eq_equiv : forall A, Equivalence (@Logic.eq A) := _.

#[local] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv : core.


(** ** [Empty] property *)

#[export] Instance Empty_eq_iff : Proper (eq ==> iff) Empty.
Proof. do 2 red; intros m m' Heq; now rewrite Heq. Qed.

Lemma Empty_eq_spec (m : t) : Empty m -> m == M.empty.
Proof. intro HEmp; apply eq_empty; now apply is_empty_1. Qed.

Lemma notEmpty_Add_spec (m m' : t) x e : Add x e m m' -> ~ Empty m'.
Proof.
  intro HAdd; intro HEmp.
  unfold Add in *. rewrite HAdd in HEmp.
  apply (HEmp x e).
  now apply add_1.
Qed.

Lemma notEmpty_find_spec (m : t) x e : Empty m -> ~ (M.find x m = Some e).
Proof.
  intro HEmp; intro Hfi.
  apply (HEmp x e).
  now apply find_2.
Qed. 


(** ** [is_empty] property *)

Lemma is_empty_Add_spec (m m' : t) x e : Add x e m m' -> M.is_empty m' = false.
Proof.
  intro HEmp. 
  apply notEmpty_Add_spec in HEmp.
  apply not_true_is_false.
  intro Hemp; apply HEmp.
  now apply is_empty_iff.
Qed.

Lemma is_empty_add_spec (m : t) x e : M.is_empty (M.add x e m) = false.
Proof.
  apply not_true_is_false; intro Hemp.
  apply is_empty_iff in Hemp.
  apply (Hemp x e).
  apply add_mapsto_iff; now left.
Qed.


(** ** [Add] property *)

#[export] Instance Add_eq_iff : forall e,
  Proper (Key.eq ==> eq ==> eq ==> iff) (fun (k : Key.t) => Add k e).
Proof.
  do 5 red. intros e k k' HKeq m m' Heqm n n' Heqn.
  split; unfold Add; intro HAdd.
  - now rewrite HKeq in *; rewrite <- Heqm; rewrite <- Heqn.
  - now rewrite <- HKeq in *; rewrite Heqm; rewrite Heqn.
Qed.

(** ** [add] property *)

Lemma add_remove_spec (m : t) x v :
  M.find x m = Some v -> m == (M.add x v (M.remove x m)).
Proof. intro Hfi; rewrite add_remove_1; symmetry; now rewrite add_id. Qed.

Lemma add_shadow (m : t) x v v' : 
  eq (M.add x v (M.add x v' m)) (M.add x v m). 
Proof.
  intro y; destruct (Key.eq_dec x y).
  - rewrite e.
    repeat rewrite add_eq_o; auto; reflexivity.
  - repeat rewrite add_neq_o; auto.
Qed.


(** ** [Submap] property *)

Lemma Submap_Empty_bot (m m' : t) : Empty m -> Submap m m'.
Proof.
  intro HEmp; apply Empty_eq_spec in HEmp.
  unfold Submap in *; split.
  - intros y HIn; rewrite HEmp in HIn.
    now apply not_in_empty in HIn. 
  - intros k e e' HMp; rewrite HEmp in HMp.
    now apply empty_mapsto_iff in HMp.
Qed.

Lemma Submap_Empty_spec (m m' : t) :
  Submap m m' -> Empty m' -> Empty m.
Proof.
  intros [HIn _] HEmp k e HM.
  assert (HInm : M.In k m) by now exists e.
  apply HIn in HInm as [e' HM'].
  now apply (HEmp k e').
Qed.

Lemma Submap_empty_bot (m : t) : Submap M.empty m.
Proof.
  split.
  - intros y HIn.
    apply empty_in_iff in HIn; contradiction.
  - intros k e e' HMp HMp'. 
    apply empty_mapsto_iff in HMp; contradiction.
Qed.

Lemma Submap_Add_spec (m m' m1 : t) x v :
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

Lemma Submap_Add_in_spec (m m' m1 : t) x v :
  Submap m' m1 -> ~ M.In x m -> Add x v m m' -> M.In x m1.
Proof.
  unfold Add; intros [HIn _] HnIn Heq.
  apply HIn; rewrite Heq.
  apply add_in_iff; now left.
Qed.

Lemma Submap_Add_find_spec (m m' m1 : t) x v :
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

Lemma Submap_Add_spec_1 (m m' m1 : t) x v :
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

Lemma Submap_add_spec (m m' : t) x v :
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

Lemma Submap_add_spec_1 (m m' : t) x v :
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

Lemma Submap_in_spec (m m' : t) x : Submap m m' -> M.In x m -> M.In x m'.
Proof. intros [HIn _]; auto. Qed.

Lemma Submap_notin_spec (m m' : t) x : Submap m m' -> ~M.In x m' -> ~M.In x m.
Proof. intros [HIn _] HIn' HIn1; apply HIn'; auto. Qed.

Lemma Submap_find_spec (m m' : t) x v :
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
    -- rewrite add_neq_o in *; auto; eapply Submap_Add_spec in Hsub; eauto.
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


(** ** [For_all] property *)
Section For_all.


#[export] Instance For_all_proper (P : Key.t -> Data.t -> Prop) : 
  Proper (eq ==> iff) (For_all P).
Proof.
  intros o o' Heqo; unfold For_all; split; intros HFa k d Hfi.
  - rewrite <- Heqo in Hfi; auto.
  - rewrite Heqo in Hfi; auto.
Qed.

Lemma For_all_empty_spec (P : Key.t -> Data.t -> Prop) : For_all P M.empty.
Proof. 
  intros k d Hfi.
  apply find_2 in Hfi.
  apply empty_mapsto_iff in Hfi; contradiction.
Qed.

Lemma For_all_Empty_spec (o : t) (P : Key.t -> Data.t -> Prop) :
  Empty o -> For_all P o.
Proof.
  intros HEmp k d Hfi; apply Empty_eq_spec in HEmp.
  rewrite HEmp in Hfi.
  apply find_2 in Hfi.
  apply empty_mapsto_iff in Hfi; contradiction.
Qed.

Lemma For_all_add_spec 
  (o : t) (k : Key.t) (d : Data.t) (P : Key.t -> Data.t -> Prop) :
 P k d /\ For_all P o -> For_all P (M.add k d o).
Proof.
  intros [HP HFa] k' d' Hfi.
  destruct (Key.eq_dec k k') as [Heq | Hneq]; subst.
  - rewrite add_eq_o in Hfi; auto.
    inversion Hfi; subst.
    apply Key.eq_leibniz in Heq; now subst.
  - rewrite add_neq_o in Hfi; auto.
Qed.

Lemma For_all_add_notin_spec 
  (o : t) (k : Key.t) (d : Data.t) (P : Key.t -> Data.t -> Prop) :
 ~ M.In k o ->
 ((P k d /\ For_all P o) <-> For_all P (M.add k d o)).
Proof.
  intro HnIn; split.
  - apply For_all_add_spec.
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

End For_all.

End MapET.













Module MapETLVL (Data : EqualityType) (M : Interface.S Level) <:  MapLVLInterface Data M.

Include MapET Level Data M.
Import OP.P.

(** ** Definition *)

Definition max_key (m : t) : nat :=
  foldkeys Nat.max m 0.

Definition new_key (m : t) : nat := 
  if M.is_empty m then 0 else S (max_key m).

(** ** [max] property *)

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

Lemma max_key_Empty_spec (m : t) : Empty m -> max_key m = 0.
Proof. intro HEmp; unfold max_key; rewrite foldkeys_Empty; auto. Qed.

Lemma max_key_empty_spec : max_key M.empty = 0.
Proof. unfold max_key; rewrite foldkeys_Empty; auto; apply empty_1. Qed.

Lemma max_key_Add_spec (m m' : t) x v :
  ~M.In x m -> Add x v m m' ->
  (max_key m' = x /\ max_key m <= x) \/ (max_key m' = max_key m /\ max_key m > x).
Proof.
  intros HnIn HAdd; unfold max_key. 
  rewrite foldkeys_Add; eauto.
  destruct (Nat.leb_spec0 (foldkeys Nat.max m 0) x).
  - apply max_l in l as l'. left; rewrite l' in *; split; auto.
  - rewrite max_r; try lia.
Qed.

Lemma max_key_Add_ge_spec (m m' : t) x v :
  ~M.In x m -> Add x v m m' ->  max_key m <= x -> max_key m' = x.
Proof.
  intros HnIn HAdd Hmax; unfold max_key.
  rewrite foldkeys_Add; eauto.
  now apply max_l.
Qed.

Lemma max_key_Add_lt_spec (m m' : t) x v :
  ~M.In x m -> Add x v m m' ->  max_key m > x -> max_key m' = max_key m.
Proof.
  intros HnIn HAdd Hmax; unfold max_key in *.
  rewrite foldkeys_Add; eauto.
  apply max_r; lia.
Qed.

Lemma max_key_add_spec (m : t) x v :
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

Lemma max_key_add_ge_spec (m : t) x v :
  ~M.In x m -> max_key m <= x -> max_key (M.add x v m) = x.
Proof.
  intros HnIn Hle; 
  apply max_key_add_spec with (v := v) in HnIn as [[Heq Hle'] | [Heq Hgt]]; auto; lia.
Qed.

Lemma max_key_add_lt_spec (m : t) x v :
  ~M.In x m -> max_key m > x -> max_key (M.add x v m) = max_key m.
Proof.
  intros HnIn Hle; 
  apply max_key_add_spec with (v := v) in HnIn as [[Heq Hle'] | [Heq Hgt]]; auto; lia.
Qed.

Lemma max_key_add_spec_1 (m m' : t) x v v':
  ~M.In x m -> ~M.In x m' ->
  max_key m = max_key m' -> max_key (M.add x v m) = max_key (M.add x v' m').
Proof.
  intros HnIn HnIn'. 
  apply max_key_add_spec with (v := v) in HnIn as HI. 
  apply max_key_add_spec with (v := v') in HnIn' as HI'.
  destruct HI as [[Heq1 Hleb1] | [Heq1 Hgt1]];
  destruct HI' as [[Heq2 Hleb2] | [Heq2 Hgt2]]; subst; try lia.
Qed.

Lemma max_key_ub_spec (m : t) x : x > max_key m -> for_all_dom (fun y => y <? x) m = true.
Proof.
  revert x; induction m using map_induction; intros y Hgt.
  - unfold for_all_dom; apply for_all_iff; auto.
    intros k e HMp; exfalso.
    apply (H k e HMp).
  - unfold for_all_dom; apply for_all_iff; auto.
    intros k e' HMp. 
    apply max_key_Add_spec in H0 as HI; auto.
    destruct HI as [[Heq Hle] | [Heq Hgt1]]; 
    subst; apply find_1 in HMp; 
    rewrite H0 in HMp; rewrite add_o in HMp.
    -- destruct (Level.eq_dec (max_key m2) k); subst.
       + apply Nat.ltb_lt; lia.
       + apply find_2 in HMp. 
         assert (y > max_key m1) by lia.
         apply IHm1 in H1. 
         unfold for_all_dom in *; rewrite for_all_iff in H1; auto.
         apply (H1 k e' HMp).
    -- destruct (Level.eq_dec x k); subst.
       + inversion HMp; subst; clear HMp. 
         rewrite Heq in *; clear Heq.
         apply Nat.ltb_lt; lia.
       + apply find_2 in HMp. rewrite Heq in *. apply IHm1 in Hgt.
         unfold for_all_dom in *; rewrite for_all_iff in *; auto. 
         apply (Hgt k e' HMp).
Qed.

Lemma max_key_notin_spec (m : t) x : x > max_key m -> ~ M.In x m.
Proof.
  intros Hgt [v HMp]. 
  apply max_key_ub_spec in Hgt as Hfa. 
  unfold for_all_dom in *; rewrite for_all_iff in *; auto.
  apply Hfa in HMp.
  apply Nat.ltb_lt in HMp; lia.
Qed.

Lemma max_key_add_max_spec (m : t) v :
  max_key (M.add (S (max_key m)) v m) = S (max_key m).
Proof.
  rewrite max_key_add_ge_spec; auto.
  apply max_key_notin_spec; lia.
Qed.

Lemma max_key_in_spec (m : t) (x : M.key) :
  M.In x m -> x <= (max_key m).
Proof.
  revert x; induction m using map_induction; intros k Hin.
  - exfalso; destruct Hin as [y Hin]; now apply (H k y).
  - unfold Add in *; rewrite H0 in *; clear H0.
    apply add_in_iff in Hin as [Heq | HIn]; subst.
    -- destruct (Nat.leb_spec0 (max_key m1) k).
       + rewrite max_key_add_ge_spec; auto; lia.
       + rewrite max_key_add_lt_spec; auto; lia.
    -- apply IHm1 in HIn.
       destruct (Nat.leb_spec0 (max_key m1) x).
       + rewrite max_key_add_ge_spec; auto; lia.
       + rewrite max_key_add_lt_spec; auto; lia.
Qed.

Lemma max_key_Submap_spec (m m' : t) : Submap m m' -> max_key m <= max_key m'.
Proof.
  revert m'; induction m using map_induction; intros m' Hsub.
  - rewrite max_key_Empty_spec; auto; lia.
  - apply max_key_Add_spec in H0 as HI; auto. 
    destruct HI as [[Heq Hle] | [Heq Hgt]]; subst;
    eapply Submap_Add_spec in Hsub as Hsub'; eauto.
    -- eapply Submap_Add_in_spec in H0; eauto.
       apply IHm1 in Hsub'.
       destruct (Nat.leb_spec0 (max_key m2) (max_key m')); try lia.
       assert ((max_key m2) > (max_key m')) by lia. clear n. 
       apply max_key_notin_spec in H1.
       contradiction.
    -- rewrite Heq in *.
       now apply IHm1. 
Qed.

Lemma max_key_add_in_spec (m: t) (x : M.key) v :
  M.In x m -> (max_key (M.add x v m)) = (max_key m).
Proof.
  intro HIn. apply Eqdom_in_add with (e := v) in HIn.
  unfold max_key. rewrite foldkeys_Proper; eauto. now symmetry.
Qed.
  
(** ** [new] property *)

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

Lemma new_key_Empty_spec (m : t) : Empty m -> new_key m = 0.
Proof.
  intro HEmp; unfold new_key; apply is_empty_1 in HEmp; now rewrite HEmp.
Qed.

Lemma new_key_empty_spec : new_key M.empty = 0.
Proof.
  assert (@Empty Data.t M.empty) by apply empty_1.
  intros; unfold new_key; apply is_empty_1 in H; now rewrite H.
Qed.

Lemma new_key_geq_max_key (m : t) : new_key m >= max_key m.
Proof.
  rewrite new_key_unfold.
  destruct (M.is_empty m) eqn:HEmp; try lia.
  apply is_empty_2 in HEmp; rewrite max_key_Empty_spec; auto.
Qed. 

Lemma new_key_add_spec (m : t) x v :
  ~M.In x m -> (new_key (M.add x v m) = S x /\ new_key m <= S x) \/ 
               (new_key (M.add x v m) = new_key m /\ new_key m > S x).
Proof.
  intro HnIn; unfold new_key. rewrite is_empty_add_spec.
  apply max_key_add_spec with (v := v) in HnIn as [[Heq Hle] | [Heq Hgt]].
  - left; split; try now f_equal.
    destruct (M.is_empty m); try lia.
  - right.
    destruct (M.is_empty m) eqn:Heq1.
    -- exfalso.
       rewrite max_key_Empty_spec in Hgt; try lia.
       now apply is_empty_iff.
    -- split; try now f_equal; lia.
Qed.

Lemma new_key_add_lt_spec (m : t) x v :
  ~M.In x m -> new_key m > S x -> new_key (M.add x v m) = new_key m.
Proof.
  intros HnIn Hle; 
  apply new_key_add_spec with (v := v) in HnIn as [[Heq Hle'] | [Heq Hgt]]; auto; lia.
Qed.

Lemma new_key_add_ge_spec (m : t) x v :
  ~M.In x m -> new_key m <= S x -> new_key (M.add x v m) = S x.
Proof.
  intros HnIn Hle; 
  apply new_key_add_spec with (v := v) in HnIn as [[Heq Hle'] | [Heq Hgt]]; auto; lia.
Qed.

Lemma new_key_add_in_spec (m: t) (x : M.key) v :
  M.In x m -> (new_key (M.add x v m)) = (new_key m).
Proof.
  intro HIn; unfold new_key.
  rewrite is_empty_add_spec.
  destruct (M.is_empty m) eqn:Heq.
  - apply is_empty_2 in Heq; exfalso.
    destruct HIn as [k HMp]. now apply (Heq x k).
  - now f_equal; apply max_key_add_in_spec.
Qed.

Lemma new_key_Add_spec (m m' : t) x v :
  ~M.In x m -> Add x v m m' ->
    (new_key m' = S x /\ new_key m <= S x) \/ (new_key m' = new_key m /\ new_key m > S x).
Proof.
  intros HnIn HAdd. 
  unfold Add in HAdd; rewrite HAdd.
  now apply new_key_add_spec.
Qed. 

Lemma  new_key_Add_ge_spec (m m' : t) x v :
  ~M.In x m -> Add x v m m' ->  new_key m <= S x -> new_key m' = S x.
Proof. 
  intros HnIn HAdd. 
  unfold Add in HAdd; rewrite HAdd.
  now apply new_key_add_ge_spec.
Qed.

Lemma new_key_Add_lt_spec (m m' : t) x v :
  ~M.In x m -> Add x v m m' ->  new_key m > S x -> new_key m' = new_key m.
Proof. 
  intros HnIn HAdd. 
  unfold Add in HAdd; rewrite HAdd.
  now apply new_key_add_lt_spec.
Qed.

Lemma new_key_add_new_key_spec (m : t) v :
  new_key (M.add (new_key m) v m) = S (new_key m).
Proof.
  unfold new_key.
  rewrite is_empty_add_spec.
  destruct (M.is_empty m) eqn:Hemp.
  - f_equal.
    apply max_key_add_ge_spec.
    -- intros [v1 HMp].
       apply is_empty_iff in Hemp.
       now apply (Hemp 0 v1).
    -- apply is_empty_iff in Hemp. 
       now rewrite max_key_Empty_spec.
  - f_equal. now rewrite max_key_add_max_spec. 
Qed.

Lemma new_key_notin_spec (m : t) x : x >= new_key m -> ~ M.In x m.
Proof.
  unfold new_key; intro ge.
  destruct (M.is_empty m) eqn:Heq.
  - intro HIn. 
    apply is_empty_iff in Heq.
    destruct HIn as [v HMp].
    now apply (Heq x v).
  - apply max_key_notin_spec; lia.
Qed.

Lemma new_key_in_spec (m : t) x : M.In x m -> x < new_key m.
Proof.
  intro HIn; unfold new_key.
  apply max_key_in_spec in HIn as Hle.
  destruct (M.is_empty m) eqn:Hemp; try lia.
  apply is_empty_iff in Hemp.
  exfalso; destruct HIn as [v HMp].
  now apply (Hemp x v).
Qed.

Lemma new_key_Submap_spec (m m' : t) :
  Submap m m' -> new_key m <= new_key m'.
Proof.
  intro Hsub; unfold new_key.
  destruct (M.is_empty m') eqn:Heq.
  - apply is_empty_iff in Heq.
    apply Submap_Empty_spec in Hsub; auto.
    apply is_empty_iff in Hsub.
    now rewrite Hsub.
  - destruct (M.is_empty m) eqn:Heq'; try lia.
    apply le_n_S. 
    now apply max_key_Submap_spec.
Qed.

Lemma new_key_Submap_add_spec (m m' : t) v v' :
  Submap m m' -> Submap m (M.add (S (new_key m')) v (M.add (new_key m') v' m')).
Proof.
  intros Hsub. 
  repeat apply Submap_add_spec_1; auto.
  - intro HIn. 
    apply add_in_iff in HIn as [Heq | HIn]; try lia.
    apply new_key_notin_spec in HIn; auto.
  - apply new_key_notin_spec; auto.
Qed.

#[export] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv max_key_proper 
max_key_diamond max_key_proper_forall : core.

End MapETLVL.