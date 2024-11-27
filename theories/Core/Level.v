From Coq Require Import Structures.OrdersEx Classes.Morphisms Arith.PeanoNat Lia.
From DeBrLevel Require Import LevelInterface.


(** * Implementation - Level 

  A level itself only require to be ordered. We require also a ground value and
  classic arithmetic operators on it. Thus, we define a level as a [Nat].
*)
Module Level <: IsBdlLvlFullOTWL.

Include Lvl.

(** *** Definitions *)

Definition shift (m: Lvl.t) (k: Lvl.t) (t: t) := if (m <=? t)%nat then t + k else t.

Definition Wf (m: Lvl.t) (t: t) := Lvl.lt t m.

Definition is_wf (m: Lvl.t) (t: t) := Lvl.ltb t m.

(** *** Properties *)

(** **** [lt] and [eq] properties *)
Section lt_eq.

Variable t1 t2 : t.

Lemma eq_leibniz : eq t1 t2 -> t1 = t2. 
Proof. auto. Qed.

Lemma lt_not_eq : lt t1 t2 -> ~ eq t1 t2. 
Proof. intros; lia. Qed.

Lemma gt_neq_nlt : ~ eq t1 t2 -> ~ lt t1 t2 -> lt t2 t1.
Proof. intros; lia. Qed.

End lt_eq.

(** **** [shift] properties *)
Section shift.

Variable m n k p : Lvl.t.
Variable t t1 : t.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_neq :
  t <> t1 -> (shift m k t) <> (shift m k t1).
Proof.
  intro Hneq; unfold shift.
  destruct (Lvl.leb_spec0 m t); destruct (Lvl.leb_spec0 m t1); lia.
Qed.

Lemma shift_neq_1 :
  (shift m k t) <> (shift m k t1) -> t <> t1.
Proof.
  intros Hneq Heq; subst.
  now apply Hneq.
Qed.

Lemma shift_eq_iff :
  t = t1 <-> (shift m k t) = (shift m k t1).
Proof.
  split; intro Heq.
  - subst; reflexivity.
  - unfold shift in Heq.
    destruct (Lvl.leb_spec0 m t); destruct (Lvl.leb_spec0 m t1); lia.
Qed.

Lemma shift_zero_refl : shift m 0 t = t.
Proof. 
  unfold shift; destruct (Lvl.leb_spec0 m t); auto.
Qed.

Lemma shift_wf_refl : Wf m t -> shift m k t = t.
Proof.
  unfold shift, Wf; intro Hlt. 
  destruct (Lvl.leb_spec0 m t); auto; lia.
Qed.

Lemma shift_trans : shift m k (shift m p t) = shift m (k + p) t.
Proof.
  unfold shift; destruct (Lvl.leb_spec0 m t) as [Hle | Hgt]; auto.
  - assert (Hle': (m <= (t + p))%nat) by lia.
    rewrite <- Lvl.leb_le in Hle'; rewrite Hle'; lia.
  - rewrite <- Lvl.leb_nle in Hgt; rewrite Hgt; reflexivity. 
Qed.

Lemma shift_permute :
  shift m k (shift m p t) = shift m p (shift m k t).
Proof.
  unfold shift; destruct (m <=? t) eqn:Hle.
  - rewrite Lvl.leb_le in Hle. 
    destruct (Lvl.leb_spec0 m (t + p));
    destruct (Lvl.leb_spec0 m (t + k)); lia.
  - now rewrite Hle.
Qed.

Lemma shift_permute_1 : 
  (shift m k (shift m p t)) = (shift (m + k) p (shift m k t)).
Proof.
  unfold shift; destruct (m <=? t) eqn:Hle.
  - assert (Hle': m + k <=? t + k = true) by (rewrite Lvl.leb_le in *; lia).
    assert (Hle'': m <=? t + p = true) by (rewrite Lvl.leb_le in *; lia).
    rewrite Hle', Hle''; lia.
  - rewrite Hle; rewrite Lvl.leb_nle in Hle.
    destruct (m + k <=? t) eqn:Hle'; auto.
    rewrite Lvl.leb_le in Hle'; lia.
Qed.

Lemma shift_permute_2 : 
  m <= n -> (shift m k (shift n p t)) = (shift (n + k) p (shift m k t)).
Proof.
  unfold shift. intros; destruct (Lvl.leb_spec0 n t); destruct (Lvl.leb_spec0 m t).
  - replace (m <=? t + p) with true; replace (n + k <=? t + k) with true; try lia;
    symmetry; rewrite Lvl.leb_le; lia.
  - replace (m <=? t + p) with false; replace (n + k <=? t) with true; try reflexivity;
    symmetry; try (rewrite Lvl.leb_le; lia); rewrite Lvl.leb_nle; lia.
  - replace (n + k <=? t + k) with false; try reflexivity; symmetry; 
    rewrite Lvl.leb_nle; lia.
  - replace (n + k <=? t) with false; try reflexivity; symmetry; rewrite Lvl.leb_nle; lia.
Qed.

Lemma shift_unfold : (shift m (k + p) t) = (shift (m + k) p (shift m k t)). 
Proof.
  unfold shift; destruct (m <=? t) eqn:Hleb.
  - replace (m + k <=? t + k) with true; try lia. symmetry; rewrite Lvl.leb_le in *; lia.
  - apply Lvl.leb_nle in Hleb. destruct (Lvl.leb_spec0 (m + k) t); lia.
Qed.

Lemma shift_unfold_1 : forall k k1 k2 r,
  k <= k1 -> k1 <= k2 ->
  (shift k1 (k2 - k1) (shift k  (k1 - k) r)) = shift k (k2 - k) r.
Proof.
  unfold shift; intros; destruct (Lvl.leb_spec0 k0 r).
  -- destruct (Lvl.leb_spec0 k1 (r + (k1 - k0))); lia.
  -- destruct (Lvl.leb_spec0 k1 r); auto; assert (r < k0) by lia; lia.
Qed.

Lemma shift_gt_iff : t > t1 <-> (shift m n t) > (shift m n t1).
Proof.
  unfold shift; split; intro Hgt;
  destruct (leb_spec m t); 
  destruct (leb_spec m t1); lia.
Qed.

Lemma shift_le : t <= (shift m n t).
Proof. unfold shift; destruct (leb_spec m t); lia. Qed.

End shift.

(** **** [Wf] property *)

Lemma Wf_is_wf_true : forall k t, Wf k t <-> is_wf k t = true. 
Proof.
  split; intros; unfold Wf,is_wf in *; now apply Lvl.ltb_lt.
Qed.

Lemma notWf_is_wf_false : forall k t, ~ Wf k t <-> is_wf k t = false.
Proof.
  split; intros; unfold Wf,is_wf in *; now apply Lvl.ltb_nlt.
Qed. 

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf := _.

#[export] Instance is_wf_eq : Proper (Logic.eq ==> eq ==> Logic.eq) is_wf := _.

Lemma Wf_weakening : forall k p t, (k <= p) -> Wf k t -> Wf p t.
Proof. unfold Wf; intros k p t Hleb Hvt; lia. Qed.

(** *** Interaction property between [Wf] and [shift] *)

Lemma shift_preserves_wf : forall k p t, Wf k t -> Wf (k + p) (shift k p t).
Proof.
  unfold Wf,shift; intros k p t Hvt; destruct (Lvl.leb_spec0 k t); try lia.
Qed.

Lemma shift_preserves_wf_1 : forall m k p t, 
  Wf k t -> Wf (k + p) (shift m p t).
Proof.
  unfold Wf,shift; intros m k p t Hvt; destruct (Lvl.leb_spec0 m t); lia.
Qed.

Lemma shift_preserves_wf_gen : forall m n k p t,
  k <= p -> m <= n -> k <= m -> p <= n -> 
  p - k = n - m -> 
  Wf m t -> Wf n (shift k (p - k) t).
Proof.
  intros m n k; revert m n; induction k; simpl; intros.
  - unfold Wf, shift in *. destruct t0; simpl; lia.
  - unfold Wf, shift in *; destruct t0; simpl; try lia.
    destruct m; try lia; destruct p; try lia.
    destruct n; try lia; simpl in *. apply le_S_n in H0,H,H1,H2.
    apply IHk with (t := t0) in H3; auto; try lia.
    destruct (Lvl.leb_spec0 k t0); simpl in *; lia.
Qed.

Lemma shift_preserves_wf_2 : forall m n t,
  m <= n -> Wf m t -> 
  Wf n (shift m (n - m) t).
Proof. intros. eapply shift_preserves_wf_gen; eauto. Qed. 

Lemma shift_preserves_wf_zero : forall k t, Wf k t -> Wf k (shift k 0 t).
Proof. 
  intros; replace k with (k + 0); try lia;
  now apply shift_preserves_wf_1. 
Qed. 

End Level.