From Coq Require Import Orders Lia RelationPairs Bool.Bool Structures.EqualitiesFacts Lists.List.
From DeBrLevel Require Import LevelInterface Level.
Import ListNotations.


(** * Implementation - Leveled List 

  We use the notation [ET] when elements satisfy [Equality Type] module, [WL] when the embedded type has an equivalent equality to the one from Coq, [FL] when the embbeded type has boolean version of [Wf] and finally [BD] when elements does not contains binders associated to levels.
*)

(** ** Leveled List Implementation - [ET] and [WL] *)
Module IsLvlListETWL (E : IsLvlETWL) <: IsLvlETWL.

(** *** Definitions *)

Definition t := list E.t.

Definition eq := @Logic.eq (list E.t).

Definition shift (lb k: Level.t) (t: t) :=  map (E.shift lb k) t.

Definition Wf (lb: Level.t) (t: t) := forall x, In x t -> E.Wf lb x.

(** *** Properties *)

(** **** [eq] properties *)

#[export] Instance eq_refl : Reflexive eq := _. 

#[export] Instance eq_sym  : Symmetric eq := _.

#[export] Instance eq_trans : Transitive eq := _.

#[export] Instance eq_equiv : Equivalence eq := _.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. now unfold eq. Qed.

(** **** [shift] properties *)

Section shift_props.

Variable lb k k' k'' : Level.t.
Variable t t' : t.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff : eq t t' <-> eq (shift lb k t) (shift lb k t').
Proof.
  split; unfold eq in *.
  - intros; now subst.
  - revert t'; induction t.
    -- unfold shift; intros; simpl in *.
       destruct t'; auto. simpl in *.
       inversion H.
    -- intros; destruct t'; simpl in *.
       + inversion H.
       + inversion H. f_equal.
         ++ apply E.eq_leibniz. 
            rewrite E.shift_eq_iff; now rewrite H1.
         ++ now apply IHt0.
Qed.

Lemma shift_zero_refl : eq (shift lb 0 t) t.
Proof.
  unfold eq; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_zero_refl. 
Qed.

Lemma shift_trans : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof. 
  unfold eq; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_trans. 
Qed.

Lemma shift_permute : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof. 
  unfold eq; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_permute. 
Qed.

Lemma shift_unfold : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof. 
  unfold eq; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  k <= k' -> k' <= k'' -> 
  eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  unfold eq; intros Hle Hle'; induction t; simpl; f_equal; auto.
  apply E.eq_leibniz; now apply E.shift_unfold_1. 
Qed.

Lemma shift_nil: eq (shift lb k nil) nil.
Proof. unfold eq, shift; now simpl. Qed.

Lemma shift_cons v: 
  eq (shift lb k (v :: t)) ((E.shift lb k v) :: (shift lb k t)).
Proof. unfold eq, shift; now simpl. Qed.

Lemma shift_app: 
  eq (shift lb k (t ++ t')) ((shift lb k t) ++ (shift lb k t')).
Proof.
  unfold eq, shift. apply map_app.
Qed.

Lemma shift_in v: In v t <-> In (E.shift lb k v) (shift lb k t).
Proof.
  split. clear k' k'' t'.
  - revert v. induction t; intros; simpl in *; auto.
    destruct H; subst; auto.
  - revert v. induction t; intros; simpl in *; auto.
    destruct H; subst; auto.
    left. apply E.eq_leibniz. 
    rewrite E.shift_eq_iff. now rewrite H.
Qed.

Lemma shift_in_e v:
  In v (shift lb k t) -> 
  exists v', v = (E.shift lb k v') /\ In (E.shift lb k v') (shift lb k t).
Proof.
  clear k' k'' t'. revert v; induction t; simpl; intros.
  - inversion H.
  - destruct H; subst.
    -- exists a. split; auto.
    -- apply IHt0 in H as [v' [Heq HIn]]; subst.
       exists v'; split; auto.
Qed.

Lemma shift_notin v : ~ In v t <-> ~ In (E.shift lb k v) (shift lb k t).
Proof.
  intros; split; unfold not; intros; apply H.
  - now rewrite <- shift_in in H0.
  - now rewrite <- shift_in.
Qed.

End shift_props.

(** **** [Wf] properties *)

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf := _.

Lemma Wf_unfold (lb: Lvl.t) (s: t) : Wf lb s <-> (forall v, List.In v s -> E.Wf lb v).
Proof. now unfold Wf. Qed.

Lemma Wf_nil (lb: Lvl.t) : Wf lb [].
Proof. unfold Wf; intros x c. inversion c. Qed.

Lemma Wf_cons (lb: Lvl.t) (v: E.t) (s: t) : Wf lb (v :: s) <-> E.Wf lb v /\ Wf lb s.
Proof.
  unfold Wf; split; intros.
  - split.
    -- apply H. simpl; now left.
    -- intros x HIn.
       apply H. simpl; now right.
  - destruct H,H0; subst; auto.
Qed.

Lemma Wf_app (lb: Lvl.t) (s s': t) : Wf lb (s ++ s') <-> Wf lb s /\ Wf lb s'.
Proof.
  unfold Wf; split; intros.
  - split; intros.
    -- apply H.
       apply in_or_app; now left.
    -- apply H.
       apply in_or_app; now right.
  - apply in_app_or in H0.
    destruct H, H0; auto.
Qed.

Lemma Wf_in (lb: Lvl.t) (v: E.t) (t: t) : Wf lb t -> In v t -> E.Wf lb v.
Proof. unfold Wf; intros; now apply H. Qed.

Lemma Wf_weakening (k k': Lvl.t) (t: t) : (k <= k') -> Wf k t -> Wf k' t.
Proof.
  intros. unfold Wf in *. intros.
  apply H0 in H1. 
  eapply E.Wf_weakening; eauto.
Qed.

Lemma shift_preserves_wf (k k': Lvl.t) (t: t) : Wf k t -> Wf (k + k') (shift k k' t).
Proof.
  induction t; simpl; intros.
  - apply Wf_nil.
  - rewrite Wf_cons in *; 
    destruct H; split; auto.
    now apply E.shift_preserves_wf.
Qed.

Lemma shift_preserves_wf_1 (lb k k': Lvl.t) (t: t) : 
  Wf k t -> Wf (k + k') (shift lb k' t).
Proof.
  induction t; simpl; intros.
  - apply Wf_nil.
  - rewrite Wf_cons in *; 
    destruct H; split; auto.
    now apply E.shift_preserves_wf_1.
Qed.

Lemma shift_preserves_wf_gen (lb lb' k k': Lvl.t) (t: t) :  
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' ->
  k' - k = lb' - lb ->  Wf lb t -> Wf lb' (shift k (k' - k) t).
Proof.
  intros Hle Hle1 Hle2 Hle3 Heq.
  induction t; simpl; intros.
  - apply Wf_nil.
  - rewrite Wf_cons in *; 
    destruct H; split; auto.
    now apply E.shift_preserves_wf_gen with lb.
Qed.

Lemma shift_preserves_wf_2 (lb lb': Lvl.t) (t: t) : 
  lb <= lb' -> Wf lb t -> Wf lb' (shift lb (lb' - lb) t).
Proof.  intros. eapply shift_preserves_wf_gen; eauto. Qed.

Lemma shift_preserves_wf_zero (k: Lvl.t) (t: t) : Wf k t -> Wf k (shift k 0 t).
Proof. 
  intros; replace k with (k + 0); try lia; 
  now apply shift_preserves_wf_1.
Qed.

End IsLvlListETWL.


(** ---- *)


(** ** Leveled List Implementation - [ET], [FL] and [WL] *)
Module IsLvlFullListETWL (E : IsLvlFullETWL) <: IsLvlFullETWL.

Include IsLvlListETWL E.

(** *** Definitions *)

Definition is_wf (lb: Level.t) (t: t) := List.forallb (E.is_wf lb) t.

(** *** Properties *)
Section props.

Variable k : Level.t.
Variable t : t.

Lemma is_wf_eq : Proper (Logic.eq ==> eq ==> Logic.eq) is_wf.
Proof.
  repeat red; intros. unfold eq in *; now subst.
Qed.

Lemma Wf_is_wf_true : Wf k t <-> is_wf k t = true.
Proof. 
  split; intros; unfold Wf,is_wf in *.
  - rewrite List.forallb_forall; intros.
    rewrite <- E.Wf_is_wf_true.
    now apply H.
  - rewrite List.forallb_forall in H; intros.
    rewrite E.Wf_is_wf_true.
    now apply H.
Qed.

Lemma notWf_is_wf_false : ~ Wf k t <-> is_wf k t = false.
Proof.
  intros; rewrite <- not_true_iff_false; split; intros; intro.
  - apply H; now rewrite Wf_is_wf_true. 
  - apply H; now rewrite <- Wf_is_wf_true.
Qed. 

End props.
  
End IsLvlFullListETWL.


(** ---- *)


(** ** Leveled List Implementation - [ET], [BD] and [WL] *)
Module IsBdlLvlListETWL (E : IsBdlLvlETWL) <: IsBdlLvlETWL.

Include IsLvlListETWL E.

Lemma shift_wf_refl (lb k: Lvl.t) (t: t) : Wf lb t -> eq (shift lb k t) t.
Proof.
  induction t; simpl; intro Hwf.
  - reflexivity.
  - apply Wf_cons in Hwf as [HWfa Hwf].
    rewrite IHt; auto.
    unfold eq; f_equal.
    apply E.eq_leibniz.
    rewrite E.shift_wf_refl; auto; reflexivity.
Qed.

End IsBdlLvlListETWL.


(** ---- *)


(** ** Leveled List Implementation - [ET], [FL] and [WL] *)
Module IsBdlLvlFullListETWL (E : IsBdlLvlFullETWL) <: IsBdlLvlFullET.

Include IsLvlFullListETWL E.

Lemma shift_wf_refl (lb k: Lvl.t) (t: t) : Wf lb t -> eq (shift lb k t) t.
Proof.
  induction t; simpl; intro Hwf.
  - reflexivity.
  - apply Wf_cons in Hwf as [HWfa Hwf].
    rewrite IHt; auto.
    unfold eq; f_equal.
    apply E.eq_leibniz.
    rewrite E.shift_wf_refl; auto; reflexivity.
Qed.
  
End IsBdlLvlFullListETWL.