From Coq Require Import Orders Lia RelationPairs Bool.Bool Structures.EqualitiesFacts.
From DeBrLevel Require Import LevelInterface Level.

(** * Implementation - Pair 

  Implementation of leveled elements embedded in a pair type. We use the notation [ET] when elements satisfy [Equality Type] module, [OT] when elements satisfy [Ordered Type] module, [WL] when the embedded type has an equivalent equality to the one from Coq, [FL] when the embbeded type has boolean version of [Wf] and finally [BD] when elements does not contains binders associated to levels.
*)

(** ** Leveled Pair Implementation - [ET] *)
Module IsLvlPairET (O1 : IsLvlET) (O2 : IsLvlET) <: IsLvlET.

(** *** Definitions *)

Definition t := (O1.t * O2.t)%type.
Definition eq := (O1.eq * O2.eq)%signature.

Definition shift (m n : Lvl.t) (t : t) := 
  (O1.shift m n (fst t),O2.shift m n (snd t)).

Definition Wf (m : Lvl.t) (t : t) := 
  (O1.Wf m (fst t)) /\ ((O2.Wf m) (snd t)).

(** *** Properties *)

(** **** [eq] properties *)


#[export] Instance eq_refl : Reflexive eq := _. 
#[export] Instance eq_sym  : Symmetric eq := _.
#[export] Instance eq_trans : Transitive eq := _.

#[export] Instance eq_equiv : Equivalence eq := _.


(** **** [shift] properties *)
Section shift.

Variable m n k p : Lvl.t.
Variable t : t.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  clear; intros m' m Heqm n' n Heqn t t' Heq; subst.
  destruct t as [ft st]; destruct t' as [ft' st'].
  destruct Heq as [Hfeq Hseq].
  unfold eq, shift, RelationPairs.RelCompFun in *; simpl in *.
  split; red; simpl.
  - now apply O1.shift_eq.
  - now apply O2.shift_eq.
Qed.

Lemma shift_eq_iff : forall m n t t1, 
  eq t t1 <-> eq (shift m n t) (shift m n t1).
Proof.
  split; intro Heq; destruct t0,t1,Heq; split;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  - now apply O1.shift_eq_iff.
  - now apply O2.shift_eq_iff.
  - rewrite O1.shift_eq_iff; eauto.
  - rewrite O2.shift_eq_iff; eauto.
Qed.

Lemma shift_zero_refl : eq (shift m 0 t) t.
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_zero_refl); now apply O2.shift_zero_refl.
Qed.

Lemma shift_trans : eq (shift m n (shift m k t)) (shift m (n + k) t).
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_trans); now apply O2.shift_trans.
Qed.

Lemma shift_permute : eq (shift m n (shift m k t)) (shift m k (shift m n t)).
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_permute); now apply O2.shift_permute.
Qed.

Lemma shift_unfold : eq (shift m (n + k) t) (shift (m + n) k (shift m n t)). 
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_unfold); now apply O2.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  n <= k -> k <= p -> 
  eq (shift k (p - k) (shift n  (k - n) t)) (shift n (p - n) t).
Proof.
  intros Hlt Hlt'; destruct t; unfold eq,shift; simpl; split; 
  unfold RelationPairs.RelCompFun; simpl.
  - now apply O1.shift_unfold_1.
  - now apply O2.shift_unfold_1.
Qed.

End shift.

(** **** [Wf] properties *)

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf.
Proof.
  repeat red; intros; subst; destruct x0,y0,H0.
  unfold RelationPairs.RelCompFun in *; simpl in *.
  split; intros; destruct H1; split; simpl in *;
  try (eapply O1.Wf_iff; eauto; now symmetry);
  eapply O2.Wf_iff; eauto; now symmetry.
Qed.

Lemma Wf_weakening (n k: Lvl.t) (t: t) : 
  (n <= k) -> Wf n t -> Wf k t.
Proof.
  intros Hle Hvt. 
  destruct Hvt,t; split; simpl in *;
  try (eapply O1.Wf_weakening; eauto); 
  eapply O2.Wf_weakening; eauto.
Qed.

Lemma shift_preserves_wf (n k: Lvl.t) (t: t) : 
  Wf n t -> Wf (n + k) (shift n k t).
Proof.
  intros; destruct t,H; split; simpl in *.
  - now apply O1.shift_preserves_wf.
  - now apply O2.shift_preserves_wf.
Qed.

Lemma shift_preserves_wf_1 (m n k: Lvl.t) (t: t) : 
  Wf n t -> Wf (n + k) (shift m k t).
Proof.
  intros; destruct t,H; split; simpl in *.
  - now apply O1.shift_preserves_wf_1.
  - now apply O2.shift_preserves_wf_1.
Qed.

Lemma shift_preserves_wf_gen (m m' n k: Lvl.t) (t: t) :  
  n <= k -> m <= m' -> n <= m -> k <= m' ->
  k - n = m' - m ->  Wf m t -> Wf m' (shift n (k - n) t).
Proof.
  intros; destruct t,H4; split; simpl in *.
  - now apply O1.shift_preserves_wf_gen with m.
  - now apply O2.shift_preserves_wf_gen with m.
Qed.

Lemma shift_preserves_wf_2 (m m': Lvl.t) (t: t) : 
  m <= m' -> Wf m t -> Wf m' (shift m (m' - m) t).
Proof.  intros. eapply shift_preserves_wf_gen; eauto. Qed.

Lemma shift_preserves_wf_zero (n: Lvl.t) (t: t) :
  Wf n t -> Wf n (shift n 0 t).
Proof. 
  intros; replace n with (n + 0); try lia; 
  now apply shift_preserves_wf_1.
Qed.

End IsLvlPairET.


(** ---- *)


(** ** Leveled Pair Implementation - [ET] and [WL] *)
Module IsLvlPairETWL (O1 : IsLvlETWL) (O2 : IsLvlETWL) <: IsLvlETWL.

Include IsLvlPairET O1 O2.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsLvlPairETWL.


(** ---- *)


(** ** Leveled Pair Implementation - [ET] and [FL] *)
Module IsLvlFullPairET (O1 : IsLvlFullET) (O2 : IsLvlFullET) <: IsLvlFullET.

Include IsLvlPairET O1 O2.

(** *** Definition *)
Definition is_wf (m : Lvl.t) (t : t) :=  (O1.is_wf m (fst t)) && ((O2.is_wf m) (snd t)).

(** *** Properties *)
Section is_wf.

Variable n : Lvl.t.
Variable t : t.

#[export] Instance is_wf_eq : Proper (Logic.eq ==> eq ==> Logic.eq) is_wf.
Proof.
  repeat red; intros; destruct x0,y0,H0;
  unfold RelationPairs.RelCompFun,is_wf in *; simpl in *; f_equal.
  - eapply O1.is_wf_eq; eauto.
  - eapply O2.is_wf_eq; eauto.
Qed.

Lemma Wf_is_wf_true : Wf n t <-> is_wf n t = true.
Proof. 
  destruct t; split; unfold is_wf,Wf; simpl;
  rewrite andb_true_iff; intros [H1 H2]; split;
  try (eapply O1.Wf_is_wf_true; eauto);
  eapply O2.Wf_is_wf_true; eauto.
Qed.

Lemma notWf_is_wf_false : ~ Wf n t <-> is_wf n t = false.
Proof.
  intros; rewrite <- not_true_iff_false; split; intros; intro.
  - apply H; now rewrite Wf_is_wf_true. 
  - apply H; now rewrite <- Wf_is_wf_true.
Qed. 

End is_wf.
  
End IsLvlFullPairET.


(** ---- *)


(** ** Leveled Pair Implementation - [ET], [WL] and [FL] *)
Module IsLvlFullPairETWL (O1 : IsLvlFullETWL) (O2 : IsLvlFullETWL) <: IsLvlFullETWL.

Include IsLvlFullPairET O1 O2.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsLvlFullPairETWL.


(** ---- *)


(** ** Leveled Pair Implementation - [ET] and [BD] *)
Module IsBdlLvlPairET (O1 : IsBdlLvlET) (O2 : IsBdlLvlET) <: IsBdlLvlET.

Include IsLvlPairET O1 O2.

Lemma shift_wf_refl (m n: Lvl.t) (t: t) : Wf m t -> eq (shift m n t) t.
Proof.
  intros; destruct t,H; split; unfold RelationPairs.RelCompFun;
  simpl in *; try (now apply O1.shift_wf_refl);
  now apply O2.shift_wf_refl.
Qed.
  
End IsBdlLvlPairET.


(** ---- *)


(** ** Leveled Pair Implementation - [ET], [WL] and [BD] *)
Module IsBdlLvlPairETWL (O1 : IsBdlLvlETWL) (O2 : IsBdlLvlETWL) <: IsBdlLvlETWL.

Include IsBdlLvlPairET O1 O2.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsBdlLvlPairETWL.


(** ---- *)


(** ** Leveled Pair Implementation - [ET], [FL] and [BD] *)
Module IsBdlLvlFullPairET (O1 : IsBdlLvlFullET) (O2 : IsBdlLvlFullET) <: IsBdlLvlFullET.

Include IsLvlFullPairET O1 O2.

Lemma shift_wf_refl (m n: Lvl.t) (t: t) : Wf m t -> eq (shift m n t) t.
Proof.
  intros; destruct t,H; split; unfold RelationPairs.RelCompFun;
  simpl in *; try (now apply O1.shift_wf_refl);
  now apply O2.shift_wf_refl.
Qed.

End IsBdlLvlFullPairET.


(** ---- *)


(** ** Leveled Pair Implementation - [ET], [FL], [WL] and [BD] *)
Module IsBdlLvlFullPairETWL (O1 : IsBdlLvlFullETWL) (O2 : IsBdlLvlFullETWL) <: IsBdlLvlFullETWL.

Include IsBdlLvlFullPairET O1 O2.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsBdlLvlFullPairETWL.


(** ---- *)


(** ** Leveled Pair Implementation - [OT] *)
Module IsLvlPairOT (O1 : IsLvlOT) (O2 : IsLvlOT) <: IsLvlOT.

Include OrdersEx.PairOrderedType O1 O2.

(** *** Definitions *)

Definition shift (m n : Lvl.t) (t : t) := 
  (O1.shift m n (fst t),O2.shift m n (snd t)).

Definition Wf (m : Lvl.t) (t : t) := 
  (O1.Wf m (fst t)) /\ ((O2.Wf m) (snd t)).

(** *** Properties *)

(** **** [shift] properties *)
Section shift.

Variable m n k p : Lvl.t.
Variable t t1 : t.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  repeat red; intros; subst; destruct x1,y1.
  destruct H1; unfold RelationPairs.RelCompFun in *; simpl in *;
  split; try (now apply O1.shift_eq); now apply O2.shift_eq.
Qed.

Lemma shift_eq_iff :
  eq t t1 <-> eq (shift m n t) (shift m n t1).
Proof.
  split; intro Heq; destruct t,t1,Heq; split;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  - now apply O1.shift_eq_iff.
  - now apply O2.shift_eq_iff.
  - rewrite O1.shift_eq_iff; eauto.
  - rewrite O2.shift_eq_iff; eauto.
Qed.

Lemma shift_zero_refl : eq (shift m 0 t) t.
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_zero_refl); now apply O2.shift_zero_refl.
Qed.

Lemma shift_trans : eq (shift m n (shift m k t)) (shift m (n + k) t).
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_trans); now apply O2.shift_trans.
Qed.

Lemma shift_permute : eq (shift m n (shift m k t)) (shift m k (shift m n t)).
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_permute); now apply O2.shift_permute.
Qed.

Lemma shift_unfold : eq (shift m (n + k) t) (shift (m + n) k (shift m n t)). 
Proof. 
  destruct t; split; unfold RelationPairs.RelCompFun; simpl;
  try (apply O1.shift_unfold); now apply O2.shift_unfold.
Qed.

Lemma shift_unfold_1 :
  n <= k -> k <= p -> 
  eq (shift k (p - k) (shift n  (k - n) t)) (shift n (p - n) t).
Proof.
  intros Hlt Hlt'; destruct t; unfold eq,shift; simpl; split; 
  unfold RelationPairs.RelCompFun; simpl.
  - now apply O1.shift_unfold_1.
  - now apply O2.shift_unfold_1.
Qed.

End shift.

(** *** [Wf] properties *)

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf.
Proof.
  repeat red; intros; subst; destruct x0,y0,H0.
  unfold RelationPairs.RelCompFun in *; simpl in *.
  split; intros; destruct H1; split; simpl in *;
  try (eapply O1.Wf_iff; eauto; now symmetry);
  eapply O2.Wf_iff; eauto; now symmetry.
Qed.

Lemma Wf_weakening (n k: Lvl.t) (t: t) : 
  (n <= k) -> Wf n t -> Wf k t.
Proof.
  intros. destruct H0,t; split; simpl in *;
  try (eapply O1.Wf_weakening; eauto); 
  eapply O2.Wf_weakening; eauto.
Qed.

Lemma shift_preserves_wf (n k: Lvl.t) (t: t) : 
  Wf n t -> Wf (n + k) (shift n k t).
Proof.
  intros; destruct t,H; split; simpl in *.
  - now apply O1.shift_preserves_wf.
  - now apply O2.shift_preserves_wf.
Qed.

Lemma shift_preserves_wf_1 (m n k: Lvl.t) (t: t) : 
  Wf n t -> Wf (n + k) (shift m k t).
Proof.
  intros; destruct t,H; split; simpl in *.
  - now apply O1.shift_preserves_wf_1.
  - now apply O2.shift_preserves_wf_1.
Qed.

Lemma shift_preserves_wf_gen (m m' n k: Lvl.t) (t: t) :  
  n <= k -> m <= m' -> n <= m -> k <= m' ->
  k - n = m' - m ->  Wf m t -> Wf m' (shift n (k - n) t).
Proof.
  intros; destruct t,H4; split; simpl in *.
  - now apply O1.shift_preserves_wf_gen with m.
  - now apply O2.shift_preserves_wf_gen with m.
Qed.

Lemma shift_preserves_wf_2 (m m': Lvl.t) (t: t) : 
  m <= m' -> Wf m t -> Wf m' (shift m (m' - m) t).
Proof.  intros. eapply shift_preserves_wf_gen; eauto. Qed.

Lemma shift_preserves_wf_zero (n: Lvl.t) (t: t) :
  Wf n t -> Wf n (shift n 0 t).
Proof. 
  intros; replace n with (n + 0); try lia; 
  now apply shift_preserves_wf_1.
Qed.

End IsLvlPairOT.


(** ---- *)


(** ** Leveled Pair Implementation - [OT] and [WL] *)
Module IsLvlPairOTWL (O1 : IsLvlOTWL) (O2 : IsLvlOTWL) <: IsLvlOTWL.

Include IsLvlPairOT O1 O2.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsLvlPairOTWL.


(** ---- *)


(** ** Leveled Pair Implementation - [OT] and [FL] *)
Module IsLvlFullPairOT (O1 : IsLvlFullOT) (O2 : IsLvlFullOT) <: IsLvlFullOT.

Include IsLvlPairOT O1 O2.

(** *** Definitions *)

Definition is_wf (m : Lvl.t) (t : t) := 
  (O1.is_wf m (fst t)) && ((O2.is_wf m) (snd t)).

(** *** Properties *)
Section is_wf.

Variable n : Lvl.t.
Variable t : t.

Lemma is_wf_eq : Proper (Logic.eq ==> eq ==> Logic.eq) is_wf.
Proof.
  repeat red; intros; destruct x0,y0,H0;
  unfold RelationPairs.RelCompFun,is_wf in *; simpl in *; f_equal.
  - eapply O1.is_wf_eq; eauto.
  - eapply O2.is_wf_eq; eauto.
Qed.

Lemma Wf_is_wf_true : Wf n t <-> is_wf n t = true.
Proof. 
  destruct t; split; unfold is_wf,Wf; simpl;
  rewrite andb_true_iff; intros [H1 H2]; split;
  try (eapply O1.Wf_is_wf_true; eauto);
  eapply O2.Wf_is_wf_true; eauto.
Qed.

Lemma notWf_is_wf_false : ~ Wf n t <-> is_wf n t = false.
Proof.
  intros; rewrite <- not_true_iff_false; split; intros; intro.
  - apply H; now rewrite Wf_is_wf_true. 
  - apply H; now rewrite <- Wf_is_wf_true.
Qed. 

End is_wf.
  
End IsLvlFullPairOT.


(** ---- *)


(** ** Leveled Pair Implementation - [OT], [WL] and [FL] *)
Module IsLvlFullPairOTWL (O1 : IsLvlFullOTWL) (O2 : IsLvlFullOTWL) <: IsLvlFullOTWL.

Include IsLvlFullPairOT O1 O2.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsLvlFullPairOTWL.


(** ---- *)


(** ** Leveled Pair Implementation - [OT] and [BD] *)
Module IsBdlLvlPairOT (O1 : IsBdlLvlOT) (O2 : IsBdlLvlOT) <: IsBdlLvlOT.

Include IsLvlPairOT O1 O2.

Lemma shift_wf_refl (m n: Lvl.t) (t: t) : Wf m t -> eq (shift m n t) t.
Proof.
  intros; destruct t,H; split; unfold RelationPairs.RelCompFun;
  simpl in *; try (now apply O1.shift_wf_refl);
  now apply O2.shift_wf_refl.
Qed.

End IsBdlLvlPairOT.


(** ---- *)


(** ** Leveled Pair Implementation - [OT], [WL] and [BD] *)
Module IsBdlLvlPairOTWL (O1 : IsBdlLvlOTWL) (O2 : IsBdlLvlOTWL) <: IsBdlLvlOTWL.

Include IsBdlLvlPairOT O1 O2.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsBdlLvlPairOTWL.


(** ---- *)


(** ** Leveled Pair Implementation - [OT], [FL] and [BD] *)
Module IsBdlLvlFullPairOT (O1 : IsBdlLvlFullOT) 
                           (O2 : IsBdlLvlFullOT) <: IsBdlLvlFullOT.

Include IsLvlFullPairOT O1 O2.

Lemma shift_wf_refl (m n: Lvl.t) (t: t) : Wf m t -> eq (shift m n t) t.
Proof.
  intros; destruct t,H; split; unfold RelationPairs.RelCompFun;
  simpl in *; try (now apply O1.shift_wf_refl);
  now apply O2.shift_wf_refl.
Qed.
  
End IsBdlLvlFullPairOT.


(** ---- *)


(** ** Leveled Pair Implementation - [OT], [WL], [FL] and [BD] *)
Module IsBdlLvlFullPairOTWL (O1 : IsBdlLvlFullOTWL) 
                            (O2 : IsBdlLvlFullOTWL) <: IsBdlLvlFullOTWL.

Include IsBdlLvlFullPairOT O1 O2.

Lemma eq_leibniz (x y: t) : eq x y -> x = y.
Proof. 
  intros; destruct x,y; inversion H;
  unfold RelationPairs.RelCompFun in *; simpl in *.
  apply O1.eq_leibniz in H0; subst.
  apply O2.eq_leibniz in H1; now subst.
Qed.

End IsBdlLvlFullPairOTWL.