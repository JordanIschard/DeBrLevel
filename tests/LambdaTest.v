From DeBrLevel Require Import LevelInterface Level MapLevel Levels OptionLevel.
From Coq Require Import Lia Classes.Equivalence Classes.Morphisms.

(** * Test - Lambda *)

Module Lambda <: IsLvlETWL.

  Module L := Level.

  (** ** Definition and notations *)

  Inductive term : Type := 
  | tm_var : L.t -> term
  | tm_app : term -> term -> term
  | tm_abs : term -> term 
  .

  Definition t := term.
  Definition eq := @Logic.eq t.
  #[export] Instance eq_equiv : Equivalence eq := _.

  (** 
  The [shift] function spreads in all subterms without alterate parameters and
  apply the shift function of the level on each variables. 
  *)
  Fixpoint shift (lb k : Lvl.t) (e : t) := 
  match e with
    | tm_var n => tm_var (L.shift lb k n)
    | tm_app e1 e2 => tm_app (shift lb k e1) (shift lb k e2)
    | tm_abs e1 => tm_abs (shift lb k e1) 
  end  
  .

  (**
  The valid property verifies that all variables are valid. Contrary to the 
  [shift] function, the parameter is incremented when it goes through an
  abstraction. This incrementation is due to the implicit bound variable which
  become accessible in the body of the abstraction.
  *)
  Inductive valid' : Lvl.t -> t -> Prop :=
  | v_var n m : 
                  L.valid n m -> 
            (*-----------------------*)      
                valid' n (tm_var m)


  | v_app n e1 e2 :
                  valid' n e1 -> valid' n e2 -> 
            (*----------------------------------*)
                    valid' n (tm_app e1 e2)

  | v_abs n e1 :
                  valid' (S n) e1 -> 
            (*--------------------------*)
                valid' n (tm_abs e1)
  .

  Definition valid := valid'.

  Definition nat_to_var (n : nat) := tm_var n.

  Declare Custom Entry lc.
  Notation "⟨ e ⟩" := e (e custom lc at level 99).
  Notation "( x )"   := x (in custom lc, x at level 99).
  Notation "x"       := x (in custom lc at level 0, x constr at level 0).
  Notation "{ x }"   := x (in custom lc at level 1, x constr).
  Coercion tm_var : L.t >-> term.
  Coercion nat_to_var : nat >-> term.
  Notation "e1 e2"     := (tm_app e1 e2) (in custom lc at level 70, left associativity).
  Notation "'\,' e"  := (tm_abs e) (in custom lc at level 90, 
                                    e custom lc at level 90, left associativity).
  Notation "'[⧐' lb '~' k ']' t" := (shift lb k t) (at level 30, 
                                                      t custom lc at level 40, right associativity).
  Notation "'[⧐' lb '~' k ']' t" := (shift lb k t) (in custom lc at level 30, 
                                                      t custom lc at level 40, right associativity).
  Infix "⊢" := valid (at level 20, no associativity).

  (** ** Equality *)

  Lemma eq_leibniz : forall e1 e2, eq e1 e2 -> e1 = e2.
  Proof. unfold eq. intros e1 e2 Heq. assumption. Qed.

  (** ** Shift *)
  Section shift.

  Variable lb lb' k k' : Lvl.t.
  Variable e e1 : t.

  #[export]
  Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
  Proof. repeat red; intros; subst; now rewrite H1. Qed.

  Lemma shift_eq_iff :
    e = e1 <-> (shift lb k e) = (shift lb k e1).
  Proof.
    split; intros; subst; auto.
    clear lb' k'; revert e1 H. 
    induction e; intros e1 Heq.
    - destruct e1; simpl in *; inversion Heq.
      f_equal. now apply L.shift_eq_iff in H0.
    - destruct e1; simpl in *; inversion Heq; subst.
      f_equal; auto.
    - destruct e1; simpl in *; inversion Heq; subst.
      f_equal; auto.
  Qed.

  Lemma shift_neq :
    e <> e1 -> (shift lb k e) <> (shift lb k e1).
  Proof.
    intros Hneq. intro Heq. apply Hneq. clear lb' k' Hneq.
    now apply shift_eq_iff.
  Qed.

  Lemma shift_neq_1 :
    (shift lb k e) <> (shift lb k e1) -> e <> e1.
  Proof.
    intro Hneq. intro Heq. 
    now apply Hneq; subst.
  Qed.

  Lemma shift_zero_refl : shift lb 0 e = e.
  Proof.
    clear lb' k k' e1; induction e; simpl in *;
    f_equal; auto.
    apply L.shift_zero_refl.
  Qed.

  Lemma shift_trans : shift lb k (shift lb k' e) = shift lb (k + k') e.
  Proof.
    clear lb' e1; induction e; simpl in *; f_equal; auto.
    apply L.shift_trans.
  Qed.

  Lemma shift_permute :
    shift lb k (shift lb k' e) = shift lb k' (shift lb k e).
  Proof.
    clear lb' e1; induction e; simpl in *; f_equal; auto.
    apply L.shift_permute.
  Qed.

  Lemma shift_permute_1 : 
    (shift lb k (shift lb k' e)) = (shift (lb + k) k' (shift lb k e)).
  Proof.
    clear lb' e1; induction e; simpl in *; f_equal; auto.
    apply L.shift_permute_1.
  Qed.

  Lemma shift_permute_2 : 
    lb <= lb' -> (shift lb k (shift lb' k' e)) = (shift (lb' + k) k' (shift lb k e)).
  Proof.
    clear e1; induction e; simpl in *; intro Hle; f_equal; auto.
    apply L.shift_permute_2; assumption.
  Qed.

  Lemma shift_unfold : (shift lb (k + k') e) = (shift (lb + k) k' (shift lb k e)). 
  Proof.
    clear e1; induction e; simpl in *; f_equal; auto.
    apply L.shift_unfold.
  Qed.

  Lemma shift_unfold_1 : forall k k1 k2 e,
    k <= k1 -> k1 <= k2 ->
    (shift k1 (k2 - k1) (shift k  (k1 - k) e)) = shift k (k2 - k) e.
  Proof.
    clear lb lb' k k' e e1. intros k k1 k2 e. 
    induction e; simpl in *; intros Hle Hle1; f_equal; auto.
    apply L.shift_unfold_1; assumption.
  Qed.
  
  End shift.

  (** ** Valid *)
  Section valid.
    
  #[export]
  Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
  Proof. repeat red; intros; subst; rewrite H0; split; auto. Qed.

  Lemma valid_weakening : forall k k' e, (k <= k') -> valid k e -> valid k' e.
  Proof.
    intros k k' e; revert k k'; induction e; intros k k' Hle Hve; 
    inversion Hve; subst; constructor; fold valid in *; eauto.
    - apply (L.valid_weakening k k' t0 Hle H1).
    - apply (IHe (S k) (S k')); auto. lia.
  Qed. 

  Lemma shift_preserves_valid_1 : forall lb k k' e, 
    valid k e -> valid (k + k') (shift lb k' e).
  Proof.
    intros lb k k' e; revert lb k k'; induction e; intros lb k k' Hve; 
    inversion Hve; subst; simpl; constructor; fold valid in *; auto.
    - now apply L.shift_preserves_valid_1.
    - replace (S (k + k')) with ((S k) + k') by lia.
      apply (IHe lb (S k) k' H1).
  Qed.

  Lemma shift_preserves_valid : forall k k' e, valid k e -> valid (k + k') (shift k k' e).
  Proof.
    intros k k' e Hve.
    apply (shift_preserves_valid_1 k k k' _ Hve).
  Qed.

  Lemma shift_preserves_valid_gen : forall lb lb' k k' e,
    k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> 
    k' - k = lb' - lb -> 
    valid lb e -> valid lb' (shift k (k' - k) e).
  Proof.
    intros lb lb' k k' e; revert lb lb' k k'.
    induction e; intros lb lb' k k' Hle Hle1 Hle2 Hle3 Heq Hve;
    simpl; inversion Hve; subst; fold valid in *; constructor.
    - apply (L.shift_preserves_valid_gen lb); assumption.
    - apply (IHe1 lb lb' k k'); assumption.
    - apply (IHe2 lb lb' k k'); assumption.
    - apply (IHe (S lb) (S lb') k k'); auto; lia.
  Qed.

  Lemma shift_preserves_valid_2 : forall lb lb' e,
    lb <= lb' -> valid lb e -> 
    valid lb' (shift lb (lb' - lb) e).
  Proof. intros. eapply shift_preserves_valid_gen; eauto. Qed. 

  Lemma shift_preserves_valid_zero : forall k e, valid k e -> valid k (shift k 0 e).
  Proof. 
    intros; replace k with (k + 0); try lia;
    now apply shift_preserves_valid_1. 
  Qed. 
  
  End valid.

End Lambda.

Import Lambda.

(** *** Tests *)

Compute [⧐ 3 ~ 2] 6.
Compute ⟨[⧐ 0 ~ 3] (2 3)⟩.
Compute ⟨[⧐ 2 ~ 3] (\,2)⟩.
Compute ⟨[⧐ 4 ~ 3] (\,(2 (1 8)))⟩.

(**
  This property does not hold for leveled element with binders.
*)
Lemma nshift_valid_refl: ~ (forall lb k e, valid lb e -> shift lb k e = e).
Proof.
  intro c.
  assert (Hvabs: 0 ⊢ ⟨\,0⟩).
  { repeat constructor; fold valid. }
  assert (Hshift: ⟨[⧐ 0 ~ 1] \,0⟩ <> ⟨\,0⟩).
  { compute. intro c1. inversion c1. }

  apply Hshift. 
  apply (c 0 1 ⟨\,0⟩ Hvabs).
Qed.

(** Creating a map between variables and terms *)
Module Context := MapLvlD.MakeLvlMapWLLVL Lambda.

(** Creating a list of variables *)
Module VarList := Levels.

(** Creating an optional term *)
Module OptionLambda <: IsLvlETWL := IsLvlOptETWL Lambda.