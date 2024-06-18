From DeBrLevel Require Import LevelInterface Level.
From Coq Require Import Lia.

(** * Test - Level *)

Module Var := Level.

(** ** Definition and notations *)

Definition var := Var.t.
Notation "'[⧐' lb '~' k ']' t" := (Var.shift lb k t) (at level 30, right associativity).
Infix "⊢" := Var.valid (at level 20, no associativity). 

(** ** Test [shift] function *)

(** *** Tests *)

Compute [⧐ 0 ~ 0] 6.
Compute [⧐ 0 ~ 3] 6.
Compute [⧐ 10 ~ 3] 6.
Compute [⧐ 6 ~ 3] 6.
Compute [⧐ 6 ~ 0] 6.
Compute [⧐ 6 ~ 0][⧐ 3 ~ 3] 6.

(** *** Playing with properties *)

(** The lower bound is strictly greater than the level, thus it keeps unchanged. *)
Example test_shift_1: [⧐ 10 ~ 3] 6 = 6.
Proof. now compute. Qed.

(** Shifting a level by 0 does not affect it. *)
Example test_shift_2 n m : [⧐ m ~ 0] n = n.
Proof. apply Var.shift_refl. Qed.

(** Shift value is cumulative. *)
Example test_shift_3 n m: [⧐ m ~ 5][⧐ m ~ 7] n = [⧐ m ~ 12] n.
Proof. rewrite Var.shift_trans. simpl. reflexivity. Qed.

(** Reciprocally, we can unfold a shift *)
Example test_shift_4 n: [⧐ 10 ~ 7] n = [⧐ 13 ~ 4][⧐ 10 ~ 3] n.
Proof.
  replace ([⧐10 ~ 7] n) with ([⧐10 ~ (3 + 4)] n) by (f_equal; lia).
  rewrite Var.shift_unfold. simpl. reflexivity.
Qed.

(** ** Test [valid] property *)

(** *** Tests *)

Compute 6 ⊢ 7.
Compute 2 ⊢ 0.
Compute 3 ⊢ 3.

(** *** Playing with properties *)

(** A level cannot be valid by itself. *)
Example test_valid_1 n: ~ n ⊢ n.
Proof. intro c. compute in c. lia. Qed.

(** The property can be weakened. *)
Example test_valid_2 k n m: 
  m <= n -> m ⊢ k -> n ⊢ k.
Proof. 
  intros Hle Hvk. 
  apply (Var.valid_weakening m n k Hle Hvk).
Qed.

(** ** Test interaction between [shift] and [valid] *)

(** Shifting preserves validity *)
Example test_shift_valid_1 n: 3 ⊢ n -> 5 ⊢ [⧐ 3 ~ 2] n.
Proof.
  intro Hvn.
  replace 5 with (3 + 2) by lia.
  apply (Var.shift_preserves_valid_1 _ 3 2 n Hvn).
Qed.

(** 
  In the context of leveled elements without binders in it,
  a shifting with a lower greater or equals to the level of validity
  does not change the elements.
*)
Example test_shift_valid_2: 
  4 ⊢ 3 -> forall (n m: var), 4 <= n -> [⧐ n ~ m] 3 = 3.
Proof.
  intros Hv3 n m Hle.
  apply (Var.shift_valid_refl n  m 3).
  apply (Var.valid_weakening 4 n 3 Hle Hv3).
Qed.