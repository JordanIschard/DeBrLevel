From Coq Require Import MSets.
From DeBrLevel Require Import LevelInterface Level SetOTwLInterface SetOTwL.

(** * Interface - Leveled Set

  Based on [SetOTwL], we define interfaces for sets with leveled elements. In addition to
  properties on [shift] and [valid], we ask the user to satisfy several interaction properties
  between them and classical set operators such as ∈,∪, etc.

  [shift] is directly applied on elements of the set (like a map) and [valid] is satisfied 
  by a set [t] under [n] only if all elements in [t] satisfy the validity property under [n]. 
*)

(** ** Leveled Set Interface - [OT] and [WL] *)
Module Type IsLvlSetInterface 
            (T : IsLvlOTWL) (Import St : SetOTWithLeibnizInterface T) <: IsLvlOTWL.

Include IsLvl St.

(** *** Definitions *)

Definition t := t.

Definition eq := eq.
Definition eq_equiv := eq_equiv.
Definition eq_dec := eq_dec.
Definition eq_leibniz := eq_leibniz.

Definition lt := lt.
Definition lt_strorder := lt_strorder.
Definition lt_compat := lt_compat.

Definition compare := compare.
Definition compare_spec := compare_spec.

(** *** Specifications *)
Section specs.

Variable m n : Lvl.t.
Variable v : elt.
Variable t t' : t.


(** **** [Wf] specifications 
  [Wf] is opaque outside, consequently we gives an explicit unfold lemma.
*)

Parameter Wf_unfold : Wf m t <-> (For_all (T.Wf m) t).

Parameter Wf_add_iff : Wf m (add v t) <-> T.Wf m v /\ Wf m t.

Parameter Wf_empty : Wf m empty.

Parameter Wf_union_iff : Wf m (union t t') <-> Wf m t /\ Wf m t'.

Parameter Wf_singleton_iff : Wf m (singleton v) <-> T.Wf m v.

Parameter Wf_in : Wf m t -> In v t -> T.Wf m v.

(** **** [shift] specifications *)

Parameter shift_Empty : Empty t -> shift m n t = empty.

Parameter shift_empty : shift m n empty = empty.

Parameter shift_singleton : shift m n (singleton v) = singleton (T.shift m n v).

Parameter shift_union : shift m n (union t t') = union (shift m n t) (shift m n t').

Parameter shift_inter : shift m n (inter t t') = inter (shift m n t) (shift m n t').

Parameter shift_diff : shift m n (diff t t') = (diff (shift m n t) (shift m n t')).

Parameter shift_add_notin :
  ~ In v t -> shift m n (add v t) = add (T.shift m n v) (shift m n t).

Parameter shift_add_in : In v t -> shift m n (add v t) = (shift m n t).

Parameter shift_add : shift m n (add v t) = add (T.shift m n v) (shift m n t).

Parameter shift_remove : shift m n (remove v t) = remove (T.shift m n v)(shift m n t).

Parameter shift_in_iff : In v t <-> In (T.shift m n v) (shift m n t).

Parameter shift_in_e :
  In v (shift m n t) -> 
  exists v', v = (T.shift m n v') /\ In (T.shift m n v') (shift m n t).

Parameter shift_notin_iff : ~ In v t <-> ~ In (T.shift m n v) (shift m n t).

End specs.

End IsLvlSetInterface.


(** ---- *)


(** ** Leveled Set Interface - [OT], [BD] and [WL] *)
Module Type IsBdlLvlSetInterface (T : IsLvlOTWL) (St : SetOTWithLeibnizInterface T) <: IsBdlLvlOTWL.

Include IsLvlSetInterface T St.
Import St.

Parameter shift_wf_refl : forall (m n: Lvl.t) (t: t), Wf m t -> eq (shift m n t) t.

Parameter Wf_in_iff : 
  forall (m k: Lvl.t) (n: elt) (t: t), Wf m t -> In n (shift m k t) <-> In n t.

End IsBdlLvlSetInterface.


(** ---- *)


(** ** Leveled Set Interface - [OT], [FL] and [WL] *)
Module Type IsLvlFullSetInterface (T : IsLvlFullOTWL) (St : SetOTWithLeibnizInterface T)
:= (IsLvlSetInterface T St) <+ IsWFFull.


(** ---- *)


(** ** Leveled Set Interface - [OT], [BD], [FL] and [WL] *)
Module Type IsBdlLvlFullSetInterface (T : IsBdlLvlFullOTWL) (St : SetOTWithLeibnizInterface T)
:= (IsBdlLvlSetInterface T St) <+ IsWFFull.


Module Type IsLvlSetLVLInterface (St: SetOTWithLeibnizInterface Level).

Include IsBdlLvlFullSetInterface Level St.
Import St.

(** *** Definitions *)

Parameter max_key : t -> Lvl.t.
Parameter new_key : t -> Lvl.t.

(** *** Specifications *)
Section specifications.

Variable m n k p: Lvl.t.
Variable v : elt.
Variable s s' : t.

(** **** [max_key] specifications *)

#[export] Declare Instance max_key_eq : Proper (eq ==> Logic.eq) max_key. 

Parameter max_key_Empty : Empty s -> max_key s = 0.

Parameter max_key_empty : max_key empty = 0.

Parameter max_key_Add_max : Add v s s' -> max_key s' = max v (max_key s). 

Parameter max_key_add_max : max_key (add v s) = max v (max_key s). 

(** **** [new_key] specifications *)

#[export] Declare Instance new_key_eq : Proper (eq ==> Logic.eq) new_key. 

Parameter new_key_Empty : Empty s -> new_key s = 0.

Parameter new_key_empty : new_key empty = 0.

Parameter new_key_Add_max : Add v s s' -> new_key s' = max (S v) (new_key s). 

Parameter new_key_add_max : new_key (add v s) = max (S v) (new_key s). 

Parameter new_key_in_spec : In v s -> (v < new_key s)%nat.

(** **** [shift] specifications *)

Parameter shift_permute_1 :
  eq (shift m n (shift m k s)) (shift (m + n) k (shift m n s)).

Parameter shift_permute_2 :
  m <= n -> eq (shift m k (shift n p s)) (shift (n + k) p (shift m k s)).

End specifications.

End IsLvlSetLVLInterface.