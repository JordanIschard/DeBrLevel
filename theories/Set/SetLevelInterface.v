From Coq Require Import MSets.
From DeBrLevel Require Import LevelInterface SetOTwLInterface SetOTwL.

(** * Interface - Leveled Set

  Based on [SetOTwL], we define interfaces for sets with leveled elements. In addition to
  properties on [shift] and [valid], we ask the user to satisfy several interaction properties
  between them and classical set operators such as ∈,∪, etc.

  [shift] is directly applied on elements of the set (like a map) and [valid] is satisfied 
  by a set [s] under [k] only if all elements in [s] satisfy the validity property under [k]. 
*)

(** *** Leveled Set Interface with ordered elements with leibniz equality *)
Module Type IsLvlSetInterface 
  (T : IsLvlOTWL) (Import St : SetOTWithLeibnizInterface T) <: IsLvlOTWL.

Include IsLvl St.

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

(** **** Valid 
  [valid] is opaque outside, consequently we gives an explicit unfold lemma.
*)
Section valid.

Variable lb : Lvl.t.
Variable v : elt.
Variable s s' : t.

Parameter valid_unfold : valid lb s <-> (For_all (T.valid lb) s).
Parameter valid_add_spec : valid lb (add v s) -> T.valid lb v /\ valid lb s.
Parameter valid_empty_spec : valid lb empty.
Parameter valid_union_spec : valid lb (union s s') <-> valid lb s /\ valid lb s'.
Parameter valid_singleton_spec : valid lb (singleton v) <-> T.valid lb v.
Parameter valid_in_spec : valid lb s -> In v s -> T.valid lb v.

End valid.

(** **** Shift *)
Section shift.

Variable lb k : Lvl.t.
Variable v : elt.
Variable s s' : t.

Parameter shift_Empty_spec : Empty s -> shift lb k s = empty.
Parameter shift_empty_spec : shift lb k empty = empty.
Parameter shift_singleton_spec : shift lb k (singleton v) = singleton (T.shift lb k v).
Parameter shift_union_spec : shift lb k (union s s') = union (shift lb k s) (shift lb k s').
Parameter shift_inter_spec : shift lb k (inter s s') = inter (shift lb k s) (shift lb k s').
Parameter shift_diff_spec : shift lb k (diff s s') = (diff (shift lb k s) (shift lb k s')).

Parameter shift_add_notin_spec :
  ~ In v s -> shift lb k (add v s) = add (T.shift lb k v) (shift lb k s).
Parameter shift_add_in_spec : In v s -> shift lb k (add v s) = (shift lb k s).
Parameter shift_add_spec : shift lb k (add v s) = add (T.shift lb k v) (shift lb k s).
Parameter shift_remove_spec : shift lb k (remove v s) = remove (T.shift lb k v)(shift lb k s).

Parameter shift_in_spec : In v s <-> In (T.shift lb k v) (shift lb k s).
Parameter shift_in_e_spec :
  In v (shift lb k s) -> 
  exists v', v = (T.shift lb k v') /\ In (T.shift lb k v') (shift lb k s).
Parameter shift_notin_spec : ~ In v s <-> ~ In (T.shift lb k v) (shift lb k s).

End shift.

End IsLvlSetInterface.

(** ---- *)

(** *** Bindless Leveled Set Interface with ordered elements with leibniz equality *)
Module Type IsBdlLvlSetInterface (T : IsLvlOTWL) (St : SetOTWithLeibnizInterface T) <: IsBdlLvlOTWL
:= IsLvlSetInterface T St <+ IsBindlessLeveledEx.


(** *** Leveled Set interface with boolean version of [valid] named [validb] *)
Module Type IsLvlFullSetInterface (T : IsLvlFullOTWL) (St : SetOTWithLeibnizInterface T)
:= (IsLvlSetInterface T St) <+ HasValidFull.


(** *** Bindless Leveled Set interface with boolean version of [valid] named [validb] *)
Module Type IsBdlLvlFullSetInterface (T : IsBdlLvlFullOTWL) (St : SetOTWithLeibnizInterface T)
:= (IsBdlLvlSetInterface T St) <+ HasValidFull.