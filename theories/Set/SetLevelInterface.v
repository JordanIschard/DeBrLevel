From Coq Require Import MSets.
From DeBrLevel Require Import Level LevelInterface SetOTwLInterface SetOTwL.

(** * Interfaces -- Set Level

  Based on the overlay [SetOTwL] we defined interfaces for sets with [shift] and [valid].
*)

(** ** General leveled set interface *)
Module Type IsLvlSetOTWLGenInterface (T : IsLvlOTWL) := (SetOTWithLeibnizInterface T) <+ IsLvl.

(** ** General leveled set interface without binders in its elements *)
Module Type IsBdlLvlSetOTWLGenInterface (T : IsBdlLvlOTWL) 
:= (SetOTWithLeibnizInterface T) <+ IsBdlLvl.

(** ** Leveled set interface 

  In addition to lemmas from [IsLvl], it is convenient to add lemmas that
  describe the interaction between [shift], [valid] functions and classic functions like [add],[union],[singleton], etc.
*)
Module Type IsLvlSetOTWLInterface (T : IsLvlOTWL) <: IsLvlSetOTWLGenInterface T.

  Include IsLvlSetOTWLGenInterface T.

  (** *** Valid *)
  Section valid.

    Variable lb : Lvl.t.
    Variable v : elt.
    Variable s s' : t.

    (** [valid] is opaque outside, consequently we gives an explicit unfold lemma. *)
    Parameter valid_unfold : valid lb s <-> (For_all (T.valid lb) s).
    Parameter valid_add_spec : valid lb (add v s) -> T.valid lb v /\ valid lb s.
    Parameter valid_empty_spec : valid lb empty.
    Parameter valid_union_spec : valid lb (union s s') <-> valid lb s /\ valid lb s'.
    Parameter valid_singleton_spec : valid lb (singleton v) <-> T.valid lb v.
    Parameter valid_in_spec : valid lb s -> In v s -> T.valid lb v.

  End valid.

  (** *** Shift *)
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

End IsLvlSetOTWLInterface.

(** ** Set interface fully constrained with extra lemmas *)
Module Type IsBdlLvlSetOTWLInterface (T : IsBdlLvlOTWL) 
                                                <: IsBdlLvlSetOTWLGenInterface T.

  Include IsBdlLvlSetOTWLGenInterface T.

  (** *** Valid *)
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

  (** *** Shift *)
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

End IsBdlLvlSetOTWLInterface.

(** ** Set interface with minimal constraints, extra lemmas and [validb] *)
Module Type IsLvlFullSetOTWLInterface (T : IsLvlFullOTWL) 
:= (IsLvlSetOTWLInterface T) <+ HasValidFull.

(** ** Set interface fully constrained with extra lemmas and [validb] *)
Module Type IsBdlLvlFullSetOTWLInterface (T : IsBdlLvlFullOTWL) 
:= (IsBdlLvlSetOTWLInterface T) <+ HasValidFull.