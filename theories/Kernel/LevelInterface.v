From Coq Require MSets Structures.Equalities Structures.Orders.
Import Structures.Equalities Structures.Orders.

(** * Interfaces -- Level *)

(** ** Level

  A level is a simple element that can be ordered. We choose to use [nat] as Level.
*)
Module Lvl <: Orders.OrderedTypeFull := Structures.OrdersEx.Nat_as_OT.


(** ** Valid and Shift interfaces 

  Like open, close functions in the locally nameless representation,  valid and shift functions are required for
  De Bruijn levels representation. For example the weakening of typing in a stlc cannot be expressed and proved without them.

  In more general way, valid is used for define the order between levels and shift is used for increase the level.
*)

(** *** Valid function

  This function ensures the respect of the hierarchy given by the level representation. A valid leveled element according to a certain level l is an element where all leveled subterm is also valid. In the case of level, the valid function will be [<] and for a set of levels, all element from the must satisfies the valid property.
*)

(** **** Minimal constraint for a valid function *)
Module Type HasValid (Import T : EqualityType).

  Section definition.

    Parameter valid : Lvl.t -> t -> Prop.

  End definition.

  Section property.
  
    Parameter valid_weakening : forall k k' t, (Lvl.le k k') -> valid k t -> valid k' t.
    #[global]
    Declare Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.

  End property.

End HasValid.

(** **** Minimal constraint for a valid function which returns a boolean *)
Module Type HasValidb (Import T : EqualityType).

  Section definition.

    Parameter validb : Lvl.t -> t -> bool.

  End definition.

  Section equality.

    #[global]
    Declare Instance validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.

  End equality.

End HasValidb.

(** **** Intermediate constraint for valid functions (with Prop and boolean) *)
Module Type HasValidFull (Import T : EqualityType) (Import V : HasValid T) <: HasValidb T.

  Include HasValidb T.

  Section property.

    Variable k : Lvl.t.
    Variable t : t.

    Parameter validb_valid : validb k t = true <-> valid k t. 
    Parameter validb_nvalid : validb k t = false <-> ~ valid k t. 

  End property.

End HasValidFull.


(** ***  Shift function

  The [shift] function increments the level and consequently the depth of the tree defined by the representation. This function takes three arguments: the lower bound [lb], the shift [k] and the leveled element [t]. All level contained in the leveled element lower than [lb] will be unchanged while the other ones would be incremented by
  [k].
<<
In the case of level directly.

shift 0 2 2 = 4
shift 3 2 2 = 2
shift 65 0 98 = 98
>>

  In a lambda calculus term, certain variable can be free and are always represented by the smallest levels. Thus, it is interested to use the [lb] argument to avoid modification on it.
<<
shift 1 3 (\. 0 1) = (\. 0 4)
>>
*)

(** **** Minimal constraint for a shift function *)
Module Type Shift (Import T : EqualityType).

  Section definition.

    Parameter shift : Lvl.t -> Lvl.t -> t -> t.

  End definition.

  Section property.

    Variable lb k k' k'' : Lvl.t.
    Variable t : t.

    Parameter shift_refl : eq (shift lb 0 t) t.
    Parameter shift_trans : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
    Parameter shift_permute : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
    Parameter shift_unfold : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
    Parameter shift_unfold_1 :
      k <= k' -> k' <= k'' -> eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).

  End property.

  Section equality.

    #[global]
    Declare Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
    Parameter shift_eq_iff : forall lb k t t1, eq t t1 <-> eq (shift lb k t) (shift lb k t1).

  End equality.

End Shift.


(** **** Intermediate constraint for valid and shift functions *)
Module Type ShiftValid (Import T : EqualityType) <: Shift T <: HasValid T.

  Include Shift T <+ HasValid T.

  Section property.

    Variable lb lb' k k' : Lvl.t.
    Variable t : t.

    Parameter shift_preserves_valid : valid k t -> valid (k + k') (shift k k' t).
    Parameter shift_preserves_valid_1 : valid k t -> valid (k + k') (shift lb k' t).
    Parameter shift_preserves_valid_2 :  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' ->
      k' - k = lb' - lb ->  valid lb t -> valid lb' (shift k (k' - k) t).
    Parameter shift_preserves_valid_3 : lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
    Parameter shift_preserves_valid_4 : valid k t -> valid k (shift k 0 t).

  End property.

End ShiftValid.


(** **** Full constraint for valid and shift functions *)
Module Type StrongShiftValid (Import T : EqualityType) <: ShiftValid T.

  Include ShiftValid T.

  Section property.

    Parameter shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.

  End property.

End StrongShiftValid.

(** **** Full constraint for valid and shift functions *)
Module Type StrongShiftValidEx (Import T : EqualityType) (Import SV : ShiftValid T).

  Section property.

    Parameter shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.

  End property.

End StrongShiftValidEx.

(** ** Some Interfaces for work with well known module types *)

Module Type EqualityTypeWithLeibniz <: EqualityType.

  Include Eq <+ IsEq.

  Section equality.

    Parameter eq_leibniz : forall x y, eq x y -> x = y.

  End equality.

  #[global]
  Hint Immediate eq_sym : core.
  #[global]
  Hint Resolve eq_refl eq_trans : core.

End EqualityTypeWithLeibniz.

Module Type DecidableTypeWithLeibniz <: DecidableType.

  Include Eq <+ IsEq <+ HasEqDec.

  Section equality.

    Parameter eq_leibniz : forall x y, eq x y -> x = y.

  End equality.

  #[global]
  Hint Immediate eq_sym : core.
  #[global]
  Hint Resolve eq_refl eq_trans : core.

End DecidableTypeWithLeibniz.

(**
  This module is the same as in MSet. It allows to define ordered type with its own equality with
  an equivalence with the leibniz equality.
*)
Module Type OrderedTypeWithLeibniz <: Orders.OrderedType.

  Include Orders.OrderedType.

  Section equality.

    Parameter eq_leibniz : forall x y, eq x y -> x = y.

  End equality.

End OrderedTypeWithLeibniz.

(** ** Collection of Interfaces compositions *)

(** *** EqualityType interface *)
Module Type ShiftValidET :=  EqualityType <+ ShiftValid.
Module Type ShiftValidETWithLeibniz := EqualityTypeWithLeibniz <+ ShiftValid.
Module Type StrongShiftValidET :=  EqualityType <+ StrongShiftValid.
Module Type StrongShiftValidETWithLeibniz := EqualityTypeWithLeibniz <+ StrongShiftValid.

Module Type ShiftValidFullET := ShiftValidET <+ HasValidFull.
Module Type ShiftValidFullETWithLeibniz := ShiftValidETWithLeibniz <+ HasValidFull.
Module Type StrongShiftValidFullET := StrongShiftValidET <+ HasValidFull.
Module Type StrongShiftValidFullETWithLeibniz := StrongShiftValidETWithLeibniz <+ HasValidFull.


(** *** DecidableType interface *)
Module Type ShiftValidDT :=  EqualityType <+ HasEqDec <+ ShiftValid.
Module Type ShiftValidDTWithLeibniz := DecidableTypeWithLeibniz <+ ShiftValid.
Module Type StrongShiftValidDT :=  EqualityType <+ HasEqDec <+ StrongShiftValid.
Module Type StrongShiftValidDTWithLeibniz := DecidableTypeWithLeibniz <+ StrongShiftValid.

Module Type ShiftValidFullDT := ShiftValidDT <+ HasValidFull.
Module Type ShiftValidFullDTWithLeibniz := ShiftValidDTWithLeibniz <+ HasValidFull.
Module Type StrongShiftValidFullDT := StrongShiftValidDT <+ HasValidFull.
Module Type StrongShiftValidFullDTWithLeibniz := StrongShiftValidDTWithLeibniz <+ HasValidFull.

(** *** OrderedType interface *)
Module Type ShiftValidOT := Orders.OrderedType <+ ShiftValid.
Module Type ShiftValidOTWithLeibniz := OrderedTypeWithLeibniz <+ ShiftValid.
Module Type StrongShiftValidOT := Orders.OrderedType <+ StrongShiftValid.
Module Type StrongShiftValidOTWithLeibniz := OrderedTypeWithLeibniz <+ StrongShiftValid.


Module Type ShiftValidFullOT := ShiftValidOT <+ HasValidFull.
Module Type ShiftValidFullOTWithLeibniz := ShiftValidOTWithLeibniz <+ HasValidFull.
Module Type StrongShiftValidFullOT := StrongShiftValidOT <+ HasValidFull.
Module Type StrongShiftValidFullOTWithLeibniz := StrongShiftValidOTWithLeibniz <+ HasValidFull.