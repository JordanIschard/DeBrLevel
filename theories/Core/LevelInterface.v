From Coq Require MSets Structures.Equalities Structures.Orders.
Import Structures.Equalities Structures.Orders.

(** * Interfaces -- Level *)

(** ** Level

  A level is a simple element that can be ordered.
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

Section operation.

Parameter valid : Lvl.t -> t -> Prop.

End operation.

Section properties.

Variable k k' : Lvl.t.
Variable t : t.
  
Parameter valid_weakening : Lvl.le k k' -> valid k t -> valid k' t.
#[export] Declare Instance valid_eq : Proper (Lvl.eq ==> eq ==> iff) valid.

End properties.

End HasValid.




(** **** Minimal constraint for a valid function which returns a boolean *)
Module Type HasValidb (Import T : EqualityType).

Section operation.

Parameter validb : Lvl.t -> t -> bool.

End operation.

Section properties.

#[export] Declare Instance validb_eq : Proper (Lvl.eq ==> eq ==> Logic.eq) validb.

End properties.

End HasValidb.




(** **** Intermediate constraint for valid functions (with Prop and boolean) *)
Module Type HasValidFull (Import T : EqualityType) (Import V : HasValid T) <: HasValidb T.

Include HasValidb T.

Section properties.

Variable k : Lvl.t.
Variable t : t.

Parameter validb_valid : validb k t = true <-> valid k t. 
Parameter validb_nvalid : validb k t = false <-> ~ valid k t. 

End properties.

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
Module Type HasShift (Import T : EqualityType).

Section operation.

Parameter shift : Lvl.t -> Lvl.t -> t -> t.

End operation.

Section properties.

Variable lb k k' k'' : Lvl.t.
Variable t t' : t.

Parameter shift_refl : eq (shift lb 0 t) t.
Parameter shift_trans : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Parameter shift_permute : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Parameter shift_unfold : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Parameter shift_unfold_1 :
  k <= k' -> k' <= k'' -> eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).

#[export] Declare Instance shift_eq : Proper (Lvl.eq ==> Lvl.eq ==> eq ==> eq) shift.
Parameter shift_eq_iff : eq t t' <-> eq (shift lb k t) (shift lb k t').

End properties.

End HasShift.


(** **** Intermediate constraint for valid and shift functions *)
Module Type IsLeveled (Import T : EqualityType) <: HasShift T <: HasValid T.

Include HasShift T <+ HasValid T.

Section properties.

  Variable lb lb' k k' : Lvl.t.
  Variable t : t.

  Parameter shift_preserves_valid : valid k t -> valid (k + k') (shift k k' t).
  Parameter shift_preserves_valid_1 : valid k t -> valid (k + k') (shift lb k' t).
  Parameter shift_preserves_valid_2 :  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' ->
    k' - k = lb' - lb ->  valid lb t -> valid lb' (shift k (k' - k) t).
  Parameter shift_preserves_valid_3 : lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
  Parameter shift_preserves_valid_4 : valid k t -> valid k (shift k 0 t).

End properties.

End IsLeveled.


(** **** Full constraint for valid and shift functions *)
Module Type IsBindlessLeveled (Import T : EqualityType) <: IsLeveled T.

Include IsLeveled T.

Parameter shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.

End IsBindlessLeveled.

(** **** Full constraint for valid and shift functions *)
Module Type IsBindlessLeveledEx (Import T : EqualityType) (Import IsLvl : IsLeveled T).

Parameter shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.

End IsBindlessLeveledEx.




(** ** Some Interfaces for work with well known module types *)

Module Type EqualityTypeWithLeibniz <: EqualityType.

Include Eq <+ IsEq.

Parameter eq_leibniz : forall x y, eq x y -> x = y.
#[export] Hint Immediate eq_sym : core.
#[export] Hint Resolve eq_refl eq_trans : core.

End EqualityTypeWithLeibniz.

Module Type DecidableTypeWithLeibniz <: DecidableType.

Include Eq <+ IsEq <+ HasEqDec.

Parameter eq_leibniz : forall x y, eq x y -> x = y.
#[export] Hint Immediate eq_sym : core.
#[export] Hint Resolve eq_refl eq_trans : core.

End DecidableTypeWithLeibniz.

(**
  This module is the same as in MSet. It allows to define ordered type with its own equality with
  an equivalence with the leibniz equality.
*)
Module Type OrderedTypeWithLeibniz <: Orders.OrderedType.

Include Orders.OrderedType.

Parameter eq_leibniz : forall x y, eq x y -> x = y.

End OrderedTypeWithLeibniz.




(** ** Collection of Interfaces compositions *)

Module Type IsLvl := IsLeveled.
Module Type IsBdlLvl := IsBindlessLeveled.


(** *** EqualityType interface *)
Module Type IsLeveledET :=  EqualityType <+ IsLeveled.
Module Type IsLeveledETWithLeibniz := EqualityTypeWithLeibniz <+ IsLeveled.
Module Type IsBindlessLeveledET :=  EqualityType <+ IsBindlessLeveled.
Module Type IsBindlessLeveledETWithLeibniz := EqualityTypeWithLeibniz <+ IsBindlessLeveled.

Module Type IsLeveledFullET := IsLeveledET <+ HasValidFull.
Module Type IsLeveledFullETWithLeibniz := IsLeveledETWithLeibniz <+ HasValidFull.
Module Type IsBindlessLeveledFullET := IsBindlessLeveledET <+ HasValidFull.
Module Type IsBindlessLeveledFullETWithLeibniz := IsBindlessLeveledETWithLeibniz <+ HasValidFull.

Module Type IsLvlET := IsLeveledET.
Module Type IsLvlETWL := IsLeveledETWithLeibniz.
Module Type IsLvlFullET := IsLeveledFullET.
Module Type IsLvlFullETWL := IsLeveledFullETWithLeibniz.

Module Type IsBdlLvlET := IsBindlessLeveledET.
Module Type IsBdlLvlETWL := IsBindlessLeveledETWithLeibniz.
Module Type IsBdlLvlFullET := IsBindlessLeveledFullET.
Module Type IsBdlLvlFullETWL := IsBindlessLeveledFullETWithLeibniz.




(** *** DecidableType interface *)
Module Type IsLeveledDT :=  EqualityType <+ HasEqDec <+ IsLeveled.
Module Type IsLeveledDTWithLeibniz := DecidableTypeWithLeibniz <+ IsLeveled.
Module Type IsBindlessLeveledDT :=  EqualityType <+ HasEqDec <+ IsBindlessLeveled.
Module Type IsBindlessLeveledDTWithLeibniz := DecidableTypeWithLeibniz <+ IsBindlessLeveled.

Module Type IsLeveledFullDT := IsLeveledDT <+ HasValidFull.
Module Type IsLeveledFullDTWithLeibniz := IsLeveledDTWithLeibniz <+ HasValidFull.
Module Type IsBindlessLeveledFullDT := IsBindlessLeveledDT <+ HasValidFull.
Module Type IsBindlessLeveledFullDTWithLeibniz := IsBindlessLeveledDTWithLeibniz <+ HasValidFull.

Module Type IsLvlDT := IsLeveledDT.
Module Type IsLvlDTWL := IsLeveledDTWithLeibniz.
Module Type IsLvlFullDT := IsLeveledFullDT.
Module Type IsLvlFullDTWL := IsLeveledFullDTWithLeibniz.

Module Type IsBdlLvlDT := IsBindlessLeveledDT.
Module Type IsBdlLvlDTWL := IsBindlessLeveledDTWithLeibniz.
Module Type IsBdlLvlFullDT := IsBindlessLeveledFullDT.
Module Type IsBdlLvlFullDTWL := IsBindlessLeveledFullDTWithLeibniz.



(** *** OrderedType interface *)
Module Type IsLeveledOT := Orders.OrderedType <+ IsLeveled.
Module Type IsLeveledOTWithLeibniz := OrderedTypeWithLeibniz <+ IsLeveled.
Module Type IsBindlessLeveledOT := Orders.OrderedType <+ IsBindlessLeveled.
Module Type IsBindlessLeveledOTWithLeibniz := OrderedTypeWithLeibniz <+ IsBindlessLeveled.

Module Type IsLeveledFullOT := IsLeveledOT <+ HasValidFull.
Module Type IsLeveledFullOTWithLeibniz := IsLeveledOTWithLeibniz <+ HasValidFull.
Module Type IsBindlessLeveledFullOT := IsBindlessLeveledOT <+ HasValidFull.
Module Type IsBindlessLeveledFullOTWithLeibniz := IsBindlessLeveledOTWithLeibniz <+ HasValidFull.

Module Type IsLvlOT := IsLeveledOT.
Module Type IsLvlOTWL := IsLeveledOTWithLeibniz.
Module Type IsLvlFullOT := IsLeveledFullOT.
Module Type IsLvlFullOTWL := IsLeveledFullOTWithLeibniz.

Module Type IsBdlLvlOT := IsBindlessLeveledOT.
Module Type IsBdlLvlOTWL := IsBindlessLeveledOTWithLeibniz.
Module Type IsBdlLvlFullOT := IsBindlessLeveledFullOT.
Module Type IsBdlLvlFullOTWL := IsBindlessLeveledFullOTWithLeibniz.