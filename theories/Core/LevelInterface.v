From Coq Require MSets Structures.Equalities Structures.Orders.
Import Structures.Equalities Structures.Orders.

(** * Interfaces -- Level 

  De-Bruijn has proposed a variation of the lambda calculus which instanciates variables
  in a determinisc way. It defines two measures: the distance and the level. The distance,
  latter called index, is the number of abstraction between a variable and its binder. The
  level is the number of abstraction encountered since the root of the representative tree
  of a term.

  For instance, λx.(λy.(x y) x) is equal to λ.(λ.(1 0) 0) with distances and λ.(λ.(0 1) 0) 
  with levels.

  This kind of representations are extremely basic and can be used in different context as
  well as be embedded in data types or data structures.
*)

(** ** Level - Definition

  A level itself only require to be ordered. We require also a ground value and
  classic arithmetic operators on it. Thus, we define a level as a [Nat].

*)
Module Lvl <: Orders.OrderedTypeFull := Structures.OrdersEx.Nat_as_OT.

(** ---- *)

(** ** Valid and Shift interfaces 

  We split the definition of an element that used levels in different module types.
  First, we want to be as flexible as possible. Second, each modules types carries
  an additional set of constraints.

  We define a function called [shift] and a property called [valid]. It is the minimal set
  of elements for working with levels. Their principles ared defined below.
*)

(** *** Valid Property

  If we define an inductive type as containing levels, the questioning about the well-formation or ill-formation appears.
  Thus we suppose a property [valid], to define by the user, which is satisfied if the instanciation is well formed.

  What is a well formed type ? If we take the most basic case, a level, when can we state that a level is valid or not ?
  We can only talk about a valid level regards of a lower bound [lb]. 

  We use the case of the lambda calculus to illustrate it. Consider the term "x", the variable is free. Thus, how do we state
  that it is a well formed term ? We suppose that "x" is defined in a certain context. Now, consider the term "λx.(x y)". "y" is 
  free and "x" bound. The term is well formed if "y" is defined in a certain context. The lower bound can be here understood as 
  the number of free variables.

*)

(** **** Minimal constraint for a valid property *)
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


(** **** Minimal constraint for a valid property which returns a boolean *)
Module Type HasValidb (Import T : EqualityType).

Section operation.

Parameter validb : Lvl.t -> t -> bool.

End operation.

Section properties.

#[export] Declare Instance validb_eq : Proper (Lvl.eq ==> eq ==> Logic.eq) validb.

End properties.

End HasValidb.

(** **** Intermediate constraint for valid properties (with Prop and boolean) *)
Module Type HasValidFull (Import T : EqualityType) (Import V : HasValid T) <: HasValidb T.

Include HasValidb T.

Section properties.

Variable k : Lvl.t.
Variable t : t.

Parameter validb_valid  : validb k t = true  <->   valid k t. 
Parameter validb_nvalid : validb k t = false <-> ~ valid k t. 

End properties.

End HasValidFull.

(** ***  Shift function

  Like indices, we will often shift levels. Consequently, we ask to the user to define a [shift] function. This function 
  takes three arguments: the lower bound [lb], the shift [k] and the leveled element [t]. The lower bound has the same 
  meaning that the one in the [valid] property. In lambda calculus, we can say that we shift only bound variables knowing
  a certain number of free variables. It is a main difference with indices. Indeed, free variables have a fix level 
  defined. Thus, no need to shift them.
  For instance, the shift function interacts as shown below with the levels.
<<
shift 0 2 2 = 4
shift 3 2 2 = 2
shift 65 0 98 = 98
>>

  In a lambda calculus term, we can see the use of [lb].
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

Parameter shift_zero_refl : eq (shift lb 0 t) t.
Parameter shift_trans     : eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Parameter shift_permute   : eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Parameter shift_unfold    : eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Parameter shift_unfold_1  :
  k <= k' -> k' <= k'' -> eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).

#[export] 
Declare Instance shift_eq : Proper (Lvl.eq ==> Lvl.eq ==> eq ==> eq) shift.
Parameter shift_eq_iff    : eq t t' <-> eq (shift lb k t) (shift lb k t').

End properties.

End HasShift.

(** ---- *)


(** ** Leveled Module Type 

  A type [t] that uses levels have to implements this module type.

*)
Module Type IsLeveled (Import T : EqualityType) <: HasShift T <: HasValid T.

Include HasShift T <+ HasValid T.

Section properties.

  Variable lb lb' k k' : Lvl.t.
  Variable t : t.

  Parameter shift_preserves_valid_gen :  
    k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb ->
    valid lb t -> valid lb' (shift k (k' - k) t).
  Parameter shift_preserves_valid   : valid k t -> valid (k + k') (shift k k' t).
  Parameter shift_preserves_valid_1 : valid k t -> valid (k + k') (shift lb k' t).
  Parameter shift_preserves_valid_2 : lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
  Parameter shift_preserves_valid_zero : valid k t -> valid k (shift k 0 t).

End properties.

End IsLeveled.


(** ** Bindless Leveled Module Type

  A type [t] that uses levels without binders has a specific property. The [shift] function did not
  impact the type if it shares the same lower bound with the [valid] property.
  This kind of types is common actually. A set, a map or a pair does not imply binders.

*)
Module Type IsBindlessLeveled (Import T : EqualityType) <: IsLeveled T.

Include IsLeveled T.

Parameter shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.

End IsBindlessLeveled.

Module Type IsBindlessLeveledEx (Import T : EqualityType) (Import IsLvl : IsLeveled T).

Parameter shift_valid_refl : forall lb k t, valid lb t -> eq (shift lb k t) t.

End IsBindlessLeveledEx.


(** ---- *)


(** ** Interfaces with _leibniz equality_ extension *)

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


(** ---- *)


(** ** Collection of starter interfaces *)

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