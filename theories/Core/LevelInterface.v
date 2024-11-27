From Coq Require MSets Structures.Equalities Structures.Orders.
Import Structures.Equalities Structures.Orders.

(** * Interface - Level 

  De-Bruijn has proposed a variation of the lambda calculus which instanciates variables in a determinisc way. It defines two measures: the distance and the level. The distance, latter called index, is the number of abstraction between a variable and its binder. The level is the number of abstraction encountered since the root of the representative tree of a term.

  For instance, λx.(λy.(x y) x) is equal to λ.(λ.(1 0) 0) with distances and λ.(λ.(0 1) 0) with levels.

  This kind of representations are extremely simple and can be used in different context as well as be embedded in data types or data structures.
*)

(** ** Level - Definition

  A level itself only requires to be ordered. We require also a ground value and classic arithmetic operators on it. Thus, we define a level as a [Nat].

*)
Module Lvl <: Orders.OrderedTypeFull := Structures.OrdersEx.Nat_as_OT.

(** ---- *)

(** ** Well-formedness and Shift interfaces 

  We split the definition of an element that used levels in different module types. First, we want to be as flexible as possible. Second, each modules types carries an additional set of constraints.

  We define a function called [shift] and a property called [Wf]. It is the minimal set of elements for working with levels. Their principles ared defined below.
*)

(** *** Well-formedness

  If we define an inductive type as containing levels, the questioning about the well-formation or ill-formation appears. Thus we suppose a property [Wf], defined by the user later, which is satisfied if the instanciation is well-formed.

  What is a well-formed type? If we take the most basic case, a level, when can we state that a level is well-formed or not ? We can only talk about a well-formed level regards of a lower bound [m]. 

  We use the case of the lambda calculus to illustrate it. Consider the term "x", the variable is free. Thus, how do we state that it is a well-formed term? We suppose that "x" is defined in a certain context. Now, consider the term "λx.(x y)". "y" is free and "x" bound. The term is well-formed if "y" is defined in a certain context. The lower bound can be here understood as 
  the number of free variables.
*)

(** **** [Wf] property interface *)
Module Type IsWF (Import T : EqualityType).

Parameter Wf : Lvl.t -> t -> Prop.

Parameter Wf_weakening : forall (m n: Lvl.t) (t: t), Lvl.le m n -> Wf m t -> Wf n t.

#[export] Declare Instance Wf_iff : Proper (Lvl.eq ==> eq ==> iff) Wf.

End IsWF.


(** **** Boolean version of [Wf] named [is_wf] *)
Module Type IsWFb (Import T : EqualityType).

Parameter is_wf : Lvl.t -> t -> bool.

#[export] Declare Instance is_wf_eq : Proper (Lvl.eq ==> eq ==> Logic.eq) is_wf.

End IsWFb.

(** **** [Wf] property with its boolean version [is_wf] *)
Module Type IsWFFull (Import T : EqualityType) (Import V : IsWF T) <: IsWFb T.

Include IsWFb T.

Section specifications.

Variable k : Lvl.t.
Variable t : t.

Parameter Wf_is_wf_true : Wf k t <-> is_wf k t = true. 
Parameter notWf_is_wf_false : ~ Wf k t <-> is_wf k t = false. 

End specifications.

End IsWFFull.

(** ***  Shift function

  Like indices, we will often shift levels. Consequently, we ask to the user to define a [shift] function. This function takes three arguments: the lower bound [m], the shift [k] and the leveled element [t]. The lower bound has the same meaning that the one in the [Wf] property. In lambda calculus, we can say that we shift only bound variables knowing a certain number of free variables. It is a main difference with indices. Indeed, free variables have a fix level defined. Thus, no need to shift them. For instance, the shift function interacts as shown below with the levels.
<<
shift 0 2 2 = 4
shift 3 2 2 = 2
shift 65 0 98 = 98
>>

  In a lambda calculus term, we can see the use of [m].
<<
shift 1 3 (\. 0 1) = (\. 0 4)
>>
*)

(** **** [shift] function interface *)
Module Type HasShift (Import T : EqualityType).

Parameter shift : Lvl.t -> Lvl.t -> t -> t.

Section specifications.

Variable m n k p : Lvl.t.
Variable t t' : t.

Parameter shift_zero_refl : eq (shift m 0 t) t.
Parameter shift_trans     : eq (shift m n (shift m k t)) (shift m (n + k) t).
Parameter shift_permute   : eq (shift m n (shift m k t)) (shift m k (shift m n t)).
Parameter shift_unfold    : eq (shift m (n + k) t) (shift (m + n) k (shift m n t)). 
Parameter shift_unfold_1  : n <= k -> k <= p -> 
                            eq (shift k (p - k) (shift n  (k - n) t)) (shift n (p - n) t).
Parameter shift_eq_iff    : eq t t' <-> eq (shift m k t) (shift m k t').

#[export] Declare Instance shift_eq : Proper (Lvl.eq ==> Lvl.eq ==> eq ==> eq) shift.

End specifications.

End HasShift.

(** ---- *)


(** ** Leveled Module Type 

  A type [t] that uses levels have to implements this module type.

*)
Module Type IsLeveled (Import T : EqualityType) <: HasShift T <: IsWF T.

Include HasShift T <+ IsWF T.

Section specifications.

Variable m n k p : Lvl.t.
Variable t : t.

Parameter shift_preserves_wf_gen :
  k <= p -> m <= n -> k <= m -> p <= n -> p - k = n - m ->
  Wf m t -> Wf n (shift k (p - k) t).
Parameter shift_preserves_wf   : Wf k t -> Wf (k + p) (shift k p t).
Parameter shift_preserves_wf_1 : Wf k t -> Wf (k + p) (shift m p t).
Parameter shift_preserves_wf_2 : m <= n -> Wf m t -> Wf n (shift m (n - m) t).
Parameter shift_preserves_wf_zero : Wf k t -> Wf k (shift k 0 t).

End specifications.

End IsLeveled.


(** ** Bindless Leveled Module Type

  A type [t] that uses levels without binders has a specific property. The [shift] function did not
  impact the type if it shares the same lower bound with the [Wf] property.
  This kind of types is common actually. A set, a map or a pair does not imply binders.

*)
Module Type IsBindlessLeveled (Import T : EqualityType) <: IsLeveled T.

Include IsLeveled T.

Parameter shift_wf_refl : forall m k t, Wf m t -> eq (shift m k t) t.

End IsBindlessLeveled.

Module Type IsBindlessLeveledEx (Import T : EqualityType) (Import IsLvl : IsLeveled T).

Parameter shift_wf_refl : forall m k t, Wf m t -> eq (shift m k t) t.

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

Module Type IsLeveledFullET := IsLeveledET <+ IsWFFull.
Module Type IsLeveledFullETWithLeibniz := IsLeveledETWithLeibniz <+ IsWFFull.
Module Type IsBindlessLeveledFullET := IsBindlessLeveledET <+ IsWFFull.
Module Type IsBindlessLeveledFullETWithLeibniz := IsBindlessLeveledETWithLeibniz <+ IsWFFull.

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

Module Type IsLeveledFullDT := IsLeveledDT <+ IsWFFull.
Module Type IsLeveledFullDTWithLeibniz := IsLeveledDTWithLeibniz <+ IsWFFull.
Module Type IsBindlessLeveledFullDT := IsBindlessLeveledDT <+ IsWFFull.
Module Type IsBindlessLeveledFullDTWithLeibniz := IsBindlessLeveledDTWithLeibniz <+ IsWFFull.

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

Module Type IsLeveledFullOT := IsLeveledOT <+ IsWFFull.
Module Type IsLeveledFullOTWithLeibniz := IsLeveledOTWithLeibniz <+ IsWFFull.
Module Type IsBindlessLeveledFullOT := IsBindlessLeveledOT <+ IsWFFull.
Module Type IsBindlessLeveledFullOTWithLeibniz := IsBindlessLeveledOTWithLeibniz <+ IsWFFull.

Module Type IsLvlOT := IsLeveledOT.
Module Type IsLvlOTWL := IsLeveledOTWithLeibniz.
Module Type IsLvlFullOT := IsLeveledFullOT.
Module Type IsLvlFullOTWL := IsLeveledFullOTWithLeibniz.

Module Type IsBdlLvlOT := IsBindlessLeveledOT.
Module Type IsBdlLvlOTWL := IsBindlessLeveledOTWithLeibniz.
Module Type IsBdlLvlFullOT := IsBindlessLeveledFullOT.
Module Type IsBdlLvlFullOTWL := IsBindlessLeveledFullOTWithLeibniz.