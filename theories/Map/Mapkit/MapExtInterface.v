Require Import Arith.PeanoNat MSets.
From DeBrLevel Require Import Level.
From MMaps Require Import MMaps.


Module Type MapInterface   (Key : OrderedTypeWithLeibniz) 
                           (Data : EqualityType) 
                           (M : Interface.S Key) <: EqualityType.

Module OP := Facts.OrdProperties Key M.
Import OP.P.

(** ** Definition *)

Definition t : Type := M.t Data.t.
Definition eq := @M.Equal Data.t.

#[export] Declare Instance eq_equiv : Equivalence eq.

Parameter Submap : t -> t -> Prop. 

Section property.

Variable m m' m1 : t.
Variable x : Key.t.
Variable e e' : Data.t.

(** ** [Empty] properties extension *)

#[export] Declare Instance Empty_eq_iff : Proper (eq ==> iff) Empty.
Parameter Empty_eq_spec : Empty m -> eq m M.empty.
Parameter notEmpty_Add_spec : Add x e m m' -> ~ Empty m'.
Parameter notEmpty_find_spec : Empty m -> ~ (M.find x m = Some e).

(** ** [is_empty] properties extension *)

Parameter is_empty_Add_spec : Add x e m m' -> M.is_empty m' = false.
Parameter is_empty_add_spec : M.is_empty (M.add x e m) = false.

(** ** [Add] properties extension *)

#[export] Declare Instance Add_eq_iff: 
  Proper (Key.eq ==> eq ==> eq ==> iff) (fun (k : Key.t) => Add k e).

(** ** [add] properties extension *)

Parameter add_shadow : eq (M.add x e (M.add x e' m)) (M.add x e m). 
Parameter add_remove_spec : M.find x m = Some e -> eq m (M.add x e (M.remove x m)).

(** ** [Submap] properties extension *)

Parameter Submap_Empty_bot : Empty m -> Submap m m'.
Parameter Submap_Empty_spec : Submap m m' -> Empty m' -> Empty m.
Parameter Submap_empty_bot : Submap M.empty m.

Parameter Submap_Add_spec :
  Submap m' m1 -> ~ M.In x m -> Add x e m m' -> Submap m m1.
Parameter Submap_Add_in_spec :
  Submap m' m1 -> ~ M.In x m -> Add x e m m' -> M.In x m1.
Parameter Submap_Add_find_spec :
  Submap m' m1 -> ~ M.In x m -> Add x e m m' ->  M.find x m1 = Some e.
Parameter Submap_Add_spec_1 :
  Submap m m1 -> ~ M.In x m -> M.find x m1 = Some e -> Add x e m m' -> Submap m' m1.

Parameter Submap_add_spec : Submap m m' -> Submap (M.add x e m) (M.add x e m').
Parameter Submap_add_spec_1 : ~ M.In x m' -> Submap m m' -> Submap m (M.add x e m').

Parameter Submap_in_spec :  Submap m m' -> M.In x m -> M.In x m'.
Parameter Submap_notin_spec : Submap m m' -> ~M.In x m' -> ~M.In x m.
Parameter Submap_find_spec : Submap m m' -> M.find x m = Some e -> M.find x m' = Some e.

#[export] Declare Instance Submap_refl : Reflexive Submap.
#[export] Declare Instance Submap_trans : Transitive Submap.
#[export] Declare Instance Submap_eq : Proper (eq ==> eq ==> iff) Submap.
#[export] Declare Instance Submap_po : PreOrder Submap.

End property.

End MapInterface.

Module Type MapLVLInterface (Data : EqualityType) 
                                (M : Interface.S Level) <: MapInterface Level Data M.

Include MapInterface Level Data M.
Import OP.P.

(** ** Definition *)

Parameter max_key : t -> nat.
Parameter new_key : t -> nat.


Section property.

Variable m m' : t.
Variable x : M.key.
Variable v v' : Data.t.

(** ** [max_key] properties *)

#[export] Declare Instance max_key_eq : Proper (eq ==> Logic.eq) max_key.
Parameter max_key_ub_spec : x > max_key m -> for_all_dom (fun y => y <? x) m = true.

(** *** [max_key] interaction properties with empty maps *)

Parameter max_key_Empty_spec : Empty m -> max_key m = 0.
Parameter max_key_empty_spec : max_key M.empty = 0.

(** *** [max_key] interaction properties with [Add] property *)

Parameter max_key_Add_spec : ~M.In x m -> Add x v m m' ->
    (max_key m' = x /\ max_key m <= x) \/ (max_key m' = max_key m /\ max_key m > x).
Parameter max_key_Add_ge_spec :
  ~M.In x m -> Add x v m m' ->  max_key m <= x -> max_key m' = x.
Parameter max_key_Add_lt_spec :
  ~M.In x m -> Add x v m m' ->  max_key m > x -> max_key m' = max_key m.

(** *** [max_key] interaction properties with [add] function *)

Parameter max_key_add_spec :
  ~M.In x m -> (max_key (M.add x v m) = x /\ max_key m <= x) \/ 
               (max_key (M.add x v m) = max_key m /\ max_key m > x).
Parameter max_key_add_ge_spec :
  ~M.In x m -> max_key m <= x -> max_key (M.add x v m) = x.
Parameter max_key_add_lt_spec :
  ~M.In x m -> max_key m > x -> max_key (M.add x v m) = max_key m.
Parameter max_key_add_in_spec :
  M.In x m -> (max_key (M.add x v m)) = (max_key m).
Parameter max_key_add_spec_1 :
  ~M.In x m -> ~M.In x m' ->
  max_key m = max_key m' -> max_key (M.add x v m) = max_key (M.add x v' m').
Parameter max_key_add_max_spec :
  max_key (M.add (S (max_key m)) v m) = S (max_key m).

(** *** [max_key] interaction properties with [In] property *)

Parameter max_key_notin_spec : x > max_key m -> ~ M.In x m.
Parameter  max_key_in_spec : M.In x m -> x <= (max_key m).

(** *** [max_key] interaction properties with [Submap] property *)

Parameter max_key_Submap_spec :
  Submap m m' -> max_key m <= max_key m'.

(** ** [new_key] properties *)

#[export] Declare Instance new_key_eq : Proper (eq ==> Logic.eq) new_key.
Parameter new_key_geq_max_key : new_key m >= max_key m. 
Parameter new_key_unfold : new_key m = if M.is_empty m then 0 else S (max_key m).

(** *** [new_key] interaction properties with empty maps *)

Parameter new_key_Empty_spec : Empty m -> new_key m = 0.
Parameter new_key_empty_spec : new_key M.empty = 0.

(** *** [new_key] interaction properties with [Add] property *)

Parameter new_key_Add_spec : ~M.In x m -> Add x v m m' ->
    (new_key m' = S x /\ new_key m <= S x) \/ (new_key m' = new_key m /\ new_key m > S x).
Parameter new_key_Add_ge_spec :
  ~M.In x m -> Add x v m m' ->  new_key m <= S x -> new_key m' = S x.
Parameter new_key_Add_lt_spec :
  ~M.In x m -> Add x v m m' ->  new_key m > S x -> new_key m' = new_key m.

(** *** [new_key] interaction properties with [add] function *)

Parameter new_key_add_spec :
  ~M.In x m -> (new_key (M.add x v m) = S x /\ new_key m <= S x) \/ 
               (new_key (M.add x v m) = new_key m /\ new_key m > S x).
Parameter new_key_add_lt_spec :
  ~M.In x m -> new_key m > S x -> new_key (M.add x v m) = new_key m.
Parameter new_key_add_ge_spec :
  ~M.In x m -> new_key m <= S x -> new_key (M.add x v m) = S x.
Parameter new_key_add_in_spec :
  M.In x m -> (new_key (M.add x v m)) = (new_key m).
Parameter new_key_add_new_key_spec :
  new_key (M.add (new_key m) v m) = S (new_key m).

(** *** [new_key] interaction properties with [In] property *)

Parameter new_key_notin_spec : x >= new_key m -> ~ M.In x m.
Parameter new_key_in_spec : forall (m : t) x, M.In x m -> x < new_key m.

(** *** [new_key] interaction properties with [Submap] property *)

Parameter new_key_Submap_spec :
  Submap m m' -> new_key m <= new_key m'.
Parameter new_key_Submap_add_spec :
  Submap m m' -> Submap m (M.add (S (new_key m')) v (M.add (new_key m') v' m')).

End property.

End MapLVLInterface.