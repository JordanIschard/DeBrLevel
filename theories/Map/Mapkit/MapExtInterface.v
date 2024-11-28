Require Import Arith.PeanoNat MSets.
From DeBrLevel Require Import Level.
From MMaps Require Import MMaps.

(** * Interface - [MMaps] extension *)

(** ** Extension of [MMaps] with new functions [Submap] and [For_all] *)
Module Type MapInterface (Key : OrderedTypeWithLeibniz) (Data : EqualityType)  
                                                        (M : Interface.S Key) <: EqualityType.

Module OP := Facts.OrdProperties Key M.
Import OP.P.

(** *** Definitions *)

Definition t : Type := M.t Data.t.
Definition eq := @M.Equal Data.t.

Parameter Submap : t -> t -> Prop. 
Parameter For_all : (Key.t -> Data.t -> Prop) -> t -> Prop.

(** *** Specifications *)
Section specifications.

Variable x : Key.t.
Variable e e' : Data.t.
Variable m m' m1 : t.

(** **** [eq] specification *)

#[export] Declare Instance eq_equiv : Equivalence eq.

(** **** [Empty] specifications extension *)

#[export] Declare Instance Empty_eq_iff : Proper (eq ==> iff) Empty.

Parameter Empty_eq : Empty m -> eq m M.empty.

Parameter notEmpty_Add : Add x e m m' -> ~ Empty m'.

Parameter notEmpty_find : Empty m -> ~ (M.find x m = Some e).

(** **** [is_empty] specifications extension *)

Parameter is_empty_Add : Add x e m m' -> M.is_empty m' = false.

Parameter is_empty_add : M.is_empty (M.add x e m) = false.

(** **** [Add] specifications extension *)

#[export] Declare Instance Add_eq_iff: 
  Proper (Key.eq ==> eq ==> eq ==> iff) (fun (k : Key.t) => Add k e).

(** **** [add] specifications extension *)

Parameter add_shadow : eq (M.add x e (M.add x e' m)) (M.add x e m). 

Parameter add_remove : M.find x m = Some e -> eq m (M.add x e (M.remove x m)).

(** **** [Submap] specifications extension *)

Parameter Submap_Empty_bot : Empty m -> Submap m m'.

Parameter Submap_Empty : Submap m m' -> Empty m' -> Empty m.

Parameter Submap_empty_bot : Submap M.empty m.

Parameter Submap_Add : Submap m' m1 -> ~ M.In x m -> Add x e m m' -> Submap m m1.

Parameter Submap_Add_in : Submap m' m1 -> ~ M.In x m -> Add x e m m' -> M.In x m1.

Parameter Submap_Add_find : Submap m' m1 -> ~ M.In x m -> Add x e m m' ->  M.find x m1 = Some e.

Parameter Submap_Add_1 : Submap m m1 ->
                         ~ M.In x m -> M.find x m1 = Some e -> Add x e m m' -> Submap m' m1.

Parameter Submap_add : Submap m m' -> Submap (M.add x e m) (M.add x e m').

Parameter Submap_add_2 : ~ M.In x m -> Submap (M.add x e m) m' -> Submap m m'.

Parameter Submap_add_1 : ~ M.In x m' -> Submap m m' -> Submap m (M.add x e m').

Parameter Submap_in :  Submap m m' -> M.In x m -> M.In x m'.

Parameter Submap_notin : Submap m m' -> ~M.In x m' -> ~M.In x m.

Parameter Submap_find : Submap m m' -> M.find x m = Some e -> M.find x m' = Some e.

#[export] Declare Instance Submap_refl : Reflexive Submap.

#[export] Declare Instance Submap_trans : Transitive Submap.

#[export] Declare Instance Submap_eq : Proper (eq ==> eq ==> iff) Submap.

#[export] Declare Instance Submap_po : PreOrder Submap.

(** **** [For_all] specifications *)

Hypothesis P : Key.t -> Data.t -> Prop. 

Parameter For_all_empty : For_all P M.empty.

Parameter For_all_Empty : Empty m -> For_all P m.

Parameter For_all_add : P x e /\ For_all P m -> For_all P (M.add x e m).

Parameter For_all_add_notin : ~ M.In x m -> ((P x e /\ For_all P m) <-> For_all P (M.add x e m)).

#[export] Declare Instance For_all_proper : Proper (eq ==> iff) (For_all P).

End specifications.

End MapInterface.


(** ---- *)


(** ** Extension of [MMaps] with new functions [max_key] and [new_key] *)
Module Type MapLVLInterface (Data : EqualityType) 
                                (M : Interface.S Level) <: MapInterface Level Data M.

Include MapInterface Level Data M.
Import OP.P.

(** *** Definitions *)

Parameter max_key : t -> nat.
Parameter new_key : t -> nat.

(** *** Specifications *)
Section specs.

Variable x : M.key.
Variable v v' : Data.t.
Variable m m' : t.

(** **** [max_key] specifications *)

#[export] Declare Instance max_key_eq : Proper (eq ==> Logic.eq) max_key.

Parameter max_key_ub : x > max_key m -> for_all_dom (fun y => y <? x) m = true.

Parameter max_key_Empty : Empty m -> max_key m = 0.

Parameter max_key_empty : max_key M.empty = 0.
(* begin hide *)
(* 
Parameter max_key_Add_spec : Add x v m m' ->
    (max_key m' = x /\ max_key m <= x) \/ (max_key m' = max_key m /\ max_key m > x). *)
(* end hide *)

Parameter max_key_Add_l : Add x v m m' ->  max_key m <= x -> max_key m' = x.

Parameter max_key_Add_r : Add x v m m' ->  max_key m > x -> max_key m' = max_key m.

Parameter max_key_Add_max : Add x v m m' -> max_key m' = max x (max_key m).
(* begin hide *)
(* Parameter max_key_add_spec :
  ~M.In x m -> (max_key (M.add x v m) = x /\ max_key m <= x) \/ 
               (max_key (M.add x v m) = max_key m /\ max_key m > x). *)
(* end hide *)

Parameter max_key_add_l : max_key m <= x -> max_key (M.add x v m) = x.

Parameter max_key_add_r : max_key m > x -> max_key (M.add x v m) = max_key m.

Parameter max_key_add_in : M.In x m -> (max_key (M.add x v m)) = (max_key m).

Parameter max_key_add_iff : max_key m = max_key m' -> 
                            max_key (M.add x v m) = max_key (M.add x v' m').

Parameter max_key_add_max_key : max_key (M.add (S (max_key m)) v m) = S (max_key m).

Parameter max_key_add_max : max_key (M.add x v m) = max x (max_key m).

Parameter max_key_notin : x > max_key m -> ~ M.In x m.

Parameter max_key_in : M.In x m -> x <= (max_key m).

Parameter max_key_Submap : Submap m m' -> max_key m <= max_key m'.

(** **** [new_key] specifications *)

#[export] Declare Instance new_key_eq : Proper (eq ==> Logic.eq) new_key.

Parameter new_key_geq_max_key : new_key m >= max_key m. 

Parameter new_key_unfold : new_key m = if M.is_empty m then 0 else S (max_key m).

Parameter new_key_Empty : Empty m -> new_key m = 0.

Parameter new_key_empty : new_key M.empty = 0.
(* begin hide *)
(* 
Parameter new_key_Add_spec : ~M.In x m -> Add x v m m' ->
    (new_key m' = S x /\ new_key m <= S x) \/ (new_key m' = new_key m /\ new_key m > S x).
*)
(* end hide *)

Parameter new_key_Add_l : Add x v m m' ->  new_key m <= S x -> new_key m' = S x.

Parameter new_key_Add_r : Add x v m m' ->  new_key m > S x -> new_key m' = new_key m.

Parameter new_key_Add_max : Add x v m m' -> new_key m' = max (S x) (new_key m).
(* begin hide *)
(* Parameter new_key_add_spec :
  ~M.In x m -> (new_key (M.add x v m) = S x /\ new_key m <= S x) \/ 
               (new_key (M.add x v m) = new_key m /\ new_key m > S x).*)
(* end hide *)

Parameter new_key_add_max : new_key (M.add x v m) = max (S x) (new_key m).

Parameter new_key_add_l : new_key m <= S x -> new_key (M.add x v m) = S x.

Parameter new_key_add_r : new_key m > S x -> new_key (M.add x v m) = new_key m.

Parameter new_key_add_in : M.In x m -> (new_key (M.add x v m)) = (new_key m).

Parameter new_key_add_new_key : new_key (M.add (new_key m) v m) = S (new_key m).

Parameter new_key_notin : x >= new_key m -> ~ M.In x m.

Parameter new_key_in : M.In x m -> x < new_key m.

Parameter new_key_Submap : Submap m m' -> new_key m <= new_key m'.

Parameter new_key_Submap_add : Submap m m' -> 
                               Submap m (M.add (S (new_key m')) v (M.add (new_key m') v' m')).

End specs.

End MapLVLInterface.