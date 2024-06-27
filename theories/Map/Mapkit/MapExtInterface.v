Require Import Arith.PeanoNat MSets.
From DeBrLevel Require Import Level.
From MMaps Require Import MMaps.


Module Type MapInterface   (Key : OrderedTypeWithLeibniz) 
                           (Data : EqualityType) 
                           (M : Interface.S Key) <: EqualityType.

Module OP := Facts.OrdProperties Key M.
Import OP.P.

Section definition.

Definition t : Type := M.t Data.t.
Definition eq := @M.Equal Data.t.
#[global]
Declare Instance eq_equiv : Equivalence eq.
Parameter Submap : t -> t -> Prop. 

End definition.

Section general.

Parameter Empty_eq_spec : forall (m m' : t), eq m m' -> Empty m <-> Empty m'.
Parameter Empty_eq_spec_1 : forall (m : t), Empty m -> eq m M.empty.
Parameter notEmpty_Add_spec : forall (m m' : t) x e, Add x e m m' -> ~ Empty m'.
Parameter notEmpty_find_spec : forall (m : t) x e, Empty m -> ~ (M.find x m = Some e).
Parameter is_empty_Add_spec : forall (m m' : t) x e, Add x e m m' -> M.is_empty m' = false.
Parameter is_empty_add_spec : forall (m : t) x e, M.is_empty (M.add x e m) = false.
Parameter Add_eq_spec : forall (n m m' : t) x v, eq m m' -> Add x v n m <-> Add x v n m'.
Parameter add_shadow : forall m x v v', eq (M.add x v (M.add x v' m)) (M.add x v m). 
Parameter add_remove_spec : forall (m : t) x v, M.find x m = Some v -> eq m (M.add x v (M.remove x m)).

End general.

Section submap.

Parameter Submap_Empty_spec : forall (m m' : t), Empty m -> Submap m m'.
Parameter Submap_Empty_spec_1 : forall (m m' : t), Submap m m' -> Empty m' -> Empty m.
Parameter Submap_empty_spec : forall (m : t), Submap M.empty m.
Parameter Submap_Add_spec : forall (m1 m m' : t) x v,
Submap m' m1 -> ~ M.In x m -> Add x v m m' -> Submap m m1.
Parameter Submap_Add_spec_1 : forall (m1 m m' : t) x v,
Submap m' m1 -> ~ M.In x m -> Add x v m m' -> M.In x m1.
Parameter Submap_Add_spec_1' : forall (m1 m m' : t) x v,
Submap m' m1 -> ~ M.In x m -> Add x v m m' ->  M.find x m1 = Some v.
Parameter Submap_Add_spec_2 : forall (m1 m m' : t) x v,
Submap m m1 -> ~ M.In x m -> M.find x m1 = Some v -> Add x v m m' -> Submap m' m1.
Parameter Submap_add_spec : forall (m m' : t) x v, Submap m m' -> Submap (M.add x v m) (M.add x v m').
Parameter Submap_add_spec_1 : forall (m m' : t) x v, ~ M.In x m' -> Submap m m' -> Submap m (M.add x v m').
Parameter Submap_in_spec :  forall (m m' : t) x, Submap m m' -> M.In x m -> M.In x m'.
Parameter Submap_notin_spec : forall (m m' : t) x, Submap m m' -> ~M.In x m' -> ~M.In x m.
Parameter Submap_find_spec : forall (m m' : t) x v, Submap m m' -> M.find x m = Some v -> M.find x m' = Some v.
Parameter Submap_refl : Reflexive Submap.
Parameter Submap_trans : Transitive Submap.
Parameter Submap_eq_left_spec : forall (m m' m1 : t), eq m m' -> Submap m m1 <-> Submap m' m1.
Parameter Submap_eq_right_spec : forall (m m' m1 : t), eq m m' -> Submap m1 m <-> Submap m1 m'.
Parameter Submap_po : PreOrder Submap.

End submap.

End MapInterface.

Module Type MapLVLInterface (Data : EqualityType) 
                                (M : Interface.S Level) <: MapInterface Level Data M.

Include MapInterface Level Data M.
Import OP.P.

Section definition.

Parameter max_key : t -> nat.
Parameter new_key : t -> nat.

End definition.

Section max.

Parameter max_key_eq : Proper (eq ==> Logic.eq) max_key.
Parameter max_key_Empty_spec : forall (m : t), Empty m -> max_key m = 0.
Parameter max_key_empty_spec : max_key M.empty = 0.
Parameter max_key_Add_spec : forall (m m' : t) x v,
  ~M.In x m -> Add x v m m' ->
    (max_key m' = x /\ max_key m <= x) \/ (max_key m' = max_key m /\ max_key m > x).
Parameter max_key_Add_spec_1 : forall (m m' : t) x v,
  ~M.In x m -> Add x v m m' ->  max_key m <= x -> max_key m' = x.
Parameter max_key_Add_spec_2 : forall (m m' : t) x v,
  ~M.In x m -> Add x v m m' ->  max_key m > x -> max_key m' = max_key m.
Parameter max_key_add_spec : forall (m : t) x v,
  ~M.In x m -> (max_key (M.add x v m) = x /\ max_key m <= x) \/ 
                (max_key (M.add x v m) = max_key m /\ max_key m > x).
Parameter max_key_add_spec_1 : forall (m : t) x v,
  ~M.In x m -> max_key m <= x -> max_key (M.add x v m) = x.
Parameter max_key_add_spec_2 : forall (m : t) x v,
  ~M.In x m -> max_key m > x -> max_key (M.add x v m) = max_key m.
Parameter max_key_add_spec_3 : forall (m: t) x v,
  M.In x m -> (max_key (M.add x v m)) = (max_key m).
Parameter max_key_add_spec_4 : forall (m m' : t) x v v',
  ~M.In x m -> ~M.In x m' ->
  max_key m = max_key m' -> max_key (M.add x v m) = max_key (M.add x v' m').
Parameter max_key_ub_spec : forall (m : t) x, x > max_key m -> for_all_dom (fun y => y <? x) m = true.
Parameter max_key_notin_spec : forall (m : t) x, x > max_key m -> ~ M.In x m.
Parameter max_key_add_max_key_spec : forall (m : t) v,
  max_key (M.add (S (max_key m)) v m) = S (max_key m).
Parameter max_key_Submap_spec : forall (m m' : t),
  Submap m m' -> max_key m <= max_key m'.
Parameter  max_key_in_spec : forall (m : t) x, M.In x m -> x <= (max_key m).

End max.

Section new.

Parameter new_key_unfold : forall (m : t), new_key m = if M.is_empty m then 0 else S (max_key m).
Parameter new_key_eq : Proper (eq ==> Logic.eq) new_key.
Parameter new_key_Empty_spec : forall (m : t), Empty m -> new_key m = 0.
Parameter new_key_empty_spec : new_key M.empty = 0.
Parameter new_key_geq_max_key : forall (m : t), new_key m >= max_key m. 
Parameter new_key_Add_spec : forall (m m' : t) x v,
  ~M.In x m -> Add x v m m' ->
    (new_key m' = S x /\ new_key m <= S x) \/ (new_key m' = new_key m /\ new_key m > S x).
Parameter new_key_add_spec : forall (m : t) x v,
  ~M.In x m -> (new_key (M.add x v m) = S x /\ new_key m <= S x) \/ 
                (new_key (M.add x v m) = new_key m /\ new_key m > S x).
Parameter new_key_add_spec_2 : forall (m : t) x v,
  ~M.In x m -> new_key m > S x -> new_key (M.add x v m) = new_key m.
Parameter new_key_add_spec_1 : forall (m : t) x v,
  ~M.In x m -> new_key m <= S x -> new_key (M.add x v m) = S x.
Parameter new_key_add_spec_3 : forall (m: t) x v,
  M.In x m -> (new_key (M.add x v m)) = (new_key m).
Parameter new_key_notin_spec : forall (m : t) x, x >= new_key m -> ~ M.In x m.
Parameter new_key_in_spec : forall (m : t) x, M.In x m -> x < new_key m.
Parameter new_key_add_new_key_spec : forall (m : t) v,
  new_key (M.add (new_key m) v m) = S (new_key m).
Parameter new_key_Submap_spec : forall (m' m : t),
  Submap m m' -> new_key m <= new_key m'.
Parameter new_key_Submap_spec_1 : forall (m' m : t) v v',
  Submap m m' -> Submap m (M.add (S (new_key m')) v (M.add (new_key m') v' m')).

End new.

End MapLVLInterface.