From Coq Require Import MSets Classical_Prop.

(** * Interface - [MSet] extension *)

(** ** Extension of [MSet] *)
Module Type SetOTWithLeibnizInterface (T : MSetList.OrderedTypeWithLeibniz) 
            <: Structures.Orders.OrderedType <: MSetList.SWithLeibniz.

Include MSetList.MakeWithLeibniz T.
Include MSetProperties.WPropertiesOn T.

(** *** Definitions *)
Parameter ltb :  t -> t -> bool.
Parameter map : (elt -> elt) -> t -> t.

(** *** Specifications *)
Section specs.

Variable x y : elt.
Variable s s' : t.

(** **** Some facts *)

Parameter Add_inv : Add x s s' -> add x s = s'.

#[export] Declare Instance proper_1 : forall f,
  Proper (T.eq ==> eq ==> eq) (fun (r0 : elt) (acc : t) => add (f r0) acc).

Parameter transpose_1 : forall f,
 transpose eq (fun (r0 : elt) (acc : t) => add (f r0) acc).

(** **** [eq] and [lt] specifications *)

Parameter eqb_refl : equal s s = true.

Parameter add_eq_leibniz :
  ~ In x s -> ~ In x s' -> s = s' <-> (add x s) = (add x s').

Parameter ltb_lt : ltb s s' = true <-> lt s s'.

Parameter gt_neq_nlt : ~ eq s s' -> ~ lt s s' -> lt s' s.

(** **** [In] specifications *)

Parameter diff_in_add_spec : In x s' -> (diff (add x s) s') = (diff s s').

Parameter union_add_spec : (union (add x s) s') =  add x (union s s').

Parameter inter_in_add_spec : In x s' -> (inter (add x s) s') = add x (inter s s').

Parameter diff_notin_add_spec : ~ In x s' -> (diff (add x s) s') = add x (diff s s').

Parameter inter_notin_add_spec : ~ In x s' -> (inter (add x s) s') =  (inter s s').

Parameter add_notin_spec : ~ In x (add y s) <-> x <> y /\ ~ In x s.

Parameter union_notin_spec : ~ In x (union s s') <-> ~ In x s /\ ~ In x s'.

Parameter diff_notin_spec : ~ In x (diff s s') <-> ~ In x s \/ In x s'.

Parameter singleton_notin_spec : ~ In x (singleton  y) <-> x <> y.

(** **** [map] specifications *)

Variable f : elt -> elt.

Parameter map_Empty_spec : Empty s -> map f s = empty.

Parameter map_empty_spec : map f empty = empty.

Parameter map_singleton_spec : map f (singleton x) = singleton (f x).

Parameter map_in_spec : In x s -> In (f x) (map f s).

Parameter map_add_notin_spec : ~ In x s -> map f (add x s) = add (f x) (map f s).

Parameter map_add_in_spec : In x s -> map f (add x s) = (map f s).

Parameter map_union_spec : (map f (union s s')) = union (map f s) (map f s').

End specs.

End SetOTWithLeibnizInterface.