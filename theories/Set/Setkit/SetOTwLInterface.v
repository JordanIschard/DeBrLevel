From Coq Require Import MSets Classical_Prop.


Module Type SetOTWithLeibnizInterface (T : MSetList.OrderedTypeWithLeibniz) <: Structures.Orders.OrderedType <: MSetList.SWithLeibniz.


  Include MSetList.MakeWithLeibniz T.
  Include MSetProperties.WPropertiesOn T.

  Section definition.

    Parameter ltb :  t -> t -> bool.
    Parameter map : (elt -> elt) -> t -> t.

  End definition.

  Section fact.

    Parameter Add_inv : forall x (s s' : t), Add x s s' -> add x s = s'.
    #[global]
    Declare Instance proper_1 : forall f,
      Proper (T.eq ==> eq ==> eq) (fun (r0 : elt) (acc : t) => add (f r0) acc).
    Parameter transpose_1 : forall f,
      transpose eq (fun (r0 : elt) (acc : t) => add (f r0) acc).

  End fact.

  Section equality.

    Parameter eqb_refl : forall s, equal s s = true.

    Parameter add_eq_leibniz : forall s s' v,
      ~ In v s -> ~ In v s' -> s = s' <-> (add v s) = (add v s').

  End equality.

  Section lt.

    Parameter ltb_lt : forall s s', ltb s s' = true <-> lt s s'.
    Parameter gt_neq_nlt : forall s s', ~ eq s s' -> ~ lt s s' -> lt s' s.

  End lt.

  Section in_set.

    Variable x : elt.
    Variable s s' : t.

    Parameter diff_in_add_spec : In x s' -> (diff (add x s) s') = (diff s s').
    Parameter union_add_spec : (union (add x s) s') =  add x (union s s').
    Parameter inter_in_add_spec : In x s' -> (inter (add x s) s') = add x (inter s s').

  End in_set.

  Section notin_set.

    Variable x r r' : elt.
    Variable s s' s1 s2 : t.

    Parameter diff_notin_add_spec : ~ In x s' -> (diff (add x s) s') = add x (diff s s').
    Parameter inter_notin_add_spec : ~ In x s' -> (inter (add x s) s') =  (inter s s').
    Parameter add_notin_spec : ~ In r (add r' s) <-> r <> r' /\ ~ In r s.
    Parameter union_notin_spec : ~ In r (union s1 s2) <-> ~ In r s1 /\ ~ In r s2.
    Parameter diff_notin_spec : ~ In r (diff s1 s2) <-> ~ In r s1 \/ In r s2.
    Parameter singleton_notin_spec : ~ In r (singleton  r') <-> r <> r'.

  End notin_set.

  Section map.

    Parameter map_Empty_spec : forall f s, Empty s -> map f s = empty.
    Parameter map_empty_spec : forall f, map f empty = empty.
    Parameter map_singleton_spec : forall f re, map f (singleton re) = singleton (f re).
    Parameter map_in_spec : forall s f re, In re s -> In (f re) (map f s).
    Parameter map_add_notin_spec : forall f re s, ~ In re s -> map f (add re s) = add (f re) (map f s).
    Parameter map_add_in_spec : forall f re s, In re s -> map f (add re s) = (map f s).
    Parameter map_union_spec : forall s s' f, (map f (union s s')) = union (map f s) (map f s').

  End map.

End SetOTWithLeibnizInterface.