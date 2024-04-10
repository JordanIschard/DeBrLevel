Require Import Kernel.Level MapExtInterface Kernel.LevelInterface Structures.Equalities.

(** * Interfaces -- Map Level with datas as equality types

  Based on the overlay [MapExt] we defined interfaces for maps with shift and valid extension
  with different levels of constraints.
*)

(** ** Map interface with leveled datas and basic keys *)

(** *** Map interface with minimal constraints *)

Module Type ShiftValidMapDInterface  (Key : OrderedTypeWithLeibniz)
                                    (Data : ShiftValidETWithLeibniz) 
                                    (M : Interface.S Key)
                                    (MO : MapInterface Key Data M) <: ShiftValid MO.

Include ShiftValid MO.
Import MO OP.P.

(** **** Valid *)
Section valid.

Variable lb : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.


Parameter valid_Empty_spec : Empty m -> valid lb m.
Parameter valid_empty_spec : valid lb M.empty.
Parameter valid_add_notin_spec : ~ M.In x m -> 
  valid lb (M.add x v m) <-> Data.valid lb v /\ valid lb m.
Parameter valid_add_in_spec : M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).
Parameter valid_Add_spec : ~ M.In x m -> Add x v m m' ->  
  (Data.valid lb v /\ valid lb m <-> valid lb m').
Parameter valid_find_spec : valid lb m -> M.find x m = Some v -> Data.valid lb v.
Parameter valid_add_spec : forall m x (v : Data.t) lb,
  Data.valid lb v /\ valid lb m -> valid lb (M.add x v m).

End valid.

(** **** Shift *)
Section shift.

Variable lb k k' : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter shift_Empty_spec_1 : Empty m -> Empty (shift lb k m).
Parameter shift_Empty_spec : Empty m -> eq (shift lb k m) m.
Parameter shift_add_notin_spec : ~ M.In x m ->  
  eq  (shift lb k (M.add x v m)) 
      (M.add x (Data.shift lb k v) (shift lb k m)).
Parameter shift_add_spec :
  eq  (shift lb k (M.add x v m)) 
      (M.add x (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_spec : ~ M.In x m -> Add x v m m' -> 
  eq (shift lb k m') (M.add x (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_spec_1 : ~ M.In x m -> Add x v m m' ->
  Add x (Data.shift lb k v) (shift lb k m) (shift lb k m').
Parameter shift_remove_spec : 
  eq (M.remove x (shift lb k m)) (shift lb k (M.remove x m)).

Parameter shift_in_spec :  M.In x m <-> M.In x (shift lb k m).
Parameter shift_notin_spec : ~ M.In x m <-> ~ M.In x (shift lb k m).
Parameter shift_find_spec :
  M.find x m = Some v <-> M.find x (shift lb k m) = Some (Data.shift lb k v).

End shift.

End ShiftValidMapDInterface.


(** *** Map interface fully constrained *)
Module Type StrongShiftValidMapDInterface  (Key : OrderedTypeWithLeibniz)
                                          (Data : StrongShiftValidETWithLeibniz) 
                                          (M : Interface.S Key) 
                                          (MO : MapInterface Key Data M) <: StrongShiftValid MO
:= ShiftValidMapDInterface Key Data M MO <+ StrongShiftValidEx MO.

(** *** Map interface with minimal constraints with [validb] *)
Module Type ShiftValidFullMapDInterface  (Key : OrderedTypeWithLeibniz)
                                        (Data : ShiftValidFullETWithLeibniz) 
                                        (M : Interface.S Key) 
                                        (MO : MapInterface Key Data M)
:= (ShiftValidMapDInterface Key Data M MO) <+ HasValidFull MO.

(** *** Map interface fully constrained with [validb] *)
Module Type StrongShiftValidFullMapDInterface  (Key : OrderedTypeWithLeibniz)
                                              (Data : StrongShiftValidFullETWithLeibniz) 
                                              (M : Interface.S Key) 
                                              (MO : MapInterface Key Data M) 
:=  (StrongShiftValidMapDInterface Key Data M MO) <+ HasValidFull MO.


(** ** Map interface with basic datas and leveled keys *)

(** *** Map interface with minimal constraints *)

Module Type ShiftValidMapInterface  (Key : ShiftValidOTWithLeibniz)
                                    (Data : EqualityType) 
                                    (M : Interface.S Key)
                                    (MO : MapInterface Key Data M) <: ShiftValid MO.

Include ShiftValid MO.
Import MO OP.P.

(** **** Valid *)
Section valid.

Variable lb : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.


Parameter valid_Empty_spec : Empty m -> valid lb m.
Parameter valid_add_notin_spec : ~ M.In x m -> 
  valid lb (M.add x v m) <-> Key.valid lb x /\ valid lb m.
Parameter valid_add_in_spec : M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).
Parameter valid_Add_spec : ~ M.In x m -> Add x v m m' ->  
  (Key.valid lb x /\ valid lb m <-> valid lb m').
Parameter valid_in_spec : valid lb m -> M.In x m -> Key.valid lb x.
Parameter valid_add_spec : forall m x (v : Data.t) lb,
  Key.valid lb x /\ valid lb m <-> valid lb (M.add x v m).

End valid.

(** **** Shift *)
Section shift.

Variable lb k k' : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter shift_Empty_iff : Empty m <-> Empty (shift lb k m).
Parameter shift_Empty_spec : Empty m -> eq (shift lb k m) m.
Parameter shift_add_notin_spec : ~ M.In x m ->  
  eq  (shift lb k (M.add x v m)) 
      (M.add (Key.shift lb k x) v (shift lb k m)).
Parameter shift_Add_spec : ~ M.In x m -> Add x v m m' -> 
  eq (shift lb k m') (M.add (Key.shift lb k x) v (shift lb k m)).
Parameter shift_Add_spec_1 : ~ M.In x m -> Add x v m m' ->
  Add (Key.shift lb k x) v (shift lb k m) (shift lb k m').
Parameter shift_add_spec :
  eq  (shift lb k (M.add x v m)) 
        (M.add (Key.shift lb k x) v (shift lb k m)).
Parameter shift_remove_spec : 
  eq (M.remove (Key.shift lb k x) (shift lb k m)) (shift lb k (M.remove x m)).

Parameter shift_in_spec :  M.In x m <-> M.In (Key.shift lb k x) (shift lb k m).
Parameter shift_notin_spec : ~ M.In x m <-> ~ M.In (Key.shift lb k x) (shift lb k m).
Parameter shift_find_spec :
  M.find x m = M.find (Key.shift lb k x) (shift lb k m).

End shift.

End ShiftValidMapInterface.


(** *** Map interface fully constrained *)
Module Type StrongShiftValidMapInterface  (Key : StrongShiftValidOTWithLeibniz)
                                          (Data : EqualityType) 
                                          (M : Interface.S Key) 
                                          (MO : MapInterface Key Data M) <: StrongShiftValid MO
:= ShiftValidMapInterface Key Data M MO <+ StrongShiftValidEx MO.

(** *** Map interface with minimal constraints with [validb] *)
Module Type ShiftValidFullMapInterface  (Key : ShiftValidFullOTWithLeibniz)
                                        (Data : EqualityType) 
                                        (M : Interface.S Key) 
                                        (MO : MapInterface Key Data M)
:= (ShiftValidMapInterface Key Data M MO) <+ HasValidFull MO.

(** *** Map interface fully constrained with [validb] *)
Module Type StrongShiftValidFullMapInterface  (Key : StrongShiftValidFullOTWithLeibniz)
                                              (Data : EqualityType) 
                                              (M : Interface.S Key) 
                                              (MO : MapInterface Key Data M) 
:=  (StrongShiftValidMapInterface Key Data M MO) <+ HasValidFull MO.










(** ** Map interface with leveled keys and datas *)

(** *** Map interface with minimal constraints *)
Module Type ShiftValidMapWLInterface  (Key : ShiftValidOTWithLeibniz)
                                        (Data : ShiftValidETWithLeibniz) 
                                        (M : Interface.S Key)
                                        (MO : MapInterface Key Data M) <: ShiftValid MO.

Include ShiftValid MO.
Import MO OP.P.

(** **** Valid *)
Section valid.

Variable lb : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter valid_Empty_spec : Empty m -> valid lb m.
Parameter valid_add_notin_spec : ~ M.In x m -> 
  valid lb (M.add x v m) <-> Key.valid lb x /\ Data.valid lb v /\ valid lb m.
Parameter valid_add_in_spec : M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).
Parameter valid_Add_spec : ~ M.In x m -> Add x v m m' ->  
  (Key.valid lb x /\ Data.valid lb v /\ valid lb m <-> valid lb m').
Parameter valid_find_spec : 
  valid lb m -> M.find x m = Some v -> Key.valid lb x /\ Data.valid lb v.
Parameter valid_in_spec : valid lb m -> M.In x m -> Key.valid lb x.
Parameter valid_add_spec : forall m x v lb,
  Key.valid lb x /\ Data.valid lb v /\ valid lb m -> valid lb (M.add x v m).

End valid.

(** **** Shift *)
Section shift.

Variable lb k k' : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter shift_Empty_iff : Empty m <-> Empty (shift lb k m).
Parameter shift_Empty_spec : Empty m -> eq (shift lb k m) m.
Parameter shift_add_notin_spec : ~ M.In x m ->  
  eq  (shift lb k (M.add x v m)) 
      (M.add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_spec : ~ M.In x m -> Add x v m m' -> 
  eq (shift lb k m') (M.add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_spec_1 : ~ M.In x m -> Add x v m m' ->
  Add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m) (shift lb k m').
Parameter shift_add_spec :
  eq  (shift lb k (M.add x v m)) 
      (M.add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Parameter shift_remove_spec : 
  eq (M.remove (Key.shift lb k x) (shift lb k m)) (shift lb k (M.remove x m)).

Parameter shift_in_spec :  M.In x m <-> M.In (Key.shift lb k x) (shift lb k m).
Parameter shift_notin_spec : ~ M.In x m <-> ~ M.In (Key.shift lb k x) (shift lb k m).
Parameter shift_find_spec :
  M.find x m = Some v <-> 
  M.find (Key.shift lb k x) (shift lb k m) = Some (Data.shift lb k v).
Parameter shift_find_e_spec :
  M.find (Key.shift lb k x) (shift lb k m) = Some v -> 
  exists v', Data.eq v (Data.shift lb k v').

End shift.

End ShiftValidMapWLInterface.

(** *** Map interface fully constrained *)
Module Type StrongShiftValidMapWLInterface (Key : StrongShiftValidOTWithLeibniz)
                                             (Data : StrongShiftValidETWithLeibniz) 
                                             (M : Interface.S Key) 
                                             (MO : MapInterface Key Data M) 
                                               <: StrongShiftValid MO
:= ShiftValidMapWLInterface Key Data M MO <+ StrongShiftValidEx MO.


(** *** Map interface with minimal constraints with [validb] *)
Module Type ShiftValidFullMapWLInterface  (Key : StrongShiftValidFullOTWithLeibniz)
                                            (Data : ShiftValidFullETWithLeibniz) 
                                            (M : Interface.S Key) 
                                            (MO : MapInterface Key Data M)
:= (ShiftValidMapWLInterface Key Data M MO) <+ HasValidFull MO.

(** *** Map interface fully constrained with [validb] *)
Module Type StrongShiftValidFullMapWLInterface  (Key : StrongShiftValidFullOTWithLeibniz)
                                                  (Data : StrongShiftValidFullETWithLeibniz) 
                                                  (M : Interface.S Key) 
                                                  (MO : MapInterface Key Data M) 
:=  (StrongShiftValidMapWLInterface Key Data M MO) <+ HasValidFull MO.







(** ** Map interface with levels as keys and basic datas *)

(** *** Map interface with minimal constraints *)
Module Type ShiftValidMapLVLInterface  (Data : EqualityType) 
                                           (M : Interface.S Level)
                                           (MO : MapLVLInterface Data M) <: ShiftValid MO.

Include ShiftValidMapInterface Level Data M MO.
Import MO OP.P.

(** **** Shift *)
Section shift.

  Variable lb k : Lvl.t.
  Variable m : t.

  Parameter shift_new_notin_spec : lb >= (new_key m) -> ~ M.In lb (shift lb k m).
  Parameter shift_new_spec : lb >= (new_key m) -> new_key (shift lb k m) = new_key m.
  Parameter shift_max_spec : lb >= (new_key m) -> max_key (shift lb k m) = max_key m.

End shift.

End ShiftValidMapLVLInterface.

(** *** Map interface fully constrained *)
Module Type StrongShiftValidMapLVLInterface  (Data : EqualityType) 
                                                 (M : Interface.S Level) 
                                                 (MO : MapLVLInterface Data M) 
                                                 <: StrongShiftValid MO
:= ShiftValidMapLVLInterface Data M MO <+ StrongShiftValidEx MO.

(** *** Map interface with minimal constraints with [validb] *)
Module Type ShiftValidFullMapLVLInterface  (Data : EqualityType) 
                                               (M : Interface.S Level) 
                                               (MO : MapLVLInterface Data M)
:= (ShiftValidMapLVLInterface Data M MO) <+ HasValidFull MO.

(** *** Map interface fully constrained with [validb] *)
Module Type StrongShiftValidFullMapLVLInterface  (Data : EqualityType) 
                                                (M : Interface.S Level) 
                                                (MO : MapLVLInterface Data M) 
:=  (StrongShiftValidMapLVLInterface Data M MO) <+ HasValidFull MO.


(** ** Map interface with leveled datas and levels as keys *)

(** *** Map interface with minimal constraints *)
Module Type ShiftValidMapWLLVLInterface  (Data : ShiftValidETWithLeibniz) 
                                               (M : Interface.S Level)
                                               (MO : MapLVLInterface Data M)
                                                <: ShiftValid MO.

Include ShiftValid MO.
Import MO OP.P.

(** **** Valid *)
Section valid.

Variable lb : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.


Parameter valid_Empty_spec : Empty m -> valid lb m.
Parameter valid_add_notin_spec : ~ M.In x m -> 
  valid lb (M.add x v m) <-> Level.valid lb x /\ Data.valid lb v /\ valid lb m.
Parameter valid_add_in_spec : M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).
Parameter valid_Add_spec : ~ M.In x m -> Add x v m m' ->  
  (Level.valid lb x /\ Data.valid lb v /\ valid lb m <-> valid lb m').
Parameter valid_find_spec : 
  valid lb m -> M.find x m = Some v -> Level.valid lb x /\ Data.valid lb v.
Parameter valid_in_spec : valid lb m -> M.In x m -> Level.valid lb x.
Parameter valid_add_spec : forall m x v lb,
  Level.valid lb x /\ Data.valid lb v /\ valid lb m -> valid lb (M.add x v m).

End valid.

(** **** Shift *)
Section shift.

Variable lb k k' : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter shift_Empty_iff : Empty m <-> Empty (shift lb k m).
Parameter shift_Empty_spec : Empty m -> eq (shift lb k m) m.
Parameter shift_add_notin_spec : ~ M.In x m ->  
  eq  (shift lb k (M.add x v m)) 
      (M.add (Level.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Parameter shift_add_spec :
  eq  (shift lb k (M.add x v m)) 
    (M.add (Level.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_spec : ~ M.In x m -> Add x v m m' -> 
  eq (shift lb k m') (M.add (Level.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_spec_1 : ~ M.In x m -> Add x v m m' ->
  Add (Level.shift lb k x) (Data.shift lb k v) (shift lb k m) (shift lb k m').
Parameter shift_remove_spec : 
  eq (M.remove (Level.shift lb k x) (shift lb k m)) (shift lb k (M.remove x m)).

Parameter shift_in_spec :  M.In x m <-> M.In (Level.shift lb k x) (shift lb k m).
Parameter shift_notin_spec : ~ M.In x m <-> ~ M.In (Level.shift lb k x) (shift lb k m).
Parameter shift_find_spec :
  M.find x m = Some v <-> 
  M.find (Level.shift lb k x) (shift lb k m) = Some (Data.shift lb k v).
Parameter shift_find_e_spec :
  M.find (Level.shift lb k x) (shift lb k m) = Some v -> 
  exists v', Data.eq v (Data.shift lb k v').

Parameter shift_new_notin_spec : lb >= (new_key m) -> ~ M.In lb (shift lb k m).
Parameter shift_new_spec : lb >= (new_key m) -> new_key (shift lb k m) = new_key m.

Parameter shift_max_spec : lb >= (new_key m) -> max_key (shift lb k m) = max_key m.

End shift.

End ShiftValidMapWLLVLInterface.

(** *** Map interface fully constrained *)
Module Type StrongShiftValidMapWLLVLInterface  
                                            (Data : StrongShiftValidETWithLeibniz) 
                                            (M : Interface.S Level) 
                                            (MO : MapLVLInterface Data M) 
                                            <: StrongShiftValid MO 
:= ShiftValidMapWLLVLInterface Data M MO <+ StrongShiftValidEx MO.

(** *** Map interface with minimal constraints with [validb] *)
Module Type ShiftValidFullMapWLLVLInterface  (Data : ShiftValidFullETWithLeibniz) 
                                                   (M : Interface.S Level) 
                                                   (MO : MapLVLInterface Data M)
:= (ShiftValidMapWLLVLInterface Data M MO) <+ HasValidFull MO.

(** *** Map interface fully constrained with [validb] *)
Module Type StrongShiftValidFullMapWLLVLInterface  
                                                    (Data : StrongShiftValidFullETWithLeibniz) 
                                                    (M : Interface.S Level) 
                                                    (MO : MapLVLInterface Data M) 
:=  (StrongShiftValidMapWLLVLInterface Data M MO) <+ HasValidFull MO.