From Coq Require Import Structures.Equalities.
From DeBrLevel Require Import Level LevelInterface MapExtInterface. 

(** * Interface - Leveled Map

  Based on the overlay [MapExt] we defined interfaces for maps with [shift] and [valid].
  The [shift] function is applied on all leveled elements (keys and/or data), and a map is 
  valid under [k] if all leveled elements in it are also valid under [k]. For each interface
  we specify via the notation [?K/?D] the configuration of the map where [K] stands for
  keys and [D] for data. ? can be [OT] for ordered 
  type, [ET] for equality type and [Lvl] for leved type.
*)

(** ** Leveled Map Interface - [OTK/LvlD] *)

Module Type IsLvlMapDInterface  
  (Key : OrderedTypeWithLeibniz) (Data : IsLvlETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsLvl MO.

Include IsLvl MO.
Import MO OP.P.

(** *** extra [valid] property *)
Section valid.

Variable lb : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.


Parameter valid_Empty_spec : Empty m -> valid lb m.
Parameter valid_empty_spec : valid lb M.empty.

Parameter valid_Add_iff : ~ M.In x m -> Add x v m m' ->  
  (Data.valid lb v /\ valid lb m <-> valid lb m').
Parameter valid_Add_spec : Add x v m m' ->  
  (Data.valid lb v /\ valid lb m -> valid lb m').
Parameter valid_add_in_spec : M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).
Parameter valid_add_spec :
  Data.valid lb v /\ valid lb m -> valid lb (M.add x v m).

Parameter valid_find_spec : valid lb m -> M.find x m = Some v -> Data.valid lb v.

End valid.

(** *** extra [shift] function property *)
Section shift.

Variable lb k k' : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter shift_Empty_iff : Empty m <-> Empty (shift lb k m).
Parameter shift_Empty_spec : Empty m -> eq (shift lb k m) m.

Parameter shift_add_spec :
  eq (shift lb k (M.add x v m)) (M.add x (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_spec : Add x v m m' -> 
  eq (shift lb k m') (M.add x (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_iff : Add x v m m' <->
  Add x (Data.shift lb k v) (shift lb k m) (shift lb k m').

Parameter shift_remove_spec : 
  eq (M.remove x (shift lb k m)) (shift lb k (M.remove x m)).

Parameter shift_in_iff :  M.In x m <-> M.In x (shift lb k m).
Parameter shift_notin_iff : ~ M.In x m <-> ~ M.In x (shift lb k m).
Parameter shift_find_iff :
  M.find x m = Some v <-> M.find x (shift lb k m) = Some (Data.shift lb k v).

End shift.

End IsLvlMapDInterface.

(** ** Bindless Leveled Map Interface - [OTK/LvlD] *)
Module Type IsBdlLvlMapDInterface  
  (Key : OrderedTypeWithLeibniz) (Data : IsBdlLvlETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsBdlLvl MO
:= IsLvlMapDInterface Key Data M MO <+ IsBindlessLeveledEx MO.

(** ** Alternative Leveled Map Interface - [OTK/LvlD]
  Map with boolean version of [valid] named [validb] 
*)
Module Type IsLvlFullMapDInterface  
  (Key : OrderedTypeWithLeibniz) (Data : IsLvlFullETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M)
:= (IsLvlMapDInterface Key Data M MO) <+ HasValidFull MO.

(** ** Alternative Bindless Leveled Map Interface  - [OTK/LvlD] 
  Map with boolean version of [valid] named [validb] 
*)
Module Type IsBdlLvlFullMapDInterface 
  (Key : OrderedTypeWithLeibniz) (Data : IsBdlLvlFullETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) 
:=  (IsBdlLvlMapDInterface Key Data M MO) <+ HasValidFull MO.


(** ---- *)


(** ** Leveled Map Interface - [LvlK/ETD] *)

Module Type IsLvlMapKInterface  
  (Key : IsLvlOTWL) (Data : EqualityType) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsLvl MO.

Include IsLvl MO.
Import MO OP.P.

(** *** extra [valid] property *)
Section valid.

Variable lb : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.


Parameter valid_Empty_spec : Empty m -> valid lb m.
Parameter valid_Empty_iff : Empty m -> valid lb m <-> True.
Parameter valid_empty_spec : valid lb M.empty.


Parameter valid_add_iff :
  Key.valid lb x /\ valid lb m <-> valid lb (M.add x v m).
Parameter valid_add_in_spec : M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).
Parameter valid_Add_iff : Add x v m m' ->  
  (Key.valid lb x /\ valid lb m <-> valid lb m').

Parameter valid_in_spec : valid lb m -> M.In x m -> Key.valid lb x.

End valid.

(** *** extra [shift] function property *)
Section shift.

Variable lb k k' : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter shift_Empty_iff : Empty m <-> Empty (shift lb k m).
Parameter shift_Empty_spec : Empty m -> eq (shift lb k m) m.

Parameter shift_add_spec :
  eq  (shift lb k (M.add x v m)) (M.add (Key.shift lb k x) v (shift lb k m)).
Parameter shift_Add_spec : Add x v m m' -> 
  eq (shift lb k m') (M.add (Key.shift lb k x) v (shift lb k m)).
Parameter shift_Add_iff : Add x v m m' <->
  Add (Key.shift lb k x) v (shift lb k m) (shift lb k m').

Parameter shift_remove_spec : 
  eq (M.remove (Key.shift lb k x) (shift lb k m)) (shift lb k (M.remove x m)).

Parameter shift_in_iff :  M.In x m <-> M.In (Key.shift lb k x) (shift lb k m).
Parameter shift_notin_iff : ~ M.In x m <-> ~ M.In (Key.shift lb k x) (shift lb k m).
Parameter shift_find_spec :
  M.find x m = M.find (Key.shift lb k x) (shift lb k m).

End shift.

End IsLvlMapKInterface.


(** ** Bindless Leveled Map Interface - [LvlK/ETD] *)
Module Type IsBdlLvlMapKInterface  
  (Key : IsBdlLvlOTWL) (Data : EqualityType) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsBdlLvl MO
:= IsLvlMapKInterface Key Data M MO <+ IsBindlessLeveledEx MO.

(** ** Alternative Leveled Map Interface - [LvlK/ETD] *)
Module Type IsLvlFullMapKInterface  
  (Key : IsLvlFullOTWL) (Data : EqualityType) 
  (M : Interface.S Key) (MO : MapInterface Key Data M)
:= (IsLvlMapKInterface Key Data M MO) <+ HasValidFull MO.

(** ** Alternative Bindless Leveled Map Interface - [LvlK/ETD] *)
Module Type IsBdlLvlFullMapKInterface 
  (Key : IsBdlLvlFullOTWL) (Data : EqualityType)
  (M : Interface.S Key) (MO : MapInterface Key Data M) 
:=  (IsBdlLvlMapKInterface Key Data M MO) <+ HasValidFull MO.


(** ---- *)


(** ** Leveled Map Interface - [LvlK/LvlD] *)

Module Type IsLvlMapKDInterface 
  (Key : IsLvlOTWL) (Data : IsLvlETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsLvl MO.

Include IsLvl MO.
Import MO OP.P.

(** *** extra [valid] property *)
Section valid.

Variable lb : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter valid_Empty_spec : Empty m -> valid lb m.
Parameter valid_Empty_iff : Empty m -> valid lb m <-> True.
Parameter valid_empty_spec : valid lb M.empty.

Parameter valid_add_spec :
  Key.valid lb x /\ Data.valid lb v /\ valid lb m -> valid lb (M.add x v m).
Parameter valid_add_notin_spec : ~ M.In x m -> 
  valid lb (M.add x v m) <-> Key.valid lb x /\ Data.valid lb v /\ valid lb m.
Parameter valid_add_in_spec : M.In x m -> valid lb m -> exists v, valid lb (M.add x v m).

Parameter valid_Add_iff : ~ M.In x m -> Add x v m m' ->  
  (Key.valid lb x /\ Data.valid lb v /\ valid lb m <-> valid lb m').
Parameter valid_Add_spec : Add x v m m' ->  
  (Key.valid lb x /\ Data.valid lb v /\ valid lb m -> valid lb m').

Parameter valid_find_spec : 
  valid lb m -> M.find x m = Some v -> Key.valid lb x /\ Data.valid lb v.
Parameter valid_in_spec : valid lb m -> M.In x m -> Key.valid lb x.

End valid.

(** *** extra [shift] function property *)
Section shift.

Variable lb k k' : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

Parameter shift_Empty_iff : Empty m <-> Empty (shift lb k m).
Parameter shift_Empty_spec : Empty m -> eq (shift lb k m) m.

Parameter shift_add_spec :
  eq  (shift lb k (M.add x v m)) 
      (M.add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_spec : Add x v m m' -> 
  eq (shift lb k m') (M.add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m)).
Parameter shift_Add_iff : Add x v m m' <->
  Add (Key.shift lb k x) (Data.shift lb k v) (shift lb k m) (shift lb k m').

Parameter shift_remove_spec : 
  eq (M.remove (Key.shift lb k x) (shift lb k m)) (shift lb k (M.remove x m)).

Parameter shift_in_iff :  M.In x m <-> M.In (Key.shift lb k x) (shift lb k m).
Parameter shift_notin_iff : ~ M.In x m <-> ~ M.In (Key.shift lb k x) (shift lb k m).

Parameter shift_find_iff :
  M.find x m = Some v <-> 
  M.find (Key.shift lb k x) (shift lb k m) = Some (Data.shift lb k v).
Parameter shift_find_e_spec :
  M.find (Key.shift lb k x) (shift lb k m) = Some v -> 
  exists v', Data.eq v (Data.shift lb k v').

End shift.

End IsLvlMapKDInterface.

(** ** Bindless Leveled Map Interface - [LvlK/LvlD] *)
Module Type IsBdlLvlMapKDInterface 
  (Key : IsBdlLvlOTWL) (Data : IsBdlLvlETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsBdlLvl MO
:= IsLvlMapKDInterface Key Data M MO <+ IsBindlessLeveledEx MO.


(** ** Alternative Leveled Map Interface - [LvlK/LvlD] *)
Module Type IsLvlFullMapKDInterface  
  (Key : IsBdlLvlFullOTWL) (Data : IsLvlFullETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M)
:= (IsLvlMapKDInterface Key Data M MO) <+ HasValidFull MO.

(** ** Alternative Bindless Leveled Map Interface - [LvlK/LvlD] *)
Module Type IsBdlLvlFullMapKDInterface  
  (Key : IsBdlLvlFullOTWL) (Data : IsBdlLvlFullETWL) 
  (M : Interface.S Key) (MO : MapInterface Key Data M) 
:=  (IsBdlLvlMapKDInterface Key Data M MO) <+ HasValidFull MO.


(** ---- *)


(** ** Leveled Map Interface - [LevelK/ETD] *)

Module Type IsLvlMapLVLInterface  
  (Data : EqualityType) (M : Interface.S Level) (MO : MapLVLInterface Data M) <: IsLvl MO.

Include IsLvlMapKInterface Level Data M MO.
Import MO OP.P.

Section props.

Variable lb k : Lvl.t.
Variable m : t.

Parameter shift_new_notin_spec : lb >= (new_key m) -> ~ M.In lb (shift lb k m).
Parameter shift_new_spec : lb >= (new_key m) -> new_key (shift lb k m) = new_key m.
Parameter shift_max_spec : lb >= (new_key m) -> max_key (shift lb k m) = max_key m.

End props.

End IsLvlMapLVLInterface.

(** ** Bindless Leveled Map Interface - [LevelK/ETD] *)
Module Type IsBdlLvlMapLVLInterface 
  (Data : EqualityType) (M : Interface.S Level) (MO : MapLVLInterface Data M) <: IsBdlLvl MO
:= IsLvlMapLVLInterface Data M MO <+ IsBindlessLeveledEx MO.

(** ** Alter. Leveled Map Interface - [LevelK/ETD] *)
Module Type IsLvlFullMapLVLInterface
  (Data : EqualityType) (M : Interface.S Level) (MO : MapLVLInterface Data M)
:= (IsLvlMapLVLInterface Data M MO) <+ HasValidFull MO.

(** ** Alter. Bindless Leveled Map Interface - [LevelK/ETD] *)
Module Type IsBdlLvlFullMapLVLInterface 
  (Data : EqualityType) (M : Interface.S Level) (MO : MapLVLInterface Data M)
:=  (IsBdlLvlMapLVLInterface Data M MO) <+ HasValidFull MO.

(** ---- *)

(** ** Leveled Map Interface - [LevelK/LvlD]  *)

Module Type IsLvlMapLVLDInterface 
  (Data : IsLvlETWL) (M : Interface.S Level) (MO : MapLVLInterface Data M) <: IsLvl MO.

Include IsLvlMapKDInterface Level Data M MO.
Import MO OP.P.

Section props.

Variable lb k : Lvl.t.
Variable m : t.

Parameter shift_new_notin_spec : lb >= (new_key m) -> ~ M.In lb (shift lb k m).
Parameter shift_new_spec : lb >= (new_key m) -> new_key (shift lb k m) = new_key m.
Parameter shift_max_spec : lb >= (new_key m) -> max_key (shift lb k m) = max_key m.

End props.

End IsLvlMapLVLDInterface.

(** ** Bindless Leveled Map Interface - [LevelK/LvlD]  *)
Module Type IsBdlLvlMapLVLDInterface  
  (Data : IsBdlLvlETWL) (M : Interface.S Level) (MO : MapLVLInterface Data M) <: IsBdlLvl MO
:= IsLvlMapLVLDInterface Data M MO <+ IsBindlessLeveledEx MO.

(** ** Alter. Leveled Map Interface - [LevelK/LvlD]  *)
Module Type IsLvlFullMapLVLDInterface
  (Data : IsLvlFullETWL) (M : Interface.S Level) (MO : MapLVLInterface Data M)
:= (IsLvlMapLVLDInterface Data M MO) <+ HasValidFull MO.

(** ** Alter. Bindless Leveled Map Interface - [LevelK/LvlD]  *)
Module Type IsBdlLvlFullMapLVLDInterface  
  (Data : IsBdlLvlFullETWL) (M : Interface.S Level) (MO : MapLVLInterface Data M) 
:=  (IsBdlLvlMapLVLDInterface Data M MO) <+ HasValidFull MO.