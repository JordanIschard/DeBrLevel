From Coq Require Import Structures.Equalities.
From DeBrLevel Require Import Level LevelInterface MapExtInterface. 

(** * Interface - Leveled Map

  Based on the overlay [MapExt] we defined interfaces for maps with [shift] and [Wf].
  The [shift] function is applied on all leveled elements (keys and/or data), and a map is 
  well-formed under [k] if all leveled elements in it are also well-formed under [k]. For each interface we specify via the notation [?K/?D] the configuration of the map where [K] stands for keys and [D] for data. ? can be [OT] for ordered type, [ET] for equality type and [Lvl] for leved type.
*)

(** ** Leveled Map Interface - [OTK/LvlD] *)
Module Type IsLvlMapDInterface (Key : OrderedTypeWithLeibniz) (Data : IsLvlETWL) 
                               (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsLvl MO.

Include IsLvl MO.
Import MO OP.P.

Section specs.

Variable k n p : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

(** *** extra [Wf] specifications *)

Parameter Wf_Empty : Empty m -> Wf k m.

Parameter Wf_empty : Wf k M.empty.

Parameter Wf_Add_iff : ~ M.In x m -> Add x v m m' ->  (Data.Wf k v /\ Wf k m <-> Wf k m').

Parameter Wf_Add : Add x v m m' ->  (Data.Wf k v /\ Wf k m -> Wf k m').

Parameter Wf_add_in : M.In x m -> Wf k m -> exists v, Wf k (M.add x v m).

Parameter Wf_add : Data.Wf k v /\ Wf k m -> Wf k (M.add x v m).

Parameter Wf_find : Wf k m -> M.find x m = Some v -> Data.Wf k v.

Parameter Wf_update : M.In x m -> Wf k m -> Data.Wf k v -> Wf k (M.add x v m).

(** *** extra [shift] specifications *)

Parameter shift_Empty_iff : Empty m <-> Empty (shift k n m).

Parameter shift_Empty : Empty m -> eq (shift k n m) m.

Parameter shift_add : eq (shift k n (M.add x v m)) (M.add x (Data.shift k n v) (shift k n m)).

Parameter shift_Add : Add x v m m' -> eq (shift k n m') (M.add x (Data.shift k n v) (shift k n m)).

Parameter shift_Add_iff : Add x v m m' <-> Add x (Data.shift k n v) (shift k n m) (shift k n m').

Parameter shift_remove : eq (M.remove x (shift k n m)) (shift k n (M.remove x m)).

Parameter shift_in_iff :  M.In x m <-> M.In x (shift k n m).

Parameter shift_notin_iff : ~ M.In x m <-> ~ M.In x (shift k n m).

Parameter shift_find_iff : M.find x m = Some v <-> M.find x (shift k n m) = Some (Data.shift k n v).

End specs.

End IsLvlMapDInterface.


(** ** Bindless Leveled Map Interface - [OTK/LvlD] *)
Module Type IsBdlLvlMapDInterface (Key : OrderedTypeWithLeibniz) (Data : IsBdlLvlETWL) 
                                  (M : Interface.S Key) (MO : MapInterface Key Data M) 
                                  <: IsBdlLvl MO
:= IsLvlMapDInterface Key Data M MO <+ IsBindlessLeveledEx MO.

(** ** Alternative Leveled Map Interface - [OTK/LvlD]
  Map with boolean version of [Wf] named [is_wf] 
*)
Module Type IsLvlFullMapDInterface (Key : OrderedTypeWithLeibniz) (Data : IsLvlFullETWL) 
                                   (M : Interface.S Key) (MO : MapInterface Key Data M)
:= (IsLvlMapDInterface Key Data M MO) <+ IsWFFull MO.

(** ** Alternative Bindless Leveled Map Interface  - [OTK/LvlD] 
  Map with boolean version of [Wf] named [is_Wf] 
*)
Module Type IsBdlLvlFullMapDInterface (Key : OrderedTypeWithLeibniz) (Data : IsBdlLvlFullETWL) 
                                      (M : Interface.S Key) (MO : MapInterface Key Data M) 
:=  (IsBdlLvlMapDInterface Key Data M MO) <+ IsWFFull MO.


(** ---- *)


(** ** Leveled Map Interface - [LvlK/ETD] *)
Module Type IsLvlMapKInterface (Key : IsLvlOTWL) (Data : EqualityType) 
                               (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsLvl MO.

Include IsLvl MO.
Import MO OP.P.

Section specs.

Variable k n p : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

(** *** extra [Wf] specifications *)

Parameter Wf_Empty : Empty m -> Wf k m.

Parameter Wf_Empty_iff : Empty m -> Wf k m <-> True.

Parameter Wf_empty : Wf k M.empty.

Parameter Wf_add_iff : Key.Wf k x /\ Wf k m <-> Wf k (M.add x v m).

Parameter Wf_add_in : M.In x m -> Wf k m -> exists v, Wf k (M.add x v m).

Parameter Wf_Add_iff : Add x v m m' -> (Key.Wf k x /\ Wf k m <-> Wf k m').

Parameter Wf_in : Wf k m -> M.In x m -> Key.Wf k x.

(** *** extra [shift] specifications *)

Parameter shift_Empty_iff : Empty m <-> Empty (shift k n m).

Parameter shift_Empty : Empty m -> eq (shift k n m) m.

Parameter shift_add : eq  (shift k n (M.add x v m)) (M.add (Key.shift k n x) v (shift k n m)).

Parameter shift_Add : Add x v m m' -> eq (shift k n m') (M.add (Key.shift k n x) v (shift k n m)).

Parameter shift_Add_iff : Add x v m m' <-> Add (Key.shift k n x) v (shift k n m) (shift k n m').

Parameter shift_remove : eq (M.remove (Key.shift k n x) (shift k n m)) (shift k n (M.remove x m)).

Parameter shift_in_e : M.In x (shift k n m) -> exists (x' : Key.t), x = Key.shift k n x'.

Parameter shift_in_iff : M.In x m <-> M.In (Key.shift k n x) (shift k n m).

Parameter shift_notin_iff : ~ M.In x m <-> ~ M.In (Key.shift k n x) (shift k n m).

Parameter shift_find : M.find x m = M.find (Key.shift k n x) (shift k n m).

End specs.

End IsLvlMapKInterface.


(** ** Bindless Leveled Map Interface - [LvlK/ETD] *)
Module Type IsBdlLvlMapKInterface (Key : IsBdlLvlOTWL) (Data : EqualityType) 
                                (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsBdlLvl MO.

Include IsLvlMapKInterface Key Data M MO.
Import MO OP.P.

Parameter Wf_in_iff : forall (m n : Lvl.t) (x : M.key) (t : t),
  Wf m t -> M.In x (shift m n t) <-> M.In x t.

Parameter shift_find_Wf : forall (k n : Lvl.t) (x : M.key) (m m' : t),
  Key.Wf k x -> M.In x m ->
  M.find x m = M.find x m' -> M.find x (shift k n m) = M.find x (shift k n m').

Parameter shift_wf_refl : forall k n t, Wf k t -> eq (shift k n t) t.

End IsBdlLvlMapKInterface.

(** ** Alternative Leveled Map Interface - [LvlK/ETD] *)
Module Type IsLvlFullMapKInterface (Key : IsLvlFullOTWL) (Data : EqualityType) 
                                   (M : Interface.S Key) (MO : MapInterface Key Data M)
:= (IsLvlMapKInterface Key Data M MO) <+ IsWFFull MO.

(** ** Alternative Bindless Leveled Map Interface - [LvlK/ETD] *)
Module Type IsBdlLvlFullMapKInterface (Key : IsBdlLvlFullOTWL) (Data : EqualityType)
                                      (M : Interface.S Key) (MO : MapInterface Key Data M) 
:=  (IsBdlLvlMapKInterface Key Data M MO) <+ IsWFFull MO.


(** ---- *)

(** ** Leveled Map Interface - [LvlK/LvlD] *)

Module Type IsLvlMapKDInterface (Key : IsLvlOTWL) (Data : IsLvlETWL) 
                                (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsLvl MO.

Include IsLvl MO.
Import MO OP.P.

Section specs.

Variable k n p : Lvl.t.
Variable x : M.key.
Variable v : Data.t.
Variable m m' : t.

(** *** extra [Wf] specifications *)

Parameter Wf_Empty : Empty m -> Wf k m.

Parameter Wf_Empty_iff : Empty m -> Wf k m <-> True.

Parameter Wf_empty : Wf k M.empty.

Parameter Wf_add : Key.Wf k x /\ Data.Wf k v /\ Wf k m -> Wf k (M.add x v m).

Parameter Wf_add_notin : ~ M.In x m -> 
                         Wf k (M.add x v m) <-> Key.Wf k x /\ Data.Wf k v /\ Wf k m.

Parameter Wf_add_in : M.In x m -> Wf k m -> exists v, Wf k (M.add x v m).

Parameter Wf_Add_iff : ~ M.In x m -> 
                       Add x v m m' -> (Key.Wf k x /\ Data.Wf k v /\ Wf k m <-> Wf k m').

Parameter Wf_Add : Add x v m m' -> (Key.Wf k x /\ Data.Wf k v /\ Wf k m -> Wf k m').

Parameter Wf_find : Wf k m -> M.find x m = Some v -> Key.Wf k x /\ Data.Wf k v.

Parameter Wf_in : Wf k m -> M.In x m -> Key.Wf k x.

Parameter Wf_update : M.In x m -> Wf k m -> Data.Wf k v -> Wf k (M.add x v m).

(** *** extra [shift] specifications *)

Parameter shift_Empty_iff : Empty m <-> Empty (shift k n m).

Parameter shift_Empty : Empty m -> eq (shift k n m) m.

Parameter shift_add :
  eq (shift k n (M.add x v m)) (M.add (Key.shift k n x) (Data.shift k n v) (shift k n m)).

Parameter shift_Add : Add x v m m' -> 
  eq (shift k n m') (M.add (Key.shift k n x) (Data.shift k n v) (shift k n m)).

Parameter shift_Add_iff : Add x v m m' <->
  Add (Key.shift k n x) (Data.shift k n v) (shift k n m) (shift k n m').

Parameter shift_remove : eq (M.remove (Key.shift k n x) (shift k n m)) (shift k n (M.remove x m)).

Parameter shift_in_e : M.In x (shift k n m) -> exists (x' : Key.t), x = Key.shift k n x'.

Parameter shift_in_iff :  M.In x m <-> M.In (Key.shift k n x) (shift k n m).

Parameter shift_notin_iff : ~ M.In x m <-> ~ M.In (Key.shift k n x) (shift k n m).

Parameter shift_find_iff :
  M.find x m = Some v <->  M.find (Key.shift k n x) (shift k n m) = Some (Data.shift k n v).

Parameter shift_find_e :
  M.find (Key.shift k n x) (shift k n m) = Some v ->  exists v', Data.eq v (Data.shift k n v').

Parameter shift_find_e_1 :
  M.find x (shift k n m) = Some v ->  (exists x', Key.eq x (Key.shift k n x')) /\ 
                                      (exists v', Data.eq v (Data.shift k n v')).

End specs.

End IsLvlMapKDInterface.

(** ** Bindless Leveled Map Interface - [LvlK/LvlD] *)
Module Type IsBdlLvlMapKDInterface (Key : IsBdlLvlOTWL) (Data : IsBdlLvlETWL) 
                                (M : Interface.S Key) (MO : MapInterface Key Data M) <: IsBdlLvl MO.

Include IsLvlMapKDInterface Key Data M MO.
Import MO OP.P.

Parameter Wf_in_iff : forall (m n : Lvl.t) (x : M.key) (t : t),
  Wf m t -> M.In x (shift m n t) <-> M.In x t.

Parameter shift_find_Wf : forall (k n : Lvl.t) (x : M.key) (m m' : t),
  Key.Wf k x -> M.In x m ->
  M.find x m = M.find x m' -> M.find x (shift k n m) = M.find x (shift k n m').

Parameter shift_wf_refl : forall k n t, Wf k t -> eq (shift k n t) t.

End IsBdlLvlMapKDInterface.

(** ** Alternative Leveled Map Interface - [LvlK/LvlD] *)
Module Type IsLvlFullMapKDInterface (Key : IsBdlLvlFullOTWL) (Data : IsLvlFullETWL)  
                                    (M : Interface.S Key) (MO : MapInterface Key Data M)
:= (IsLvlMapKDInterface Key Data M MO) <+ IsWFFull MO.

(** ** Alternative Bindless Leveled Map Interface - [LvlK/LvlD] *)
Module Type IsBdlLvlFullMapKDInterface (Key : IsBdlLvlFullOTWL) (Data : IsBdlLvlFullETWL) 
                                       (M : Interface.S Key) (MO : MapInterface Key Data M) 
:=  (IsBdlLvlMapKDInterface Key Data M MO) <+ IsWFFull MO.


(** ---- *)


(** ** Leveled Map Interface - [LevelK/ETD] *)
Module Type IsLvlMapLVLInterface (Data : EqualityType) (M : Interface.S Level) 
                                 (MO : MapLVLInterface Data M) <: IsLvl MO.

Include IsLvlMapKInterface Level Data M MO.
Import MO OP.P.

Section specs.

Variable k m n : Lvl.t.
Variable x: M.key.
Variable t t' : t.

Parameter Wf_in_iff : Wf m t -> M.In x (shift m n t) <-> M.In x t.

Parameter shift_in_new_key : M.In x (shift (new_key t) n t) <-> M.In x t.

Parameter shift_find_Wf :
  Level.Wf k x -> M.In x t ->
  M.find x t = M.find x t' -> M.find x (shift k n t) = M.find x (shift k n t').

Parameter shift_new_notin : k >= (new_key t) -> ~ M.In k (shift k n t).

Parameter shift_new_refl : k >= (new_key t) -> new_key (shift k n t) = new_key t.

Parameter shift_max_refl : k >= (new_key t) -> max_key (shift k n t) = max_key t.

Parameter shift_max_key_gt_iff : max_key t > n <-> max_key (shift k m t) > (Level.shift k m n).

Parameter shift_max_key_le : max_key t <= max_key (shift k n t).

Parameter shift_new_key_le : new_key t <= new_key (shift k n t).

End specs.

End IsLvlMapLVLInterface.

(** ** Bindless Leveled Map Interface - [LevelK/ETD] *)
Module Type IsBdlLvlMapLVLInterface 
  (Data : EqualityType) (M : Interface.S Level) (MO : MapLVLInterface Data M) <: IsBdlLvl MO
:= IsLvlMapLVLInterface Data M MO <+ IsBindlessLeveledEx MO.

(** ** Alter. Leveled Map Interface - [LevelK/ETD] *)
Module Type IsLvlFullMapLVLInterface
  (Data : EqualityType) (M : Interface.S Level) (MO : MapLVLInterface Data M)
:= (IsLvlMapLVLInterface Data M MO) <+ IsWFFull MO.

(** ** Alter. Bindless Leveled Map Interface - [LevelK/ETD] *)
Module Type IsBdlLvlFullMapLVLInterface 
  (Data : EqualityType) (M : Interface.S Level) (MO : MapLVLInterface Data M)
:=  (IsBdlLvlMapLVLInterface Data M MO) <+ IsWFFull MO.

(** ---- *)

(** ** Leveled Map Interface - [LevelK/LvlD]  *)

Module Type IsLvlMapLVLDInterface 
  (Data : IsLvlETWL) (M : Interface.S Level) (MO : MapLVLInterface Data M) <: IsLvl MO.

Include IsLvlMapKDInterface Level Data M MO.
Import MO OP.P.

Section props.

Variable k m n : Lvl.t.
Variable x : M.key.
Variable t t' : t.

Parameter Wf_in_iff : Wf m t -> M.In x (shift m n t) <-> M.In x t.

Parameter shift_find_Wf :
  Level.Wf k x -> M.In x t ->
  M.find x t = M.find x t' -> M.find x (shift k n t) = M.find x (shift k n t').
  
Parameter shift_in_new_key : M.In x (shift (new_key t) n t) <-> M.In x t.

Parameter shift_new_notin : k >= (new_key t) -> ~ M.In k (shift k n t).

Parameter shift_new_refl : k >= (new_key t) -> new_key (shift k n t) = new_key t.

Parameter shift_max_refl : k >= (new_key t) -> max_key (shift k n t) = max_key t.

Parameter shift_max_key_gt_iff : max_key t > n <-> max_key (shift k m t) > (Level.shift k m n).

Parameter shift_max_key_le : max_key t <= max_key (shift k n t).

Parameter shift_new_key_le : new_key t <= new_key (shift k n t).

End props.

End IsLvlMapLVLDInterface.

(** ** Bindless Leveled Map Interface - [LevelK/LvlD]  *)
Module Type IsBdlLvlMapLVLDInterface  
  (Data : IsBdlLvlETWL) (M : Interface.S Level) (MO : MapLVLInterface Data M) <: IsBdlLvl MO
:= IsLvlMapLVLDInterface Data M MO <+ IsBindlessLeveledEx MO.

(** ** Alter. Leveled Map Interface - [LevelK/LvlD]  *)
Module Type IsLvlFullMapLVLDInterface
  (Data : IsLvlFullETWL) (M : Interface.S Level) (MO : MapLVLInterface Data M)
:= (IsLvlMapLVLDInterface Data M MO) <+ IsWFFull MO.

(** ** Alter. Bindless Leveled Map Interface - [LevelK/LvlD]  *)
Module Type IsBdlLvlFullMapLVLDInterface  
  (Data : IsBdlLvlFullETWL) (M : Interface.S Level) (MO : MapLVLInterface Data M) 
:=  (IsBdlLvlMapLVLDInterface Data M MO) <+ IsWFFull MO.