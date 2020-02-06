(**
----
_This file is part of_

----
*** A Formal Definition of JML in Coq #<br/># and its Application to Runtime Assertion Checking
Ph.D. Thesis by Hermann Lehner
----
Online available at #<a href="http://jmlcoq.info/">jmlcoq.info</a>#

Authors:
  - Hermann Lehner
  - David Pichardie (Bicolano)
  - Andreas Kaegi (Syntax Rewritings, Implementation of ADTs)

Copyright 2011 Hermann Lehner

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

----
*)


(** Formalization of Java semantic domain.
Based on The "Java (TM) Virtual Machine Specification, Second Edition, 
Tim Lindholm, Frank Yellin" *)

Require Export JMLExpressionNotations.
Require Export JMLNumeric.
Require Import List.
Require Import Relation_Operators.
Require Import DecidableType.
Require Import FSetInterface.

Open Scope Z_scope.

(** ** Semantic Domain *)

Module Type SEMANTIC_DOMAIN.

  Parameter UndefinedProp : Prop.

  Declare Module Prog : PROGRAM.
  Import Prog.

  Module JmlNotations := EXPRESSION_NOTATIONS Prog.
  Import JmlNotations.
  Import METHODSPEC.
  Import TYPESPEC.

  (** Numeric types *)

  Declare Module Byte  : NUMERIC with Definition power := 7.
  Declare Module Short : NUMERIC with Definition power := 15.
  Declare Module Int   : NUMERIC with Definition power := 31.
  Declare Module Long  : NUMERIC with Definition power := 63.

  Parameter UndefinedInt : Int.t.

  Parameter b2i : Byte.t -> Int.t.
  Parameter b2i_prop : forall b , Byte.toZ b = Int.toZ (b2i b).

  Parameter s2i : Short.t -> Int.t.
  Parameter s2i_prop : forall s , Short.toZ s = Int.toZ (s2i s).

  Parameter i2b : Int.t -> Byte.t.
  Parameter i2b_prop1 : forall i ,
    (Int.toZ i) mod 2^8 < 2^7 ->
    (Int.toZ i) mod 2^8 = Byte.toZ (i2b i).
  Parameter i2b_prop2 : forall i ,
    2^7 <= (Int.toZ i) mod 2^8 ->
    (Int.toZ i) mod 2^8 - 2^8 = Byte.toZ (i2b i).

  Parameter i2s : Int.t -> Short.t.
  Parameter i2s_prop1 : forall i ,
    (Int.toZ i) mod 2^16 < 2^15 ->
    (Int.toZ i) mod 2^16 = Short.toZ (i2s i).
  Parameter i2s_prop2 : forall i ,
    2^15 <= (Int.toZ i) mod 2^16 ->
    (Int.toZ i) mod 2^16 - 2^16 = Short.toZ (i2s i).

  Parameter i2bool : Int.t -> Prop.
  Parameter i2bool_prop_f : forall i ,
    (Int.toZ i) = 0 -> 
    i2bool i = False.	
  Parameter i2bool_prop_t : forall i ,
    (Int.toZ i) <> 0 -> 
    i2bool i = True.

  Inductive num : Set :=
    | I : Int.t -> num
    | B : Byte.t -> num
    | Sh : Short.t -> num.

  Parameter UndefinedNum : num.
 
  Definition n2i (n : num) : Int.t :=
    match n with
    | I i => i
    | B b => b2i b
    | Sh s => s2i s
    end.

  Definition n2z (n : num) : Z :=
    Int.toZ (n2i n).

  (** Object is the domain of objects in the heap *)
  Parameter Object : Set.

  Declare Module ObjDec : DecidableType with Definition t := Object
	                                with Definition eq := eq (A := Object).
  Declare Module ObjSet : WS with Module E := ObjDec.

  Parameter UndefinedObject : Object.

  (** Domain of primitive and reference values *)

  Inductive Value : Type :=
    | Bool  (b : Prop)
    | Num  (n :  num)
    | Ref  (o : Object)
    | Null.

  Parameter UndefinedValue : Value.

  Definition init_value (t : StaticType) : Value :=
    match t with
    | ReferenceType _ => Null
    | PrimitiveType BOOLEAN => Bool False
    | PrimitiveType _ => Num (I (Int.const 0))
    end.

  Definition v2b (v : option Value) : Prop :=
    match v with
    | Some (Bool b) => b
    | _ => UndefinedProp
    end.

  Definition v2n (v : option Value) : num :=
    match v with
    | Some (Num n) => n
    | _ => UndefinedNum
    end.

  Definition v2i (v : option Value) : Int.t :=
    match v with
    | Some (Num (I i)) => i
    | _ => UndefinedInt
    end.

  Definition v2l (v : option Value) : option Object :=
    match v with
    | Some (Ref l) => Some l
    | _ => None
    end.

  Definition l2v (o : option Object) : Value :=
    match o with
    | Some o' => Ref o'
    | None => Null
    end.

  Definition init_field_value (f : Field) : Value :=
    match FIELD.initValue f with
    | Some (int z)%jml => Num (I (Int.const z))
    | Some (true')%jml => Bool True
    | Some (false')%jml => Bool False
    | Some null => Null
    | _ => init_value (FIELDSIGNATURE.type (FIELD.signature f))
    end.
	
  (** General Purpose Dictionary, used for local Vars, Parameters, Assignable 
  maps, etc... *)
  Module Type DICT.

    Parameter t : Type.

    Parameter Key : Type.
    Parameter Val : Type.

    Parameter empty : t.


    Parameter get : t-> Key -> option Val.
    Parameter update : t -> Key -> Val -> t.
    Parameter remove: t -> Key -> t.
    Parameter filter: t -> (Key -> Prop) -> list Val.

    Definition In (y : Val) (l : t) : Prop := exists x, get l x = Some y. 

    Parameter content: t -> list Val.
    Parameter keys : t -> list Key.

    Parameter get_empty : forall v, get empty v = None.

    Definition singleton (a : Key) (b : Val) : t := update empty a b.

    Parameter get_update_same : forall l x v , get (update l x v) x = Some v.
    Parameter get_update_old : forall l x y v , x <> y -> 
      get (update l x v) y = get l y.

    Parameter get_remove_none: forall l x, get (remove l x) x = None.
    Parameter get_remove_old: forall l x y, x <> y -> 
      get (remove l x) y = get l y.

    Parameter filter_1: forall l f y ,
      List.In y (filter l f)  
        <-> 
      (exists x, get l x = Some y   /\ f x).

    Parameter content_1: forall l y,
	List.In y (content l)
	<->
	In y l.

    Parameter keys_1 : forall l x,
	List.In x (keys l)
	<->
	get l x <> None.

  End DICT.

  Declare Module VarDict : DICT 
    with Definition Key := Var
    with Definition Val := Value.

  Declare Module ParamDict : DICT
    with Definition Key := Param
    with Definition Val := Value.

  (** Helper definitions for ParamDict *)

  Fixpoint fill_param_dict(args : list Param) (params : list (Value)) (paramlist : ParamDict.t) {struct params} : ParamDict.t :=
    match args, params with
    | arg::argtail, par::partail => 
      fill_param_dict argtail partail (ParamDict.update paramlist arg par)
    | _ , _ => paramlist (* And cross the fingers that both lists are empty now (!wf) *)
    end.

  Definition lv2params (m : Method) (params : list Value) : ParamDict.t :=
    let args_tail := METHODSIGNATURE.parameters (METHOD.signature m) in
    let args := if METHOD.isStatic m then args_tail else paramThis :: args_tail in
    fill_param_dict args params ParamDict.empty.

  (** ** Heap Formalization *)

  Module Type HEAP.
    Parameter t : Type.

    Inductive Location : Set :=
      | StaticField : FieldSignature -> Location
      | InstanceField : Object -> FieldSignature -> Location
      | ArrayElement : Object -> Int.t -> Location.

    (* Runtime Type of a location. *)
    Inductive ObjectType : Set :=
      | ObjectObject : ClassName -> utsModifier -> ObjectType  
      | ObjectArray : Int.t -> StaticType -> utsModifier -> ObjectType.
    (* (ObjectArray length element_type) *)

    Parameter get : t -> Location -> option Value.
    Parameter update : t -> Location -> Value -> t.
    Parameter typeof : t -> Object -> option ObjectType.   
      (** typeof h loc = None -> no object, no array allocated at location loc *)
    Parameter new : t -> Program -> ObjectType -> option (Object * t).
      (** program is required to compute the size of the allocated element, i.e. to know
          the Class associated with a ClassName  *)

    (** Compatibility between a heap and a location *)
    Inductive Compat (h : t) : Location -> Prop :=
      | CompatStatic : forall f ,
          Compat h (StaticField f)
      | CompatObject : forall cn um loc f ,
          typeof h loc = Some (ObjectObject cn um) ->
          Compat h (InstanceField loc f)
      | CompatArray : forall length tp um loc i ,
          0 <= Int.toZ i < Int.toZ length ->
          typeof h loc = Some (ObjectArray length tp um) ->
          Compat h (ArrayElement loc i).

    Parameter get_update_same : forall h am v , Compat h am ->  get (update h am v) am = Some v.
    Parameter get_update_old : forall h am1 am2 v , am1<>am2 -> get (update h am1 v) am2 = get h am2.
    Parameter get_uncompat : forall h am , ~ Compat h am -> get h am = None.

    Parameter typeof_update_same : forall h loc am v ,
      typeof (update h am v) loc = typeof h loc.

    Parameter new_fresh_location : forall (h : t) (p : Program) (lt : ObjectType) (loc : Object) (h' : t) ,
      new h p lt = Some (loc, h') ->
      typeof h loc = None.

    Parameter new_typeof : forall (h : t) (p : Program) (lt : ObjectType) (loc : Object) (h' : t) ,
      new h p lt = Some (loc, h') ->
      typeof h' loc = Some lt.

    Parameter new_typeof_old : forall (h : t) (p : Program) (lt : ObjectType) (loc loc' : Object) (h' : t) ,
      new h p lt = Some (loc, h') ->
      loc <> loc' ->
      typeof h' loc' = typeof h loc'.

    Parameter new_defined_object_field : forall (h : t) (p : Program) (cn : ClassName) (um : utsModifier) (fs : FieldSignature) (f : Field) (loc : Object) (h' : t) ,
      new h p (ObjectObject cn um) = Some (loc, h') ->
      is_defined_field p cn fs f ->
      get h' (InstanceField loc fs) = Some (init_field_value f).

    Parameter new_undefined_object_field : forall (h : t) (p : Program) (cn : ClassName) (um : utsModifier) (fs : FieldSignature) (loc : Object) (h' : t),
      new h p (ObjectObject cn um) = Some (loc, h') ->
      ~ defined_field p cn fs ->
      get h' (InstanceField loc fs) = None.
 
    Parameter new_object_no_change : 
      forall (h : t) (p : Program) (cn : ClassName) (um: utsModifier) (loc : Object) (h' : t) (am : Location) ,
      new h p (ObjectObject cn um) = Some (loc, h') ->
      (forall (fs : FieldSignature) , am <> (InstanceField loc fs)) ->
      get h' am = get h am.

    Parameter new_valid_array_index : forall (h : t) (p : Program) (length : Int.t) (tp : StaticType) (um : utsModifier) (i : Int.t) (loc : Object) (h' : t) ,
      new h p (ObjectArray length tp um) = Some (loc, h') ->
      0 <= Int.toZ i < Int.toZ length ->
      get h' (ArrayElement loc i) = Some (init_value tp).

    Parameter new_unvalid_array_index : forall (h : t) (p : Program) (length : Int.t) (tp : StaticType) (um : utsModifier) (i : Int.t) (loc : Object) (h' : t) ,
      new h p (ObjectArray length tp um) = Some (loc, h') ->
      ~ 0 <= Int.toZ i < Int.toZ length ->
      get h' (ArrayElement loc i) = None.

    Parameter new_array_no_change : 
      forall (h : t) (p : Program) (length : Int.t) (tp : StaticType) (um : utsModifier) (loc : Object) (h' : t) (am : Location) ,
      new h p (ObjectArray length tp um) = Some (loc, h') ->
      (forall (i : Int.t) , am <> (ArrayElement loc i)) ->
      get h' am = get h am.

  End HEAP.

  Declare Module Heap : HEAP.

  Parameter InitHeap : Heap.t.

  Open Scope jml_scope.

  Parameter UndefinedType : Heap.ObjectType.
  Parameter UndefinedAM : Heap.Location.

  Declare Module LocDec : DecidableType with Definition t := Heap.Location
    with Definition eq := eq (A := Heap.Location).

  Declare Module LocSet : WS with Module E := LocDec.

  Definition Location := Heap.Location.

  Fixpoint list2LocSet (l : list Location) : LocSet.t :=
    match l with 
    | nil => LocSet.empty
    | (h::t) => LocSet.add h (list2LocSet t)
    end.

  Parameter LocSetAll : LocSet.t.
  Axiom LocSetAll_def : forall e, LocSet.In e LocSetAll.

Lemma LocSet_empty:
forall l,
~ LocSet.In l LocSet.empty.
Proof.
generalize LocSet.empty_1.
intros.
unfold LocSet.Empty in H.
apply H.
Qed.

Lemma ObjSet_empty:
forall l,
~ ObjSet.In l ObjSet.empty.
Proof.
generalize ObjSet.empty_1.
intros.
unfold ObjSet.Empty in H.
apply H.
Qed.

Lemma list2LocSet_1:
forall x l,
In x l <-> LocSet.In x (list2LocSet l).
Proof.
induction l.
 split; intros.
  inversion H.
  
  unfold list2LocSet in H.
  generalize LocSet.empty_1.
  intros.
  unfold LocSet.Empty in H0.
  elim H0 with x; trivial.
  
 split; intros.
  simpl in H.
  destruct H.
   unfold list2LocSet.
   apply LocSet.add_1.
   trivial.
   
   destruct IHl.
   unfold list2LocSet.
   apply LocSet.add_2.
   apply H0; trivial.
   
  unfold list2LocSet in H.
  case_eq (LocDec.eq_dec x a); intros.
   intuition.
   unfold LocDec.eq in e.
   rewrite e.
   auto with *.
   
   apply LocSet.add_3 in H.
    rewrite <- IHl in H.
    auto with *.
    
    auto.
Qed.

  (* Axiomatic definition to get all fields referenced by a star *)
  Parameter AllFields: Program -> Heap.t -> Object -> list FieldSignature.
  Axiom AllFields_def: forall p h loc fsig ,
   match Heap.typeof h loc with
   | Some (Heap.ObjectObject cn um) =>
      (In fsig (AllFields p h loc) <-> defined_field p cn fsig)
   | _ => AllFields p h loc = []
   end.

  Definition AllAmOfObject (p : Program) (h : Heap.t) (obj : Object) : LocSet.t :=
    fold_right 
      (fun fsig ams => 
        match findField p fsig with
        | Some f => 
          LocSet.add
          (
            if FIELD.isStatic f then
              Heap.StaticField fsig 
            else
              Heap.InstanceField obj fsig
          ) 
          ams
        | None => ams
        end
      )
      LocSet.empty 
      (AllFields p h obj).

  Definition LocInObjSet (loc : Location) (objs : ObjSet.t) : bool :=
  match loc with
    | Heap.InstanceField obj _
    | Heap.ArrayElement obj _ => ObjSet.mem obj objs
    | _ => false
  end.

  Definition LocInObj (loc : Location) (obj : Object) : bool :=
  match loc with
    | Heap.InstanceField o _
    | Heap.ArrayElement o _ => 
      if ObjDec.eq_dec o obj then true else false
    | _ => false
  end.

(** Facts on Object and Location Sets *)

Lemma LocInObjSet_empty:
forall loc,
~ LocInObjSet loc ObjSet.empty = true.
Proof.
intros.
unfold LocInObjSet.
destruct loc.
auto.
generalize ObjSet_empty.
intros.
intuition.
elim H with o.
apply ObjSet.mem_2;trivial.
generalize ObjSet_empty.
intros.
intuition.
elim H with o.
apply ObjSet.mem_2;trivial.
Qed.

Lemma IntersectEqual:
forall a b a' b',
LocSet.Equal a  b ->
LocSet.Equal a'  b' ->
LocSet.Equal (LocSet.inter a a') (LocSet.inter b b').
Proof.
split; intros.
 apply LocSet.inter_3.
  apply LocSet.inter_1 in H1.
  destruct H with a0; auto.
  
  apply LocSet.inter_2 in H1.
  destruct H0 with a0; auto.
  
 apply LocSet.inter_3.
  apply LocSet.inter_1 in H1.
  destruct H with a0; auto.
  
  apply LocSet.inter_2 in H1.
  destruct H0 with a0; auto.
Qed.

Lemma UnionEqual:
forall a b a' b',
ObjSet.Equal a  b ->
ObjSet.Equal a'  b' ->
ObjSet.Equal (ObjSet.union a a') (ObjSet.union b b').
Proof.
split; intros.
  apply ObjSet.union_1 in H1;destruct H1.
  destruct H with a0.
  apply H2 in H1.
 apply ObjSet.union_2;trivial.
 destruct H0 with a0.
 apply H2 in H1.
 apply ObjSet.union_3;trivial.
  apply ObjSet.union_1 in H1;destruct H1.
  destruct H with a0.
  apply H3 in H1.
 apply ObjSet.union_2;trivial.
 destruct H0 with a0.
 apply H3 in H1.
 apply ObjSet.union_3;trivial.
Qed.

Lemma LocInObj_ObjSet: forall loc obj objs,
  LocInObj loc obj = true ->
  ObjSet.In obj objs ->
  LocInObjSet loc objs = true.
Proof.
intros.
unfold LocInObj in H.
unfold LocInObjSet.
destruct loc.
inversion H.

destruct (ObjDec.eq_dec o).
unfold ObjDec.eq in e.
subst.
apply ObjSet.mem_1;trivial.
inversion H.

destruct (ObjDec.eq_dec o).
unfold ObjDec.eq in e.
subst.
apply ObjSet.mem_1;trivial.
inversion H.

Qed.

  Parameter ObjSet2LocSet: ObjSet.t ->LocSet.t.
  Axiom ObjSet2LocSet_def:
  forall loc objs , LocSet.In loc (ObjSet2LocSet objs) <-> LocInObjSet loc objs = true.

  Definition alive (h : Heap.t) (loc : Location) : Prop :=
  match loc with
  | Heap.InstanceField obj _ 
  | Heap.ArrayElement obj _ => Heap.typeof h obj <> None
  | _ => True
  end.

  Parameter AllLoc: Heap.t -> LocSet.t.
  Axiom AllLoc_def :
    forall h loc , alive h loc <-> LocSet.In loc (AllLoc h).
  	
(** Field statically or dynamically contained in  Datagroup *)

  Inductive direct_FieldInDg_static (p : Program): (*field*) Location -> (*dg*) Location -> Prop :=
  | direct_FieldInDg_static_def:
    forall dg_loc field_loc dg_obj dg_fsig field_obj field_fsig field_f dg,
    dg_loc = Heap.InstanceField dg_obj dg_fsig ->
    field_loc = Heap.InstanceField field_obj field_fsig ->
    dg_obj = field_obj ->
    findField p field_fsig = Some field_f ->
    In dg (FIELD.dataGroups field_f) ->
    DATA_GROUP.isDynamic dg = false ->
    In dg_fsig (DATA_GROUP.dataGroups dg) ->
    direct_FieldInDg_static p field_loc dg_loc.

  Inductive direct_FieldInDg_dynamic (p : Program) (h : Heap.t): (*field*) Location -> (*dg*) Location -> (* pivot *) Location -> Prop :=
  | direct_FieldInDg_dynamic_def:
    forall dg_loc field_loc dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f pivot_loc dg, 
    dg_loc = Heap.InstanceField dg_obj dg_fsig ->
    field_loc = Heap.InstanceField field_obj field_fsig ->
    pivot_loc = Heap.InstanceField pivot_obj pivot_fsig ->
    Heap.get h pivot_loc = Some (Ref field_obj)->
    findField p pivot_fsig = Some pivot_f ->
    In dg (FIELD.dataGroups pivot_f) ->
    DATA_GROUP.isDynamic dg = true ->
    DATA_GROUP.pivotTarget dg = Some (FieldDg field_fsig) ->
    In dg_fsig (DATA_GROUP.dataGroups dg) ->
    dg_obj = pivot_obj ->
    direct_FieldInDg_dynamic p h field_loc dg_loc pivot_loc.



  Inductive FieldInDg (p : Program) (h : Heap.t): (* field *) Location -> (* dg *) Location -> Prop :=
  | FieldInDg_step : forall field dg dg',
    FieldInDg p h dg' dg ->
    FieldInDg p h field dg' ->
    FieldInDg p h field dg
  | FieldInDg_static : forall field dg,
    direct_FieldInDg_static p field dg ->
    FieldInDg p h field dg
  | FieldInDg_dynamic : forall field dg pivot,
    direct_FieldInDg_dynamic p h field dg pivot ->
    FieldInDg p h field dg
  | FieldInDg_same : forall field dg, 
    field = dg ->  
    FieldInDg p h field dg.

  Parameter UnfoldDatagroup: Program -> Heap.t -> Location -> LocSet.t.
  Axiom UnfoldDatagroup_def:  forall p h f dg, 
      LocSet.In f (UnfoldDatagroup p h dg) <-> FieldInDg p h f dg.

  Parameter UnfoldDatagroups: Program -> Heap.t -> LocSet.t -> LocSet.t.
  Axiom UnfoldDatagroups_def: forall p h f dgs,
      LocSet.In f (UnfoldDatagroups p h dgs) <-> exists dg, LocSet.In dg dgs /\ LocSet.In f (UnfoldDatagroup p h dg). 

  Parameter PivotTargets: Program -> Heap.t -> (*pivot*) Location -> (*fields*) LocSet.t.
  Axiom PivotTargets_def : forall p h pivot f,
    LocSet.In f (PivotTargets p h pivot) <-> exists dg, direct_FieldInDg_dynamic p h f dg pivot.

  Parameter DynDgs: Program -> Heap.t -> (* field *) Location -> (* pivot *) Location -> (* dgs *) LocSet.t.
  Axiom DynDgs_def: forall p h f pivot dg,
    LocSet.In dg (DynDgs p h f pivot) <-> direct_FieldInDg_dynamic p h f dg pivot.

  Inductive PivotField (p : Program) (loc : Location) : Prop :=
  | PivotField_def:  forall fsig obj f dg,
    loc = Heap.InstanceField obj fsig ->
    findField p fsig = Some f ->
    In dg (FIELD.dataGroups f) ->
    DATA_GROUP.isDynamic dg = true ->
    PivotField p loc.

  Definition isPivot (p : Program) (loc : Location) : bool :=
    match loc with
    | Heap.InstanceField _ fsig => 
      match findField p fsig with
      | Some f =>
        fold_right 
          (fun a b => orb (DATA_GROUP.isDynamic a) b)
          false
          (FIELD.dataGroups f)
      | _ => false
      end
    | _ => false
    end.

 Lemma isPivot_PivotField:
    forall p loc,
    isPivot p loc = true <-> PivotField p loc.
Proof.
intros.
split; intros.
 unfold isPivot in H.
 case_eq loc; intros; rewrite H0 in H; try discriminate H.
 case_eq (findField p f); intros; rewrite H1 in H.
  case_eq (FIELD.dataGroups f0); intros; rewrite H2 in H.
   discriminate H.
   
   assert (forall dg , In dg (t :: l) -> In dg (FIELD.dataGroups f0)).
    intuition.
    rewrite H2 in |- *.
    trivial.
    
    clear H2.
    induction (t :: l).
     discriminate H.
     
     case_eq (DATA_GROUP.isDynamic a); intros.
      apply PivotField_def with f o f0 a; trivial.
      apply H3.
      auto with *.
      
      apply IHl0.
       simpl in H.
       rewrite H2 in H.
       unfold orb in H.
       trivial.
       
       intros.
       apply H3.
       auto with *.
       
  discriminate H.
  
 destruct H.
 unfold isPivot in |- *.
 rewrite H in |- *.
 rewrite H0 in |- *.
 induction (FIELD.dataGroups f).
  elim H1.
  
  simpl in H1.
  destruct H1.
   subst.
   simpl in |- *.
   rewrite H2 in |- *.
   progress trivial.
   
   simpl in |- *.
   destruct (DATA_GROUP.isDynamic a); trivial.
   simpl in |- *.
   apply IHl; trivial.
Qed.


  (** A value with the implicit information if a step was normal, exceptional or a runtime exception *)
  Inductive StepValue :=
    | normal_step : StepValue
    | normal_step_v : Value -> StepValue
    | exception_step : Object -> StepValue
    | error_step: Object -> StepValue.

  (** Return Value including termination condition *)
  Inductive ReturnVal : Type :=
    | Normal : option Value -> ReturnVal
    | Exception : Object -> ReturnVal.

  (** Universe Types at runtime *)
  Parameter Owner : Object -> Object.

  Definition isPeer (this : Object) (other : Object): Prop :=
    Owner this = Owner other.

  Definition isRep (this : Object) (other : Object) : Prop :=
    this = Owner other.

  Definition isTransRep: Object -> Object -> Prop :=
    clos_trans Object isRep.

  (* Used for invariants, RM8.2 RM18 *)
  Definition isRelevant (this : Object) (other : Object) : Prop :=
    isTransRep (Owner this) other.

  (* input-output native method execution *)
  Inductive NativeMethod : Type := 
    | NoImplem
    | Implem :  (Heap.t * list Value -> Heap.t * ReturnVal -> Prop) -> NativeMethod.

  Parameter native_implementation : Method -> NativeMethod.

  (** compatibility between ArrayKind and type *) 
  Inductive compat_ArrayKind_type : ArrayKind -> StaticType -> Prop :=
    | compat_ArrayKind_type_ref : forall rt,
        compat_ArrayKind_type Aarray (ReferenceType rt)
    | compat_ArrayKind_type_int : 
        compat_ArrayKind_type Iarray (PrimitiveType INT)
    | compat_ArrayKind_type_byte : 
        compat_ArrayKind_type Barray (PrimitiveType BYTE)
    | compat_ArrayKind_type_bool : 
        compat_ArrayKind_type Barray (PrimitiveType BOOLEAN)
    | compat_ArrayKind_type_short : 
        compat_ArrayKind_type Sarray (PrimitiveType SHORT).

  Inductive isReference : Value -> Prop :=
    | isReference_null : isReference Null
    | isReference_ref : forall loc , isReference (Ref loc).

  (** compatibility between ValKind and value *) 
  Inductive compat_ValKind_value : ValKind -> Value -> Prop :=
    | compat_ValKind_value_ref : forall v ,
        isReference v -> compat_ValKind_value Aval v
    | compat_ValKind_value_int : forall n ,
        compat_ValKind_value Ival (Num (I n)).

  (** compatibility between ArrayKind and value *) 
  Inductive compat_ArrayKind_value : ArrayKind -> Value -> Prop :=
    | compat_ArrayKind_value_ref : forall v ,
        isReference v -> compat_ArrayKind_value Aarray v
    | compat_ArrayKind_value_int : forall n ,
        compat_ArrayKind_value Iarray (Num (I n))
    | compat_ArrayKind_value_byte : forall n ,
        compat_ArrayKind_value Barray (Num (B n))
    | compat_ArrayKind_value_short : forall n ,
        compat_ArrayKind_value Sarray (Num (Sh n)).

  (** convert a value to be pushed on the stack *)
  Definition conv_for_stack (v : Value) : Value :=
    match v with
    | Num (B b) => Num (I (b2i b))
    | Num (Sh s) => Num (I (s2i s))
    | _ => v
    end.

  (** convert a value to be store in an array *)
  Definition conv_for_array (v : Value) (t : StaticType) : Value :=
    match v with
    | Ref loc => v
    | Num (I i) =>
      match t with
      | PrimitiveType INT => v
      | PrimitiveType BOOLEAN => Bool (i2bool i)
      | PrimitiveType BYTE => Num (B (i2b i))
      | PrimitiveType SHORT => Num (Sh (i2s i))
      | _ => v  (* impossible clase *)
      end
    | _ => v (* impossible case *)
    end.

  (** [assign_compatible_num source target] holds if a numeric value [source] can be 
    assigned to a variable of type [target]. This point is not clear in the JVM spec. *)
  Inductive assign_compatible_num : num -> primitiveType -> Prop :=
    | assign_compatible_int_int : forall i , assign_compatible_num (I i) INT
    | assign_compatible_short_int : forall sh , assign_compatible_num (Sh sh) INT
    | assign_compatible_byte_int : forall b , assign_compatible_num (B b) INT
    | assign_compatible_short_short : forall sh , assign_compatible_num (Sh sh) SHORT
    | assign_compatible_byte_byte : forall b , assign_compatible_num (B b) BYTE
    | assign_compatible_byte_boolean : forall b , assign_compatible_num (B b) BOOLEAN.

  (** [assign_compatible h source target] holds if a value [source] can be 
     assigned to a variable of type [target] *)
   
  Inductive assign_compatible (p : Program) (h : Heap.t) : Value -> StaticType -> Prop :=
    | assign_compatible_null : forall (t : refType) , 
        assign_compatible p h Null (ReferenceType t)
    | assign_compatible_ref_object_val : forall (obj : Object) (u : utsModifier) (t : refType) (en : TypeDefName) , 
        Heap.typeof h obj = Some (Heap.ObjectObject en u) ->
        compat_refType p (TypeDefType en u) t ->
        (*TODO Check Universe Type Modifier Compatibility here *)
        assign_compatible p h (Ref obj) (ReferenceType t)
    | assign_compatible_ref_array_val : forall (obj : Object) (u : utsModifier) (t : refType) (length : Int.t) (tp : StaticType) , 
        Heap.typeof h obj = Some (Heap.ObjectArray length tp u) ->
        compat_refType p (ArrayType tp u) t ->
        (*TODO Check Universe Type Modifier Copatibility here *)
        assign_compatible p h (Ref obj) (ReferenceType t)
    | assign_compatible_num_val : forall (n : num) (t : primitiveType) ,
        assign_compatible_num n t -> assign_compatible p h (Num n) (PrimitiveType t).


  Inductive types_compatible (p : Program) : Heap.ObjectType -> Heap.ObjectType -> Prop :=
    | subtype_object_val : forall lt1 lt2 cn1 cn2 um1 um2,
        lt1 = Heap.ObjectObject cn1 um1 ->
        lt2 = Heap.ObjectObject cn2 um2 ->
        compat_refType p (TypeDefType cn1 um1) (TypeDefType cn2 um2) ->
        types_compatible p lt1 lt2
    | subtype_array_val : forall lt1 lt2 l1 l2 t1 t2 um1 um2,
        lt1 = Heap.ObjectArray l1 t1 um1 ->
        lt2 = Heap.ObjectArray l2 t2 um2 ->
        compat_refType p (ArrayType t1 um1) (ArrayType t2 um2) ->
        types_compatible p lt1 lt2.

  Inductive handler_catch (p:Program) : ExceptionHandler -> PC -> ClassName -> Prop :=
        (* The current handler catches all the exceptions in its range *)
    | handler_catch_all : forall pc ex e ,
        EXCEPTIONHANDLER.catchType ex = None ->
        EXCEPTIONHANDLER.isPCinRange ex pc = true ->
        handler_catch p ex pc e

        (* The current handler specifies the type of exception it catches *)
    | handler_catch_one : forall pc ex cl1 cl2 ,
        EXCEPTIONHANDLER.catchType ex = Some cl1 ->
        EXCEPTIONHANDLER.isPCinRange ex pc = true ->
        subclass_name p cl2 cl1 ->
        handler_catch p ex pc cl2.

  (** Lookup in the given list of exception handlers if one of them catches
      the current exception *)

  Inductive lookup_handlers (p : Program) : list ExceptionHandler -> PC -> ClassName -> PC -> Prop :=
        (* The current handler catches the exception *)
    | lookup_handlers_hd_catchAll : forall pc ex exl e ,
        handler_catch p ex pc e ->
        lookup_handlers p (ex :: exl) pc e (EXCEPTIONHANDLER.handler ex)

        (* Continue with the next handler *)
    | lookup_handlers_tl : forall ex exl pc e pc' ,
        ~ handler_catch p ex pc e ->
        lookup_handlers p exl pc e pc' ->
        lookup_handlers p (ex :: exl) pc e pc'.


(** ** Signature of a Java Frame *)

Module Type ADDS.
  Parameter t : Type.
End ADDS.

Module Type FRAME.

  Declare Module Adds : ADDS.

  Record t : Type := make {
    params : ParamDict.t;
    vars : VarDict.t;
    pc : PC;
    ret : ReturnVal;
    adds : Adds.t
  }.

  Definition param (fr : t) (x : Param) : option Value :=
    ParamDict.get (params fr) x.

  Definition var (fr : t) (x : Var) : option Value :=
    VarDict.get (vars fr) x.

  Definition set_params (fr : t) (x : ParamDict.t) : t := 
    make  x (vars fr) (pc fr) (ret fr) (adds fr).

  Definition set_param (fr : t) (x : Param) (v : Value) : t :=
    set_params fr (ParamDict.update (params fr) x v).

  Definition set_vars (fr : t) (x : VarDict.t) : t :=
    make  (params fr) x (pc fr) (ret fr) (adds fr).

  Definition set_var (fr : t) (x : Var) (v : Value) : t :=
    set_vars fr (VarDict.update (vars fr) x v).

  Definition set_pc (fr : t) (x : PC) : t :=
    make  (params fr) (vars fr) x (ret fr) (adds fr).

  Definition set_ret (fr : t) (x : ReturnVal) : t :=
    make  (params fr) (vars fr) (pc fr) x (adds fr).

  Definition set_adds (fr : t) (x : Adds.t) : t :=
    make (params fr) (vars fr) (pc fr) (ret fr) x.

  Definition build (callee : Method) (params : ParamDict.t) (adds : Adds.t) : t :=
    let pc' := match METHOD.body callee with
    	| Some body =>
      	  STATEMENT.pc (METHODBODY.compound body)
	| None =>
	  NoBodyPC
	end  in      
    make params VarDict.empty pc' (Normal None) adds.

  Definition  this (fr : t) : option Object :=
    match ParamDict.get (params fr) paramThis with
    | Some (Ref loc) => Some loc
    | _ => None
    end.

End FRAME.

(** ** Signature of the State *)

Module Type STATE.
  
  Declare Module Adds : ADDS.

  Declare Module Frame : FRAME.

  Record t : Type := make {
    h : Heap.t;
    fr : Frame.t;
    adds : Adds.t
  }.

  Definition set_h (st : t) (h : Heap.t) : t :=
    make h (fr st) (adds st).
  Definition set_fr (st : t) (fr : Frame.t) : t :=
    make (h st) fr (adds st).
  Definition set_adds (st : t) (adds : Adds.t) : t :=
    make (h st) (fr st) adds.

  Definition build := make.

End STATE.

End SEMANTIC_DOMAIN.
