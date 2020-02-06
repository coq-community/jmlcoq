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

Require Import JMLProgramPlus.
Require Import ZArith.
Require Import ZHelpers.
Require Import LogicHelpers.
Require Import Bool.

Require Import Sumbool.

Require Import Ndec.
Require Import PosAux.
Require Import EqBoolAux.

Require Import Relation_Operators.

Require Import List.
Require Import ListFunctions.
Require Import ListHelpers.
Require Import OptionHelpers.
(** 
  Implementation of both the PROGRAM and PROGRAM_PLUS (see end of file)
  signatures based on the list data type.
 
 *)
Module Make <: PROGRAM.

  Definition decidable (A:Type) := forall x y:A, x=y \/ ~x=y.

  Definition PackageName   : Set := Z.
   
  Definition ShortTypeDefName      : Set := Z.
  Definition ShortMethodName     : Set := Z.
  Definition ShortFieldName      : Set := Z.
  Definition ShortModelFieldName := ShortFieldName.

  Definition ParamName  : Set := Z.
  Definition VarName    : Set := Z.

  Definition TypeDefName := PackageName * ShortTypeDefName.

  Definition ShortClassName := ShortTypeDefName.
  Definition ClassName := TypeDefName.

  Definition ShortInterfaceName := ShortTypeDefName.
  Definition InterfaceName := TypeDefName.

  Definition MethodName          := ClassName * ShortMethodName.
  Definition FieldName           := ClassName * ShortFieldName.
  Definition ModelFieldName      := ClassName * ShortModelFieldName.

  (* Comparison of entity names and associated proofs *)
  Definition eq_TypeDefName : TypeDefName -> TypeDefName -> bool := ZPair_eqb.
  Lemma eq_TypeDefName_spec : forall x y:TypeDefName, if eq_TypeDefName x y then x = y else x <> y.
    Proof. exact ZPair_eqb_spec. Qed.

  Definition PC : Set := Z.
  Definition PC_eq_dec : forall pc1 pc2:PC, {pc1=pc2}+{pc1<>pc2} := Z_eq_dec.
       
  (* Definition eq_PC : PC -> PC -> bool := Neqb. *)
  
  Inductive utsModifier : Set :=
    | peer
    | rep
    | any.

  Definition utsModifier_eq_dec : forall x y:utsModifier, {x=y}+{x<>y}.
  Proof.
    decide equality.
  Defined.

  Inductive primitiveType : Set :=
    | BOOLEAN  | BYTE | SHORT | INT.

  Inductive StaticType : Set :=
    | ReferenceType (rt : refType)
    | PrimitiveType (pt : primitiveType)
  with refType : Set := 
    | ArrayType (typ : StaticType) (um : utsModifier)
    | TypeDefType  (et : TypeDefName) (um : utsModifier)
    | NullType.

    (* + Int64, Float,Double *)
    (* + ReturnAddressType subroutines *)  

  Scheme my_type_ind := Minimality for StaticType Sort Prop
  with   my_refType_ind := Minimality for refType Sort Prop.

  Scheme my_type_rec := Minimality for StaticType Sort Set
  with   my_refType_rec := Minimality for refType Sort Set.

  Definition primitiveType_eq_dec : forall x y:primitiveType, {x=y}+{x<>y}.
  Proof. 
    decide equality. 
  Defined.

  Definition primitiveType_eq_bool : forall x y:primitiveType, {b : bool | if b then x = y else x <> y} := 
    fun x y => bool_of_sumbool (primitiveType_eq_dec x y).

  (* Comparison of primitive types *)
  Definition eq_primitiveType (x y:primitiveType) : bool :=
    match x, y with
    | BOOLEAN, BOOLEAN => true
    | BYTE, BYTE => true
    | SHORT, SHORT => true
    | INT, INT => true 
    | _, _ => false
    end.
  Lemma eq_primitiveType_spec : forall x y, if eq_primitiveType x y then x = y else x <> y.
  Proof.
   destruct x;destruct y;simpl;trivial; intro;discriminate.
  Qed.
  Lemma primitiveType_dec : decidable primitiveType.
  Proof.  exact (Aeq_dec _ eq_primitiveType eq_primitiveType_spec). Qed.  

  (* Comparison of types *)
  Fixpoint eq_type (t1 t2: StaticType) {struct t1} : bool := 
    match t1, t2 with 
    | ReferenceType rt1, ReferenceType rt2 => eq_reftype rt1 rt2
    | PrimitiveType pt1, PrimitiveType pt2 => eq_primitiveType pt1 pt2
    | _, _ => false
    end
  (* Comparison of reference types *)
  with eq_reftype (rt1 rt2: refType) {struct rt1} : bool := 
    match rt1, rt2 with
    | ArrayType t1 _, ArrayType t2 _           => eq_type t1 t2
    | TypeDefType en1 _, TypeDefType en2 _       => eq_TypeDefName en1 en2
    |_, _ => false
    end.
  Axiom eq_type_spec : forall t1 t2:StaticType, if eq_type t1 t2 then t1 = t2 else t1 <> t2.
  Axiom type_dec : decidable StaticType.


  Module FIELDSIGNATURE.
    Record t : Set := {
      name : ShortFieldName;
      type : StaticType
    }.    
    Axiom eq_dec : forall f1 f2:t, f1 = f2 \/ ~f1 = f2.
  End FIELDSIGNATURE.

  Definition ShortFieldSignature : Set := FIELDSIGNATURE.t.

  Module Type FIELDSIGNATURE_TYPE.
    Parameter name : ShortFieldSignature  -> ShortFieldName.
    Parameter type : ShortFieldSignature -> StaticType.
    Parameter eq_dec : forall f1 f2:ShortFieldSignature, f1 = f2 \/ ~f1 = f2.
  End FIELDSIGNATURE_TYPE.

  (* Check that FIELDSIGNATURE conforms to FIELDSIGNATURE_TYPE... *)
  Module FIELDSIGNATURE' : FIELDSIGNATURE_TYPE := FIELDSIGNATURE.

  Inductive Visibility : Set :=
    | Package | Protected | Private | Public
    | Spec_Public | Spec_Protected.

  Definition Visibility_eq_dec (v1 v2:Visibility) : {v1=v2}+{v1<>v2}.
  Proof.
    case v1; case v2; (left; reflexivity) || (right; discriminate).
  Defined.
  
  Definition eq_Visibility (v1 v2:Visibility) : bool := 
    let (b,_) := bool_of_sumbool (Visibility_eq_dec v1 v2) in b.

  Inductive MethodKind : Set :=
    | Default | Constructor | Finalizer | Initializer.

  (* Check that FIELD conforms to FIELD_TYPE... *)
  (*
  Module MODELFIELDSIGNATURE.
    Record t : Set := {
      name : ShortModelFieldName;
      type : type
    }.
    Axiom eq_dec : forall f1 f2:t, f1 = f2 \/ ~f1 = f2.
  End MODELFIELDSIGNATURE.
  *)

  Definition ShortModelFieldSignature := ShortFieldSignature. 

  (*
  Module Type MODELFIELDSIGNATURE_TYPE.
    Parameter name : ShortModelFieldSignature -> ShortModelFieldName.
    Parameter type : ShortModelFieldSignature -> type.
    Parameter eq_dec : forall f1 f2:ShortModelFieldSignature, f1 = f2 \/ ~f1 = f2.
  End MODELFIELDSIGNATURE_TYPE.
  *)

  (* Check that MODELFIELDSIGNATURE conforms to MODELFIELDSIGNATURE_TYPE... *)
  (* Module MODELFIELDSIGNATURE' : MODELFIELDSIGNATURE_TYPE := MODELFIELDSIGNATURE. *)
  
  Module PARAMSIGNATURE.
    Record t : Set := {
      name : ParamName;
      type : StaticType
    }.
    Definition eq_t (ps1 ps2:t) : bool := 
      let (n1,t1) := ps1 in
      let (n2,t2) := ps2 in 
        (Z_eqb n1 n2) && (eq_type t1 t2).
    Axiom eq_t_spec : forall p1 p2:t, if eq_t p1 p2 then p1=p2 else p1<>p2.
    Axiom eq_dec : forall p1 p2:t, p1 = p2 \/ ~p1 = p2.
  End PARAMSIGNATURE.

  Definition ParamSignature : Set := PARAMSIGNATURE.t.

  Module Type PARAMSIGNATURE_TYPE.
    Parameter name : ParamSignature -> ParamName.
    Parameter type : ParamSignature -> StaticType.
    Parameter eq_dec : forall p1 p2:ParamSignature, p1 = p2 \/ ~p1 = p2.
  End PARAMSIGNATURE_TYPE.

  (* Check that PARAMSIGNATURE conforms to PARAMSIGNATURE_TYPE... *)
  Module PARAMSIGNATURE' : PARAMSIGNATURE_TYPE := PARAMSIGNATURE.

  Module PARAM.
    Record t : Set := {
      signature : ParamSignature;
      isFinal : bool;
      isNullable : bool
    }.
    
    Definition eq_t (p1 p2:t) : bool := PARAMSIGNATURE.eq_t (signature p1) (signature p2).
    Axiom eq_t_spec : forall p1 p2:t, if eq_t p1 p2 then p1=p2 else p1<>p2.
    Axiom eq_dec : forall p1 p2:t, p1 = p2 \/ ~p1 = p2.
  End PARAM.

  Definition Param : Set := PARAM.t.

  (* TODO *)
  Parameter paramThis : Param.

  Definition PKG_lang_ : PackageName := 1%Z.
  Definition C_Exception_ : ShortClassName := 4%Z.

  Definition Exception_e_name : ParamName := 1%Z.

  (**
    In a signals clause /signals (Exception e) p/
    after the full2basic desugaring of the method specification clauses
    exception parameter e has its name always equal to signalsVarName.
   *)
  Definition Exception_e : Param := 
    let javaLangException : StaticType := ReferenceType (TypeDefType (PKG_lang_, C_Exception_) any) in
    PARAM.Build_t (PARAMSIGNATURE.Build_t Exception_e_name javaLangException) false false.

  Module Type PARAM_TYPE.
    Parameter signature : Param -> ParamSignature.
    Parameter isFinal : Param -> bool.
    Parameter isNullable : Param -> bool.
  End PARAM_TYPE.

  (* Check that PARAM conforms to PARAM_TYPE... *)
  Module PARAM' : PARAM_TYPE := PARAM.

  Module METHODSIGNATURE.
    Record t : Set := {
      name : ShortMethodName;
      parameters : list Param;
      result : option StaticType
    }.
    Definition eq_t (x y : t) : bool :=
      let (n1,p1,r1) := x in
      let (n2,p2,r2) := y in
        (Z_eqb n1 n2) && (list_eq _ PARAM.eq_t p1 p2) && (opt_eq _ eq_type r1 r2).
    Axiom eq_bool_spec : forall m m':t, if eq_t m m' then m=m' else m<>m'.
    Axiom eq_dec : forall m m':t, m=m' \/ m<>m'.
  End METHODSIGNATURE.

  Definition ShortMethodSignature : Set := METHODSIGNATURE.t.

  Module Type METHODSIGNATURE_TYPE.
    Parameter name : ShortMethodSignature -> ShortMethodName.
    Parameter parameters : ShortMethodSignature -> list Param.
    Parameter result : ShortMethodSignature -> option StaticType.
    Parameter eq_dec : forall mid1 mid2:ShortMethodSignature, mid1 = mid2 \/ ~mid1 = mid2.
  End METHODSIGNATURE_TYPE.

  (* Check that METHODSIGNATURE conforms to METHODSIGNATURE_TYPE... *)
  Module METHODSIGNATURE' : METHODSIGNATURE_TYPE := METHODSIGNATURE.

  Module EXCEPTIONHANDLER.
    Record t : Set := {
      catchType : option ClassName;
      isPCinRange : PC -> bool;
      handler : PC
    }.
  End EXCEPTIONHANDLER.

  Definition ExceptionHandler : Set := EXCEPTIONHANDLER.t.

  Module Type EXCEPTIONHANDLER_TYPE.
    Parameter catchType : ExceptionHandler -> option ClassName.
    Parameter isPCinRange : ExceptionHandler -> PC -> bool.
    Parameter handler : ExceptionHandler -> PC.
  End EXCEPTIONHANDLER_TYPE.

  (* Check that EXCEPTIONHANDLER conforms to EXCEPTIONHANDLER_TYPE... *)
  Module EXCEPTIONHANDLER' : EXCEPTIONHANDLER_TYPE := EXCEPTIONHANDLER.
 
  Module VARSIGNATURE.
    Record t : Set := {
      name : VarName;
      type : StaticType
    }.
    Axiom eq_dec : forall p1 p2:t, p1 = p2 \/ ~p1 = p2.
  End VARSIGNATURE.

  Definition VarSignature : Set := VARSIGNATURE.t.

  Module Type VARSIGNATURE_TYPE.
    Parameter name : VarSignature -> VarName.
    Parameter type : VarSignature -> StaticType.
    Parameter eq_dec : forall p1 p2:VarSignature, p1 = p2 \/ ~p1 = p2.
  End VARSIGNATURE_TYPE.

  (* Check that VARSIGNATURE conforms to VARSIGNATURE_TYPE... *)
  Module VARSIGNATURE' : VARSIGNATURE_TYPE := VARSIGNATURE.

  Module VAR.
    Record t : Set := {
      signature : VarSignature;
      isFinal : bool;
      isNullable : bool;
      isGhost : bool;
      isUninitialized : bool
    }.
  End VAR.

  Definition Var : Set := VAR.t.

  Module Type VAR_TYPE.
    Parameter signature : Var -> VarSignature.
    Parameter isFinal : Var -> bool.
    Parameter isNullable : Var -> bool.
    Parameter isGhost : Var -> bool.
    Parameter isUninitialized : Var -> bool.
  End VAR_TYPE.

  (* Check that VAR conforms to VAR_TYPE... *)
  Module VAR' : VAR_TYPE := VAR.

  Definition Label : Set := Z.
  Definition L_beginBody : Label := 0%Z.

  Definition MethodSignature     := ClassName * ShortMethodSignature.
  Definition FieldSignature      := ClassName * ShortFieldSignature.
  Definition ModelFieldSignature := ClassName * ShortModelFieldSignature.

  
  (* IMPORTANT CONSTANT CONVENTIONS FOR PARSER !! *)
  Definition javaLang         : PackageName := 1%Z.
  Definition EmptyPackageName : PackageName := 2%Z.
  Definition javaIo           : PackageName := 3%Z.
  
  Definition object                         : ShortClassName :=  1%Z.
  Definition exception                      : ShortClassName :=  4%Z.
  Definition RuntimeException               : ShortClassName :=  3%Z.
  Definition NullPointerException           : ShortClassName :=  4%Z.
  Definition ArrayIndexOutOfBoundsException : ShortClassName :=  5%Z.
  Definition ArrayStoreException            : ShortClassName :=  6%Z.
  Definition NegativeArraySizeException     : ShortClassName :=  7%Z.
  Definition ClassCastException             : ShortClassName :=  8%Z.
  Definition ArithmeticException            : ShortClassName :=  9%Z.
  Definition throwable                      : ShortClassName := 10%Z.
  Definition cloneable                      : ShortClassName := 11%Z.
  Definition serializable                   : ShortClassName := 12%Z.
  Definition class                          : ShortClassName := 13%Z.

  Definition NoBodyPC : Z :=( -1)%Z.

  Inductive optional (A : Type) : Type :=
    | NotSpecified : optional A
    | Specified: A -> optional A.
  Arguments Specified [A].
 Arguments NotSpecified {A}.

  (* REM: Needed? *)
  Inductive ArrayKind : Set :=
    | Aarray
    | Iarray
    | Barray
    | Sarray.
    
  (* REM: Needed? *)
  Inductive ValKind : Set :=
    | Aval
    | Ival.

  (* REM: Needed? *)
  Module Type OFFSET_TYPE.
    Parameter t : Set.
    Parameter jump : PC -> t -> PC.
  End OFFSET_TYPE.
  Declare Module OFFSET : OFFSET_TYPE.
  
  Module EXPRESSION.


    (* Identifier for LBLNEG LBLPOS *)
    (* TODO: Do we need this parameter? *)
    Definition Ident := Z.

    Inductive Quantifier : Set :=
      | Forall | Exists | Max | Min | NumOf | Product | Sum.

    Inductive Literal : Set :=
      | BoolLiteral (b : bool)
      | IntLiteral (z : Z).

    Inductive UnaryIntOp : Set :=
      | PostfixIncrement
      | PostfixDecrement
      | PrefixIncrement
      | PrefixDecrement
      | UnaryPlus
      | UnaryMinus
      | BitwiseComplement. (* ~ *)
   
    Inductive UnaryBoolOp : Set :=
      | LogicalComplement. (* ! *)
  
    Inductive BinaryIntOp : Set :=
      | Multiplication
      | Division
      | Remainder
      | Addition
      | Subtraction
      | BitwiseAnd (* & *)
      | BitwiseXor (* ^ *)
      | BitwiseOr (* | *)
      | ShiftLeft (* << *)
      | ShiftRightSigned (* >> *)
      | ShiftRightUnsigned. (* >>> *)
  
    Inductive RelationalOp : Set :=
      | IntEquality
      | IntInequality
      | Less
      | LessEqual
      | Greater
      | GreaterEqual.

    Inductive BinaryBoolOp : Set :=
      | BoolEquality
      | BoolInequality
      | LogicalAnd (* & *)
      | LogicalXor (* ^ *)
      | LogicalOr. (* | *)

    Inductive ConditionalOp : Set :=
      | ConditionalAnd (* && *)
      | ConditionalOr. (* || *)

    Inductive BoolAssignmentOp : Set :=
      | AssignmentLogicalAnd
      | AssignmentLogicalXor
      | AssignmentLogicalOr.

    Inductive IntAssignmentOp : Set :=
      | AssignmentMultiplication
      | AssignmentDivision
      | AssignmentRemainder
      | AssignmentAddition
      | AssignmentSubtraction
      | AssignmentShiftLeft
      | AssignmentShiftRightSigned
      | AssignmentShiftRightUnsigned
      | AssignmentBitwiseAnd
      | AssignmentBitwiseXor
      | AssignmentBitwiseOr.

    Inductive JMLBoolOp : Set :=
      | Equivalence (* <==> *)
      | Inequivalence (* <=!=> *)
      | LeftImplication (* <== *)
      | RightImplication (* ==> *).

    Inductive BinaryRefOp : Set :=
      | RefEquality
      | RefInequality.

    Inductive Expression : Type  :=
          (** Basics *)
      | null
      | literal (l : Literal)
      | new (t : StaticType)
      | newarray (t : StaticType) (dims : list Expression) (um : utsModifier) (initializers : option (list Expression))
      | method (method : MethodSignature) (target : option Expression) (params: list Expression)      
      | field (field : FieldSignature) (target : option Expression)
      | modelField (field : ModelFieldSignature) (target : option Expression)
      | var (var : Var)
      | array (target : Expression) (index : Expression)
      | arrayLength (target:Expression)
      | quantifier (quant : Var)
      | param (par : Param)
      | this

      | UnaryIntExpr (op : UnaryIntOp) (expr : Expression)
      | UnaryBoolExpr (op : UnaryBoolOp) (expr : Expression)
      | BinaryIntExpr (op : BinaryIntOp) (left : Expression) (right : Expression)
      | RelationalExpr (op : RelationalOp) (left : Expression) (right : Expression)
      | BinaryBoolExpr (op : BinaryBoolOp) (left : Expression) (right : Expression)
      | BinaryCondBoolExpr (op : ConditionalOp) (left : Expression) (right : Expression)
      | BinaryRefExpr (op : BinaryRefOp) (left : Expression) (right : Expression)
      | JMLBinaryBoolExpr (op : JMLBoolOp) (left : Expression) (right : Expression)
      | BoolAssignmentExpr (op : BoolAssignmentOp) (left : Expression) (right : Expression)
      | IntAssignmentExpr (op : IntAssignmentOp) (left : Expression) (right : Expression)
      | Assignment (left : Expression) (right : Expression)

        (** Conditional a?b:c *)
      | Conditional (cond : Expression) (_true : Expression) (_false : Expression)

          (** Type Ops *)
      | Cast (class : StaticType) (expr : Expression)
      | Subtype (left : Expression) (right : Expression) (** left <: right *)
      | InstanceOf (expr : Expression) (class : StaticType)

          (** JML Primaries *)
      | Result 
      | Old (expr : Expression)
      | OldL (expr : Expression) (l : Label)

          (** Coverage of Spec *)
      | NotAssigned (refs : list Expression)
      | NotModified (refs : list Expression) 
      | OnlyAccessed (refs : list Expression)
      | OnlyAssigned (refs : list Expression)
      | OnlyCalled (methods : list MethodSignature)
      | OnlyCaptured (methods : list MethodSignature)

          (** Location Properties *)
      | Fresh (refs : list Expression)
      | Reach (ref : Expression)

          (** Ressource Guarantees *)
      | DurationExpr (period : Expression)
      | Space (size : Expression)
      | WorkingSpaceExpr (size : Expression)

          (** Type Queries *)
      | TypeOf (loc : Expression) (** \typeof: Expression -> java.lang.Class *)
      | ElemType (array : Expression) 
      | GetType (type : StaticType)  (** \type: type -> java.lang.Class *)

          (** Array *)
      | NonNullElements (array : Expression)

          (** Multi-Threading Issues *)
      | Lockset
      | MaxObject (lockset : Expression)

          (** Other *)
      | IsInitialized (type : StaticType)
      | InvariantFor (loc : Expression)

          (** Labels *)
      | LblNeg (ident : Ident) (expr : Expression)
      | LblPos (ident : Ident) (expr : Expression)

          (** Quantifiaction *)
      | Quantification (q : Quantifier) (var : Var) (range : Expression) (expr : Expression).

  (* simplified version of store refs *)
  Inductive StoreRefPrefix :=
    | ThisRef
    | ParamRef (param : Param)
    | PathRef (target : StoreRefPrefix) (fsig: FieldSignature).

  Inductive StoreRef :=
    | StaticFieldRef (fsig : FieldSignature)
    | FieldRef (target : StoreRefPrefix) (fsig : FieldSignature)
    | AllFieldsRef (target : StoreRefPrefix).
(*    | AllArrayElemsRef (target : StoreRef)
    | ArrayElemRef (target : StoreRef) (elem: Expression)
    | ArrayRangeRef (target : StoreRef) (from : Expression) (to : Expression).
*)

  Inductive StoreRefList :=
    | Nothing
    | Everything
    | StoreRefs (sr: list StoreRef).


  (* HEL simplified version of dynamic datagroup maps to clause *)
  Inductive DynDgPivotTarget :=
    | FieldDg (fsig : FieldSignature).
    (*| AllFieldsDg.*)

    (* Definition expressionFold (A:Type) (f : Expression -> list A -> A) (e:Expression) : A. *)

    (**
      expressionMap f e
      Map function /f/ : Expression->Expression over expression /e/.
      f is recursively called on every subexpression of e and on e itself.
      E.g. expressionMap f ((var i) + (int 1)).
        (1) r1 = f (var i)
        (2) r2 = f (int 1)
        (3) f (r1 + r2)
     *)
    Fixpoint expressionMap (f : Expression -> Expression) (e:Expression) {struct e} : Expression := 
      let mapF := expressionMap f in

      let listMapF := List.map (expressionMap f) in

      let optionMapF oe := 
        match oe with
        | None => None
        | Some e => Some (expressionMap f e)
        end in

      match e with
      | null => f null
      | literal l => f (literal l)
      | new t => f (new t)
      | newarray t dims um None => f (newarray t (listMapF dims) um None)
      | newarray t dims um (Some inits) => f (newarray t (listMapF dims) um (Some (listMapF inits)))
      | method m target params => f (method m (optionMapF target) (listMapF params))
      | field fi target => f (field fi (optionMapF target))
      | modelField fi target => f (modelField fi (optionMapF target))
      | var v => f (var v)
      | array target index => f (array (mapF target) (mapF index))
      | arrayLength target => f (arrayLength (mapF target))
      | quantifier q => f (quantifier q)
      | param p => f (param p)
      | this => f this
      | UnaryIntExpr op e => f (UnaryIntExpr op (mapF e))
      | UnaryBoolExpr op e => f (UnaryBoolExpr op (mapF e))
      | BinaryIntExpr op l r => f (BinaryIntExpr op (mapF l) (mapF r))
      | RelationalExpr op l r => f (RelationalExpr op (mapF l) (mapF r))
      | BinaryBoolExpr op l r => f (BinaryBoolExpr op (mapF l) (mapF r))
      | BinaryCondBoolExpr op l r => f (BinaryCondBoolExpr op (mapF l) (mapF r))
      | BinaryRefExpr op l r => f (BinaryRefExpr op (mapF l) (mapF r))
      | JMLBinaryBoolExpr op l r => f (JMLBinaryBoolExpr op (mapF l) (mapF r))
      | BoolAssignmentExpr op l r => f (BoolAssignmentExpr op (mapF l) (mapF r))
      | IntAssignmentExpr op l r => f (IntAssignmentExpr op (mapF l) (mapF r))
      | Assignment l r => f (Assignment (mapF l) (mapF r))
      | Conditional i t e => f (Conditional (mapF i) (mapF t) (mapF e))
      | Cast cl e => f (Cast cl (mapF e))
      | Subtype e1 e2 => f (Subtype (mapF e1) (mapF e2))
      | InstanceOf e cl => f (InstanceOf (mapF e) cl)
      | Result => f Result
      | Old e => f (Old (mapF e))
      | OldL e l => f (OldL (mapF e) l)
      | NotAssigned refs => f (NotAssigned (listMapF refs))
      | NotModified refs => f (NotModified (listMapF refs))
      | OnlyAccessed refs => f (OnlyAccessed (listMapF refs))
      | OnlyAssigned refs => f (OnlyAssigned (listMapF refs))
      | OnlyCalled ms => f (OnlyCalled ms)
      | OnlyCaptured ms => f (OnlyCaptured ms)
      | Fresh refs => f (Fresh (listMapF refs))
      | Reach ref => f (Reach (mapF ref))
      | DurationExpr e => f (DurationExpr (mapF e))
      | Space e => f (Space (mapF e))
      | WorkingSpaceExpr e => f (WorkingSpaceExpr (mapF e))
      | TypeOf e => f (TypeOf (mapF e))
      | ElemType e => f (ElemType (mapF e))
      | GetType t => f (GetType t)
      | NonNullElements e => f (NonNullElements (mapF e))
      | Lockset => f Lockset
      | MaxObject e => f (MaxObject (mapF e))
      | IsInitialized t => f (IsInitialized t)
      | InvariantFor e => f (InvariantFor (mapF e))
      | LblNeg i e => f (LblNeg i (mapF e))
      | LblPos i e => f (LblPos i (mapF e))
      | Quantification q v r e => f (Quantification q v (mapF r) (mapF e))
      end.

    Section substitute.
      Variable x : Expression.
      Variable eq_x : Expression -> bool.

      (**
        expressionSubstitute x eq_x t e.
        Substitute t for x in e.
       *)
      Definition expressionSubstitute (x:Expression) (eq_x : Expression -> bool) (t:Expression) (e:Expression) : Expression :=
        let mapF (y:Expression) : Expression :=
          match eq_x y with
          | true  => t
          | false => y
          end in

        expressionMap mapF e.      
  End substitute.

  End EXPRESSION.
  Export EXPRESSION.

  Module Type DATA_GROUP_TYPE.
    Parameter t : Type.
    Parameter pivotTarget : t -> option DynDgPivotTarget.
    Parameter dataGroups : t -> list FieldSignature.
    Parameter isRedundant : t -> bool.

    Definition isDynamic (dg : t) : bool :=
    if pivotTarget dg then true else false.

    Parameter dataGroups_not_nil: forall t, dataGroups t <> nil.
  End DATA_GROUP_TYPE.

  Module DATA_GROUP <: DATA_GROUP_TYPE.
    Record tRec : Type := Build_t {
      pivotTarget : option DynDgPivotTarget;
      dataGroups : list FieldSignature;
      isRedundant : bool
    }.
    Definition t : Type := tRec.
    Definition isDynamic (dg : t) : bool :=
    if pivotTarget dg then true else false.

    Parameter dataGroups_not_nil: forall t, dataGroups t <> nil.
  End DATA_GROUP.


  Module FIELD.
    Inductive value : Set :=
      | Int (v:Z)
      | NULL
      | UNDEF. 

    Record t : Type := {
      signature : ShortFieldSignature;
      isFinal : bool;
      visibility : Visibility;
      specVisibility : Visibility;
      isStatic : bool;
      isGhost : bool;
      isNullable : bool;
      isMonitored : bool;
      initValue : option Expression;
      dataGroups : list DATA_GROUP.t
    }.   
  End FIELD.
  
  Definition Field : Type := FIELD.t.

  (* Operations on fields *)
  Module Type FIELD_TYPE.
    Parameter signature : Field -> ShortFieldSignature.    
    Parameter isFinal : Field -> bool.
    Parameter visibility : Field -> Visibility.
    Parameter specVisibility : Field -> Visibility. (* not sensible for ghost fields *)
    Parameter isStatic : Field -> bool.
       (* REM IMO makes only sense for local variables, see RM Appendix B, AKA *)
    (* Parameter isUninitialized : Field -> bool. *) 
    Parameter isGhost : Field -> bool.
    Parameter isNullable : Field -> bool.
    Parameter isMonitored : Field -> bool.
    (* Initial (default) value. Must be compatible with the type of the field. *)
    Parameter initValue : Field ->  option Expression.
    Parameter dataGroups : Field -> list DATA_GROUP.t.
  End FIELD_TYPE.

  (* Check that MODELFIELD conforms to MODELFIELD_TYPE... *)
  Module FIELD' : FIELD_TYPE := FIELD.

  Module MODELFIELD.
    Record t : Type := {
      signature : ShortModelFieldSignature;   
      visibility : Visibility;
      isStatic : bool;
      isNullable : bool;
      dataGroups : list DATA_GROUP.t
    }.
  End MODELFIELD.

  Definition ModelField : Type := MODELFIELD.t.

  Module Type MODELFIELD_TYPE.
    Parameter signature : ModelField -> ShortModelFieldSignature.    
    Parameter visibility : ModelField -> Visibility.
    Parameter isStatic : ModelField -> bool.
    Parameter isNullable : ModelField -> bool.
    Parameter dataGroups : ModelField -> list DATA_GROUP.t.

  End MODELFIELD_TYPE.

  (* Check that MODELFIELD conforms to MODELFIELD_TYPE... *)
  Module MODELFIELD' : MODELFIELD_TYPE := MODELFIELD.

  Module Type LOOP_ANNOTATION_TYPE.
    Parameter t : Type.
    
    Parameter expression : t -> optional Expression.
    Parameter expressionRedundantly : t -> optional Expression.
    Parameter invariants : t -> list Expression.
    Parameter invariantsRedundantly : t -> list Expression.
    Parameter variants : t -> list Expression.
    Parameter variantsRedundantly : t -> list Expression.
  End LOOP_ANNOTATION_TYPE.

  Module LOOP_ANNOTATION <: LOOP_ANNOTATION_TYPE.
    Record tRec : Type := Build_t {
      expression : optional Expression;
      expressionRedundantly : optional Expression;
      invariants : list Expression;
      invariantsRedundantly : list Expression;
      variants : list Expression;
      variantsRedundantly : list Expression
    }.
    Definition t : Type := tRec.
  End LOOP_ANNOTATION.

  Definition LoopAnnotation := LOOP_ANNOTATION.t.

  Inductive StatementType {Statement Block : Type} : Type :=
        (** The Basics *)
    | Compound (block : Block)
    | ExprStmt (e : Expression)

        (** Conditional *)
    | IfStmt (test : Expression) (_then : Statement) (_else : option Statement)
    | SwitchStmt (expr : Expression) (cases : list ((list Expression)*(list Statement))) (default : option (list Statement))

        (** Loops *)
    | WhileLoop (anno:LOOP_ANNOTATION.t) (test : Expression) (body : Statement)
    | DoLoop    (anno:LOOP_ANNOTATION.t) (body : Statement) (test : Expression)
    | ForLoop   (anno:LOOP_ANNOTATION.t) (init : list Statement) (test : Expression) (step : list Expression) (body : Statement)

        (** Abnormal Termination *)
    | BreakStmt (label : option Label)
    | ContStmt (label : option Label)

        (** Return Statement *)
    | ReturnStmt (expr : option Expression)

        (** Exception Handling Statements *)
    | TryBlock (block : Statement) (handlers : list (Param * Statement)) (finally : option Statement)
    | ThrowStmt (expr : Expression)

        (** Java Assertion *)
    | JavaAssertion (expr : Expression)  (label : option Expression)

        (** JML Statements *)
    | LocalAssertion (expr : Expression) (label : option Expression) (redundantly : bool) 
    | LocalAssumption (expr : Expression) (label : option Expression) (redundantly : bool) 
    | SetGhost (assignment : Expression)
    | Unreachable

        (*|  Redefining (* Eh?! Only used in Model Programs, i guess... kicked out for the moment *) *)
    | Debug (expr : Expression)
    | HenceBy (expr : Expression) (redundantly : bool)
        
    (*| LoopInvariant (expr : Expression) (redundantly : bool)*)
    (*| LoopVariant (expr : Expression) (redundantly : bool)*)

    | varDeclStmt (var : Var) (expr : option Expression)

        (* No operation (= empty statement ;), also used within an empty block *)
    | Nop

        (* this(...), super(...) *)
    | ThisCallStmt  (method : MethodSignature) (params: list Expression)
    | SuperCallStmt (method : MethodSignature) (params: list Expression).

  (** The inductive types for statments/blocks have to be defined together as they are mutually dependent. *)
  Inductive statementRec : Type := Build_statementRec (pc:PC) (label:option Label) (type:StatementType (Statement := statementRec) (Block := blockRec))
       with blockRec     : Type := Build_blockRec (localVariables : list Var) (statements:list statementRec).

  Module Type STATEMENT_TYPE.
    (* Statement module type, holding relevent statement data and 
     * the type of statement *)
    Parameter t : Type.
    Parameter b : Type.
    Parameter label : t -> option Label.
    Parameter pc    : t -> PC.
    Parameter type  : t -> StatementType (Statement := t) (Block := b).
  End STATEMENT_TYPE.

  Module STATEMENT <: STATEMENT_TYPE.
    Definition t : Type := statementRec.
    Definition b : Type := blockRec.

    Definition Build_t : PC -> option Label -> StatementType -> t := Build_statementRec.
    Definition label (stmt:t) : option Label     := match stmt with Build_statementRec _ l _ => l end.
    Definition pc (stmt:t) : PC                  := match stmt with Build_statementRec p _ _ => p end.
    Definition type (stmt:t) : StatementType     := match stmt with Build_statementRec _ _ s => s end.
  End STATEMENT.

  Module Type BLOCK_TYPE.
    Definition t := STATEMENT.b.

    (** List of local variables defined directly within this block, not within subblocks *)
    Parameter localVariables : t -> list Var.

    (** PC of the first statement in this block, if present *)
    Parameter first          : t -> option PC.

    (** PC of the last statement in this block, if present *)
    Parameter last           : t -> option PC.   

    (** Statement at the given pc, if present *)
    Parameter statementAt    : t -> PC -> option STATEMENT.t.

    (** Next PC if present *)
    Parameter next           : t -> PC -> option PC.

    (** Is the given PC part of this block? *)
    Parameter elem : t -> PC -> bool.

    (** A given PC is part of this block if there exists a statement with this pc *)
    Axiom elem_def : forall t pc, 
      elem t pc = true -> exists s, statementAt t pc = Some s /\ STATEMENT.pc s = pc.

    (** If statementAt returns a statement s for a given pc, the pc of s must match the given pc. *)
    Axiom statementAt_def : forall t pc s, 
      statementAt t pc = Some s -> STATEMENT.pc s = pc.

    (** The result of first is a valid pc in the given block. *)
    Axiom first_elem : forall t pc, first t = Some pc -> elem t pc = true.

    (** The result of last is a valid pc in the given block. *)
    Axiom last_elem : forall t pc, last t = Some pc -> elem t pc = true.

    (** If pc is the last pc in a given block, then there is no next pc in the same block. *)
    Axiom last_def : forall b pc, last b = Some pc -> next b pc = None.

    (** the result of next is a valid pc in the given block. *)
    Axiom next_elem : forall t pc1 pc2, next t pc1 = Some pc2 -> elem t pc2 = true.

  End BLOCK_TYPE.

  Module BLOCK <: BLOCK_TYPE.
    Import STATEMENT.

    Definition t := STATEMENT.b.
    Definition Build_t : list STATEMENT.t -> t := Build_blockRec nil.

    (** The list of statements is directly stored in the statementRec type *)
    Definition statements (stmt:t) : list STATEMENT.t := match stmt with Build_blockRec _ s => s end. 

    (** 
      The list of local variables is extracted from the list of statements;
      It corresponds to the list of variables of all variable declaration statements.
     *)
    Definition localVariables (block:t) : list Var := 
      (* match stmt with Build_blockRec v _ => v end. *)
      let fix variables (stmts:list STATEMENT.t) : list Var :=
        match stmts with
        | nil => nil
        | (Build_statementRec _ _(varDeclStmt v _))::ss => v :: variables ss
        | _::ss => variables ss
        end in
      variables (statements block).

    (** eq_PC_Stmt pc1 s <-> pc1 = STATEMENT.pc s *)
    Definition eq_PC_Stmt    (pc1:PC) (s:STATEMENT.t) : Prop := pc1 = pc s.

    (** neq_PC_Stmt pc1 s <-> pc1 <> STATEMENT.pc s *)
    Definition neq_PC_Stmt   (pc1:PC) (s:STATEMENT.t) : Prop := pc1 <> pc s.

    (** The equality pc1 ?= STATEMENT.pc s is decidable *)
    Definition PC_Stmt_eq_dec (pc1:PC) (s:STATEMENT.t) : {eq_PC_Stmt pc1 s}+{neq_PC_Stmt pc1 s} :=
      PC_eq_dec pc1 (pc s).

    (**
      Strongly specified counterpart of the statementAt function,
      statementAtS either returns a statement s together with a proof that
      its pc matches pc1 or a proof that no statement in the given block matches pc1.
     *)
    Definition statementAtS (b:BLOCK.t) (pc1:PC) :
      {s:STATEMENT.t | In s (statements b) & eq_PC_Stmt pc1 s}+{AllS (neq_PC_Stmt pc1) (statements b)}.
    Proof.
      apply (Find _ _ (PC_Stmt_eq_dec pc1) (statements b)).
    Defined.

    (** statementAt is easily defined in terms of its strongly specified counterpart statementAtS *)
    Definition statementAt (block:t) (pc1:PC) : option STATEMENT.t :=
      match (statementAtS block pc1) with
      | inleft (exist2 _ _ s P Q) => Some s
      | inright _ => None
      end.

    (*
      Idea of proof:
      - unfold/destruct statementAtS:
      (1) case {AllS (neq_PC_Stmt pc1) (statements b)} is easily discharged using discriminate
      (2) case {s:STATEMENT.t | In s (statements b) & eq_PC_Stmt pc1 s}
            is discharged by using the given proof eq_PC_Stmt pc1 s,
            tactic case_eq is used such to not loose to much information during the proof.
    *)
    Theorem statementAt_def : forall b pc1 s, 
      statementAt b pc1 = Some s 
      -> STATEMENT.pc s = pc1.
    Proof.
      intros b0 pc1 s H. 
      unfold statementAt in H.
      destruct (statementAtS b0 pc1) as [Ex x|Ex x]. 
      Focus 2.
      discriminate H.

      case_eq Ex.
      intros x P Q ex.
      rewrite ex in H.
      inversion H.
      rewrite Q.
      rewrite H1.
      reflexivity.
    Qed.

    (* elem is sort of isomorphic to statementAt *)
    Definition elem (block:t) (pc1:PC) : bool :=
      match (statementAtS block pc1) with
      | inleft (exist2 _ _ s P Q) => true
      | inright _ => false
      end.

    (*
      Idea of proof:
      - unfold elem, destruct statementAtS
      - interesting case: 
          {s:STATEMENT.t | In s (statements b) & eq_PC_Stmt pc1 s} (sS)
          instantiate and use the given proof
    *)
    Theorem elem_def : forall t pc, 
      elem t pc = true -> exists s, statementAt t pc = Some s /\ STATEMENT.pc s = pc.
    Proof.
      intros b0 pc1 in_b0.
      unfold elem in in_b0.
      case_eq (statementAtS b0 pc1).
      Focus 2.
      intros.
      rewrite H in in_b0. 
      discriminate in_b0.

      intros sS H.
      destruct sS.
      exists x.
      split.
      unfold statementAt.
      rewrite H.
      reflexivity.
      auto.
    Qed.
    
    (** 
      Inverse elem_def statement: for every statement s0 in (statements t) holds that
      elem t (STATEMENT.pc s0) is true.
     *)
    (* Idea of proof:
       case distinction on statementAtS t0 (pc s0):
       - left case trivial
       - right case discharged by contradiction, using the fact that 
         (1) it holds that AllS (neq_PC_Stmt (pc s0)) (statements t0)
             (and therefore neq_PC_Stmt (pc s0) s0 but
         (2) we know that eq_PC_Stmt (pc s0) s0 holds
    *)
    Theorem elem_def_inv : forall t s0, In s0 (statements t) -> elem t (STATEMENT.pc s0) = true.
    Proof.
      intros.
      unfold elem.
      destruct (statementAtS t0 (pc s0)).
      destruct s as (s1,_,_).
      reflexivity.

      assert (neq_PC_Stmt (pc s0) s0).
      apply AllS_x_P with (l := statements t0); assumption.
      unfold neq_PC_Stmt in H0.
      auto.
    Qed.

    (**
      Stmts_unique:
      For any two distinct statements s1 and s2 in the same block, it must hold that
      the pc's of s1 and s2 are different.
      This implies that no statement s may appear more than once in a block (-> PC_unique_impl).
      The frontend must guarantee that every built BLOCK.t value respects this axiom.
     *)
    Axiom Stmts_unique : forall b x ss,
      Suffix (x::ss) (statements b) ->
      AllS (neq_PC_Stmt (pc x)) ss.

    (**
      For any two statements in the same block, it holds that if the pc's of the 
      two statements are equal, then the two statements are equal as well.
      This is a simple consequence of axiom Stmts_unique.
     *)
    (* Idea of proof: use Stmts_unique
       - prove: either x is in suffix (y::s) or y is in suffix (x::s)
       - in both cases either x = y or we can 
         generate a contradiction to pc x = pc y using Stmts_unique
     *)
    Lemma PC_unique_impl : forall x y b, 
      In x (statements b) -> 
      In y (statements b) -> 
      pc x = pc y -> 
      x = y.
    Proof.
      intros.
      assert ((exists s, Suffix (x::s) (statements b0) /\ In y (x::s)) \/
      (exists s, Suffix (y::s) (statements b0) /\ In x (y::s))).
      apply Suffix_x_y_or_y_x; assumption.
      case H2; clear H2.

      (* case In y (x::s) *)
      intro H3.
      elim H3; intros.
      destruct H2.
      elim H4.
      (* trivial case x=y *)
      intuition.
      (* case In y s, contradiction pc x <> pc y and pc x = pc y *)
      intro H5.
      assert (neq_PC_Stmt (pc x) y).
      apply AllS_x_P with (l := x0).
      apply Stmts_unique with (b := b0); assumption.
      assumption.
      unfold neq_PC_Stmt in H6.
      elim H6; auto.
      
      (* case In x (y::s), analogous *)
      intro H3.
      elim H3; intros.
      destruct H2.
      elim H4.
      intuition.
      intro H5.
      assert (neq_PC_Stmt (pc y) x).
      apply AllS_x_P with (l := x0).
      apply Stmts_unique with (b := b0); assumption.
      assumption.
      unfold neq_PC_Stmt in H6.
      elim H6; auto.
    Qed.

    (**
      Inverse statement to statementAt_def:
      For every statement s in statements b,
      statementAt b (STATEMENT.pc s) = Some s.
     *)
    (* Idea of proof: case distinction of statementAtS 
       (1) case {s:STATEMENT.t | In s (statements b) & eq_PC_Stmt pc1 s}
            is discharged by using the given proofs and axiom PC_unique_impl. 
       (2) case {AllS (neq_PC_Stmt pc1) (statements b)} is again discharged using contradiction
            and lemma AllS_x_P.
    *)
    Theorem statementAt_def_inv : forall b pc1 s, In s (statements b) -> 
      STATEMENT.pc s = pc1 -> statementAt b pc1 = Some s.
    Proof.
      intros b0 pc1 s H1 H2.
      unfold statementAt.
      destruct (statementAtS b0 pc1) as [Ex x|Ex x]. 
      case Ex.
      intros x P Q.
      assert (x=s).
      apply (PC_unique_impl x s b0).
      assumption. assumption.
      rewrite <- Q. 
      auto. 
      rewrite H; reflexivity.
      assert (pc1 <> pc s).
      apply (AllS_x_P STATEMENT.t (neq_PC_Stmt pc1) (statements b0) s Ex H1).
      unfold not in H.
      elim H.
      auto.
    Qed.

    (**
      Strongly specified version of function first,
      returning either the statement at the head of the list of statemements
      or a proof that the list of statements is empty.
     *)
    Definition firstS : forall (block:BLOCK.t), 
      {s:STATEMENT.t | head (statements block) = Some s}+{statements block=nil}.
    Proof.
      intro block.
      case (statements block).
      right; reflexivity.
      
      intros s0 l.
      left.
      exists s0.
      auto.
    Defined.

    (** first is easily defined in terms of firstS *)
    Definition first (block:t) : option PC :=
      match (firstS block) with
      | inleft (exist _ s0 _) => Some (STATEMENT.pc s0)
      | inright _ => None
      end.

    Theorem first_elem : forall t pc, first t = Some pc -> elem t pc = true.
    Proof.
      intros b0 pc1 H.
      unfold first in H.
      destruct (firstS b0).
      destruct s.
      inversion H.
      apply (elem_def_inv b0 x).
      apply In_head.
      assumption.

      discriminate H.
    Qed.

    (**
      Retrieve the suffix s of the list of stmts where the PC of the first element of the suffix s
      is equal to the given pc.
      Returns a proof that s is a suffix of l and that the head of the suffix has the desired property,
      or a proof that no element in the list has the given pc.
     *)

    Definition suffixS : forall (stmts:list STATEMENT.t) (pc:PC),
      {l:list STATEMENT.t &{s | Suffix l stmts /\ head l = Some s /\ STATEMENT.pc s = pc}}+{AllS (neq_PC_Stmt pc) stmts}.
    Proof.
      intros stmts pc0.
      induction stmts.
      (* case stmts = nil *)
      right.
      auto with *.
      (* case a :: stmts *)
      case IHstmts.
      (* case pc 'in' stmts *)
      intro Hst.
      left.
      destruct Hst; destruct s.
      exists x; exists x0.
      split; [apply Suffix_step; intuition | intuition].
      (* case pc not 'in' stmts --> case on a *)
      intro Hns.
      case (PC_Stmt_eq_dec pc0 a).
      intro Heq.
      (* case pc0 = pc of a *)
      left.
      exists (a::stmts); exists a.
      split; [apply Suffix_l_l | idtac].
      split; [auto | rewrite Heq; auto].
      (* case pc0 <> pc of a *)
      intro Hneq.
      right.
      auto with *.
  Defined.

    (**
      next is easily defined in terms of suffixS:
      the result is the PC of the tail (if present) of the suffix.
     *)
    Definition next (block:t) (pc0:PC) : option PC :=
      match suffixS (statements block) pc0 with
      | inleft (existT _ l _) =>
          match tail l with
          | n::_ => Some (STATEMENT.pc n)
          | nil => None
          end
      | inright _ => None
      end.

    (* Idea of proof:
       - use the proof contained in the result of suffixS
       - use elem_def_inv, i.e. that for every element s In the list elem t (pc s) is true
       - use Suffix_in to proof that the element is in the list.
    *)
    Theorem next_elem : forall t pc1 pc2, next t pc1 = Some pc2 -> elem t pc2 = true.
    Proof.
      intros block pc1 pc2.
      unfold next.
      destruct (suffixS (statements block) pc1).
      destruct s; destruct s.
      case_eq (tail x).
      intros _ Hdis; discriminate Hdis. 

      intros n tl Htl Hpc.
      inversion Hpc.
      apply elem_def_inv.
      apply Suffix_In with (s := x).
      intuition.
      destruct x.
      discriminate Htl.
      simpl in Htl.
      rewrite Htl.
      intuition.
      intro Hdis; discriminate Hdis.
    Qed.

    (** last is easily defined in terms of lastS, its strong counterpart. *)
    Definition last (block:t) : option PC :=
      match lastS (statements block) with
      | inleft (exist _ s0 _) => Some (STATEMENT.pc s0)
      | inright _   => None
      end.

    (** 
      last_elem is easily proved using the proof contained in the result of lastS
      and elem_def_inv/Last_In.
     *)
    Theorem last_elem : forall t pc, last t = Some pc -> elem t pc = true.
    Proof.
      intros b0 pc1 H.
      unfold last in H.
      destruct (lastS (statements b0)).
      destruct s. 
      inversion H.
      apply (elem_def_inv b0 x).
      apply Last_In.
      assumption.

      discriminate H.
    Qed.

    (**
      For any suffix s in a statement list:
      If the first and the last element of s are the same statement x,
      then s consists of this statement x only.
     *)
    (* Idea of proof:
       Three cases:
       1. s=nil     -> trivial 
       2. s=x::nil  -> assumption
       3. s=x::y::s -> generate contradiction pc x <> pc x using Stmts_unique
    *)
    Lemma Last_head_singleton : forall b s x,
      Suffix s (statements b) -> 
      head s = Some x ->
      Last x s ->
      s = x::nil.
    Proof.
      intros.
      destruct s.
      (* case s = nil *)
      discriminate H0.

      destruct s.
      (* case s = t0::nil *)
      inversion H0; reflexivity.
    
      (* case t0::t1::s *)
      inversion H0. (* t0 = x *)
      assert (neq_PC_Stmt (pc x) x).
      apply AllS_x_P with (l := t1::s).
      apply Stmts_unique with (b := b0).
      rewrite <- H3; assumption.
      apply Last_In.
      apply Last_step_inv with (y := t0).
      intro Hdis; discriminate Hdis.
      assumption.
      auto.
      unfold neq_PC_Stmt in H2. 
      elim H2; reflexivity.
    Qed.         

    (* Idea of proof:
       Interesting case in next implementation:
       match suffixS (statements block) pc0 with
       | inleft (existT l _) => match tail l with ...
       
       -> Prove that l = x::nil using Last_head_singleton,
          since we now that x is the last element (assumption) and
          that x is the first element of the suffix (pc x = pc0)
    *)
    Theorem last_def : forall b pc, last b = Some pc -> next b pc = None.
    Proof.
      intros block pc0 Hlast.
      unfold last in Hlast.
      destruct (lastS (statements block)).
      destruct s.
      inversion Hlast; clear Hlast.
      unfold next.
      rewrite H0.
      destruct (suffixS (statements block) pc0).
      destruct s; destruct s.
      destruct a.
      destruct H1.
      assert (Last x x0).
        elim H; intros p Heq.
        rewrite <- Heq in l.
        apply Last_app_inv with (l1 := p).
        intro Hnil.
        rewrite Hnil in H1; discriminate H1.
        assumption.
      rewrite <- H0 in H2.
      apply PC_unique_impl with (b := block) in H2.
      rewrite H2 in H1.
      assert (x0 = x::nil).
      apply Last_head_singleton with (b := block); assumption.
      rewrite H4; reflexivity.
      apply Suffix_In with (s := x0). 
      assumption.
      apply In_head; assumption.
      apply Suffix_In with (s := x0).
      assumption.
      apply Last_In; assumption.
      reflexivity.
      discriminate Hlast.
    Qed. 

  End BLOCK.

  Module METHODBODY.
    Record t : Type := {
      block : BLOCK.t;
      exceptionHandlers : list ExceptionHandler
    }.

    Definition compound (body:t) : STATEMENT.t :=
      STATEMENT.Build_t 0%Z (Some L_beginBody) (Compound (block body)).

    (* /compound/ is always a compound statement (block) with label L_beginBody *)
    Lemma compound_is_compound : forall body:t, 
      exists bl, 
      STATEMENT.type (compound body) = Compound bl 
      /\ STATEMENT.label (compound body) = Some L_beginBody.
    Proof.
      intro body.
      exists (block body).
      simpl.
      split; reflexivity.
    Qed.

  End METHODBODY.

  Definition MethodBody : Type := METHODBODY.t.

  Module Type METHODBODY_TYPE.
    Parameter compound : MethodBody -> STATEMENT.t.

    (* /compound/ is always a compound statement (block) with label L_beginBody *)
    Axiom compound_is_compound : forall body:MethodBody, 
      exists bl, 
      STATEMENT.type (compound body) = Compound bl 
      /\ STATEMENT.label (compound body) = Some L_beginBody.

    (* The list of exception is supposed to be ordered from the innermost to
     *  the outermost handler, otherwise the behavior might be unexpected 
     *  @see JVMS 3.10 *)
    Parameter exceptionHandlers : MethodBody -> list ExceptionHandler.
  End METHODBODY_TYPE.

  (* Check that METHODBODY conforms to METHODBODY_TYPE... *)
  Module METHODBODY' : METHODBODY_TYPE := METHODBODY.

  Module METHODSPEC. (* Represents a Heavy Weight Specification CASE *)
    Inductive CallableList : Type :=
      | EveryMethod
      | These (ml : list MethodSignature).

    (* RM9.9.1.1 *)
    Module Type FORALL_VAR_DECL_TYPE.
      Parameter t : Type.
      Parameter vars : t -> list Var.
    End FORALL_VAR_DECL_TYPE.

    (* RM9.9.1.2 *)
    Module Type OLD_VAR_DECL_TYPE.
      Parameter t : Type.
      Parameter varDecls : t -> list (Var * Expression).  (* needs to be varDecl *)
    End OLD_VAR_DECL_TYPE.

    (* RM9.9.2 *)
    Module Type REQUIRES_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
      Parameter isSame      : t -> bool.
    End REQUIRES_TYPE.

    (* RM9.9.3 *)
    Module Type ENSURES_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
    End ENSURES_TYPE.

    (* RM9.9.4 *)
    Module Type SIGNALS_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
      Parameter exception   : t -> Param.
    End SIGNALS_TYPE.

    (* RM9.9.5 *)
    Module Type SIGNALS_ONLY_TYPE.
      Parameter t : Type.
      Parameter types       : t -> list StaticType.
    End SIGNALS_ONLY_TYPE.

    (* RM9.9.7 *)
    Module Type DIVERGES_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
    End DIVERGES_TYPE.

    (* RM9.9.8 *)
    Module Type WHEN_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
    End WHEN_TYPE.

    (* RM9.9.9 *)
    Module Type ASSIGNABLE_TYPE.
      Parameter t : Type.
      Parameter storeRefs   : t -> optional (StoreRefList).
    End ASSIGNABLE_TYPE.

    (* RM9.9.10 *)
    Module Type ACCESSIBLE_TYPE.
      Parameter t : Type.
      Parameter storeRefs   : t -> optional (StoreRefList).
    End ACCESSIBLE_TYPE.

    (* RM9.9.11 *)
    Module Type CALLABLE_TYPE.
      Parameter t : Type.
      Parameter methods     : t -> optional CallableList.
    End CALLABLE_TYPE.

    (* RM9.9.12 *)
    Module Type MEASURED_BY_TYPE.
      Parameter t : Type.
      Parameter expr        : t -> optional Expression.  (* Needs to be of type int *)
      Parameter cond        : t -> option Expression.
    End MEASURED_BY_TYPE.

    (* RM9.9.13 *)
    Module Type CAPTURES_TYPE.
      Parameter t : Type.
      Parameter storeRefs   : t -> optional (StoreRefList).
    End CAPTURES_TYPE.

    (* RM9.9.14 *)
    Module Type WORKING_SPACE_TYPE.
      Parameter t : Type.
      Parameter expr 	    : t -> optional Expression. (* Needs to be of type long/int *)
      Parameter cond        : t -> option Expression.
    End WORKING_SPACE_TYPE.

    (* RM9.9.15 *)
    Module Type DURATION_TYPE.
      Parameter t : Type.
      Parameter expr        : t -> optional Expression. (* Needs to be of type long/int *)
      Parameter cond        : t -> option Expression.
    End DURATION_TYPE.

    Module FORALL_VAR_DECL <: FORALL_VAR_DECL_TYPE.
      Record tRec : Type := Build_t {
        vars : list Var
      }.
      Definition t : Type := tRec.
    End FORALL_VAR_DECL.

    (* RM9.9.1.2 *)
    Module OLD_VAR_DECL <: OLD_VAR_DECL_TYPE.
      Record tRec : Type := Build_t {
        varDecls : list (Var * Expression)
      }.
      Definition t : Type := tRec.
    End OLD_VAR_DECL.

    (* RM9.9.2 *)
    Module REQUIRES <: REQUIRES_TYPE.
      Record tRec : Type := Build_t {
        pred        : optional Expression;
        isSame      : bool
      }.
      Definition t : Type := tRec.
    End REQUIRES.

    (* RM9.9.3 *)
    Module ENSURES <: ENSURES_TYPE.
      Record tRec : Type := Build_t {
        pred        : optional Expression
      }.
      Definition t : Type := tRec.
    End ENSURES.

    (* RM9.9.4 *)
    Module SIGNALS <: SIGNALS_TYPE.
      Record tRec : Type := Build_t {
        pred        : optional Expression
      }.
      Definition t : Type := tRec.

      Definition exception (s:SIGNALS.t) : Param :=
	Exception_e.

     Lemma signalsParam_eq_Exception_e : forall s:SIGNALS.t,
       SIGNALS.exception s = Exception_e.
     Proof. auto. Qed.

    End SIGNALS.

    (* RM9.9.5 *)
    Module SIGNALS_ONLY <: SIGNALS_ONLY_TYPE.
      Record tRec : Type := Build_t {
        types       : list StaticType
      }.
      Definition t : Type := tRec.
    End SIGNALS_ONLY.

    (* RM9.9.7 *)
    Module DIVERGES <: DIVERGES_TYPE.
      Record tRec : Type := Build_t {
        pred        : optional Expression
      }.
      Definition t : Type := tRec.
    End DIVERGES.

    (* RM9.9.8 *)
    Module WHEN <: WHEN_TYPE.
      Record tRec : Type := Build_t {
        pred        : optional Expression
      }.
      Definition t : Type := tRec.
    End WHEN.

    (* RM9.9.9 *)
    Module ASSIGNABLE <: ASSIGNABLE_TYPE.
      Record tRec : Type := Build_t {
        storeRefs   : optional (StoreRefList)
      }.
      Definition t : Type := tRec.
    End ASSIGNABLE.

    (* RM9.9.10 *)
    Module ACCESSIBLE <: ACCESSIBLE_TYPE.
      Record tRec : Type := Build_t {
        storeRefs   : optional (StoreRefList)
      }.
      Definition t : Type := tRec.
    End ACCESSIBLE.

    (* RM9.9.11 *)
    Module CALLABLE <: CALLABLE_TYPE.
      Record tRec : Type := Build_t {
        methods     : optional CallableList
      }.
      Definition t : Type := tRec.
    End CALLABLE.

    (* RM9.9.12 *)
    Module MEASURED_BY <: MEASURED_BY_TYPE.
      Record tRec : Type := Build_t {
        expr        : optional Expression;  (* Needs to be of type int *)
        cond        : option Expression
      }.
      Definition t : Type := tRec.
    End MEASURED_BY.

    (* RM9.9.13 *)
    Module CAPTURES <: CAPTURES_TYPE.
      Record tRec : Type := Build_t {
        storeRefs   : optional (StoreRefList)
      }.
      Definition t : Type := tRec.
    End CAPTURES.

    (* RM9.9.14 *)
    Module WORKING_SPACE <: WORKING_SPACE_TYPE.
      Record tRec : Type := Build_t {
        expr        : optional Expression; (* Needs to be of type long/int *)
        cond        : option Expression
      }.
      Definition t : Type := tRec.
    End WORKING_SPACE.

    (* RM9.9.15 *)
    Module DURATION <: DURATION_TYPE.
      Record tRec : Type := Build_t {
        expr        : optional Expression; (* Needs to be of type long/int *)
        cond        : option Expression
      }.
      Definition t : Type := tRec.

    End DURATION.


    (* RM9.6 *)
    Module Type SPECIFICATION_CASE_TYPE.
      Parameter t : Type.
      Parameter visibility    : t -> Visibility.
      Parameter forallVarDecl : t -> FORALL_VAR_DECL.t.
      Parameter oldVarDecl    : t -> OLD_VAR_DECL.t.
      Parameter requires      : t -> REQUIRES.t.
      Parameter ensures       : t -> ENSURES.t.
      Parameter signals       : t -> SIGNALS.t.
      Parameter signalsOnly   : t -> SIGNALS_ONLY.t.
      Parameter diverges      : t -> DIVERGES.t.
      Parameter when          : t -> WHEN.t.
      Parameter assignable    : t -> ASSIGNABLE.t.
      Parameter accessible    : t -> ACCESSIBLE.t.
      Parameter callable      : t -> CALLABLE.t.
      Parameter measuredBy    : t -> MEASURED_BY.t.
      Parameter captures      : t -> CAPTURES.t.
      Parameter workingSpace  : t -> WORKING_SPACE.t.
      Parameter duration      : t -> DURATION.t.
      Parameter requiresRedundantly      : t -> REQUIRES.t.
      Parameter ensuresRedundantly       : t -> ENSURES.t.
      Parameter signalsRedundantly       : t -> SIGNALS.t.
      Parameter signalsOnlyRedundantly   : t -> SIGNALS_ONLY.t.
      Parameter divergesRedundantly      : t -> DIVERGES.t.
      Parameter whenRedundantly          : t -> WHEN.t.
      Parameter assignableRedundantly    : t -> ASSIGNABLE.t.
      Parameter accessibleRedundantly    : t -> ACCESSIBLE.t.
      Parameter callableRedundantly      : t -> CALLABLE.t.
      Parameter measuredByRedundantly    : t -> MEASURED_BY.t.
      Parameter capturesRedundantly      : t -> CAPTURES.t.
      Parameter workingSpaceRedundantly  : t -> WORKING_SPACE.t.
      Parameter durationRedundantly      : t -> DURATION.t.
      Parameter isRedundant    : t -> bool.
      Parameter isCodeContract : t -> bool.
    End SPECIFICATION_CASE_TYPE.
    
    (* RM9.6 *)
    Module CASE <: SPECIFICATION_CASE_TYPE.
      Record tRec : Type := Build_t {
	visibility    : Visibility;	

        forallVarDecl : FORALL_VAR_DECL.t;
        oldVarDecl    : OLD_VAR_DECL.t;

        requires      : REQUIRES.t;
        ensures       : ENSURES.t;
        signals       : SIGNALS.t;
        signalsOnly   : SIGNALS_ONLY.t;
        diverges      : DIVERGES.t;
        when          : WHEN.t;
        assignable    : ASSIGNABLE.t;
        accessible    : ACCESSIBLE.t;
        callable      : CALLABLE.t;
        measuredBy    : MEASURED_BY.t;
        captures      : CAPTURES.t;
        workingSpace  : WORKING_SPACE.t;
        duration      : DURATION.t;
        
	requiresRedundantly      : REQUIRES.t;
        ensuresRedundantly       : ENSURES.t;
        signalsRedundantly       : SIGNALS.t;
        signalsOnlyRedundantly   : SIGNALS_ONLY.t;
        divergesRedundantly      : DIVERGES.t;
        whenRedundantly          : WHEN.t;
        assignableRedundantly    : ASSIGNABLE.t;
        accessibleRedundantly    : ACCESSIBLE.t;
        callableRedundantly      : CALLABLE.t;
        measuredByRedundantly    : MEASURED_BY.t;
        capturesRedundantly      : CAPTURES.t;
        workingSpaceRedundantly  : WORKING_SPACE.t;
        durationRedundantly      : DURATION.t;

        isRedundant    : bool;
        isCodeContract : bool
      }.

      Definition setRequires (sc:CASE.tRec) (r:REQUIRES.t) : CASE.tRec := 
        let (v, fvd, ovd, _, e, s, so, div, w, ass, acc, cal, mb, cap, ws, dur, rR, eR, sR, soR, divR, wR, assR, accR, calR, mbR, capR, wsR, durR, red, cc) := sc in
          CASE.Build_t v fvd ovd r e s so div w ass acc cal mb cap ws dur rR eR sR soR divR wR assR accR calR mbR capR wsR durR red cc.

      Definition setEnsures (sc:CASE.tRec) (e:ENSURES.t) : CASE.tRec := 
        let (v, fvd, ovd, r, _, s, so, div, w, ass, acc, cal, mb, cap, ws, dur, rR, eR, sR, soR, divR, wR, assR, accR, calR, mbR, capR, wsR, durR, red, cc) := sc in
          CASE.Build_t v fvd ovd r e s so div w ass acc cal mb cap ws dur rR eR sR soR divR wR assR accR calR mbR capR wsR durR red cc.

      Definition setSignals (sc:CASE.tRec) (s:SIGNALS.t) : CASE.tRec := 
        let (v, fvd, ovd, r, e, _, so, div, w, ass, acc, cal, mb, cap, ws, dur, rR, eR, sR, soR, divR, wR, assR, accR, calR, mbR, capR, wsR, durR, red, cc) := sc in
          CASE.Build_t v fvd ovd r e s so div w ass acc cal mb cap ws dur rR eR sR soR divR wR assR accR calR mbR capR wsR durR red cc.

      Definition setDiverges (sc:CASE.tRec) (div:DIVERGES.t) : CASE.tRec := 
        let (v, fvd, ovd, r, e, s, so, _, w, ass, acc, cal, mb, cap, ws, dur, rR, eR, sR, soR, divR, wR, assR, accR, calR, mbR, capR, wsR, durR, red, cc) := sc in
          CASE.Build_t v fvd ovd r e s so div w ass acc cal mb cap ws dur rR eR sR soR divR wR assR accR calR mbR capR wsR durR red cc.

      Definition setAssignable (sc:CASE.tRec) (ass:ASSIGNABLE.t) : CASE.tRec := 
        let (v, fvd, ovd, r, e, s, so, div, w, _, acc, cal, mb, cap, ws, dur, rR, eR, sR, soR, divR, wR, assR, accR, calR, mbR, capR, wsR, durR, red, cc) := sc in
          CASE.Build_t v fvd ovd r e s so div w ass acc cal mb cap ws dur rR eR sR soR divR wR assR accR calR mbR capR wsR durR red cc.



      Definition t : Type := tRec.
    End CASE.

  End METHODSPEC.  
  Export METHODSPEC.

  Definition SpecificationCase : Type := METHODSPEC.CASE.t.

  Module METHODSPEC_PLUS.

    (** Type of method specification case *)
    Inductive SpecCaseType : Set := 
      | lightweight 
      | behaviour
      | normal_behaviour
      | exceptional_behaviour.

    (** Type for requires clause argument *)
    Inductive optionalSame (A : Type) : Type :=
      | NotSpecifiedOS : optionalSame A
      | SpecifiedOS    : A -> optionalSame A
      | same : optionalSame A.
    Arguments NotSpecifiedOS {A}.
    Arguments SpecifiedOS {A}.
    Arguments same {A}.

    (**
      Full syntax type for spec header
     *)
    Inductive SpecHeader : Type :=
      | requiresSH (redundant : bool) (pred : optionalSame Expression).
  
    (** 
      Full syntax type for simple body clauses.
      @see RM 9.4 simple-spec-body
     *)
    Inductive MethodSpecClause : Type := 
      | ensuresC (redundant : bool) (pred : optional Expression)
      | signalsC (redundant : bool) (pair : Param * optional Expression)
      | signalsOnlyC (redundant : bool) (types : list StaticType)
      | divergesC (redundant : bool) (pred : optional Expression)
      | whenC (redundant : bool) (pred : optional Expression)
      | assignableC (redundant : bool) (storeRefs : optional StoreRefList)
      | accessibleC (redundant : bool) (storeRefs : optional StoreRefList)
      | callableC (redundant : bool) (storeRefs : optional CallableList)
      | measuredByC (redundant : bool) (pair : optional Expression * option Expression)
      | capturesC (redundant : bool) (storeRefs : optional StoreRefList)
      | workingSpaceC (redundant : bool) (pair : optional Expression * option Expression)
      | durationC (redundant : bool) (pair : optional Expression * option Expression).
  
    Module Type GENERIC_SPEC_CASE_TYPE.
      Parameter t : Type.
      Parameter forallVarDecl : t -> list FORALL_VAR_DECL.t.
      Parameter oldVarDecl    : t -> list OLD_VAR_DECL.t.
      Parameter specHeader    : t -> list SpecHeader.
      Parameter genericBody   : t -> (list MethodSpecClause) + (list t).
    End GENERIC_SPEC_CASE_TYPE.

    Module GENERIC_SPEC_CASE <: GENERIC_SPEC_CASE_TYPE.
      (** @see RM 9.4 generic-spec-case *)
      Inductive GenericSpecCase : Type := 
        Build_t (forallVarDecl  : list FORALL_VAR_DECL.t)
                (oldVarDecl     : list OLD_VAR_DECL.t)
                (specHeader     : list SpecHeader)
                  (* either a simple-spec-body or a generic-spec-case-seq *)
                (genericBody    : (list MethodSpecClause) + (list GenericSpecCase)).
  
      (** Convenience type synonym for type of genericBody component of GenericSpecCase. *)
      Definition GenericBodyType := (list MethodSpecClause) + (list GenericSpecCase).

      (** GenericSpecCase selectors *)
      Definition forallVarDecl (nb:GenericSpecCase) := let (f,_,_,_) := nb in f.
      Definition oldVarDecl (nb:GenericSpecCase)    := let (_,o,_,_) := nb in o.
      Definition specHeader (nb:GenericSpecCase)    := let (_,_,s,_) := nb in s.
      Definition genericBody (nb:GenericSpecCase)   := let (_,_,_,g) := nb in g.

      Definition t : Type := GenericSpecCase.
    End GENERIC_SPEC_CASE.
  
    Module Type FULL_SPEC_CASE_TYPE.
      Parameter t : Type.
      Parameter specCaseType    : t -> SpecCaseType.
      Parameter visibility      : t -> option Visibility.
      Parameter isRedundant     : t -> bool.
      Parameter isCodeContract  : t -> bool.
      Parameter genericSpecCase : t -> GENERIC_SPEC_CASE.t.
    End FULL_SPEC_CASE_TYPE.

    Module FULL_SPEC_CASE <: FULL_SPEC_CASE_TYPE.
      Record tRec : Type := Build_t {
        specCaseType    : SpecCaseType;
        visibility      : option Visibility;
        isRedundant     : bool;
        isCodeContract  : bool;
        genericSpecCase : GENERIC_SPEC_CASE.t
      }.
      Definition t : Type := tRec.
    End FULL_SPEC_CASE.

  End METHODSPEC_PLUS.
  Export METHODSPEC_PLUS.

  Inductive ExceptionType : Set := 
    | ErrorET (t : StaticType) 
    | RuntimeExceptionET (t : StaticType) 
    | ExceptionET (t : StaticType)
    | ThrowableET (t : StaticType).

  Module METHOD. 
    Record t : Type := {
      signature : ShortMethodSignature;
      throws : list ExceptionType;
      body : option MethodBody;
      override : option MethodSignature;
      kind : MethodKind;
      isFinal : bool;
      isStatic : bool;
      isNative : bool;  
      visibility : Visibility;
      specVisibility : Visibility;
      isPure : bool;
      isHelper : bool;
      isNullable : bool;

      (** true iff this is the implicitly defined zero-argument default ctor *)
      isImplicitDefaultConstructor : bool;

      specs : list SpecificationCase;

      (** 
        In addition to the selectors specified in the METHOD_TYPE signature,
        the full syntax stores a list of full specification cases with each methods.
        The basic syntax list of SpecificationCase's are only filled in later in the 
        full2basic rewrite.
        @see JMLFull2Basic.METHODSPEC_REWRITINGS_TYPE.rewriteFullSpecification
       *)
      fullSpecs : list FULL_SPEC_CASE.t
    }.

    Definition isAbstract (m:t) : bool :=
      match body m with
        | None   => true
        | Some _ => false
      end.

    Definition setSpecs (m:t) (specs:list SpecificationCase) : t := 
      METHOD.Build_t (signature m) (throws m) (body m) (override m) (kind m) (isFinal m) (isStatic m) (isNative m)
        (visibility m) (specVisibility m) (isPure m) (isHelper m) (isNullable m) (isImplicitDefaultConstructor m) specs (fullSpecs m).
  End METHOD.

  Definition Method : Type := METHOD.t.

  Parameter InitMethod : Method.

  Module Type METHOD_TYPE.
    Parameter signature : Method -> ShortMethodSignature.
    Parameter throws : Method -> list ExceptionType.
    Parameter body : Method -> option MethodBody.
    Parameter override : Method -> option MethodSignature.
    Parameter kind : Method -> MethodKind.
    Parameter isFinal : Method -> bool.
    Parameter isStatic : Method -> bool.
    Parameter isNative : Method -> bool.  
    Definition isAbstract (m:Method) : bool :=
      match body m with
        | None   => true
        | Some _ => false
      end.
    Parameter visibility : Method -> Visibility.
    Parameter specVisibility : Method -> Visibility.
    Parameter isPure : Method -> bool.
    Parameter isHelper : Method -> bool.
    Parameter isNullable : Method -> bool.
    Parameter isImplicitDefaultConstructor : Method -> bool.
    Parameter specs : Method -> list SpecificationCase.
    
      (** Setter for specs *)
    (* Parameter setSpecs : Method -> list SpecificationCase -> Method. *)
  End METHOD_TYPE.

  (* Check that METHOD conforms to METHOD_TYPE... *)
  Module METHOD' : METHOD_TYPE := METHOD.

  Module TYPESPEC.
    Inductive ConstrainedFor : Type :=
      | EveryMethod
      | These (ms : list MethodSignature).

    (* RM8.2 *)
    Module Type INVARIANT_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> Expression. 
      Parameter visibility  : t -> Visibility.
      Parameter isStatic    : t -> bool.
      Parameter isRedundant : t -> bool.
    End INVARIANT_TYPE.

    (* RM8.3 *)
    Module Type CONSTRAINT_TYPE.
      Parameter t : Type.
      Parameter pred           : t -> Expression.
      Parameter visibility     : t -> Visibility.
      Parameter constrainedFor : t -> ConstrainedFor.
      Parameter isStatic       : t -> bool.
      Parameter isRedundant    : t -> bool.
    End CONSTRAINT_TYPE.

    (* RM8.4 *)
    Module Type REPRESENTS_TYPE.
      Parameter t : Type.
      Parameter visibility   : t -> Visibility.
      Parameter model        : t -> Expression.
      Parameter expr         : t -> Expression.
      Parameter isRelational : t -> bool.
      Parameter isStatic     : t -> bool.
      Parameter isRedundant  : t -> bool.
    End REPRESENTS_TYPE.

    (* RM8.5 *)
    Module Type INITIALLY_TYPE.
      Parameter t : Type.
      Parameter visibility : t -> Visibility.
      Parameter pred       : t -> Expression.
    End INITIALLY_TYPE.
 
    (* RM8.6 *)
    Module Type AXIOM_TYPE.
      Parameter t : Type.
      Parameter pred       : t -> Expression. 
    End AXIOM_TYPE.

    (* RM8.7 *)
    Module Type READABLE_IF_TYPE.
      Parameter t : Type.
      Parameter field      : t -> FieldSignature.
      Parameter visibility : t -> Visibility.
      Parameter condition  : t -> Expression.
    End READABLE_IF_TYPE.

    (* RM8.8 *)
    Module Type WRITABLE_IF_TYPE.
      Parameter t : Type.
      Parameter field      : t -> FieldSignature.
      Parameter visibility : t -> Visibility.
      Parameter condition  : t -> Expression.
    End WRITABLE_IF_TYPE.

    (* RM8.9 *)
    Module Type MONITORS_FOR_TYPE.
      Parameter t : Type.
      Parameter field      : t -> FieldSignature.
      Parameter visibility : t -> Visibility.
      Parameter objects    : t -> list Expression.
    End MONITORS_FOR_TYPE.
    
    Module INVARIANT <: INVARIANT_TYPE.
      Record tRec : Type := Build_t {
        pred        : Expression; 
        visibility  : Visibility;
        isStatic    : bool;
        isRedundant : bool
      }.
      Definition t : Type := tRec.
    End INVARIANT.

    Module CONSTRAINT <: CONSTRAINT_TYPE.
      Record tRec : Type := Build_t {
        pred           : Expression;
        visibility     : Visibility;
        constrainedFor : ConstrainedFor;
        isStatic       : bool;
        isRedundant : bool
      }.
      Definition t : Type := tRec.
    End CONSTRAINT.

    Module REPRESENTS <: REPRESENTS_TYPE.
      Record tRec : Type := Build_t {
        visibility   : Visibility;
        model        : Expression;
        expr         : Expression;
        isRelational : bool;
        isStatic     : bool;
        isRedundant  : bool
      }.
      Definition t : Type := tRec.
    End REPRESENTS.

    Module INITIALLY <: INITIALLY_TYPE.
      Record tRec : Type := Build_t {
        visibility : Visibility;
        pred       : Expression
      }.
      Definition t : Type := tRec.
    End INITIALLY.

    Module AXIOM <: AXIOM_TYPE.
      Record tRec : Type := Build_t {
        pred       : Expression
      }.
      Definition t : Type := tRec.
    End AXIOM.

    Module READABLE_IF <: READABLE_IF_TYPE.
      Record tRec : Type := Build_t {
        field      : FieldSignature;
        visibility : Visibility;
        condition  : Expression
      }.
      Definition t : Type := tRec.
    End READABLE_IF.

    Module WRITABLE_IF <: WRITABLE_IF_TYPE.
      Record tRec : Type := Build_t {
        field      : FieldSignature;
        visibility : Visibility;
        condition  : Expression
      }.
      Definition t : Type := tRec.
    End WRITABLE_IF.

    Module MONITORS_FOR <: MONITORS_FOR_TYPE.
      Record tRec : Type := Build_t {
        field      : FieldSignature;
        visibility : Visibility;
        objects    : list Expression
      }.
      Definition t : Type := tRec.
    End MONITORS_FOR.

    Module Type TYPESPEC_TYPE.
      Parameter t : Type.
      Parameter invariant    : t -> list INVARIANT.t.
      Parameter constraint   : t -> list CONSTRAINT.t.
      Parameter represents   : t -> list REPRESENTS.t.
      Parameter initially    : t -> list INITIALLY.t.
      Parameter axiom        : t -> list AXIOM.t.
      Parameter readable_if  : t -> list READABLE_IF.t.
      Parameter writable_if  : t -> list WRITABLE_IF.t.
      Parameter monitors_for : t -> list MONITORS_FOR.t.
    End TYPESPEC_TYPE.

    Module TYPESPEC <: TYPESPEC_TYPE.
      Record tRec : Type := Build_t {
        invariant    : list INVARIANT.t;
        constraint   : list CONSTRAINT.t;
        represents   : list REPRESENTS.t;
        initially    : list INITIALLY.t;
        axiom        : list AXIOM.t;
        readable_if  : list READABLE_IF.t;
        writable_if  : list WRITABLE_IF.t;
        monitors_for : list MONITORS_FOR.t
      }.

      Definition t : Type := tRec.

      Definition setInvariant (ts:TYPESPEC.t) (inv:list INVARIANT.t) : TYPESPEC.t :=
	let (_, c, rep, i, a, read, w, m) := ts in TYPESPEC.Build_t inv c rep i a read w m.
      
    End TYPESPEC.

  End TYPESPEC.
  Export TYPESPEC.
  Definition TypeSpec : Type := TYPESPEC.TYPESPEC.t.

  Module Type TYPEDEF_TYPE.
    Parameter t : Type.
    Parameter name : t -> TypeDefName.

    Parameter visibility : t -> Visibility.
    Parameter specVisibility : t -> Visibility.
    Parameter superInterfaces : t -> list t.
    Parameter weaklyImplements : t -> t -> bool.
    Parameter superClass: t -> option t.
    Parameter weaklyExtends : t -> bool.

    Parameter field : t -> ShortFieldName -> option Field.
    Definition definedField (c : t) (f : Field) :=
      field c (FIELDSIGNATURE.name (FIELD.signature f)) = Some f.

    Parameter modelField : t -> ShortModelFieldName -> option ModelField.
    Parameter method : t -> ShortMethodSignature -> option Method.
    Definition definedMethod (c : t) (m : Method) :=
      method c (METHOD.signature m) = Some m.

   (* modifiers *)
    Parameter isFinal : t -> bool.
    Parameter isPublic : t -> bool. (* Bicolano compatibility *)
    Parameter isAbstract : t -> bool.

    Parameter typeSpec : t -> TypeSpec.
  End TYPEDEF_TYPE.

  Module TYPEDEF <: TYPEDEF_TYPE.

    Inductive tRec : Type := Build_t 
      (isClass : bool)
      (name : TypeDefName)
      (visibility : Visibility)
      (specVisibility : Visibility)

      (superClass : option tRec) (* only applicable for CLASS.t *)
      (weaklyExtends : bool)   (* only applicable for CLASS.t *) 

      (strongSuperInterfaces : list tRec)
      (weakSuperInterfaces : list tRec)
      (fields : list Field)
      (modelFields : list ModelField)
      (methods : list Method)
      (isFinal : bool)
      (isAbstract : bool)
      (typeSpec : TypeSpec).

    Definition t := tRec.

    Definition isClass (e:t) : bool :=
      let (c,_,_,_,_,_,_,_,_,_,_,_,_,_) := e in c.

    Definition name (e:t) : TypeDefName :=
      let (_,n,_,_,_,_,_,_,_,_,_,_,_,_) := e in n.

    Definition visibility (e:t) : Visibility :=
      let (_,_,v,_,_,_,_,_,_,_,_,_,_,_) := e in v.

    Definition specVisibility (e:t) : Visibility :=
      let (_,_,_,sv,_,_,_,_,_,_,_,_,_,_) := e in sv.

    Definition superClass (e:t) : option t :=
      let (_,_,_,_,sc,_,_,_,_,_,_,_,_,_) := e in sc.

    Definition weaklyExtends (e:t) : bool :=
      let (_,_,_,_,_,we,_,_,_,_,_,_,_,_) := e in we.

    Definition strongSuperInterfaces (e:t) : list t :=
      let (_,_,_,_,_,_,ssi,_,_,_,_,_,_,_) := e in ssi.

    Definition weakSuperInterfaces (e:t) : list t :=
      let (_,_,_,_,_,_,_,wsi,_,_,_,_,_,_) := e in wsi.

    Definition fields (e:t) : list Field :=
      let (_,_,_,_,_,_,_,_,fs,_,_,_,_,_) := e in fs.

    
    Definition modelFields (e:t) : list ModelField :=
      let (_,_,_,_,_,_,_,_,_,mfs,_,_,_,_) := e in mfs.

    Definition methods (e:t) : list Method :=
      let (_,_,_,_,_,_,_,_,_,_,ms,_,_,_) := e in ms.

    Definition isFinal (e:t) : bool :=
      let (_,_,_,_,_,_,_,_,_,_,_,f,_,_) := e in f.

    Definition isAbstract (e:t) : bool :=
      let (_,_,_,_,_,_,_,_,_,_,_,_,a,_) := e in a.

    Definition typeSpec (e:t) : TypeSpec :=
      let (_,_,_,_,_,_,_,_,_,_,_,_,_,ts) := e in ts.

    Definition superInterfaces (e:t) : list t :=
      (strongSuperInterfaces e) ++ (weakSuperInterfaces e).

    Definition weaklyImplements (e:t) (other:t) : bool :=
      existsb (eq_TypeDefName (TYPEDEF.name other)) (map TYPEDEF.name (TYPEDEF.weakSuperInterfaces e)).

    Definition field (e:t) (sfn:ShortFieldName) : option Field :=
      let eq_sfn (f:Field) := Z_eqb (FIELDSIGNATURE.name (FIELD.signature f)) sfn in
        List.find eq_sfn (fields e).

    Definition definedField (c : t) (f : Field) :=
      field c (FIELDSIGNATURE.name (FIELD.signature f)) = Some f.

    Definition modelField (e:t) (sfn:ShortModelFieldName) : option ModelField :=
      let eq_sfn (f:ModelField) := Z_eqb (FIELDSIGNATURE.name (MODELFIELD.signature f)) sfn in
        List.find eq_sfn (modelFields e).

    Definition method (e:t) (sms:ShortMethodSignature) : option Method :=
      let eq_sms (m:Method) := METHODSIGNATURE.eq_t (METHOD.signature m) sms in
        List.find eq_sms (methods e).

    Definition definedMethod (c : t) (m : Method) :=
      method c (METHOD.signature m) = Some m.

    Definition isPublic (cl:t) := eq_Visibility (visibility cl) Public.

    Definition setMethods (e:t) (ms:list Method) : t :=
      let (c, n,v,sv,sc,we,ssi,wsi,fs,mfs,_,f,a,ts) := e in
      Build_t c n v sv sc we ssi wsi fs mfs ms f a ts.

    Definition setTypeSpec (e:t) (ts:TypeSpec) : t :=
      let (c, n,v,sv,sc,we,ssi,wsi,fs,mfs,ms,f,a,_) := e in
      Build_t c n v sv sc we ssi wsi fs mfs ms f a ts.
  End TYPEDEF.


  Parameter MainClass : TYPEDEF.t.

  Definition Class := TYPEDEF.t.
  Definition Interface := TYPEDEF.t.

  Module Type CLASS_TYPE.
    Definition name := TYPEDEF.name.

    Definition visibility := TYPEDEF.visibility.
    Definition specVisibility := TYPEDEF.specVisibility.

    (* direct superclass *)
    (* All the classes have a superClass except [java.lang.Object]. (see [Wf.v]) *)
    Definition superClass := TYPEDEF.superClass.

    (* RM 6.1.1: only weak subtype relationship *)
    Definition weaklyExtends := TYPEDEF.weaklyExtends.

    (* list of implemented interfaces *)
    Definition superInterfaces := TYPEDEF.superInterfaces.
    (* RM 6.1.1: only weak subtype relationship *)
    Definition weaklyImplements := TYPEDEF.weaklyImplements.

    Definition field := TYPEDEF.field.
    Definition definedField := TYPEDEF.definedField.
    Definition modelField := TYPEDEF.modelField.
    Definition method := TYPEDEF.method.
    Definition definedMethod := TYPEDEF.definedMethod.
    (* modifiers *)
    Definition isFinal := TYPEDEF.isFinal.
    Definition isPublic := TYPEDEF.isPublic. (* Bicolano compatibility *)
    Definition isAbstract := TYPEDEF.isAbstract.

    
    Definition typeSpec := TYPEDEF.typeSpec.
  End CLASS_TYPE.

  Module CLASS <: CLASS_TYPE.
    Definition Build_t := TYPEDEF.Build_t true.
    Definition name := TYPEDEF.name.

    Definition visibility := TYPEDEF.visibility.
    Definition specVisibility := TYPEDEF.specVisibility.

    Definition superClass (cl:Class) : option Class := 
      TYPEDEF.superClass cl.

    Definition weaklyExtends (cl:Class) : bool := TYPEDEF.weaklyExtends cl.

    (* list of implemented interfaces *)
    Definition superInterfaces := TYPEDEF.superInterfaces.
    (* RM 6.1.1: only weak subtype relationship *)
    Definition weaklyImplements := TYPEDEF.weaklyImplements.

    Definition field := TYPEDEF.field.
    Definition definedField := TYPEDEF.definedField.
    Definition modelField := TYPEDEF.modelField.
    Definition method := TYPEDEF.method.
    Definition definedMethod := TYPEDEF.definedMethod.

    Definition isFinal := TYPEDEF.isFinal.
    Definition isPublic := TYPEDEF.isPublic. (* Bicolano compatibility *)
    Definition isAbstract := TYPEDEF.isAbstract.

    
    Definition typeSpec := TYPEDEF.typeSpec.
  End CLASS.
    
  Module INTERFACE.

    Definition Build_t 
        (n:InterfaceName) (v:Visibility) (sv:Visibility) (ssi:list Interface) (wsi:list Interface) 
        (mfs:list ModelField) (ms:list Method) (f:bool) (a:bool) (ts:TypeSpec) := 
      TYPEDEF.Build_t false n v sv None true ssi wsi nil mfs ms f a ts.

    Definition name := TYPEDEF.name.

    Definition visibility := TYPEDEF.visibility.
    Definition specVisibility := TYPEDEF.specVisibility.

    (* list of implemented interfaces *)
    Definition superInterfaces := TYPEDEF.superInterfaces.

    (* RM 6.1.1: only weak subtype relationship *)
    Definition weaklyImplements := TYPEDEF.weaklyImplements.

    Definition field := TYPEDEF.field.
    Definition definedField := TYPEDEF.definedField.
    Definition modelField := TYPEDEF.modelField.
    Definition method := TYPEDEF.method.
    Definition definedMethod := TYPEDEF.definedMethod.
    (* modifiers *)
    Definition isFinal := TYPEDEF.isFinal.
    Definition isPublic := TYPEDEF.isPublic. (* Bicolano compatibility *)
    Definition isAbstract := TYPEDEF.isAbstract.

    
    Definition typeSpec := TYPEDEF.typeSpec.

  End INTERFACE.

  Module PROG.
    Record t : Type := {
      classes : list Class;
      interfaces : list Interface
    }.

    Definition class (p:t) (en:TypeDefName) : option TYPEDEF.t := 
      let eq_en (e:TYPEDEF.t) := eq_TypeDefName (TYPEDEF.name e) en in
        List.find eq_en (classes p).

    Definition defined_Class (p:t) (cl:Class) : Prop := class p (CLASS.name cl) = Some cl.

    Definition interface (p:t) (en:TypeDefName) : option TYPEDEF.t := 
      let eq_en (e:TYPEDEF.t) := eq_TypeDefName (TYPEDEF.name e) en in
        List.find eq_en (interfaces p).

    Definition defined_Interface (p:t) (i:Interface) : Prop := interface p (INTERFACE.name i) = Some i.

  End PROG.

  Definition Program : Type := PROG.t.

  Module Type PROG_TYPE.

    (** accessor to a class from its qualified name *)
    Parameter class : Program -> ClassName -> option Class.
    Definition defined_Class (p : Program) (cl : Class) :=
      class p (CLASS.name cl) = Some cl.

    (** accessor to an interface from its qualified name *)
    Parameter interface : Program -> InterfaceName -> option Interface.
    Definition defined_Interface (p : Program) (i : Interface) :=
      interface p (INTERFACE.name i) = Some i.

  End PROG_TYPE.
  
  (* Check that PROG conforms to PROG_TYPE... *)
  Module PROG' : PROG_TYPE := PROG.

    (** Definitions on programs  *)

  Inductive isStatic (p : Program) (fs : FieldSignature) : Prop :=
    | isStatic_field : forall (cn : ClassName) (cl : Class) (f : Field) ,
        PROG.class p (fst fs) = Some cl ->
        CLASS.field cl (FIELDSIGNATURE.name (snd fs)) = Some f ->
        FIELD.isStatic f = true ->
        isStatic p fs.

  Definition javaLangObject : ClassName := (javaLang,object).
  Definition javaLangClass : ClassName := (javaLang,class).
  Definition javaLangThrowable : InterfaceName := (javaLang,throwable).
  Definition javaLangCloneable : InterfaceName := (javaLang,cloneable).
  Definition javaIoSerializable : InterfaceName := (javaIo,serializable).
  Inductive direct_subclass (p : Program) (sub : Class) (super : Class) : Prop :=
    | direct_subclass1 : 
        PROG.defined_Class p sub -> 
        PROG.defined_Class p super ->
        CLASS.superClass sub = Some super -> 
        direct_subclass p sub super.

  (* [subclass] is the reflexive transitive closure of the [direct_subclass] relation 
   * (defined over the classes of the program) *)
  Definition subclass (p : Program) (sub : Class) (super : Class) : Prop :=
    clos_refl_trans Class (direct_subclass p) sub super.

  Inductive subclass_name (p : Program) (sub : ClassName) (super : ClassName) : Prop :=
    | subclass_name1 : forall sub' super' ,
        sub = CLASS.name sub' ->
        super = CLASS.name super' ->
        subclass p sub' super' -> 
        subclass_name p sub super.

  Inductive direct_subclass_name (p : Program) (sub : ClassName) (super : ClassName) : Prop :=
    | direct_subclass_name1 : forall sub' super' ,
        sub = CLASS.name sub' ->
        super = CLASS.name super' ->
        direct_subclass p sub' super' ->
        direct_subclass_name p sub super.

  (* Similar definitions for interfaces *)
  Inductive direct_subinterface (p : Program) (sub : Interface) (super : Interface) : Prop :=
    | direct_subinterface1 : 
        PROG.defined_Interface p sub ->
        PROG.defined_Interface p super ->
        In super (INTERFACE.superInterfaces sub) -> 
        direct_subinterface p sub super.

  (* [subinterface] is the reflexive transitive closure of the [direct_subinterface] 
   * relation (defined over the interfaces of the program) *)
  Definition subinterface (p : Program) (sub : Interface) (super : Interface) : Prop :=
    clos_refl_trans Interface (direct_subinterface p) sub super.

  Inductive subinterface_name (p : Program) (sub : InterfaceName) (super : InterfaceName) : Prop :=
    | subinterface_name1 : forall sub' super' ,
        sub = INTERFACE.name sub' ->
        super = INTERFACE.name super' ->
        subinterface p sub' super' -> 
        subinterface_name p sub super.

  Inductive direct_subinterface_name (p : Program) (sub : InterfaceName) (super : InterfaceName) : Prop :=
    | direct_subinterface_name1 : forall sub' super' ,
        sub = INTERFACE.name sub' ->
        super = INTERFACE.name super' ->
        direct_subinterface p sub' super' ->
        direct_subinterface_name p sub super.

  Inductive class_declares_field (p : Program) (cn : ClassName) (fd : ShortFieldSignature) : Field -> Prop :=
    | class_decl_field : forall cl f ,
        PROG.class p cn = Some cl -> 
        CLASS.field cl (FIELDSIGNATURE.name fd) = Some f -> 
        class_declares_field p cn fd f.

  Inductive interface_declares_field (p : Program) (cn : InterfaceName) (fd : ShortFieldSignature) : Field -> Prop :=
    | interface_decl_field : forall cl f ,
        PROG.interface p cn = Some cl -> 
        INTERFACE.field cl (FIELDSIGNATURE.name fd) = Some f -> 
        interface_declares_field p cn fd f.

  (** [defined_field p c fd] holds if the class [c] declares or inherits a field 
      of signature [fd] *)
  Inductive is_defined_field (p : Program) (c : ClassName) (fsig : FieldSignature): Field -> Prop :=
    | def_class_field : forall super f,
        subclass_name p c super -> 
        class_declares_field p super (snd fsig) f -> 
        is_defined_field p c fsig f
    | def_interface_field : forall c' sub super f , 
        PROG.class p c = Some c' -> 
        In sub (CLASS.superInterfaces c') ->
        subinterface_name p (INTERFACE.name sub) super -> 
        interface_declares_field p super (snd fsig) f -> 
        is_defined_field p c fsig f.

  Definition defined_field (p : Program) (cn : ClassName) (fs : FieldSignature) : Prop :=
    exists f, is_defined_field p cn fs f.

  Definition findMethod (p : Program) (msig : MethodSignature) : option Method :=
    let (cn, smsig) := msig in
      match PROG.class p cn with
	      | None => None
	      | Some cl => CLASS.method cl smsig 
      end.

  Definition findField (p : Program) (fd : FieldSignature) : option Field :=
    let (cn, sfs) := fd in   
      match PROG.class p cn with
	      | None => None
	      | Some cl => CLASS.field cl (FIELDSIGNATURE.name sfs)
      end.

  Definition methodPackage (mname : MethodName) : PackageName :=  fst (fst mname).

  Inductive check_visibility : Visibility -> PackageName -> PackageName ->  Prop :=
    | check_public :  forall p1 p2 , check_visibility Public p1 p2
    | check_protected : forall p1 p2 , check_visibility Protected p1 p2
    | check_package : forall p , check_visibility Package p p.

  Inductive lookup (p : Program) (cn : ClassName) (msig:ShortMethodSignature) : (ClassName * Method) -> Prop :=
    | lookup_no_up : 
	forall meth , 
	findMethod p (cn, msig) = Some meth -> 
	lookup p cn msig (cn, meth)
    | lookup_up : 
	findMethod p (cn, msig) = None -> 
      	forall super res , direct_subclass_name p cn super -> 
	lookup p super msig res -> 
	lookup p cn msig res.

Lemma lookup_deterministic:
forall p cn msig r r',
lookup p cn msig r ->
lookup p cn msig r' ->
r = r'.
Proof.
intros.
induction H.
 inversion H0.
  subst; rewrite H in H1; inversion H1; trivial.
  
  rewrite H in H1; inversion H1.
  
 inversion H0.
  rewrite H3 in H; inversion H.
  
  apply IHlookup; clear IHlookup.
  inversion H1; inversion H4.
  rewrite H10 in H7.
  inversion H9; inversion H12.
  unfold PROG.defined_Class in H13, H16.
  rewrite H7 in H16; rewrite H16 in H13; inversion H13.
  rewrite H20 in H18; rewrite H18 in H15; inversion H15.
  rewrite H21 in H11; rewrite <- H11 in H8; rewrite H8.
  trivial.
Qed.

  Inductive direct_stmt_in_stmt : STATEMENT.t -> STATEMENT.t -> Prop :=
    | stmt_in_then : forall s test _then _else ,
      STATEMENT.type s  = IfStmt test _then _else  ->
      direct_stmt_in_stmt  _then s
    | stmt_in_else : forall test s _then _else ,
      STATEMENT.type s  = IfStmt test _then (Some _else)  ->
      direct_stmt_in_stmt  _else s
    | stmt_in_case : forall s expr case cases s' default,
      STATEMENT.type s  = SwitchStmt expr cases default ->
      In case cases ->
      In s' (snd case) ->
      direct_stmt_in_stmt s' s
    | stmt_in_default : forall s expr cases s' default,
      STATEMENT.type s  = SwitchStmt expr cases (Some default) ->
      In s' default ->
      direct_stmt_in_stmt s' s
    | stmt_in_while_body : forall s anno test s',
      STATEMENT.type s = WhileLoop anno test s' ->
      direct_stmt_in_stmt s' s
    | stmt_in_do_body : forall s anno test s',
      STATEMENT.type s = DoLoop anno s' test ->
      direct_stmt_in_stmt s' s
    | stmt_in_for_body : forall s anno init test step s',
      STATEMENT.type s = ForLoop anno init test step s' ->
      direct_stmt_in_stmt s' s
    | stmt_in_tryblock : forall s s' handlers finally ,
      STATEMENT.type s = TryBlock s' handlers finally ->
      direct_stmt_in_stmt s' s
    | stmt_in_handler : forall s block handler s' handlers finally ,
      STATEMENT.type s = TryBlock block handlers finally ->
      In handler handlers ->
      s' = snd handler ->
      direct_stmt_in_stmt s' s
    | stmt_in_finally : forall s block handlers s' ,
      STATEMENT.type s = TryBlock block handlers (Some s') ->
      direct_stmt_in_stmt s' s.

  Definition stmt_in_stmt : STATEMENT.t -> STATEMENT.t -> Prop :=
    clos_refl_trans STATEMENT.t direct_stmt_in_stmt.

  Inductive stmt_in_block : STATEMENT.t -> BLOCK.t -> Prop :=
    | stmt_in_block_def: forall s b pc ,
      BLOCK.statementAt b pc = Some s ->
      stmt_in_block s b.

  Inductive block_in_stmt : BLOCK.t -> STATEMENT.t -> Prop :=
    | block_in_stmt_def: forall b s ,
      STATEMENT.type s = Compound b ->
      block_in_stmt b s.

  Inductive direct_block_in_block : BLOCK.t -> BLOCK.t -> Prop :=
    | direct_block_in_block_def : forall s s' b b' ,
      stmt_in_block s b ->
      stmt_in_stmt s' s ->
      block_in_stmt b' s' ->
      direct_block_in_block b' b.

  Definition block_in_block : BLOCK.t -> BLOCK.t ->  Prop :=
    clos_refl_trans BLOCK.t direct_block_in_block.

  Inductive statement_at_prop : Method -> PC -> StatementType (Statement := STATEMENT.t) (Block := BLOCK.t) -> Prop :=
  | statement_at_def: forall m pc b b' s s' body ,
    METHOD.body m = Some body ->
    METHODBODY.compound body = s ->
    STATEMENT.type s = Compound b ->
    block_in_block b' b ->
    BLOCK.statementAt b' pc = Some s' ->
    statement_at_prop m pc (STATEMENT.type s').


  Parameter statement_at : Method -> PC -> option (StatementType (Statement := STATEMENT.t) (Block := BLOCK.t)).
  Axiom statement_at_1: forall m pc st,
  statement_at_prop m pc st <-> statement_at m pc = Some st.
  Axiom statement_at_2: forall m pc,
  (~ exists st, statement_at_prop m pc st) <-> statement_at m pc = None.

  Inductive implements (p : Program) : ClassName -> InterfaceName -> Prop :=
    | implements_def: forall i cl i' , 
        PROG.defined_Interface p i -> 
        PROG.defined_Class p cl ->
        In i (CLASS.superInterfaces cl) ->
        subinterface_name p (INTERFACE.name i) i' ->
        implements p (CLASS.name cl) i'.

  Inductive implements_trans (p : Program) : ClassName -> InterfaceName -> Prop :=
    | implements_trans_ind_ind : forall c c' i i',
        subclass_name p c c' ->
        subinterface_name p i' i ->
        implements p c' i' ->
        implements_trans p c i
    | implements_trans_ind_c : forall c c' i,
        subclass_name p c c' ->
        implements p c' i ->
        implements_trans p c i
    | implements_trans_ind_i : forall c i i',
        subinterface_name p i' i ->
        implements p c i' ->
        implements_trans p c i
    | implements_trans_direct : forall c i ,
        implements p c i ->
        implements_trans p c i.

  Inductive direct_subtype (sub : TYPEDEF.t) (super: TYPEDEF.t) : Prop :=
    | direct_subtype_extends: 
        CLASS.superClass sub = Some super ->
        direct_subtype sub super
    | direct_subtype_implements: (* includes case IF1 extends IF2 *)
        In super (TYPEDEF.superInterfaces sub) ->
        direct_subtype sub super.

  Definition strict_subtype (sub : TYPEDEF.t) (super : TYPEDEF.t):=
    clos_trans TYPEDEF.t (direct_subtype) sub super.

  Definition SubType (sub : TYPEDEF.t) (super : TYPEDEF.t) : Prop :=
    clos_refl_trans TYPEDEF.t (direct_subtype) sub super.

  Definition subtype_name (p : Program) (sub_name : TypeDefName) (super_name : TypeDefName) : Prop :=
    forall sub super ,
    TYPEDEF.name sub = sub_name ->
    TYPEDEF.name super = super_name ->
    SubType sub super.

  Inductive visible (v : Visibility) (accessed : TYPEDEF.t) (declared : TYPEDEF.t): Prop :=
    | vis_public :
      v = Public ->
      visible v accessed declared
    | vis_package :
      v = Package \/ v = Protected ->
      fst (TYPEDEF.name accessed) = fst (TYPEDEF.name declared) ->
      visible v accessed declared
    | vis_private :
      v = Private ->
      accessed = declared ->
      visible v accessed declared
    | vis_protected:
      v = Protected ->
      SubType accessed declared ->
      visible v accessed declared.


  Import METHODSPEC.
  Import TYPESPEC.

  (* A super specification case is one that is defined in the current
   * or in a method of a supertype, that is visible in the current type *)
  Inductive DefinedCase (c : TYPEDEF.t) (m : Method) (sc : SpecificationCase) : Prop :=
    DefinedCase_def : forall m' c',
      (*TYPEDEF.definedMethod c m ->*)
      SubType c c' ->
      TYPEDEF.method c' (METHOD.signature m) = Some m' ->
      In sc (METHOD.specs m') ->
      DefinedCase c m sc.

  (* A visible specification case is one that is defined a class that
   * is visible from the current class *)
  Inductive VisibleCase (c : TYPEDEF.t)(sc : SpecificationCase) : Prop :=
  | VisibleCase_def : forall m' c' ,
    visible (CASE.visibility sc) c c' ->
    CLASS.definedMethod c' m' ->
    In sc (METHOD.specs m') ->
    VisibleCase c sc.

  (* Analogous to DefinedCase *)
  Inductive DefinedTypeSpec (c : Class) (ts : TypeSpec) : Prop :=
  | DefinedTypeSpec_def: forall super ,
    SubType c super ->
    ts = (TYPEDEF.typeSpec super) ->
    DefinedTypeSpec c ts.

  (* Invariant defined in c or some supertype of c *)
  Inductive DefinedInvariant (c : Class) (inv : INVARIANT.t) : Prop :=
  | DefinedInvariant_def : forall ts ,
    DefinedTypeSpec c ts ->
    In inv (TYPESPEC.invariant ts) ->
    DefinedInvariant c inv.

  (* Invariant defined in c or some supertype of c *)
  Inductive DefinedInitially (c : Class) (ini : INITIALLY.t) : Prop :=
  | DefinedInitially_def : forall ts ,
    DefinedTypeSpec c ts ->
    In ini (TYPESPEC.initially ts) ->
    DefinedInitially c ini.

  (* Constraint defined in c or some supertype of c *)
  Inductive DefinedConstraint (c : Class) (con : CONSTRAINT.t) : Prop :=
  | DefinedConstraint_def : forall ts ,
    DefinedTypeSpec c ts ->
    In con (TYPESPEC.constraint ts) ->
    DefinedConstraint c con.

  (* Represents Clause defined in c or some supertype of c *)
  Inductive DefinedRepresents (c : Class) (rep : REPRESENTS.t) : Prop :=
  | DefinedRepresents_def : forall ts ,
    DefinedTypeSpec c ts ->
    In rep (TYPESPEC.represents ts) ->
    DefinedRepresents c rep.

  Inductive compat_refType (p : Program): refType -> refType -> Prop :=
    | compat_refType_ref : forall umS umT enS enT ,
        subtype_name p enS enT ->
        compat_refType p (TypeDefType enS umS) (TypeDefType enT umT)
    | compat_refType_object : forall enS umS umT,
        compat_refType p (TypeDefType enS umS) (TypeDefType javaLangObject umT)
    | compat_refType_array_class : forall tpS umS umT,
        compat_refType p (ArrayType tpS umS) (TypeDefType javaLangObject umT)
    | compat_refType_array_cloneable : forall atS umS umT,
        compat_refType p (ArrayType atS umS) (TypeDefType javaLangCloneable umT)
    | compat_refType_array_serializable : forall atS umS umT,
        compat_refType p (ArrayType atS umS) (TypeDefType javaIoSerializable umT)
    | compat_refType_array_array_primitive_type : forall t umS umT,       
        compat_refType p (ArrayType (PrimitiveType t) umS) (ArrayType (PrimitiveType t) umT)
    | compat_refType_array_array_reference_type : forall tpS tpT umS umT,       
        compat_refType p tpS tpT ->
        compat_refType p (ArrayType (ReferenceType tpS) umS) (ArrayType (ReferenceType tpT) umT).


End Make.

Module MakePlus <: PROGRAM_PLUS.
  Module Program := Make.
  Export Program.
  Module METHODSPEC_PLUS := Make.METHODSPEC_PLUS.
End MakePlus.

Module P := MakePlus.
Export P.
