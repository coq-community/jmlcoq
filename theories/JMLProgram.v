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

(** Formalization of Java programs.
Based on The "Java (TM) Virtual Machine Specification, Second Edition, 
Tim Lindholm, Frank Yellin"
*)

From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Relation_Operators.

Open Scope type_scope.

Module Type PROGRAM.

  (** Main types to be manipulated by the API *)
  Parameter Program : Type.
  Parameter Var : Set.
  Parameter Field : Type.
  Parameter ModelField : Type.
  Parameter Method : Type.
  Parameter MethodBody : Type.
  Parameter ExceptionHandler : Set.
  Parameter ShortMethodSignature : Set.
  Parameter ShortFieldSignature : Set.
  Parameter ParamSignature : Set.
  Parameter VarSignature : Set.
  Parameter PC : Set.
  (* Additional JML Constructs *)
  
  Definition ShortModelFieldSignature := ShortFieldSignature.

  Parameter Label : Set.
  (* The compound statement of a method body has its label always set to L_beginBody. *)
  Parameter L_beginBody : Label.

  Parameter Param : Set.
  Parameter paramThis : Param.

  (** Handling of qualified names *)
  Parameter PackageName : Set.
  Parameter ShortTypeDefName : Set.
  Parameter ShortMethodName : Set.
  Parameter ShortFieldName : Set.

  (* Additional JML Constructs *)
  Definition ShortModelFieldName := ShortFieldName.
  Parameter ParamName : Set.
  Parameter VarName : Set.

  (* For example the qualified name [java.lang.String] of the class [String],
   * is decomposed into [java.lang] for the package name and [String] for the
   * short name.  *)

  Definition TypeDefName := PackageName * ShortTypeDefName.

  Definition ShortClassName := ShortTypeDefName.
  Definition ClassName := TypeDefName.

  Definition ShortInterfaceName := ShortTypeDefName.
  Definition InterfaceName := TypeDefName.

  Definition MethodName := ClassName * ShortMethodName.
  Definition FieldName := ClassName * ShortFieldName.
  Definition MethodSignature := ClassName * ShortMethodSignature.
  Definition FieldSignature := ClassName * ShortFieldSignature.
  (* Additional JML Constructs *)
  Definition ModelFieldName := ClassName * ShortModelFieldName.
  Definition ModelFieldSignature := ClassName * ShortModelFieldSignature.

  
  (* Some constants *)
  Parameter class : ShortClassName.
  Parameter javaLang : PackageName.
  Parameter object : ShortClassName.
  Parameter throwable : ShortClassName.
  Parameter cloneable : ShortClassName.
  Parameter javaIo : PackageName.
  Parameter serializable : ShortClassName.
  Parameter exception : ShortClassName.


  Parameter InitMethod : Method.
  Parameter NoBodyPC : PC.

  (** Native Exceptions *)
  Parameter RuntimeException NullPointerException ArrayIndexOutOfBoundsException ArrayStoreException
            NegativeArraySizeException ClassCastException ArithmeticException : ShortClassName.

  (** visibility modifiers including JML modifiers *)
  Inductive Visibility : Set :=
    | Package 
    | Protected 
    | Private 
    | Public
    | Spec_Public
    | Spec_Protected.

  Inductive MethodKind : Set :=
    | Default | Constructor | Finalizer | Initializer.

  (** For optional specification constructs *)
  Inductive optional (A : Type) : Type :=
    | NotSpecified
    | Specified (a : A).
  Arguments Specified [A].
  Arguments NotSpecified {A}.

  (** Universe Type modifiers *)
  Inductive utsModifier : Set :=
    | peer
    | rep
    | any.

  (** Supported Primitive Types *)
  Inductive primitiveType : Set :=
    | BOOLEAN | BYTE | SHORT | INT.

  (** Static Type Definitions *)
  Inductive StaticType : Set :=
    | ReferenceType (rt : refType)
    | PrimitiveType (pt : primitiveType)
  with refType : Set := 
    (* Multidimensional Arrays: Inner arrays always need to be of type 'peer' *)
    | ArrayType (typ : StaticType) (um : utsModifier)
    | TypeDefType  (td : TypeDefName) (um : utsModifier)
    | NullType.

  (* Type information used for Vaload and Saload *)
  Inductive ArrayKind : Set :=
    | Aarray
    | Iarray
    | Barray
    | Sarray.
    
  (* Type information used for Vload, Vstore and Vreturn *)
  Inductive ValKind : Set :=
    | Aval
    | Ival.

  Module Type OFFSET_TYPE.
    (* The type of address offsets *)
    Parameter t : Set.
    (* Jumps are defined in terms of offsets with respect to the current address. **)
    Parameter jump : PC -> t -> PC.
  End OFFSET_TYPE.
  Declare Module OFFSET : OFFSET_TYPE.

  (** Operations on the signatures of fields *)
  Module Type FIELDSIGNATURE_TYPE.
    Parameter name : ShortFieldSignature  -> ShortFieldName.
    Parameter type : ShortFieldSignature -> StaticType.
    Parameter eq_dec : forall f1 f2 : ShortFieldSignature , f1 = f2 \/ ~f1 = f2.
  End FIELDSIGNATURE_TYPE.
  Declare Module FIELDSIGNATURE : FIELDSIGNATURE_TYPE.

  (** Operations on the signatures of fields *)
  (*
  Module Type MODELFIELDSIGNATURE_TYPE.
    Parameter name : ShortModelFieldSignature  -> ShortModelFieldName.
    Parameter type : ShortModelFieldSignature -> type.
    Parameter eq_dec : forall f1 f2 : ShortModelFieldSignature , f1 = f2 \/ ~f1 = f2.
  End MODELFIEDSIGNATURE_TYPE.
  Declare Module MODELFIELDSIGNATURE : MODELFIELDSIGNATURE_TYPE.
  *)

  Module Type PARAMSIGNATURE_TYPE.
    Parameter name : ParamSignature -> ParamName.
    Parameter type : ParamSignature -> StaticType.
    Parameter eq_dec : forall p1 p2 : ParamSignature ,  p1 = p2 \/ ~p1 = p2.
  End PARAMSIGNATURE_TYPE.
  Declare Module PARAMSIGNATURE : PARAMSIGNATURE_TYPE.

  Module Type VARSIGNATURE_TYPE.
    Parameter name : VarSignature -> VarName.
    Parameter type : VarSignature -> StaticType.
    Parameter eq_dec : forall p1 p2 : VarSignature , p1 = p2 \/ ~p1 = p2.
  End VARSIGNATURE_TYPE.
  Declare Module VARSIGNATURE : VARSIGNATURE_TYPE.

  (** Content of a method signature *)
  Module Type METHODSIGNATURE_TYPE.
    (* The method name *)
    Parameter name : ShortMethodSignature -> ShortMethodName.
    (* Java types for parameters values *)
    Parameter parameters : ShortMethodSignature -> list Param.
    (* Java type for return value, the constructor [None] of type option being used for the [Void] type *)
    Parameter result : ShortMethodSignature -> option StaticType.
    Parameter eq_dec : 
      forall mid1 mid2 : ShortMethodSignature , mid1 = mid2 \/ ~mid1 = mid2.
  End METHODSIGNATURE_TYPE.
  Declare Module METHODSIGNATURE : METHODSIGNATURE_TYPE.

  (** ** JML Expressions *)
  Module EXPRESSION.

    (* Identifier for LBLNEG LBLPOS *)
    (* TODO: Do we need this parameter? *)
    Parameter Ident : Set.

    Inductive Quantifier : Set :=
      | Forall | Exists | Max | Min | NumOf | Product | Sum.

Open Scope Z_scope.

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
      | LogicalOr (* | *).

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

  Inductive StoreRefList :=
    | Nothing
    | Everything
    | StoreRefs (sr: list StoreRef).

  (* Simplified version of dynamic datagroup maps to clause *)
  Inductive DynDgPivotTarget :=
    | FieldDg (fsig : FieldSignature).
    (*| AllFieldsDg.*)

  End EXPRESSION.
  Export EXPRESSION.

  (** ** JML Statements *)

  Module Type LOOP_ANNOTATION_TYPE.
    Parameter t : Type.
    
    Parameter expression : t -> optional Expression.
    Parameter invariants : t -> list Expression.
    Parameter variants   : t -> list Expression.

    Parameter expressionRedundantly : t -> optional Expression.
    Parameter invariantsRedundantly : t -> list Expression.	
    Parameter variantsRedundantly   : t -> list Expression.
  End LOOP_ANNOTATION_TYPE.

  Declare Module LOOP_ANNOTATION : LOOP_ANNOTATION_TYPE.

  Inductive StatementType {Statement Block: Type}: Type := (* Statement and Block are implicit arguments *)
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

    | Debug (expr : Expression)
    | HenceBy (expr : Expression) (redundantly : bool)
        
    | varDeclStmt (var : Var) (expr : option Expression)

    (** No operation (= empty statement ;), also used within an empty block *)
    | Nop

    (** this(...), super(...) *)
    | ThisCallStmt  (method : MethodSignature) (params: list Expression)
    | SuperCallStmt (method : MethodSignature) (params: list Expression).

  Module Type STATEMENT_TYPE.
    (* Statement module type, holding relevent statement data and 
     * the type of statement *)
    Parameter t : Type.
    Parameter b : Type.
    Parameter label : t -> option Label.
    Parameter pc    : t -> PC.
    Parameter type  : t -> StatementType (Statement := t) (Block := b). (* Explicitely set implicit arguments *)
  End STATEMENT_TYPE.
  Declare Module STATEMENT : STATEMENT_TYPE.

  Module Type BLOCK_TYPE.
    Definition t := STATEMENT.b.

    Parameter localVariables : t -> list Var.
    Parameter first          : t -> option PC.
    Parameter last           : t -> option PC.   
    Parameter statementAt    : t -> PC -> option STATEMENT.t.
    Parameter next           : t -> PC -> option PC.
    Parameter elem : t -> PC -> bool.

    Axiom elem_def : forall t pc, 
      elem t pc = true -> exists s, statementAt t pc = Some s /\ STATEMENT.pc s = pc.
    Axiom statementAt_def : forall t pc s, 
      statementAt t pc = Some s -> STATEMENT.pc s = pc.
    Axiom first_elem : forall t pc, first t = Some pc -> elem t pc = true.
    Axiom last_elem : forall t pc, last t = Some pc -> elem t pc = true.
    Axiom last_def : forall b pc, last b = Some pc -> next b pc = None.
    Axiom next_elem : forall t pc1 pc2, next t pc1 = Some pc2 -> elem t pc2 = true.
  End BLOCK_TYPE.
  Declare Module BLOCK : BLOCK_TYPE.

  (** ** JML Type Specifications *)

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

    Declare Module INVARIANT : INVARIANT_TYPE.
    Declare Module CONSTRAINT : CONSTRAINT_TYPE.
    Declare Module REPRESENTS : REPRESENTS_TYPE.
    Declare Module INITIALLY : INITIALLY_TYPE.
    Declare Module AXIOM : AXIOM_TYPE.
    Declare Module READABLE_IF : READABLE_IF_TYPE.
    Declare Module WRITABLE_IF : WRITABLE_IF_TYPE.
    Declare Module MONITORS_FOR : MONITORS_FOR_TYPE.

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
    Declare Module TYPESPEC : TYPESPEC_TYPE.
  End TYPESPEC.

  Definition TypeSpec := TYPESPEC.TYPESPEC.t.

  (** Represents a Heavy Weight Specification CASE *)
  Module METHODSPEC. 
    Inductive CallableList : Type :=
      | EveryMethod
      | These (ml : list MethodSignature).

    (** RM9.9.1.1 *)
    Module Type FORALL_VAR_DECL_TYPE.
      Parameter t : Type.
      Parameter vars : t -> list Var.
    End FORALL_VAR_DECL_TYPE.

    (** RM9.9.1.2 *)
    Module Type OLD_VAR_DECL_TYPE.
      Parameter t : Type.
      Parameter varDecls : t -> list (Var * Expression).  (* needs to be varDecl *)
    End OLD_VAR_DECL_TYPE.

    (** RM9.9.2 *)
    Module Type REQUIRES_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
      Parameter isSame      : t -> bool.
    End REQUIRES_TYPE.

    (** RM9.9.3 *)
    Module Type ENSURES_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
    End ENSURES_TYPE.

    (** RM9.9.4 *)
    Module Type SIGNALS_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
      Parameter exception   : t -> Param.
    End SIGNALS_TYPE.

    (** RM9.9.5 *)
    Module Type SIGNALS_ONLY_TYPE.
      Parameter t : Type.
      Parameter types       : t -> list StaticType.
    End SIGNALS_ONLY_TYPE.

    (** RM9.9.7 *)
    Module Type DIVERGES_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
    End DIVERGES_TYPE.

    (** RM9.9.8 *)
    Module Type WHEN_TYPE.
      Parameter t : Type.
      Parameter pred        : t -> optional Expression.
    End WHEN_TYPE.

    (** RM9.9.9 *)
    Module Type ASSIGNABLE_TYPE.
      Parameter t : Type.
      Parameter storeRefs   : t -> optional (StoreRefList).
    End ASSIGNABLE_TYPE.

    (** RM9.9.10 *)
    Module Type ACCESSIBLE_TYPE.
      Parameter t : Type.
      Parameter storeRefs   : t -> optional (StoreRefList).
    End ACCESSIBLE_TYPE.

    (** RM9.9.11 *)
    Module Type CALLABLE_TYPE.
      Parameter t : Type.
      Parameter methods     : t -> optional CallableList.
    End CALLABLE_TYPE.

    (** RM9.9.12 *)
    Module Type MEASURED_BY_TYPE.
      Parameter t : Type.
      Parameter expr        : t -> optional Expression.  (* Needs to be of type int *)
      Parameter cond        : t -> option Expression.
    End MEASURED_BY_TYPE.

    (** RM9.9.13 *)
    Module Type CAPTURES_TYPE.
      Parameter t : Type.
      Parameter storeRefs   : t -> optional (StoreRefList).
    End CAPTURES_TYPE.

    (** RM9.9.14 *)
    Module Type WORKING_SPACE_TYPE.
      Parameter t : Type.
      Parameter expr 	    : t -> optional Expression. (* Needs to be of type long/int *)
      Parameter cond        : t -> option Expression.
    End WORKING_SPACE_TYPE.

    (** RM9.9.15 *)
    Module Type DURATION_TYPE.
      Parameter t : Type.
      Parameter expr        : t -> optional Expression. (* Needs to be of type long/int *)
      Parameter cond        : t -> option Expression.
    End DURATION_TYPE.

    Declare Module FORALL_VAR_DECL : FORALL_VAR_DECL_TYPE.
    Declare Module OLD_VAR_DECL : OLD_VAR_DECL_TYPE.
    Declare Module REQUIRES : REQUIRES_TYPE.
    Declare Module ENSURES : ENSURES_TYPE.
    Declare Module SIGNALS : SIGNALS_TYPE.
    Declare Module SIGNALS_ONLY : SIGNALS_ONLY_TYPE.
    Declare Module DIVERGES : DIVERGES_TYPE.
    Declare Module WHEN : WHEN_TYPE.
    Declare Module ASSIGNABLE : ASSIGNABLE_TYPE.
    Declare Module ACCESSIBLE : ACCESSIBLE_TYPE.
    Declare Module CALLABLE : CALLABLE_TYPE.
    Declare Module MEASURED_BY : MEASURED_BY_TYPE.
    Declare Module CAPTURES : CAPTURES_TYPE.
    Declare Module WORKING_SPACE : WORKING_SPACE_TYPE.
    Declare Module DURATION : DURATION_TYPE.

    (** RM9.6, full behaviour specification case *)
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
    Declare Module CASE : SPECIFICATION_CASE_TYPE.
  End METHODSPEC.

  Definition SpecificationCase := METHODSPEC.CASE.t.

  (** Operations on exception handlers *)
  Module Type EXCEPTIONHANDLER_TYPE.
    (* class of the caught exception *)
    (* The constructor [None] of type option being used to implement [finally]. It
     * matches any exception *)
    Parameter catchType : ExceptionHandler -> option ClassName.
    (* is the given PC in range of the handler *)
    Parameter isPCinRange : ExceptionHandler -> PC -> bool.
    (* location of the handler code *) 
    Parameter handler : ExceptionHandler -> PC.
  End EXCEPTIONHANDLER_TYPE.
  Declare Module EXCEPTIONHANDLER : EXCEPTIONHANDLER_TYPE.

  Inductive ExceptionType : Set := 
    | ErrorET (t : StaticType) 
    | RuntimeExceptionET (t : StaticType) 
    | ExceptionET (t : StaticType)
    | ThrowableET (t : StaticType).

  (* Operations on bytecode methods *)
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
  Declare Module METHODBODY : METHODBODY_TYPE.
 
  (** Content of a method *)
  Module Type METHOD_TYPE.
    Parameter signature : Method -> ShortMethodSignature.
    
    Parameter throws : Method -> list ExceptionType.

    Parameter body : Method -> option MethodBody. 

    Parameter override : Method -> option MethodSignature.   
    
    (* modifiers *)
    Parameter kind : Method -> MethodKind.
    Parameter isFinal : Method -> bool.
    Parameter isStatic : Method -> bool.
    Parameter isNative : Method -> bool.  
    
    (* A method that is not abstract has an empty method body *)
    Definition isAbstract (m : Method) : bool :=
      if body m then false else true.

    Parameter visibility : Method -> Visibility.
    Parameter specVisibility : Method -> Visibility.

    Parameter isPure : Method -> bool.
    Parameter isHelper : Method -> bool.
    Parameter isNullable : Method -> bool.

    (* true if this is the implicit default (zero-arg) ctor *)
    Parameter isImplicitDefaultConstructor : Method -> bool.

    Parameter specs          : Method -> list SpecificationCase.

  End METHOD_TYPE.
  Declare Module METHOD : METHOD_TYPE.

  Module Type DATA_GROUP_TYPE.
    Parameter t : Type.

    Parameter pivotTarget : t -> option DynDgPivotTarget.
    Parameter dataGroups : t -> list FieldSignature.
    Parameter isRedundant : t -> bool.

    Definition isDynamic (dg : t) : bool :=
    if pivotTarget dg then true else false.
    
    Parameter dataGroups_not_nil: forall t, dataGroups t <> nil.
  End DATA_GROUP_TYPE.
  Declare Module DATA_GROUP : DATA_GROUP_TYPE.


  (* Operations on fields *)
  Module Type FIELD_TYPE.
    Parameter signature : Field -> ShortFieldSignature.    
    Parameter isFinal : Field -> bool.
    Parameter visibility : Field -> Visibility.
    Parameter specVisibility : Field -> Visibility. (* not sensible for ghost fields *)
    Parameter isStatic : Field -> bool.
    Parameter isGhost : Field -> bool.
    Parameter isNullable : Field -> bool.
    Parameter isMonitored : Field -> bool.
    (* Initial (default) value. Must be compatible with the type of the field. *)
    Parameter initValue : Field ->  option Expression.

    Parameter dataGroups : Field -> list DATA_GROUP.t.
  End FIELD_TYPE.
  Declare Module FIELD : FIELD_TYPE.

  (** Operations on fields *)
  Module Type MODELFIELD_TYPE.
    Parameter signature : ModelField -> ShortModelFieldSignature.    
    Parameter visibility : ModelField -> Visibility.
    Parameter isStatic : ModelField -> bool.
    Parameter isNullable : ModelField -> bool.

    Parameter dataGroups : ModelField -> list DATA_GROUP.t.

  End MODELFIELD_TYPE.
  Declare Module MODELFIELD : MODELFIELD_TYPE.

  Module Type PARAM_TYPE.
    Parameter signature : Param -> ParamSignature.
    Parameter isFinal : Param -> bool.
    Parameter isNullable : Param -> bool.
  End PARAM_TYPE.
  Declare Module PARAM : PARAM_TYPE.

  Module Type VAR_TYPE.
    Parameter signature : Var -> VarSignature.
    Parameter isFinal : Var -> bool.
    Parameter isNullable : Var -> bool.
    Parameter isGhost : Var -> bool.
    Parameter isUninitialized : Var -> bool.
  End VAR_TYPE.
  Declare Module VAR : VAR_TYPE.

  Module Type TYPEDEF_TYPE.
    Parameter t : Type.
    Parameter name : t -> TypeDefName.

    Parameter visibility : t -> Visibility.
    Parameter specVisibility : t -> Visibility.
    Parameter superInterfaces : t -> list t.
    Parameter weaklyImplements : t -> t -> bool.

    Parameter superClass : t -> option t.
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

  Declare Module TYPEDEF : TYPEDEF_TYPE.

  Parameter MainClass : TYPEDEF.t.

  Definition Class := TYPEDEF.t.
  Definition Interface := TYPEDEF.t.

  (** Content of a Java class *)
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
  Declare Module CLASS : CLASS_TYPE.

  (** Content of a Java interface *)
  Module INTERFACE.

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

  (** Content of a Java Program *)
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
  Declare Module PROG : PROG_TYPE.

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

  (* [defined_field p c fd] holds if the class [c] declares or inherits a field 
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

  Inductive direct_subtype (sub super: TYPEDEF.t) : Prop :=
    | direct_subtype_extends: 
        CLASS.superClass sub = Some super ->
        direct_subtype sub super
    | direct_subtype_implements: (* includes case IF1 extends IF2 *)
        In super (TYPEDEF.superInterfaces sub) ->
        direct_subtype sub super.

  Definition strict_subtype (sub super : TYPEDEF.t):=
    clos_trans TYPEDEF.t (direct_subtype) sub super.

  Definition SubType (sub super : TYPEDEF.t) : Prop :=
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
  Inductive VisibleCase (c :Class)(sc : SpecificationCase) : Prop :=
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

End PROGRAM.
Declare Module Prog : PROGRAM.
