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

Require Export JMLDomain.

Require Import List.
Require Import ListSet.
Require Import FSetInterface.
Require Import Bool.
Require Import ZArith.
Require Import Relation_Operators.
Require Import ListHelpers.

Declare Module Dom  : SEMANTIC_DOMAIN.
Import Dom.
Import Prog.
Import JmlNotations.
Import METHODSPEC.
Import TYPESPEC.

Open Scope jml_scope.

(** * JML Annotation Interface 
The two modules [ANNOTATION_TABLE] and [ASSIGNABLES] provide access to all JML
annotations. The annotation table yields conditions that have to hold at a given point
in time whereas the module Assignables provides the means to check frame properties 
that have to hold throughout program execution. *)

(** ** Annotation Table
The annotation table yields a proposition (logical formula) that needs
to be valid at the given point in the program.
  - [Precondition] yields the condition that needs to hold at method entry. This
includes the \requires clause but also object invariants.
  - [Postcondition] yields the condition that any execution the method establishes.
The condition describes the behavior for both normal and abrupt (exceptional) termination.
  - [LocalAssertion] yields the assertion that needs to hold before the execution of a statement 
at a given program counter (PC).
  - [LoopInvariant] yields the condition that is preserved by the loop at the given
program counter.*)


Module Type ANNOTATION_TABLE (State : STATE).
  Parameter Precondition  : Program -> Class -> Method       -> State.t -> Prop.
  Parameter Postcondition : Program -> Class -> Method       -> State.t -> Prop.
  Parameter LocalAssertion  : Program -> Class -> Method -> PC -> State.t -> option Prop.
  Parameter LoopInvariant :  Program -> Class -> Method -> PC -> State.t -> option Prop.
End ANNOTATION_TABLE.

(** ** Interface for Assignable Clauses 
To ensure that a frame property holds throughout program execution, we need to 
perform certain checks and actions at the right time.
  - [FieldUpdateCheck] yields a proposition that is valid if a given location is 
currently assignable. This assertion needs to be inserted before any field or array update. 
  - [MethodCallAction] is called upon method invocation and evaluates the assignable 
clause of the method to a set of locations and stores the set in the frame.
  - [NewObjectAction] is called upon object creation and marks all fields of an object
as 'fresh' (i.e. assignable).
  - [MethodReturnAction] is called upon method termination and takes care 
that locations that were freshly allocated during method execution are assignable in the
caller of the method.
  - [FieldUpdateAction] is called if a pivot field gets assigned to. It ensures that the data
structures for dynamic datagroups get updated.
*)

Module Type ASSIGNABLES (State : STATE).
  Parameter FieldUpdateCheck:           Program -> Location         -> State.t -> Prop.
  Parameter MethodCallAction: Program -> Class -> Method            -> State.t -> State.t.
  Parameter NewObjectAction:    Program -> Object                   -> State.t -> State.t.
  Parameter MethodReturnAction:   Program -> State.t                    -> State.t -> State.t.
  Parameter FieldUpdateAction:     Program -> Location -> Value-> State.t -> State.t. 
End ASSIGNABLES.

(** ** JML Annotation Module
This module serves as a parameter to the operational semantics module. There will be several
implementations of this module. One to define the semantics, and others to define (some aspects of)
runtime assertion checking. *)

Module Type JML.
  Declare Module FrameAdds : ADDS.
  Declare Module Adds : ADDS.

  Declare Module Frame : FRAME  with Module Adds := FrameAdds.
  Declare Module State : STATE with Module Frame := Frame with Module Adds := Adds.

  Parameter NewFrame : Method -> ParamDict.t -> State.t -> Frame.t.

  Notation "st '@h'" := (State.h st) (at level 0): jml_scope.
  Notation "st '@fr'" := (State.fr st) (at level 0) : jml_scope.
  Notation "st '@adds'" := (State.adds st) (at level 0) : jml_scope.

  Notation "st '[h' ':=' h ']'" := (State.set_h st h) (at level 0): jml_scope.
  Notation "st '[fr' ':=' fr ']'" := (State.set_fr st fr) (at level 0) : jml_scope.
  Notation "st '[adds' ':=' adds ']'" := (State.set_adds st adds) (at level 0) : jml_scope.

  Notation "[ h , fr , adds ]" := (State.build h fr adds) : jml_scope.

  Declare Module AnnotationTable : ANNOTATION_TABLE State.
  Declare Module Assignables : ASSIGNABLES State.
End JML.

(** * The JML Semantics 
This module describes the semantics of all JML-Level 0 constructs *)

Module Sem <: JML.


(** ** Implementation of the JML Frame
Module [Frame] is the implementation of a frame for the JML semantics. Technically, [Frame] 
implements [SEMANTIC_DOMAIN.FRAME]. *)

Module FrameAdds <: ADDS.

(** We use records for implementation. This creates an inductive datatype [Fields] and getter 
Functions for all constructs of [Fields]. *)

  Record t_rec : Type := make {
    assignables: LocSet.t;
    fresh : ObjSet.t;
    pre : Heap.t * ParamDict.t;
    quants : VarDict.t
  }.

(** Instead of this, we could directly name our record "[t]". But then, Coq doesn't realize, that [t]
is an implementation for the [t : Type] form [FRAME]. This way, it works. *)

  Definition t := t_rec.

  Definition empty := t.

(** Setters and other accessor functions for [Fields] below *)

  Definition set_pre (fr : t) (h : Heap.t) (param : ParamDict.t) : t :=
    make (assignables fr) (fresh fr) (h, param) (quants fr).

  Definition set_assignables (fr : t) (x : LocSet.t) : t :=
    make x (fresh fr) (pre fr) (quants fr).
  Definition inter_assignables (fr : t) (x : LocSet.t) : t :=
    set_assignables fr (LocSet.inter (assignables fr) x).
  Definition add_assignable (fr : t ) (x : Location) : t :=
    set_assignables fr (LocSet.add x (assignables fr)).

  Definition set_fresh (fr : t) (x : ObjSet.t) : t :=
    make (assignables fr) x (pre fr) (quants fr).
  Definition add_fresh (fr : t) (x : Object) : t :=
    set_fresh fr (ObjSet.add x (fresh fr)).
  Definition union_fresh (fr : t) (x : ObjSet.t) : t :=
    set_fresh fr (ObjSet.union x (fresh fr)).

  Definition set_quants (fr : t) (x : VarDict.t) : t :=
    make (assignables fr) (fresh fr) (pre fr) x.
  Definition quant (fr : t) (x : Var) : option Value :=
    VarDict.get (quants fr) x.
  Definition set_quant (fr : t) (x : Var) (v : Value) : t :=
    set_quants fr (VarDict.update (quants fr) x v).

End FrameAdds.

Module Adds <: ADDS.
  Inductive Singleton : Type :=
  | singleton : Singleton.
  Definition t := Singleton.
End Adds.


Declare Module Frame : FRAME with Module Adds := FrameAdds.
Declare Module State : STATE 
  with Module Frame := Frame 
  with Module Adds := Adds.

Module Notations.

  Delimit Scope sem_scope with sem.

  Open Scope sem_scope.

  Notation "st '@h'" := (State.h st) (at level 1, left associativity): sem_scope.
  Notation "st '@fr'" := (State.fr st) (at level 1, left associativity) : sem_scope.
  Notation "st '@adds'" := (State.adds st) (at level 1, left associativity) : sem_scope.

  Notation "st '[h' ':=' h ']'" := (State.set_h st h) (at level 1, left associativity): sem_scope.
  Notation "st '[fr' ':=' fr ']'" := (State.set_fr st fr) (at level 1, left associativity) : sem_scope.
  Notation "st '[adds' ':=' adds ']'" := (State.set_adds st adds) (at level 1, left associativity) : sem_scope.

  Notation "[ h , fr , adds ]" := (State.build h fr adds) : sem_scope.

  Notation "fr '@params'" := (Frame.params fr) (at level 1, left associativity) : sem_scope.
  Notation "fr '@vars'" := (Frame.vars fr) (at level 1, left associativity) : sem_scope.
  Notation "fr '@pc'" := (Frame.pc fr) (at level 1, left associativity) : sem_scope.
  Notation "fr '@ret'" := (Frame.ret fr) (at level 1, left associativity) : sem_scope.
  Notation "fr '@this'" := (Frame.this fr) (at level 1, left associativity) : sem_scope.

  Notation "fr '@fradds'" := (Frame.adds fr) (at level 1, left associativity) : sem_scope.
  Notation "fr '@pre'" := (FrameAdds.pre (Frame.adds fr)) (at level 1, left associativity) : sem_scope.
  Notation "fr '@preheap'" := (fst (fr@pre)) (at level 1, left associativity) : sem_scope.
  Notation "fr '@preparams'" := (snd (fr@pre)) (at level 1, left associativity) : sem_scope.
  Notation "fr '@assignables'" := (FrameAdds.assignables (Frame.adds fr)) (at level 1, left associativity) : sem_scope.
  Notation "fr '@fresh'" := (FrameAdds.fresh (Frame.adds fr)) (at level 1, left associativity) : sem_scope.
  Notation "fr '@quants'" := (FrameAdds.quants (Frame.adds fr)) (at level 1, left associativity) : sem_scope.
  Notation "fr '[this' ':=' obj ']'" := (Frame.set_param fr paramThis (Ref obj)) (at level 1, left associativity): sem_scope.
  Notation "fr '[fradds' ':=' adds ']'" := (Frame.set_adds fr adds) (at level 1, left associativity): sem_scope.
  Notation "fr '[quants' ':=' q ']'" := ( fr[fradds := (FrameAdds.set_quants fr@fradds q)]) (at level 1, left associativity) : sem_scope.
  Notation "fr '[assignables' ':=' a ']'" := ( fr[fradds := (FrameAdds.set_assignables fr@fradds a)]) (at level 1, left associativity) : sem_scope.
  Notation "fr '[assignables' ':/\' a ']'" := ( fr[fradds := (FrameAdds.inter_assignables fr@fradds a)]) (at level 1, left associativity) : sem_scope.
  Notation "fr '[assignables' ':+' a ']'" := ( fr[fradds := (FrameAdds.add_assignable fr@fradds a)]) (at level 1, left associativity) : sem_scope.
  Notation "fr '[fresh' ':=' f ']'" := ( fr[fradds := (FrameAdds.set_fresh fr@fradds f)]) (at level 1, left associativity) : sem_scope.
  Notation "fr '[fresh' ':\/' f ']'" := ( fr[fradds := (FrameAdds.union_fresh fr@fradds f)]) (at level 1, left associativity) : sem_scope.
  Notation "fr '[fresh' ':+' f ']'" := ( fr[fradds := (FrameAdds.add_fresh fr@fradds f)]) (at level 1, left associativity): sem_scope.
  Notation "fr '[ret' ':=' r ']'" := (Frame.set_ret fr r) (at level 1, left associativity) : sem_scope.
  (** common to all sem and rac *)
  Notation "s [=] t" := (LocSet.Equal s t) (at level 70, no associativity).
  Notation "s [[=]] t" := (ObjSet.Equal s t) (at level 70, no associativity).

  Notation "e ∈ s" := (LocSet.In e s) (at level 40, no associativity).
  Notation "e ∈ s" := (ObjSet.In e s) (at level 40, no associativity).
  Notation "e ∉ s" := (~ LocSet.In e s) (at level 40, no associativity).
  Notation "e ∉ s" := (~ ObjSet.In e s) (at level 40, no associativity).
  Notation "s1 ⊇ s2" := (LocSet.Subset s2 s1) (at level 70, no associativity).
  Notation "s1 ⊆ s2" := (LocSet.Subset s1 s2) (at level 70, no associativity).
  Notation "s1 ∩ s2" := (LocSet.inter s1 s2) (at level 60, no associativity).
  Notation "s1 ∩ s2" := (ObjSet.inter s1 s2) (at level 60, no associativity).
  Notation "s1 ∪ s2" := (LocSet.union s1 s2) (at level 60, no associativity).
  Notation "s1 ∪ s2" := (ObjSet.union s1 s2) (at level 60, no associativity).
  Notation "s ∪ { e }" := (LocSet.add e s) (at level 60, no associativity).
  Notation "s ∪ { e }" := (ObjSet.add e s) (at level 60, no associativity).

  Notation "{}" := (LocSet.empty).
  Notation "{}" := (ObjSet.empty).
  Notation "∅" := (LocSet.empty).
  Notation "∅" := (ObjSet.empty).
  Notation "( x )₁" := (fst x).
  Notation "( x )₂" := (snd x).

 Notation "s \ { e }" := (LocSet.remove e s) (at level 60, no associativity).
 Notation "s1 \ s2" := (LocSet.diff s1 s2) (at level 60, no associativity).

End Notations.

Import Notations.

(** Recreate a JML frame that represents the pre-state of a method. As we only store
the pre heap and the parameters, we need to figure out the PC again. *)

Definition InitState : State.t :=
  let frameadds := FrameAdds.make LocSet.empty ObjSet.empty (InitHeap, ParamDict.empty) VarDict.empty in
  let frame := Frame.build InitMethod ParamDict.empty frameadds in
  State.build InitHeap frame Adds.singleton.

(** A new JML Frame is initialized with the effectively assignable locations from the caller *)
Definition NewFrame (m : Method) (p : ParamDict.t) (st : State.t) : Frame.t :=
  let adds := FrameAdds.make (LocSet.union st@fr@assignables (ObjSet2LocSet st@fr@fresh)) ObjSet.empty (st@h , p) VarDict.empty in
  Frame.build m p adds.

Definition pre_frame (m : Method) (fr : Frame.t) : Frame.t :=
  let adds := FrameAdds.make fr@assignables ObjSet.empty (fr@preheap, fr@preparams) VarDict.empty in 
  Frame.build m fr@preparams adds.

Definition pre_state (m : Method) (st : State.t) : State.t :=
  [ st@fr@preheap, pre_frame m st@fr , st@adds].

(** Recreate the pre-state of a method. *)

(** ** Implementation of the Annotation Table
The implementation defines a purely functional evaluation of JML level 0 constructs. *)

Module AnnotationTable <: ANNOTATION_TABLE State.

(** A little collection of shortcuts, helpers and simplifications *)

  Definition MinInt : Z := (-Int.half_base)%Z.
  Definition MaxInt : Z := (Int.half_base-1)%Z.

  Parameter P2b : Prop -> bool.
      Axiom P2b_true: forall (P : Prop) , P -> P2b P = true.
      Axiom P2b_false: forall (P : Prop) , ~P -> P2b P = false.

  Coercion Is_true : bool >-> Sortclass.

  Definition lt2t (lt : Heap.ObjectType): StaticType :=
    match lt with
    | Heap.ObjectObject cn um => ReferenceType (TypeDefType cn um)
    | Heap.ObjectArray _ t um => ReferenceType (ArrayType t um)
    end.


(** Signatures used to evaluate methods in specs and model fields. *)

  Parameter EvalPureMethod : Program -> Class -> Method -> State.t ->  option Value.
  Parameter EvalModel      : Program -> ModelFieldSignature -> option Object -> State.t -> option Value.


Section AnnotationTableDefs.

(** Within this section, use implicit parameters p c m to define the current whereabouts.
Outside this section, the variables appear as explicit paramters when used.*)

  Variable p : Program.
  Variable c : Class.
  Variable m : Method.

(** Operations on integers *)

  Definition EvalBinaryIntOp (op : BinaryIntOp) (i1 : Int.t) (i2 : Int.t) : Int.t :=
    match op with
    | Addition           => Int.add i1 i2
    | Subtraction        => Int.sub i1 i2
    | Multiplication     => Int.mul i1 i2
    | Division           => Int.div i1 i2
    | Remainder          => Int.rem i1 i2
    | ShiftRightSigned   => Int.shr i1 i2
    | ShiftRightUnsigned => Int.ushr i1 i2
    | ShiftLeft          => Int.shl i1 i2
    | BitwiseAnd         => Int.and i1 i2
    | BitwiseOr          => Int.or i1 i2
    | BitwiseXor         => Int.xor i1 i2
    end.

  Definition EvalUnaryIntOp (op : UnaryIntOp) (i : Int.t) :=
    match op with
    | UnaryPlus         => i
    | UnaryMinus        => Int.neg i
    | PrefixIncrement   => Int.add i (Int.const 1)
    | PrefixDecrement   => Int.sub i (Int.const 1)
    | PostfixIncrement  => Int.add i (Int.const 1)
    | PostfixDecrement  => Int.sub i (Int.const 1)
    | BitwiseComplement => Int.not i
    end.

(** Widening and narrowing of numbers (Java Reference Manual 5.1.4) *)

  Open Scope precedence_scope.

  Definition EvalBinaryNumOp (op : BinaryIntOp) (n1 : num) (n2 : num) : num :=
    match n1 , n2 with
    | I i1 , I i2  =>  I (EvalBinaryIntOp op i1 i2)
    | I i1 , B b2  =>  I (EvalBinaryIntOp op i1 (b2i b2))
    | I i1 , Sh s2 =>  I (EvalBinaryIntOp op i1 (s2i s2))
    | B b1 , I i2  =>  I (EvalBinaryIntOp op (b2i b1) i2)
    | B b1 , B b2  =>  B (i2b $ EvalBinaryIntOp op (b2i b1) (b2i b2))
    | B b1 , Sh s2 =>  B (i2b $ EvalBinaryIntOp op (b2i b1) (s2i s2))
    | Sh s1, I i2  =>  I (EvalBinaryIntOp op (s2i s1) i2)
    | Sh s1, B b2  =>  B (i2b $ EvalBinaryIntOp op (s2i s1) (b2i b2))
    | Sh s1, Sh s2 =>  Sh(i2s $ EvalBinaryIntOp op (s2i s1) (s2i s2))
    end.

  Definition EvalUnaryNumOp (op : UnaryIntOp) (n : num) : num :=
    match n with
    | I i  =>  I (EvalUnaryIntOp op i )
    | B b  =>  B (i2b $ EvalUnaryIntOp op (b2i b))
    | Sh s =>  Sh(i2s $ EvalUnaryIntOp op (s2i s))
    end.

(** Boolean operations *)

  Definition EvalBinaryBoolOp (op : BinaryBoolOp) (b1 : Prop) (b2 : Prop) : Prop :=
    match op with
    | BoolEquality   => b1 <-> b2
    | BoolInequality
    | LogicalXor     => not (b1 <-> b2)
    | LogicalAnd => b1 /\ b2
    | LogicalOr  => b1 \/ b2
    end.

  Definition EvalUnaryBoolOp (op : UnaryBoolOp) (b : Prop) :=
    match op with LogicalComplement => not b end.

  Definition EvalRelationalOp (op : RelationalOp) (n1 : num) (n2 : num) : Prop :=
    match op with
    | IntEquality   => ((n2z n1) = (n2z n2))%Z
    | IntInequality => ((n2z n1) <> (n2z n2))%Z
    | Less          => ((n2z n1) < (n2z n2))%Z
    | Greater       => ((n2z n1) > (n2z n2))%Z
    | LessEqual     => ((n2z n1) <= (n2z n2))%Z
    | GreaterEqual  => ((n2z n1) >= (n2z n2))%Z
    end.

  Definition EvalJMLBoolOp (op : JMLBoolOp) (b1 : Prop) (b2 : Prop) : Prop :=
    match op with
    | Equivalence      => b1 <-> b2
    | Inequivalence    => not (b1 <-> b2)
    | LeftImplication  => b2 -> b1
    | RightImplication => b1 -> b2
    end.

(** Operations on object references *)

  Definition EvalBinaryRefOp (op : BinaryRefOp) (r1 : option Object) (r2 : option Object) : Prop :=
    let refEqual r1 r2 :=
      match r1 , r2 with
      | None    , None    => True
      | Some l1 , Some l2 => l1 = l2
      | _       , _       => False
      end in 
    match op with
    | RefEquality   => refEqual r1 r2
    | RefInequality => not (refEqual r1 r2)
    end.

(** Boolean and Number literals *)

  Definition EvalLiteral (l : Literal) : Value :=
    match l with
    | BoolLiteral b => Bool b
    | IntLiteral z  => Num (I (Int.const z))
    end.

Section EvalHelpers.

(** Evaluation functions for JML expressions have circular dependencies. In Coq, it's not possible to 
refer to a function that is defined later in the text. That's why we introduce variables with
signatures of the functions that we need to know already. That way, we don't have to carry them around as parameters. *)

  Variable EvalBoolExpression : Expression -> State.t -> Prop.
  Variable EvalRefExpression  : Expression -> State.t -> option Object.
  Variable EvalNumExpression  : Expression -> State.t -> num.


  Definition EvalBinaryCondBoolOp (op : ConditionalOp) (e1 : Expression) (e2 : Expression) (st : State.t) : Prop :=
    match op with
    | ConditionalAnd => if  P2b (EvalBoolExpression e1 st) then (EvalBoolExpression e2 st) else False
    | ConditionalOr  => if  P2b (EvalBoolExpression e1 st) then True else (EvalBoolExpression e2 st)
    end.


(** \fresh: A location is considered fresh, if the location wasn't alive in the prestate. *)
  Definition EvalFresh (flist : list Expression) (st : State.t) : Prop :=
    forall loc ,
      In loc 
        (map
          (fun e => 
             match EvalRefExpression e st with
             | Some loc => loc 
             | _        => UndefinedObject 
             end
          ) 
          flist
        ) ->
      Heap.typeof (st@fr@preheap) loc = None.

(** Field Access *)

  Definition EvalFieldAccess (fsig : FieldSignature) (target : option Expression) (st : State.t) : option Value :=
    match target with
    | Some target' =>
      match EvalRefExpression target' st with
      | None     => None
      | Some loc => Heap.get st@h (Heap.InstanceField loc fsig)
      end
    | None => Heap.get st@h (Heap.StaticField fsig)
    end.

  Definition EvalModelFieldAccess (fsig : ModelFieldSignature) (target : option Expression) (st : State.t) : option Value :=
    match target with
    | Some target' =>
      match EvalRefExpression target' st with
      | None     => None
      | Some loc => EvalModel p fsig (Some loc) st
      end
    | None => EvalModel p fsig None st
    end.

(** Method call *)

  Definition EvalParam (f : Param) (e : Expression) (st : State.t) :  Value :=
    match PARAMSIGNATURE.type (PARAM.signature f) with
    | PrimitiveType BOOLEAN => Bool (EvalBoolExpression e st)
    | PrimitiveType _ => Num (EvalNumExpression  e st)
    | ReferenceType _ => match EvalRefExpression e st with
      | Some loc => Ref loc
      | None => Null
      end
    end.

  Fixpoint EvalParams (formals : list Param) (actuals : list Expression) (st : State.t) {struct actuals} : list (Value) :=
    match formals , actuals with
    | f::fs, e::es => (EvalParam f e st) :: EvalParams fs es st
    | _    , _     => nil
    end.

  Parameter Lookup : Program -> ClassName -> ShortMethodSignature -> option (ClassName * Method ).
  Axiom Lookup_def: 
    forall p cn msig cn' m ,
    Lookup p cn msig = Some (cn',m)  <->  lookup p cn msig (cn',m).
  Axiom Lookup_undef: 
    forall p cn msig ,
    Lookup p cn msig = None  <->  (forall cn' m, ~ lookup p cn msig (cn',m)).

  Definition EvalMethodInvocation (msig : MethodSignature) (target : option Expression) (actuals : list Expression) (st : State.t) : option Value :=
    let pv := EvalParams (METHODSIGNATURE.parameters (snd msig)) actuals st in
    match target with
    | Some target' => 
      match EvalRefExpression target' st with
      | Some target'loc =>
        match Heap.typeof st@h target'loc with
        | Some (Heap.ObjectObject cn um) => 
          match Lookup p cn (snd msig) with
          |Some (cn', m') =>
          match PROG.class p cn with
          | Some c' =>  
            let params := lv2params m' ((l2v (Some target'loc))::pv) in
            let fr' := NewFrame m' params st in
            EvalPureMethod p c' m' st[fr:=fr']
          | None => None
          end 
        | _ => None
        end
        | _ => None
        end
      | None => None
      end
    | None => 
      match PROG.class p (fst msig) with
      | Some c' => 
        match findMethod p msig with
	| Some m' => 
            let params := lv2params m' pv in
            let fr' := NewFrame m' params st in
            EvalPureMethod p c' m' st[fr:=fr']
	| None => None
        end
      | None => None
      end
    end.
     
(** Instance of operator *)

  Definition EvalInstanceof (e : Expression) (t : StaticType) (st : State.t) : Prop :=
    match EvalRefExpression e st with
    | None   => False
    | Some l => 
      match Heap.typeof st@h l with
      | Some lt => lt2t lt = t
      | None => False
      end  
   end.

(** \result keyword*)
	
  Definition EvalResult (st : State.t) : option Value :=
    match Frame.ret st@fr with 
    | Normal val    => val 
    | Exception loc => Some (Ref loc)
    end.

(** Conditional (only for booleans, int/ref missing) *)

  Definition EvalBoolConditional (c : Expression) (t : Expression) (e : Expression) (st : State.t) : Prop :=
    let bc := EvalBoolExpression c st in 
    let bt := EvalBoolExpression t st in 
    let be := EvalBoolExpression e st in 
    (bc -> bt) /\ (~bc -> be).

(** Array Elements nonnull *)

  Definition EvalNonnullElements (e : Expression) (st : State.t) : Prop :=
    forall loc ,
      EvalRefExpression e st = Some loc /\
      forall elem index,
        Heap.get st@h (Heap.ArrayElement loc index) = Some elem ->
        elem <> Null.

(** Forall/Exists quantification, see [EvalBoolExpression] below *)

  Definition EvalQuantifier (qvar : Var) (r : Expression) (e : Expression) (v : Value) (st : State.t) : Prop := 
    let fr' := st@fr[quants:= VarDict.update st@fr@quants qvar v] in
    let e'  := EvalBoolExpression e st[fr:=fr'] in
    let r'  := EvalBoolExpression r st[fr:=fr'] in
    r' -> e'.

(** Generalized Quantifiers *)

  Parameter QuantSet : set Int.t.
      Axiom QuantSet_def : forall i z, 
        set_In i QuantSet <-> (z = Int.toZ i -> (z >= MinInt)%Z /\ (z <= MaxInt)%Z).

  Definition QuantOp (q : Quantifier) : Int.t -> Int.t -> Int.t :=
    match q with
    | Sum     => Int.add
    | Product => Int.mul
    | Min     => fun a b => Int.const (Z.min (Int.toZ a) (Int.toZ b))
    | Max     => fun a b => Int.const (Z.min (Int.toZ a) (Int.toZ b))
    | _       => fun a b => Int.const 0
    end.

  Definition QuantIdentityElement (q : Quantifier) : Int.t :=
    match q with
    | Sum => Int.const 0
    | Product => Int.const 1
    | Min => Int.const MaxInt
    | Max => Int.const MinInt
    | _ => Int.const 0
    end.

  Definition QuantFilter  (v : Var) (e : Expression) (st : State.t) (i : Int.t) : bool :=
    let fr' := st@fr[quants:=VarDict.update st@fr@quants v (Num (I i))] in
    P2b $ EvalBoolExpression e st[fr := fr'].

  Definition QuantExpression (v : Var) (e : Expression) (st : State.t) (i : Int.t) : Int.t :=
    let fr' := st@fr[quants:=VarDict.update st@fr@quants v (Num (I i))] in
    match EvalNumExpression e st[fr := fr'] with
    | I n  => n
    | B n  => b2i n
    | Sh n => s2i n
    end.

  Definition EvalGeneralizedQuantifier (q : Quantifier) (v : Var) (r : Expression) (e : Expression) (st : State.t): Int.t :=
    fold_right
      ( QuantOp q)
      ( QuantIdentityElement q)
      ( map 
        (QuantExpression v e st)
        ( filter 
          (QuantFilter v r st) 
          QuantSet
        )
      ).


(** Get type of expression *)

  Definition EvalType (e : Expression) (st : State.t) : Heap.ObjectType :=
    match e with
    | \type (ReferenceType (TypeDefType cn um)) => (Heap.ObjectObject cn um)
    | \typeof expr => 
      match EvalRefExpression e st with
      | Some loc =>
        match Heap.typeof st@h loc with
        | Some t   => t
        | _        => UndefinedType (* location not alive in heap *)
        end
      | _ => UndefinedType (* expr evaluates to null *)
      end
    | _ => UndefinedType (* e is no type expression *) 
    end.

  Definition EvalNewExpression (t : StaticType) (st : State.t) : option Object :=
    match t with
    | ReferenceType (TypeDefType cn um) =>
       match (Heap.new st@h p (Heap.ObjectObject cn um)) with
       | Some (loc, h') => Some loc
       | _ => None
       end
     | _ => None
     end.

(** Evaluations of expressions that are common to int/bool/ref *)

  Definition EvalExpression (e : Expression) (st : State.t) : option Value :=
    match e with
    | var l                      => VarDict.get st@fr@vars l
    | quantifier q               => VarDict.get st@fr@quants q
    | param par                  => ParamDict.get st@fr@params par
    | field fsig target          => EvalFieldAccess fsig target st
    | modelField fsig target     => EvalModelFieldAccess fsig target st
    | method msig target params  => EvalMethodInvocation msig target params st
    | \result                    => EvalResult st
    | _                          => None
    end.

End EvalHelpers.

(** Semantics of JML Expressions *)

  Fixpoint EvalBoolExpression (e : Expression) (st : State.t) {struct e} : Prop :=
    match e with
    | var _ | quantifier _ | param _ | field _ _ | modelField _ _ | method _ _ _  | \result                    
                                 => v2b $ EvalExpression EvalBoolExpression EvalRefExpression EvalNumExpression e st
    | literal (BoolLiteral b)    => b
    | UnaryBoolExpr op e         => EvalUnaryBoolOp op (EvalBoolExpression e st)
    | BinaryBoolExpr op e1 e2    => EvalBinaryBoolOp op (EvalBoolExpression e1 st) (EvalBoolExpression e2 st)
    | BinaryCondBoolExpr op e1 e2 => EvalBinaryCondBoolOp EvalBoolExpression op e1 e2 st
    | RelationalExpr op e1 e2    => EvalRelationalOp op (EvalNumExpression e1 st) (EvalNumExpression e2 st)
    | BinaryRefExpr op e1 e2     => EvalBinaryRefOp op (EvalRefExpression e1 st) (EvalRefExpression e2 st)
    | JMLBinaryBoolExpr op e1 e2 => EvalJMLBoolOp op (EvalBoolExpression e1 st) (EvalBoolExpression e2 st)
    | Conditional cond t e       => EvalBoolConditional EvalBoolExpression cond t e st
    | e1 <: e2                   => types_compatible p (EvalType EvalRefExpression e1 st) (EvalType EvalRefExpression e2 st)
    | e instanceof t             => EvalInstanceof EvalRefExpression e t st
    | \old e                     => EvalBoolExpression e (pre_state m st)      (* RM11.4.2 *)
    | \fresh flist               => EvalFresh EvalRefExpression flist st                           (* RM11.4.9 *)
    | \nonnullelements e         => EvalNonnullElements EvalRefExpression e st                     (* RM11.4.14 *)
    | \forall1 qvar ; r ; e      => forall v , EvalQuantifier EvalBoolExpression qvar r e v st      (* HEL, RM11.4.24.1 *)
    | \exists1 qvar ; r ; e      => exists v , EvalQuantifier EvalBoolExpression qvar r e v st      (* HEL, RM11.4.24.1 *) 
    | _                          => UndefinedProp
    end
  with EvalRefExpression (e : Expression) (st : State.t) {struct e} : option Object :=
    match e with
    | var _ | quantifier _ | param _ | field _ _ | modelField _ _ | method _ _ _  | \result                    
                                 => v2l $ EvalExpression EvalBoolExpression EvalRefExpression EvalNumExpression e st
    | null => None
    | this                       => v2l $ ParamDict.get (Frame.params st@fr) paramThis
    | Cast t e                   => EvalRefExpression e st (* Assuming that the cast is fine *)
    | \old e                     => EvalRefExpression e (pre_state m st)       (* RM11.4.2 *)
    | new t                    => EvalNewExpression t st
    | _                          => None
    end
  with EvalNumExpression (e : Expression) (st : State.t) {struct e} : num :=
    match e with
    | var _ | quantifier _ | param _ | field _ _ | modelField _ _ | method _ _ _  | \result                    
                                 => v2n $ EvalExpression EvalBoolExpression EvalRefExpression EvalNumExpression e st
    | literal (IntLiteral n)     => I (Int.const n)
    | UnaryIntExpr op e          => EvalUnaryNumOp op (EvalNumExpression e st)
    | BinaryIntExpr op e1 e2     => EvalBinaryNumOp op (EvalNumExpression e1 st) (EvalNumExpression e2 st)
    | Cast t e                   => EvalNumExpression e st (* Assuming that the cast is fine *)
    | \old e                     => EvalNumExpression e (pre_state m st)       (* RM11.4.2 *)
    | Quantification q v r e     => I (EvalGeneralizedQuantifier EvalBoolExpression EvalNumExpression q v r e st)
    | _                          => UndefinedNum
    end.

(** A predicate is a boolean expression *)

  Definition EvalPredicate := EvalBoolExpression.

  (** Requires Clause *)

  Definition NotSpecifiedRequires : Prop := True.

  (* HEL, RM9.9.2 *)
  Definition EvalRequires (sc : SpecificationCase) (st : State.t) : Prop := 
    forall r , 
      r = CASE.requires sc ->
      match REQUIRES.pred r with
      | (:expr:)          => EvalPredicate expr st  
      | \not_specified => NotSpecifiedRequires
      end.

  (** Ensures Clause *)

  Definition NotSpecifiedEnsures : Prop := True.

  (* HEL, RM9.9.3 *)
  Definition EvalEnsures (sc : SpecificationCase) (st : State.t) : Prop := 
    match ENSURES.pred (CASE.ensures sc) with
      | (:expr:)       => EvalPredicate expr st
      | \not_specified => NotSpecifiedEnsures
      end.

  (** Signals Clause *)

  Definition NotSpecifiedSignals : Prop := False.

  Definition EvalSignals (sc : SpecificationCase) (st : State.t) : Prop :=
    let s := CASE.signals sc in
    forall e, 
      Exception e = Frame.ret st@fr ->
      let fr' := (Frame.set_param st@fr (SIGNALS.exception s) (Ref e)) in
        match SIGNALS.pred s with
        | (:expr:)       => EvalPredicate expr st[fr:=fr']
        | \not_specified => NotSpecifiedSignals 
        end. 

  (** SignalsOnly Clause *)

  Definition NotSpecifiedSignalsOnly : Prop := False.
     
  Definition EvalSignalsOnly  (sc : SpecificationCase) (st : State.t) : Prop :=
    let s := CASE.signalsOnly sc in
    forall loc , 
      Exception loc = Frame.ret st@fr ->
      exists t , In t (SIGNALS_ONLY.types s) /\
      assign_compatible p st@h (Ref loc) t.

  (** Evaluating all invariants *)

Definition LookupTypedef (p: Program) (n : TypeDefName) : option TYPEDEF.t :=
match PROG.class p n ,  PROG.interface p n with
| Some c , _ => Some c
| _ , Some i => Some i
|_, _ => None
end.

  Definition EvalObjectInvariant (o : Object) (st : State.t) : Prop :=
    if METHOD.isHelper m then
      True
    else
      forall cn um t,
	Heap.typeof st@h o = Some (Heap.ObjectObject cn um) ->
	LookupTypedef p cn = Some t ->
         ( forall inv ,
          DefinedInvariant t inv ->
          EvalPredicate (INVARIANT.pred inv) st[fr := st@fr[this := o]] ).

  Definition EvalStaticInvariant (st : State.t) : Prop :=
    if METHOD.isHelper m then
      True
    else
         ( forall inv ,
          DefinedInvariant c inv ->
          INVARIANT.isStatic inv = true ->
          EvalPredicate (INVARIANT.pred inv) st).

  Definition EvalInitially (st : State.t) : Prop :=
    if METHOD.isHelper m then
      True
    else
         forall ini ,
          DefinedInitially c ini ->
          EvalPredicate (INITIALLY.pred ini) st.


End AnnotationTableDefs.

  (** Implementation of the Annotation Table functions *)

  Definition Precondition (p : Program) (c : Class) (m : Method) (st : State.t) : Prop := 
    (
      match METHOD.kind m , st@fr@this with
      | Constructor, Some loc =>
          forall o : Object, o <> loc -> EvalObjectInvariant p m o st
      | _ , _  => forall o : Object,  EvalObjectInvariant p m o st
      end )
    /\
      forall c', EvalStaticInvariant p c' m st
    /\
    (exists sc ,
      DefinedCase c m sc /\ 
      EvalRequires p m sc st
    ).

  Definition Postcondition (p : Program) (c : Class) (m : Method) (st : State.t) : Prop :=
    let st' := pre_state m st in
    (
      match METHOD.kind m , st@fr@this with
      | Constructor, Some loc =>
        (forall o : Object,  EvalObjectInvariant p m o st) /\ EvalInitially p c m st
      | Finalizer, Some loc =>
          forall o : Object, o <> loc -> EvalObjectInvariant p m o st
      | _ , _  => forall o : Object,  EvalObjectInvariant p m o st
      end )
    /\
      forall c', EvalStaticInvariant p c' m st
    /\
    (forall sc ,
      DefinedCase c m sc ->
      match Frame.ret st@fr with
      | Normal _    => 
        EvalRequires p m sc st' ->
        EvalEnsures p m sc st
      | Exception _ => 
        EvalRequires p m sc st' -> (
        EvalSignals p m sc st /\
        EvalSignalsOnly p sc st
        )
      end
    ).

  Definition LocalAssertion (p : Program) (c : Class) (m : Method) (pc : PC) (st : State.t) : option Prop :=
    match statement_at m pc with
    | Some (LocalAssertion e _ _) 
    | Some (LocalAssumption e _ _) => Some (EvalPredicate p m e st)
    | _ => None
    end. 

  Definition NotSpecifiedLoopInvariant := Some True.

  Definition LoopInvariant (p : Program) (c : Class) (m : Method) (pc : PC) (st : State.t) : option Prop :=
    match statement_at m pc with
    | Some (WhileLoop anno _ _) 
    | Some (DoLoop anno _ _)
    | Some (ForLoop anno _ _ _ _) => 
    match LOOP_ANNOTATION.expression anno with
      | (:e:)           => Some (EvalPredicate p m e st)
      | \not_specified  => NotSpecifiedLoopInvariant
    end
    | _ => None
    end. 

Axiom EvalPureMethod_def: 
    forall p c m st ,
      Precondition p c m st ->
      exists ret,
        ret = EvalPureMethod p c m st /\
        Postcondition p c m st[fr := st@fr[ret := Normal (ret)]].

End AnnotationTable.

(** ** Semantics Implementation of the [ASSIGNABLES] Module Type *)

Module Assignables <: ASSIGNABLES State.

  Import AnnotationTable.

(** Implementation of the interface *)

(** Simply find the location in the list of assignable locations *)

  Definition FieldUpdateCheck (p : Program) (am : Location) (st : State.t): Prop :=
    LocSet.In am st@fr@assignables 
    \/ 
    (LocInObjSet am st@fr@fresh = true).
  
(** Evaluate the assignable clause, including unfolding of dynamic datagroups *)

  Parameter ValidCase : Program -> Class -> Method -> State.t -> list SpecificationCase.
  Axiom ValidCase_def :
    forall p c m st sc,
    In sc (ValidCase p c m st) <->
    DefinedCase c m sc /\ EvalRequires p m sc (pre_state m st).

  (* choose between \nothing and \everything *)
  Definition NotSpecifiedAssignableClause := \everything.
 
  Fixpoint ExtractAssignableClauses (sc_list : list SpecificationCase) : list StoreRefList :=
  match sc_list with
  | nil => nil
  | sc::sc_list' =>
    match METHODSPEC.ASSIGNABLE.storeRefs (CASE.assignable sc) with
    | \not_specified => NotSpecifiedAssignableClause :: ExtractAssignableClauses sc_list'
    | (: sr :) => sr :: ExtractAssignableClauses sc_list'
    end
  end.

  Fixpoint AssignableEverything (sr_list : list StoreRefList) : bool :=
  match sr_list with
  | nil => match NotSpecifiedAssignableClause with
    | \everything => true
    | _ => false
    end
  | sr::sr_list' => match sr with
    | \everything => true
    | _ => AssignableEverything sr_list'
    end
  end.

  Fixpoint AssignableNothing (sr_list : list StoreRefList) : bool :=
  match sr_list with
  | nil => match NotSpecifiedAssignableClause with
    | \nothing => true
    | _ => false
    end
  | sr::sr_list' => match sr with
    | \nothing => true
    | _ => AssignableNothing sr_list'
    end
  end.
  
  Fixpoint ConcatinateStoreRefs (sr_list : list StoreRefList) : list StoreRef :=
  match sr_list with
  | nil => nil
  | \nothing :: sr_list' => ConcatinateStoreRefs sr_list'
  | \everything :: sr_list' => nil
  | StoreRefs srl :: sr_list' => srl +++ ConcatinateStoreRefs sr_list'
  end.

  Definition ValidStoreRefs (p : Program) (c : Class) (m : Method) (st : State.t) : StoreRefList :=
  let sr_list := ExtractAssignableClauses (ValidCase p c m st) in
  if AssignableEverything sr_list then \everything else
  if AssignableNothing sr_list then \nothing else
  StoreRefs (ConcatinateStoreRefs sr_list).

  Fixpoint StoreRefPrefix2Object (fr : Frame.t) (sr : StoreRefPrefix) : Object :=
  match sr with
  | ThisRef => match Frame.this fr with
    | Some loc => loc
    | _ => UndefinedObject
    end
  | ParamRef p => match ParamDict.get (Frame.params fr) p with
    | Some (Ref loc) => loc
    | _ => UndefinedObject
    end
  | PathRef target fsig => match Heap.get fr@preheap (Heap.InstanceField (StoreRefPrefix2Object fr target) fsig) with
    | Some (Ref loc) => loc
    | _ => UndefinedObject
    end
  end.

  Definition StoreRef2Location (p : Program) (fr : Frame.t) (sr : StoreRef) : LocSet.t :=
  match sr with
  | StaticFieldRef fsig => LocSet.singleton (Heap.StaticField fsig)
  | FieldRef target fsig => LocSet.singleton (Heap.InstanceField (StoreRefPrefix2Object fr target) fsig)
  | AllFieldsRef target => AllAmOfObject p fr@preheap (StoreRefPrefix2Object fr target)
  end.

  (** Evaluate an Assignable Clause into a set of Locations. *)
  Definition EvalAssignableClause (p : Program) (c : Class) (m : Method) (st : State.t) : LocSet.t :=
  let sr := ValidStoreRefs p c m st in 
  match sr with
  | \nothing => LocSet.empty
  | \everything => AllLoc st@fr@preheap
  | StoreRefs srl => 
      fold_right 
        (fun sr locs => 
          LocSet.union (StoreRef2Location p st@fr sr) locs) 
        LocSet.empty 
        srl
  end.

  Definition MethodCallAction (p : Program) (c : Class) (m : Method) (st : State.t) : State.t :=
  let locs := UnfoldDatagroups p st@h (EvalAssignableClause p c m st) in
  st[fr:=st@fr[assignables :/\ locs]].

(** Add all fields of a newly created object to the list of fresh locations, as well
to the assignable list *)

Definition NewObjectAction (p : Program) (obj : Object) (st : State.t) : State.t :=
    st[fr:=st@fr[fresh :+ obj]].

(** Upon method return, add all freshly created locations to the list of fresh locations from the caller *)

  Definition MethodReturnAction (p : Program) (st_c : State.t) (st : State.t) : State.t :=
  st_c[fr:=st@fr[fresh :\/ st_c@fr@fresh]].

(** No action needed in the semantics (this function will be used in RAC) *)

  Definition FieldUpdateAction (p : Program) (loc : Location) (v : Value) (st : State.t) : State.t :=
    st.

End Assignables.

End Sem.
