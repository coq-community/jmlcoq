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

(* Coq Parser extensions for JML/Java syntax.
   JMLSyntax contains implementation independent Notation shorthands  for 
   expressions (JML/Java) and some JML keywords.
 *)

Require Export JMLProgram.
Require Import ZArith.
Require Import List.

Module EXPRESSION_NOTATIONS (P:PROGRAM).
Import P.

Declare Scope jml_scope.
Delimit Scope jml_scope with jml.

(** Notation for convenient list construction syntax, e.g. [1; 2; 3] instead of 1::2::3::nil *)
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) : jml_scope.

Notation "[]" := nil : jml_scope.

(** Visibility (access control) modifiers are written in lowercase in Java *)
(* Visibility now treated as normal modifiers in full syntax
Definition public := Public.
Definition protected := Protected.
Definition package := Package.
Definition private := Private.
*)

(** Type declaration shorthands *)
Definition int_t : StaticType := PrimitiveType INT.
Definition boolean_t : StaticType := PrimitiveType BOOLEAN.
Definition byte_t : StaticType := PrimitiveType BYTE.
Definition short_t : StaticType := PrimitiveType SHORT.

Definition class_t (name:ClassName) (um:utsModifier) := ReferenceType (TypeDefType name um).
Definition interface_t (name:InterfaceName) (um:utsModifier) := ReferenceType (TypeDefType name um).

Definition array_t (inner:StaticType) (um:utsModifier) := ReferenceType (ArrayType inner um).

(** alternative names for UTS modifiers *)
Notation "\peer" := peer : jml_scope.
Notation "\rep" :=  rep : jml_scope.
Notation "\any" :=  any : jml_scope.
Notation "'readonly'" :=  any : jml_scope.
Notation "\readonly" :=  any : jml_scope.

(** JML \TYPE constant *)
Notation "\TYPE" := javaLangClass : jml_scope.

(** Notations for optional expressions (Specified/Not specified) *)
Notation "\not_specified" := NotSpecified : jml_scope.
Notation "(: expr :)"     := (Specified expr) : jml_scope.

(** Expression notations *)
Notation "'int' x" := (literal (IntLiteral x)) (at level 0) : jml_scope.
Notation "'false''" := (literal (BoolLiteral false)) (at level 0) : jml_scope.
Notation "'true''" := (literal (BoolLiteral true)) (at level 0) : jml_scope.
Notation "x + y" := (BinaryIntExpr Addition  x y ) : jml_scope.
Notation "x - y" := (BinaryIntExpr Subtraction x y ) : jml_scope.
Notation "x * y" := (BinaryIntExpr Multiplication x y ) : jml_scope.
Notation "x / y" := (BinaryIntExpr Division x y ) : jml_scope.
Notation "x 'mod' y" := (BinaryIntExpr Remainder x y ) (at level 40) : jml_scope.
Notation "x >> y" := (BinaryIntExpr ShiftRightSigned  x y) (at level 60) : jml_scope.
Notation "x >>> y" := (BinaryIntExpr ShiftRightUnsigned x y) (at level 60) : jml_scope.
Notation "x << y" := (BinaryIntExpr ShiftLeft x y) (at level 60) : jml_scope.
Notation "x &' y" := (BinaryIntExpr BitwiseAnd x y) (at level 73) : jml_scope.
Notation "x |' y" := (BinaryIntExpr BitwiseOr x y) (at level 75) : jml_scope.
Notation "x ^' y" := (BinaryIntExpr BitwiseXor x y) (at level 77) : jml_scope.
Notation "x < y" := (RelationalExpr Less x y) : jml_scope.
Notation "x > y" := (RelationalExpr Greater x y) : jml_scope.
Notation "x <= y" := (RelationalExpr LessEqual x y) : jml_scope.
Notation "x >= y" := (RelationalExpr GreaterEqual x y) : jml_scope.

Notation "x == y" := (RelationalExpr IntEquality x y) (at level 72) : jml_scope.
Notation "x != y" := (RelationalExpr IntInequality x y) (at level 72) : jml_scope.

Notation "x ==' y" := (BinaryRefExpr RefEquality x y) (at level 72) : jml_scope.
Notation "x !=' y" := (BinaryRefExpr RefInequality x y) (at level 72) : jml_scope.

Notation "x =='' y" := (BinaryBoolExpr BoolEquality x y) (at level 72) : jml_scope.
Notation "x !='' y" := (BinaryRefExpr BoolInequality x y) (at level 72) : jml_scope.

Notation "x <: y" := (Subtype x y) (at level 70) : jml_scope.
Notation "x &&' y" := (BinaryCondBoolExpr ConditionalAnd x y) (at level 80) : jml_scope.
Notation "x ||' y" := (BinaryCondBoolExpr ConditionalOr x y) (at level 85): jml_scope.
Notation "+ x" := (UnaryIntExpr UnaryPlus x) (at level 35) : jml_scope.
Notation "- x" := (UnaryIntExpr UnaryMinus x) : jml_scope.

(* pre-/postfix increment operators render list append ++ useless *)
(*   --> replace list append ++ by +++ *)
Infix "+++" := app (right associativity, at level 60) : list_scope.

Notation "++ x" := (UnaryIntExpr PrefixIncrement x) (at level 35) : jml_scope.
Notation "-- x" := (UnaryIntExpr PrefixDecrement x) (at level 35) : jml_scope.
Notation "~' x" := (UnaryIntExpr BitwiseComplement x) (at level 35) : jml_scope.
Notation "! x" := (UnaryBoolExpr LogicalComplement x) (at level 35) : jml_scope.
Notation "x ++" := (UnaryIntExpr PostfixIncrement x) (at level 35) : jml_scope.
Notation "x --" := (UnaryIntExpr PostfixIncrement x) (at level 35) : jml_scope.

Notation "x =' y" := (Assignment x y) (at level 98) : jml_scope.

Notation "x += y" := (IntAssignmentExpr AssignmentAddition x y ) (at level 98) : jml_scope.
Notation "x -= y" := (IntAssignmentExpr AssignmentSubtraction x y ) (at level 98) : jml_scope.
Notation "x *= y" := (IntAssignmentExpr AssignmentMultiplication x y ) (at level 98) : jml_scope.
Notation "x /= y" := (IntAssignmentExpr AssignmentDivision x y ) (at level 98) : jml_scope.
Notation "x %= y" := (IntAssignmentExpr AssignmentRemainder x y ) (at level 98) : jml_scope.
Notation "x <<= y" := (IntAssignmentExpr AssignmentShiftLeft x y ) (at level 98) : jml_scope.
Notation "x >>= y" := (IntAssignmentExpr AssignmentShiftRightSigned x y ) (at level 98) : jml_scope.
Notation "x >>>= y" := (IntAssignmentExpr AssignmentShiftRightUnsigned x y ) (at level 98) : jml_scope.


Notation "x &= y" := (IntAssignmentExpr AssignmentBitwiseAnd x y ) (at level 98) : jml_scope.
Notation "x |= y" := (IntAssignmentExpr AssignmentBitwiseOr x y ) (at level 98) : jml_scope.
Notation "x ^= y" := (IntAssignmentExpr AssignmentBitwiseXor x y ) (at level 98) : jml_scope.

Notation "x &=' y" := (BoolAssignmentExpr AssignmentLogicalAnd x y ) (at level 98) : jml_scope.
Notation "x |=' y" := (BoolAssignmentExpr AssignmentLogicalOr x y ) (at level 98) : jml_scope.
Notation "x ^=' y" := (BoolAssignmentExpr AssignmentLogicalXor x y ) (at level 98) : jml_scope.

Notation "(% x %) y"  := (Cast x y) (at level 35, x at next level) : jml_scope.

Notation "x 'instanceof' y"  := (InstanceOf x y) (at level 70) : jml_scope.
Notation "x 'then''  y 'else'' z " := (Conditional x y z) ( at level 97, y at next level) : jml_scope.
Notation "\nothing" := Nothing : jml_scope.
Notation "\everything" := Everything : jml_scope.
Notation "\result" := (Result)  : jml_scope.
Notation "\oldl e 'at' l" := (OldL e l) (at level 0, e at level 200) : jml_scope.
Notation "\old e" := (Old e) (at level 0) : jml_scope.
Notation "\not_assigned l" := (NotAssigned l) (at level 0) : jml_scope.
Notation "\not_modified l" := (NotModified l) (at level 0) : jml_scope.
Notation "\only_accessed l" := (OnlyAccessed l) (at level 0) : jml_scope.
Notation "\only_assigned l" := (OnlyAssigned l) (at level 0) : jml_scope.
Notation "\only_called m" := (OnlyCalled m) (at level 0) : jml_scope.
Notation "\only_captured m" := (OnlyCaptured m) (at level 0) : jml_scope.
Notation "\fresh f" := (Fresh f) (at level 0) : jml_scope.
Notation "\reach r" := (Reach r) (at level 0) : jml_scope.
Notation "\duration d" := (DurationExpr d) (at level 0) : jml_scope.
Notation "\space s" := (Space s) (at level 0) : jml_scope.
Notation "\working_space w" := (WorkingSpaceExpr w) (at level 0) : jml_scope.
Notation "\nonnullelements x" := (NonNullElements x) (at level 0) : jml_scope.
Notation "\typeof e" := (TypeOf e) (at level 0) : jml_scope.
Notation "\elemtype e" := (ElemType e) (at level 0) : jml_scope.
Notation "\type e" := (GetType e) (at level 0): jml_scope.
Notation "\lockset" := (Lockset) : jml_scope.
Notation "\max m" := (MaxObject m) (at level 0) : jml_scope.
Notation "\is_initialized e" := (IsInitialized e) (at level 0) : jml_scope.
Notation "\invariant_for e" := (InvariantFor e) (at level 0) : jml_scope.
Notation "\lblneg x y" := (LblNeg x y) (at level 0) : jml_scope.
Notation "\lblpos x y" := (LblPos x y) (at level 0) : jml_scope.
Notation "\forall1 v ; r ; e" := (Quantification Forall v r e) (at level 0, e at level 200) : jml_scope.
Notation "\exists1 v ; r ; e" := (Quantification Exists v r e) (at level 0, e at level 200) : jml_scope.
Notation "\max1 v ; r ; e" := (Quantification Max v r e) (at level 0, e at level 200) : jml_scope.
Notation "\min1 v ; r ; e" := (Quantification Min v r e) (at level 0, e at level 200) : jml_scope.
Notation "\num_of1 v ; r ; e" := (Quantification NumOf v r e) (at level 0, e at level 200) : jml_scope.
Notation "\product1 v ; r ; e" := (Quantification Product v r e) (at level 0, e at level 200) : jml_scope.
Notation "\sum1 v ; r ; e" := (Quantification Sum v r e) (at level 0, e at level 200) : jml_scope.
Notation "x <==> y" := (JMLBinaryBoolExpr Equivalence x y) (at level 96) : jml_scope.
Notation "x <=!=> y" := (JMLBinaryBoolExpr Inequivalence x y) (at level 96) : jml_scope.
Notation "x ==>' y" := (JMLBinaryBoolExpr RightImplication x y) (at level 95) : jml_scope.
Notation "x <== y" := (JMLBinaryBoolExpr LeftImplication x y) (at level 95) : jml_scope.

(* Helper to get rid of some brakets *)

Declare Scope precedence_scope.
Notation "f $ x" := (f x) (at level 99): precedence_scope.

Notation "'ℕ'" := (nat).
Notation "'℞'" := (Prop).

(* Notation "t .> m p" := (method m (Some t) p) (at level 95) : jml_scope. *)

Definition callR r m p := method m (Some r) p.
Definition call m p := method m None p.

End EXPRESSION_NOTATIONS.
