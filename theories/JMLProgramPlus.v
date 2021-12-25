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

From JML Require Export JMLProgram.
From Coq Require Import List.

(**
  PROGRAM_PLUS extends the PROGRAM signature (JMLProgram)
  with full syntax constructs that need explicit representation
  and cannot be rewritten in place. 
  Currently, the added constructs are those for the
  representation of method specification cases.
 
  *)

Module Type PROGRAM_PLUS.

  (** 
    Declare and export the original PROGRAM signature,
    s.t. PROGRAM_PLUS implementors also fulfill the PROGRAM signature.
   *)    
  Declare Module Program : PROGRAM.
  Export Program.

  Module METHODSPEC_PLUS.

    Import Program.METHODSPEC.

    (** The different kind of method specification cases *)
    Inductive SpecCaseType : Set := 
      | lightweight 
      | behaviour
      | normal_behaviour
      | exceptional_behaviour.

    (**
      Special type for the predicate argument of a requires clause,
      that can be either a specified expression, \not_specified or \same.
     *)
    Inductive optionalSame (A : Type) : Type :=
      | NotSpecifiedOS : optionalSame A
      | SpecifiedOS    : A -> optionalSame A
      | same : optionalSame A.
  
    (**
      Full syntax type for a spec header.
      @see JML RM 9.4 spec header
     *)
    Inductive SpecHeader : Type :=
      | requiresSH (redundant : bool) (pred : optionalSame Expression).
  
    (** 
      Full syntax type for simple body clauses.
      @see JML RM 9.4 simple-spec-body
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
  
    (** 
      Full syntax ADT for a generic-spec-case
      @see JML RM 9.4 generic-spec-case
     *)
    Module Type GENERIC_SPEC_CASE_TYPE.
      Parameter t : Type.
      Parameter forallVarDecl : t -> list FORALL_VAR_DECL.t.
      Parameter oldVarDecl    : t -> list OLD_VAR_DECL.t.
      Parameter specHeader    : t -> list SpecHeader.
      Parameter genericBody   : t -> (list MethodSpecClause) + (list t).
    End GENERIC_SPEC_CASE_TYPE.
    Declare Module GENERIC_SPEC_CASE : GENERIC_SPEC_CASE_TYPE.
  
    (** 
      Full syntax ADT for a full specification case,
      i.e. a lightweight-spec-case (JML RM 9.4) or 
      a heavyweight-spec-case (JML RM 9.5)
      @see JML RM 9.4/9.5
     *)
    Module Type FULL_SPEC_CASE_TYPE.
      Parameter t : Type.
      Parameter specCaseType    : t -> SpecCaseType.
      Parameter visibility      : t -> option Visibility.
      Parameter isRedundant     : t -> bool.
      Parameter isCodeContract  : t -> bool.
      Parameter genericSpecCase : t -> GENERIC_SPEC_CASE.t.
    End FULL_SPEC_CASE_TYPE.
    Declare Module FULL_SPEC_CASE : FULL_SPEC_CASE_TYPE.

  End METHODSPEC_PLUS.
End PROGRAM_PLUS.
