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

Require Import List.
Require Import TaggedList.

(**
  FULL2BASIC provides functions that perform, explicitly or implicitly,
  rewritings from the full syntax into the basic syntax constructs.
  The rewritings divide into three categories:
  - method specification desugarings
  - expression rewritings (quantifiers, variants)
  - declaration functions
 
  Both (2) and (3) are in-place rewritings for which no additional full syntax constructs exist.
  This means that, e.g. a variant (var i) is not found in any syntax data type as such, but only
  in its rewritten form (rewriteVariant lbl (var i)) as an invariant.
  
  In contrast, for method specification cases, there exist additional syntactic data types defined
  in the PROGRAM_PLUS signature. Thus, method specification cases are explicitly represented in the 
  corresponding full syntax data types (METHOD.fullSpecs).
  Only after the top-down rewriting of methods is performed (rewriteMethod), the basic syntax equivalent
  (METHOD.specs), i.e. the desugared specification cases, can be found in the data type.
 
  The desugaring of JML method specifications closely follows:
  "Desugaring JML Method Specifications, Arun D. Raghavan and Gary T. Leavens, TR 00-03e".
 *)

Module FULL2BASIC (P:PROGRAM_PLUS).
  Import P.

  Module METHODSPEC_PLUS.
    Export P.METHODSPEC_PLUS.

    (** 
      Identifying tags for the different simple-spec-body-clauses that allow to
      uniformely treat the different clause types while still guaranteeing type safety.
      (For more details, see the full2basic implementation)
     *)
    Inductive ClauseTag : Set := 
      | ensuresT
      | signalsT
      | signalsOnlyT
      | divergesT
      | whenT
      | assignableT
      | accessibleT
      | callableT
      | measuredByT
      | capturesT
      | workingSpaceT
      | durationT.
  
    (** 
      Record for default values for the different clauses.
      @see METHODSPEC_REWRITINGS.lightweightDefaults
      @see METHODSPEC_REWRITINGS.heavyweightDefaults
      *)
    Record FullSpecCaseDefaults : Type := Build_FullSpecCaseDefaults {
      headerDefault : SpecHeader;
      bodyDefault   : ClauseTag -> MethodSpecClause
    }.
  End METHODSPEC_PLUS.

  Module Type METHODSPEC_REWRITINGS_TYPE.
    Import METHODSPEC_PLUS.

    (**
      desugarAll scs m e 

      desugarAll performs the desugarings 3.1, 3.2, 3.3, 3.4, 3.5, 3.6, 3.8 and 3.9 in sequence.
      Desugarings 3.7 (Inheritance and Refinement), 
      3.10 (Make Assignable and Signals_Only Clauses the Same) and
      3.11 (Desugaring Also Combinations) are not treated here but in the semantics (see JMLSemantics).
     *)
    Parameter desugarAll : list FULL_SPEC_CASE.t -> Method -> TYPEDEF.t -> list FULL_SPEC_CASE.t.

    (** Desugaring 3.1 of TR 00-03e: Desugaring Non_Null for Arguments *)
    Parameter desugarNonNullArguments : list FULL_SPEC_CASE.t -> Method -> list FULL_SPEC_CASE.t.

    (** Desugaring 3.2 of TR 00-03e: Desugaring Non_Null Results *)
    Parameter desugarNonNullResult : list FULL_SPEC_CASE.t -> Method -> list FULL_SPEC_CASE.t.

    (** Desugaring 3.3 of TR 00-03e: Desugaring Pure *)
    Parameter desugarPure : list FULL_SPEC_CASE.t -> Method -> list FULL_SPEC_CASE.t.

    (** Desugaring 3.4 of TR 00-03e: Desugaring Empty Specifications *)
    Parameter desugarEmptySpecification : list FULL_SPEC_CASE.t -> Method -> TYPEDEF.t -> list FULL_SPEC_CASE.t.

    (** Desugaring 3.5 of TR 00-03e: Desugaring Nested Specifications *)
    Parameter desugarNested : list FULL_SPEC_CASE.t -> list FULL_SPEC_CASE.t.

    (** 
      addDefaults sc m defaults

      Helper function that adds default clauses from /defaults/ to sc for every kind of clause that
      is missing in sc.
      Valid only on flattened specification cases (after desugaring step 3.5).
     *)
    Parameter addDefaults : FULL_SPEC_CASE.t -> Method -> FullSpecCaseDefaults -> FULL_SPEC_CASE.t.

    (** Default clause values for a lightweight specification case *)
    Parameter lightweightDefaults : FULL_SPEC_CASE.t -> Method -> FullSpecCaseDefaults.

    (** Default clause values for a heavyweight specification case *)
    Parameter heavyweightDefaults : FULL_SPEC_CASE.t -> Method -> FullSpecCaseDefaults.

    (** 
      Desugaring 3.6 of TR 00-03e: Desugaring Lightweight, Normal, and Exceptional Specifications
      Note that, as opposed to described in the TR, specification cases of the same visibilty are not combined here.
      This desugaring depends on desugaring 3.5.
     *)
    Parameter desugarBehaviour : list FULL_SPEC_CASE.t -> Method -> list FULL_SPEC_CASE.t.

    (** Desugaring 3.8 of TR 00-03e: Standardizing Signals Clauses *)
    Parameter desugarSignals : list FULL_SPEC_CASE.t -> list FULL_SPEC_CASE.t.

    (** Desugaring 3.9 of TR 00-03e: Desugaring Multiple Clauses of the Same Kind *)
    Parameter desugarMultiple : list FULL_SPEC_CASE.t -> list FULL_SPEC_CASE.t.

    (**
      rewriteFullSpecs scs m e

      Performs all rewritings (desugarAll) on the list of spec cases scs and
      transforms the full syntax data type FULL_SPEC_CASE.t into the basic syntax type SpecificationCase.
      Note that TR 00-03e does not fill in default values for heavyweight cases in desugaring 3.6,
      so this is necessarily done here.
     *)
    Parameter rewriteFullSpecification : list FULL_SPEC_CASE.t -> Method -> TYPEDEF.t -> list SpecificationCase.

  End METHODSPEC_REWRITINGS_TYPE.

  Module Type TYPESPEC_REWRITINGS_TYPE.
    Import TYPESPEC.

    (**
      rewriteInvariants invs e

      For every non_null (model-)field f of type e, an additional invariant
      (f != null) is conjoined to the existing invariants /invs/.
     *)
    Parameter rewriteInvariants : list INVARIANT.t -> TYPEDEF.t -> list INVARIANT.t.

    (**
      rewriteTypeSpecs ts e

        -> rewriteInvariants 
     *)
    Parameter rewriteTypeSpecs : TYPESPEC.t -> TYPEDEF.t -> TYPESPEC.t.
  End TYPESPEC_REWRITINGS_TYPE.

  Module Type ALL_REWRITINGS_TYPE.
    (**
      rewriteTypeDef e

        -> rewriteMethod for every method m declared in e

        -> rewriteTypeSpec
     *)
    Parameter rewriteTypeDef : TYPEDEF.t -> TYPEDEF.t.

    (**
      rewriteMethod m e

        -> rewriteFullSpecification
     *)
    Parameter rewriteMethod : Method -> TYPEDEF.t -> Method.
  End ALL_REWRITINGS_TYPE.

  Module EXPRESSION_REWRITINGS.
    (** 
      Inductive type to create quantified expressions with multiple variables

      @see RM 11.4.24
     *)
    Inductive FullQuantifier : Type := 
      FullQuantification (q : Quantifier) (vars : list Var) (range : Expression) (expr : Expression).
  End EXPRESSION_REWRITINGS.

  Module Type EXPRESSION_REWRITINGS_TYPE.
    Import EXPRESSION_REWRITINGS.

    (**
      rewriteVariant lbl pred

      Rewrite of a variant as an invariant:
      Tr [decreasing expr] = maintaining (0 <= expr) && (expr <= \old(expr, loopLabel))
     *)
    Parameter rewriteVariant : Label -> Expression -> Expression.

    (**
      rewriteFullQuantifier fq, fq = Q vs range expr
     
      Rewriting of a full quantified expressions (with possibly multiple variables vs) 
      as a nested quantified expression with only a single variable per quantified expression.
     
      Tr [Q v::nil range expr] = Q v range expr

      Tr [Q v::vs  range expr] = Q v -     (Tr [Q vs range expr)
     *)
    Parameter rewriteFullQuantifier : FullQuantifier -> Expression.
  End EXPRESSION_REWRITINGS_TYPE.

  Module DECLARATIONS.

    (** 
      Modifiers for Java/JML declaration supported by the full syntax
      @see JML RM Appendix B
     *)
    Inductive Modifier : Set :=
      | public
      | protected
      | private
      | abstract
      | static
      | final
      | native
      | spec_public
      | spec_protected
      | model
      | ghost
      | pure
      | instance
      | helper
      | non_null
      | nullable
      | nullable_by_default
      | monitored
      | uninitialized
      | code
      | implicit_constructor.
  
    (** Data type for return values *)
    Inductive ReturnType : Set := Void | Return (t:StaticType).
  
    (**
      extends declaration
      In JML, types may be extended weakly, i.e. without inheriting history constraints.
      @see JML RM 6.1.1 Subtyping for Type Definitions
     *)
    Inductive Extends : Type := 
        | extends (cn:Class)
        | extends_weakly (cn:Class)
        | no_extends.
  
    (**
      implements declaration
      In JML, interfaces may be implemented weakly, i.e. without inheriting history constraints.
      @see JML RM 6.1.1 Subtyping for Type Definitions
     *)
    Inductive Implements : Type :=
        | implements (ifn:Interface)
        | implements_weakly (ifn:Interface).
  
    (**
      The entity kind is given in the full syntax declaration functions 
      to distinguish between classes (kind of_class) and interfaces (kind of_interface).
     *)
    Inductive TypeDefKind : Set := ClassEK | InterfaceEK.
  
    (**
       Tag to differentiate between (redundant/non-redundant) invariants and
      (redundant/non-redundant variants.
     *)
    Inductive LoopAnnotationTag : Set := 
      | INVARIANT_TAG
      | INVARIANT_REDUNDANTLY_TAG
      | VARIANT_TAG
      | VARIANT_REDUNDANTLY_TAG.

    (** functional or relational represents type spec clause *)
    Inductive RepresentsKind : Set := Functional | Relational.
  End DECLARATIONS.

  Module Type DECLARATION_REWRITINGS_TYPE.
    Import DECLARATIONS.
    Import METHODSPEC_PLUS.

    (**
      varDecl mods t name
      Declaration of a local variable /name/ of type /t/ with modifiers /mods/.
      Opposed to all other kind of declarations, variable declarations are 
      implicitly declared as nullable unless an explicit non_null modifier is given.
      (JML RM 6.2.12)
      Allowed modifiers are: final, ghost, non_null, nullable, uninitialized
     *)
    Parameter varDecl   : list Modifier -> StaticType -> VarName -> Var.

    (**
      paramDecl mods t name
      Declaration of a formal parameter /name/ of type /t/ with modifiers /mods/.
      Allowed modifiers are: final, non_null, nullable
     *)
    Parameter paramDecl : list Modifier -> StaticType -> ParamName -> Param.
  
    (**
      fieldDecl ek mods t name
      Declaration of a field /name/ of type /t/ with modifiers /mods/ 
      within a class (ek=ClassEK) or an interface (ek=InterfaceEK).
      Allowed modifiers are: public, protected, private, final, static
                             spec_public, spec_protected, non_null, nullable, instance, monitored
     *)
    Parameter fieldDecl : TypeDefKind -> list Modifier -> StaticType -> ShortFieldName -> 
	option Expression -> list DATA_GROUP.t -> Field.

    (**
      modelFieldDecl ek mods t name
      Declaration of a field /name/ of type /t/ with modifiers /mods/ 
      within a class (ek=ClassEK) or an interface (ek=InterfaceEK).
      Allowed modifiers are: public, protected, private, static
                             non_null, nullable, instance
     *)
    Parameter modelFieldDecl : TypeDefKind -> list Modifier -> StaticType -> ShortModelFieldName -> 
	list DATA_GROUP.t -> ModelField.

    (**
      methodSpecDecl red mods sct generic-spec-case
      Declaration of a method specification case from a given /generic-spec-case/,
      of a given type (sct=lightweight, normal_behaviour, exceptional_behaviour, behaviour),
      with modifiers and redundant or non-redundant (red).
      
      Allowed modifiers are: public, protected, private, code
     
        e.g. methodSpecDecl false [private] lightweight generic-spec-case.
     *)
    Parameter methodSpecDecl : bool (* isRedundant *) -> list Modifier -> SpecCaseType 
      -> GENERIC_SPEC_CASE.t -> FULL_SPEC_CASE.t.

    (**
      m = methodDecl ek mk scs super mods result name params exceptions body
      
      Declaration of a method (or constructor, initializer or static initializer).
      @param ek    declaration either within a class (ek=ClassEK) or an interface (ek=InterfaceEK)
      @param mk    Default, Constructor or Initializer
      @param scs   list of specification cases (see methodSpecDecl)
      @param super None if /m/ is statically bound or Some m', if m overrides method m'
      @param excs  list of exceptions (see ExceptionType)
      @param body  None if /m/ is an abstract method or Some b, if m has body b
     
      Allowed modifiers: public, protected, private, abstract, final, static, native
                         spec_public, spec_protected, pure, non_null, nullable, helper
     
        e.g. methodDecl ClassEK Constructor scs None [public, pure] (PrimitiveType INT) name params excs body
     *)
    Parameter methodDecl : TypeDefKind -> MethodKind -> list FULL_SPEC_CASE.t -> option MethodSignature (* super *)
                           -> list Modifier 
                           -> ReturnType -> ShortMethodName -> list Param -> list ExceptionType (* throws *)
                           -> option BLOCK.t
                           -> Method.

    (**
      classDecl mods name ext impls fields modelFields methods typeSpecs
      
      Declaration of a class /name/ extending class /ext/ and implementing interfaces /impls/.
      Note that classDecl performs the type-level rewriting (rewriteTypeDef).
     
      Allowed modifiers: public, final, abstract, pure, nullable_by_default spec_public, spec_protected
      Note that pure and nullable_by_default are ignored and must thus be handled in the frontend.
     
      @see rewriteTypeDef
     *)
    Parameter classDecl : list Modifier -> ClassName -> Extends (* super *)
	-> list Implements (* implements/implements_weakly *) 
        -> list Field -> list ModelField -> list Method -> TypeSpec -> Class.

    (**
      interfaceDecl mods name impls fields modelFields methods typeSpecs
      Declaration of an interface
      @see classDecl
     *)
    Parameter interfaceDecl : list Modifier -> InterfaceName
	-> list Implements (* implements/implements_weakly *) 
        -> list Field -> list ModelField -> list Method -> TypeSpec -> Interface.

    (** 
      loopAnnotationDecl lbl annos
      Declaration of loop annotations /annos/ (list of invariants and variants) for the loop with label /lbl/.
      This declaration function performs the rewriting of variants as invariants (thus the necessity of the label).
      Result field LOOP_ANNOTATION.expression is one single &&-conjoined expression built from all invariants 
      and rewritten variants.
      
      @see rewriteVariant
      @see LoopAnnotationTag (tag type for variants and invariants)
     *)
    Parameter loopAnnotationDecl : Label -> list (LoopAnnotationTag * Expression) -> LOOP_ANNOTATION.t.

    Import TYPESPEC.

    (**
      invariantDecl red ek mods pred
      Declaration of a (non-/)redundant invariant with predicate /pred/ within a class or interface (ek).
      Allowed modifiers: public, protected, private, static
     *)
    Parameter invariantDecl : bool -> TypeDefKind -> list Modifier -> Expression -> INVARIANT.t.

    (**
      constraintDecl red ek mods pred
      Declaration of a (non-/)redundant history constraint with predicate /pred/ within a class or interface (ek).
      Allowed modifiers: public, protected, private, static
     *)
    Parameter constraintDecl : bool -> TypeDefKind -> list Modifier -> Expression -> TYPESPEC.ConstrainedFor -> CONSTRAINT.t.

    (**
      representsDecl red ek mods model-field-expression repr-kind repr-expression
      Declaration of a (non-/)redundant represents declaration within a class or interface (ek).
      Allowed modifiers: public, protected, private, static
     
      Represents clauses come in two forms, either as a functional or relational abstraction.
        e.g. representsDecl false of_class [private] modelField1 <- field1 (functional)
             representsDecl false of_class [private] modelField1 \such_that p(modelField1, field1) (relational)
        (both examples use notations from JMLNotations)
     *)
    Parameter representsDecl : bool -> TypeDefKind -> list Modifier -> Expression -> RepresentsKind -> Expression -> REPRESENTS.t.

    (**
      initiallyDecl ek mods pred
      Declaration of an initially clause.
      Every non-helper constructor of the enclosing type (class or interface, ek) 
      must establish the given /pred/.
      Allowed modifiers: public, protected, private
     *)
    Parameter initiallyDecl : TypeDefKind -> list Modifier -> Expression -> INITIALLY.t.
   
    (**
      axiomDecl pred
      Declaration of an axiom
     *)
    Parameter axiomDecl : Expression -> AXIOM.t.
  
    (**
      readableIfDecl ek mods field pred
      Declaration of a "readable field if pred" clause.
      Field /field/ is readable only if the given predicate /pred/ holds.
      Allowed modifiers: public, protected, private
     *)
    Parameter readableIfDecl : TypeDefKind -> list Modifier -> FieldSignature -> Expression -> READABLE_IF.t.

    (**
      writableIfDecl ek mods field pred
      Declaration of a "writable field if pred" clause.
      Field /field/ is writable only if the given predicate /pred/ holds.
      Allowed modifiers: public, protected, private
     *)
    Parameter writableIfDecl : TypeDefKind -> list Modifier -> FieldSignature -> Expression -> WRITABLE_IF.t.

    (**
      monitorsForDecl ek mods field exprs
      Declaration a monitors_for declaration.
      All expressions in /exprs/ must be locked in order to read /field/.
     *)
    Parameter monitorsForDecl : TypeDefKind -> list Modifier -> FieldSignature -> list Expression -> MONITORS_FOR.t.

  End DECLARATION_REWRITINGS_TYPE.

End FULL2BASIC.
