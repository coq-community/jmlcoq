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

Require Import Prelude.
Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import TaggedList.
Require Import ListHelpers.
Require Import ListFunctions.
Require Import OptionHelpers.

Require Import JMLProgramPlusImpl.
Require Import JMLFull2Basic.

Module FULL2BASIC_P := FULL2BASIC P.
Import FULL2BASIC_P.

Require Import JMLExpressionNotations.
Module EXPRESSION_NOTATIONS_P := EXPRESSION_NOTATIONS P.Program.
Import EXPRESSION_NOTATIONS_P.

(**
  Implementation of the different rewritings/desugarings 
  specified in the FULL2BASIC module.
 *)

  Module METHODSPEC_REWRITINGS <: METHODSPEC_REWRITINGS_TYPE.
    Export METHODSPEC_PLUS.

    (** Explicit conversion from optional to optionalSame *)
    Definition optional2optionalSame (A:Type) (o:optional A) : optionalSame A :=
      match o with
      | NotSpecified => NotSpecifiedOS
      | Specified x  => SpecifiedOS x
      end.
    Implicit Arguments optional2optionalSame [A].

    (** Implicit conversion from optional to optionalSame *)
    Coercion optional2optionalSame : optional >-> optionalSame.

    (** Lift a basic binary operation into the "optional world" *)
    Definition liftOptional2 (A:Type) (op:A->A->A) (oa ob:optional A) :  optional A :=
      match oa, ob with
      | Specified a,  Specified b => Specified (op a b)
      | NotSpecified, b => b
      | a, NotSpecified => a
      end.
    Implicit Arguments liftOptional2 [A].

    (** Lift a basic unary operation into the "optional world" *)
    Definition liftOptional1 (A B:Type) (op:A->B) (oa:optional A) : optional B :=
     match oa with
      | Specified a  => Specified (op a)
      | NotSpecified => NotSpecified
      end.
    Implicit Arguments liftOptional1 [A B].

    (**
      addHeaders sc reqs
      Adds the given list of requires clauses reqs to sc.
      See TR 00-03e, Appendix A
     *)
    Definition addHeaders (specs:FULL_SPEC_CASE.t) (reqs:list SpecHeader) : FULL_SPEC_CASE.t :=
      let (sct,v,r,cc,case) := specs in
      FULL_SPEC_CASE.Build_t sct v r cc
	(GENERIC_SPEC_CASE.Build_t nil nil reqs (inr _ (case::nil))).

    (** Is the given method specification clause a signals or signals_only clause? *)
    Definition isSignalsClause (clause:MethodSpecClause) : bool :=
      match clause with
      | signalsC _ _ => true
      | signalsOnlyC _ _ => true
      | _ => false
      end.

    (** Is the given method specification clause an ensures clause? *)
    Definition isEnsuresClause (clause:MethodSpecClause) : bool :=
      match clause with
      | ensuresC _ _ => true
      | _ => false
      end.

    (**
      clausesMap f case
      Helper function that recursively maps function f over all simple-spec-bodies
      (simple-spec-body-clause lists) of the given /case/.
     *)
    Fixpoint clausesMap (f : list MethodSpecClause -> list MethodSpecClause) (case : GENERIC_SPEC_CASE.t) 
        : GENERIC_SPEC_CASE.t :=
      let (fvd,ovd,sh,body) := case in
      match body with
      | inl clauses => GENERIC_SPEC_CASE.Build_t fvd ovd sh (inl _ (f clauses))
      | inr nested0  => 
          let nested1 := map (clausesMap f) nested0 in 
          GENERIC_SPEC_CASE.Build_t fvd ovd sh (inr _ nested1)
      end.

    (**
      addBody sc cl
      Adds the given method spec clause /cl/ to every simple body in the given spec case /spec/.
      Clause /cl/ is not added if 
       - cl is an ensures clause and sc is an exceptional_behaviour case or
       - cl is a signals/signals_only clause and sc is a normal_behaviour case
     *)
    Definition addBody (specs0:FULL_SPEC_CASE.t) (clause:MethodSpecClause) : FULL_SPEC_CASE.t :=
      let (sct,v,r,cc,case) := specs0 in
      let addClause (clauses:list MethodSpecClause) := (clause :: clauses) in 
      let specs1 := FULL_SPEC_CASE.Build_t sct v r cc (clausesMap addClause case) in
      match sct with
      | lightweight => specs1
      | behaviour   => specs1
      | normal_behaviour => 
          if isSignalsClause clause then specs0 else specs1
      | exceptional_behaviour =>
          if isEnsuresClause clause then specs0 else specs1
      end.
    
    (**
      Implementation of the tagged list infrastructure for lists of MethodSpecClause.
      This enables kind of heterogenous lists that allow to pull out all elements of the same clause type
      (= same tag).
      @see TaggedList
     *)
    Module TAG.
      (** MethodSpecClause is the data type *)
      Definition data := MethodSpecClause.

      (** ClauseTag is the tag type *)
      Definition tag := ClauseTag.

      (** Equality on tags must be decidable. *)
      Definition tag_eq_dec (x y:tag) : {x=y}+{x<>y}.
      Proof.
        case x; case y; (left; reflexivity) || (right; discriminate).
      Defined.

      (**
        t = tagOf cl
        ClauseTag t of a given clause /cl/.
       *)
      Definition tagOf (d:data) : tag :=
        match d with
        | ensuresC _ _       => ensuresT
        | signalsC _ _       => signalsT
        | signalsOnlyC _ _   => signalsOnlyT
        | divergesC _ _      => divergesT
        | whenC _ _          => whenT
        | assignableC _ _    => assignableT
        | accessibleC _ _    => accessibleT
        | callableC _ _      => callableT
        | measuredByC _ _    => measuredByT
        | capturesC _ _      => capturesT
        | workingSpaceC _ _  => workingSpaceT
        | durationC _ _      => durationT
      end.

      (**
        mapType t is the type of the data represented by a method spec clause of tag t.
        E.g. an ensures clause stores a predicate p of type optional Expression.
        Thus mapType ensuresT = optionalExpression.
       *)
      Definition mapType (t:tag) : Type :=
        match t with
        | ensuresT       => optional Expression
        | signalsT       => (Param * optional Expression)
        | signalsOnlyT   => list StaticType
        | divergesT      => optional Expression
        | whenT          => optional Expression
        | assignableT    => optional StoreRefList
        | accessibleT    => optional StoreRefList
        | callableT      => optional CallableList
        | measuredByT    => (optional Expression * option Expression)
        | capturesT      => optional StoreRefList
        | workingSpaceT  => (optional Expression * option Expression)
        | durationT      => (optional Expression * option Expression)
        end.

      (**
        basicClauseType t is the basic syntax data type corresponding to a a method spec clause of tag t.
        E.g. basicClauseType ensuresT = ENSURES.t
       *)
      Definition basicClauseType (t:tag) : Type :=
        match t with
        | ensuresT       => ENSURES.t
        | signalsT       => SIGNALS.t
        | signalsOnlyT   => SIGNALS_ONLY.t
        | divergesT      => DIVERGES.t
        | whenT          => WHEN.t
        | assignableT    => ASSIGNABLE.t
        | accessibleT    => ACCESSIBLE.t
        | callableT      => CALLABLE.t
        | measuredByT    => MEASURED_BY.t
        | capturesT      => CAPTURES.t
        | workingSpaceT  => WORKING_SPACE.t
        | durationT      => DURATION.t
        end.

      (**
        mkBasicClause t cl is the basic syntax type value corresponding to clause /cl/ of type (mapType t)
        E.g. mkBasicClause ensuresT cl is a value of type ENSURES.t corresponding to the ensures clause /cl/.
       *)
      Definition mkBasicClause : forall t:tag, mapType t -> basicClauseType t :=
        fun t0 cl =>
        match t0 as x return (t0 = x -> basicClauseType x) with
        | ensuresT       => fun Heq => ENSURES.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl ensuresT Heq in H)
        | signalsT       => fun Heq => SIGNALS.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl signalsT Heq in snd H)
        | signalsOnlyT   => fun Heq => SIGNALS_ONLY.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl signalsOnlyT Heq in H)
        | divergesT      => fun Heq => DIVERGES.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl divergesT Heq in H)
        | whenT          => fun Heq => WHEN.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl whenT Heq in H)
        | assignableT    => fun Heq => ASSIGNABLE.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl assignableT Heq in H)
        | accessibleT    => fun Heq => ACCESSIBLE.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl accessibleT Heq in H)
        | callableT      => fun Heq => CALLABLE.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl callableT Heq in H)
        | measuredByT    =>
            fun Heq => MEASURED_BY.Build_t 
              (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl measuredByT Heq in fst H)
              (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl measuredByT Heq in snd H)
        | capturesT      => fun Heq => CAPTURES.Build_t (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl capturesT Heq in H)
        | workingSpaceT  =>
            fun Heq => WORKING_SPACE.Build_t
              (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl workingSpaceT Heq in fst H)
              (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl workingSpaceT Heq in snd H)
        | durationT => 
            fun Heq => DURATION.Build_t
              (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl durationT Heq in fst H)
              (let H := eq_rect t0 (fun t1 : tag => mapType t1) cl durationT Heq in snd H)
        end (refl_equal t0).

      (** @see TaggedList.mapF *)
      Definition mapF : forall t:tag, {d:data | t=tagOf d} -> mapType t.
      Proof.
        intros t0 (d,H).
        destruct t0; destruct d as [r v | r v | r v | r v | r v | r v | r v | r v | r v | r v | r v | r v ];
        (exact v || discriminate H).
      Defined.

      (** @see TaggedList.filterTag *)
      Definition filterTag := filterTag tag tag_eq_dec data tagOf.

      (** @see TaggedList.mapData2Type *)
      Definition mapData2Type := mapData2Type tag data tagOf mapType mapF.

      (** @see TaggedList.filterTagData *)
      Definition filterTagData := filterTagData tag data tagOf.

      (** @see TaggedList.mapTag *)
      Definition mapTag := mapTag tag data tagOf.
    End TAG.

    (** Is the given spec clause redundant? *)
    Definition methodSpecClauseRedundant (c:MethodSpecClause) : bool :=
      match c with
      | ensuresC r _       
      | signalsC r _       
      | signalsOnlyC r _   
      | divergesC r _      
      | whenC r _          
      | assignableC r _    
      | accessibleC r _    
      | callableC r _      
      | measuredByC r   _  
      | capturesC r _      
      | workingSpaceC r _  
      | durationC r _      => r
      end.

    (**
      extractClauses t r l
      Extract either redundant or non-redundant method spec clauses of the given type tag
      from a list of (heterogeneous) method spec clauses.
      E.g. extractClauses ensuresT false extracts all non-redundant ensures clauses from /l/.
      The result is of type list (mapType ensuresT) = list (optional Expression).
     *)
    Definition extractClauses (t:TAG.tag) (redundant:bool) (l:list TAG.data) : list (TAG.mapType t) :=
      let lFiltered1 := TAG.filterTag t l in
      let lFiltered2 := TAG.filterTagData t (fun c => eqb (methodSpecClauseRedundant c) redundant) lFiltered1 in
      TAG.mapData2Type t lFiltered2.

    (** Is the given type a reference type? *)
    Definition isReferenceType (typ:StaticType) : bool :=
      match typ with
      | ReferenceType _ => true
      | PrimitiveType _ => false
      end.

    (**
      paramNonNullRequires p
      non_null parameter /p/ of reference type -> [param p != null]
      otherwise -> nil
     *)
    Definition paramNonNullRequires (p:Param) : list SpecHeader :=
      if PARAM.isNullable p || negb (isReferenceType (PARAMSIGNATURE.type (PARAM.signature p)))
        then nil
        else requiresSH false (: param p != null :)%jml :: nil.

    (**
      paramsNonNullRequires params
      Each non_null parameter p (of reference type) in /params/ 
      creates a requires clause that is appended to the result list.
      @see paramNonNullRequires
     *)
    Definition paramsNonNullRequires (params:list Param) : list SpecHeader :=
      flat_map paramNonNullRequires params.

    (**
      Desugaring 3.1 of TR 00-03e: Desugaring Non_Null for Arguments.
      
      desugarNonNullArguments scs m
      For every non_null parameter p (of reference type) of method m,
      an additinal requires clause (p != null) is added to every spec case in /scs/.
      If there were no specs in /scs/, the additional clauses are added as a lightweight spec case.
     *)
    Definition desugarNonNullArguments (specs: list FULL_SPEC_CASE.t) (m:METHOD.t) : list FULL_SPEC_CASE.t :=
      let reqs := paramsNonNullRequires (METHODSIGNATURE.parameters (METHOD.signature m)) in
      let defaultCase := GENERIC_SPEC_CASE.Build_t nil nil reqs (inl _ nil) in
      let defaultSpecs := FULL_SPEC_CASE.Build_t lightweight None false false defaultCase in

      match reqs, specs with
      | nil,  _ => specs 
      | _, nil  => defaultSpecs :: nil
      | _, _    => map (fun s => addHeaders s reqs) specs
      end.

    (**
      resultNonNullEnsures m
      m non_null -> [\result != null]
      m nullable -> nil
     *)
    Definition resultNonNullEnsures (m:Method) : option MethodSpecClause :=
      if METHOD.isNullable m
        then None
        else 
	  match METHODSIGNATURE.result (METHOD.signature m) with
	  | Some (ReferenceType _) => Some (ensuresC false (: \result != null :)%jml)
	  | Some (PrimitiveType _) => None
          | None => None
	  end.

    (**
      Desugaring 3.2 of TR 00-03e: Desugaring Non_Null Results.
      
      desugarNonNullResults scs m
      If method /m/ is non_null, an additinal ensures clause (\result != null) is recursively added (addBody) to 
      every spec case in /scs/.
      If there were no specs in /scs/, the additional clause is added as a lightweight spec case.
     
      @see addBody
     *)
    Definition desugarNonNullResult (specs:list FULL_SPEC_CASE.t) (m:METHOD.t) : list FULL_SPEC_CASE.t :=
      let ens := resultNonNullEnsures m in

      let defaultCase ens'  := GENERIC_SPEC_CASE.Build_t nil nil nil (inl _ (ens'::nil)) in
      let defaultSpecs ens' := FULL_SPEC_CASE.Build_t lightweight None false false (defaultCase ens') in
          
      match ens, specs with
      | None, _ => specs (* 1 *)
      | Some ens', nil => defaultSpecs ens' :: nil
      | Some ens', _   => map (fun s => addBody s ens') specs
      end.

    (** 
      Desugaring 3.3 of TR 00-03e: Desugaring Pure.
     
      desugarPure scs m
      Updates the given specification with
        - diverges false; assignable this.*; if the method is a constructor
        - diverges false; assignable \nothing; otherwise
      if the method is pure, otherwise leaves the specs intact.
      If there were no specs in /scs/, the clauses are addes as a lightweight spec case.
     *)
    Definition desugarPure (specs:list FULL_SPEC_CASE.t) (m:METHOD.t) : list FULL_SPEC_CASE.t :=
      let addBody2 clause1 clause2 spec := addBody (addBody spec clause1) clause2 in
      let div := divergesC false (: false' :)%jml in
      let ass := 
        match METHOD.kind m with
        | Constructor => assignableC false (: StoreRefs [AllFieldsRef ThisRef] :)%jml
        | _           => assignableC false (: \nothing :)%jml
        end in 

      let defaultCase  := GENERIC_SPEC_CASE.Build_t nil nil nil (inl _ (div :: ass :: nil)) in
      let defaultSpecs := FULL_SPEC_CASE.Build_t lightweight None false false defaultCase in

      match METHOD.isPure m, specs with
      | false, _ => specs
      | true, nil => defaultSpecs :: nil
      | true, _ => map (addBody2 ass div) specs
      end.

    (**
      Is the given list of specification cases empty?
      A list of specification cases is considered empty if it contains no 
      non-redundant specification case.
     
      @see Section 3.4 of TR 00-03e
     *)
    Fixpoint isEmptySpecification (specs:list FULL_SPEC_CASE.t) : bool :=
      match specs with
      | nil   => true
      | s::ss => if FULL_SPEC_CASE.isRedundant s then (isEmptySpecification ss) else false
      end.

    (* Require Import ListSet. *)
    (* Print Module ListSet. *)

    (**
      (assignableList case) is the list of concatenated assignable expressions  
      of the given generic spec /case/.
     *)
    Fixpoint assignableList (case:GENERIC_SPEC_CASE.t) : list (optional StoreRefList) :=
      match GENERIC_SPEC_CASE.genericBody case with
      | inl simpleBody => extractClauses assignableT false simpleBody
      | inr nested => concat (map assignableList nested)
      end.

    (**
      Concatenate two lists of locations.
      If either list is [\nothing], the result is the other list.
      If a list is [\everything], the result is [\everything]
      Otherwise the result is the normal concatenation of the two lists.
     *)
    Definition appLocations (l1 l2:StoreRefList) : StoreRefList :=
      match l1, l2 with
      | Nothing, _  | _, Everything  => l2
      | Everything, _ | _, Nothing   => l1
      | StoreRefs s1, StoreRefs s2 => StoreRefs (List.app s1 s2)
      end.

    (** Rewrites multiple assignable clauses as one assignable clause *)
    Definition mergeAssignable (l:list (optional StoreRefList)) : option (optional StoreRefList) :=
      match l with
      | nil => None
      | _   => Some (fold_left1 (liftOptional2 appLocations) l NotSpecified)
      end.

    (**
      assignableUnion scs is the union of all assignable expression lists of all
      non-redundant spec cases in /scs/.
     *)
    Definition assignableUnion (fullSpecs : list FULL_SPEC_CASE.t) : option (optional StoreRefList) :=
      let fullSpecsNR := filter (fun fs => negb (FULL_SPEC_CASE.isRedundant fs)) fullSpecs in
      let assignableLists := flat_map (fun fs => assignableList (FULL_SPEC_CASE.genericSpecCase fs)) fullSpecsNR in
      mergeAssignable assignableLists.

    (** 
      zeroArgCtor e
      zeroArgCtor = None, if e has no zero-argument default constructor, or
      zeroArgCtor = Some m, if m is the zero-argument default constructor of e.
     *)
    Definition zeroArgCtor (enc:TYPEDEF.t) : option METHOD.t :=
      let fix zeroArgCtorRec (l:list METHOD.t) : option METHOD.t :=
        match l with
        | m::ms => 
            match METHOD.kind m, METHODSIGNATURE.parameters (METHOD.signature m) with
            | Constructor, nil => Some m (* ctor with zero args *)
            | _, _ => zeroArgCtorRec ms
            end
        | nil => None
        end in
      zeroArgCtorRec (TYPEDEF.methods enc).
      
    (** 
      implicitCtorDefaultSpecs e
      Default specification case for the implicit zero-argument default constructor.
      
      According to 3.4 of the TR 00-03e, the default specification case for 
      the implicit zero-argument default constructor is a lightweight specification case
      with a copy of the assignable clause of /e/'s parent class' default constructor.
     *)
    Definition implicitCtorDefaultSpecs (enc:TYPEDEF.t) : FULL_SPEC_CASE.t :=
      let parentCtor :=
        match TYPEDEF.superClass enc with
        | Some sup => zeroArgCtor sup
        | None => None
        end in 

      let parentSpecs := 
        match parentCtor with
        | Some ctor => METHOD.fullSpecs ctor
        | None => nil
        end in
 
      let clauses := 
        match assignableUnion parentSpecs with
        | Some ole => (assignableC false ole) :: nil
        | None => nil
        end in

      let case  := GENERIC_SPEC_CASE.Build_t nil nil nil (inl _ clauses) in
      FULL_SPEC_CASE.Build_t lightweight None false false case.

    (**
      Desugaring 3.4 of TR 00-03e: Desugaring Empty Specifications
     
      desugarEmptySpecification scs m e
      Default spec case for a method if none is present:
       implicit zero-argument ctor: (implicitCtorDefaultSpecs e)
       new method: LW-SC requires \not_specified
       override:   LW-SC also requires false
     *)
    Definition desugarEmptySpecification (specs:list FULL_SPEC_CASE.t) (m:METHOD.t) (enc:TYPEDEF.t) 
	: list FULL_SPEC_CASE.t :=

      let req := 
        match METHOD.override m with
        | None   => requiresSH false \not_specified%jml
        | Some _ => requiresSH false (: false' :)%jml
        end in

      let defaultCase  := GENERIC_SPEC_CASE.Build_t nil nil (req::nil) (inl _ nil) in
      let defaultSpecs := FULL_SPEC_CASE.Build_t lightweight None false false defaultCase in

      match METHOD.isImplicitDefaultConstructor m, isEmptySpecification specs with
      | true, _      => (implicitCtorDefaultSpecs enc) :: nil
      | false, true  => defaultSpecs :: nil
      | false, false => specs
      end.

    (** 
      flatten case
      Flattens the given nested specification /case/ as described in the RM.
      @see JML RM 9.6.5: Semantics of Nested Behavior Specification Cases
     *)
    Fixpoint flatten (case:GENERIC_SPEC_CASE.t) : list GENERIC_SPEC_CASE.t :=
      let (fvd, ovd, sh, genBody) := case in

      let addDecls (flattenedCase:GENERIC_SPEC_CASE.t) := 
        let (fvd1, ovd1, sh1, simpleBody1) := flattenedCase in
          GENERIC_SPEC_CASE.Build_t (List.app fvd fvd1) (List.app ovd ovd1) (List.app sh sh1) simpleBody1 in

      let fix flattenNested (l:list GENERIC_SPEC_CASE.t) : list GENERIC_SPEC_CASE.t :=
        match l with 
        | nil       => nil
        | (nb::nbs) => List.app (flatten nb) (flattenNested nbs)
        end in

      match genBody with
      | inl simpleBody => case :: nil
      | inr nested     => map addDecls (flattenNested nested) (* concat map flatten nested *)
      end.

    (**
      Desugaring 3.5 of TR 00-03e: Desugaring Nested Specifications
      desugarNested scs
      Applies the unnesting (flatten) to every specification case in /scs/.
     *)
    Definition desugarNested (specs:list FULL_SPEC_CASE.t) : list FULL_SPEC_CASE.t :=
      let desugar1 (spec:FULL_SPEC_CASE.t) : list FULL_SPEC_CASE.t :=
        let (sct,v,r,cc,case) := spec in
        map (FULL_SPEC_CASE.Build_t sct v r cc) (flatten case) in
      flat_map desugar1 specs.

    (** Select all checked exceptions from a list of exceptions *)
    Fixpoint filterCheckedExceptions (l: list ExceptionType) : list StaticType :=
      match l with
      | nil  => nil
      | (RuntimeExceptionET t)::ll => t :: filterCheckedExceptions ll
      | (ExceptionET t)::ll        => t :: filterCheckedExceptions ll
      | _::ll => filterCheckedExceptions ll
      end.

    (**
      lightweightDefaults sc m
      Generates a FullSpecCaseDefaults record value representing the default clause values
      for a lightweight specification case.
      Method /m/ is needed to determine the defaults for the signals_only clause.
     
      @see JML RM Section 9: Method Specifications for the different default values
     *)
    Definition lightweightDefaults (spec:FULL_SPEC_CASE.t) (this:METHOD.t) : FullSpecCaseDefaults :=
      let headerDefault := requiresSH false NotSpecified in (* requires default *)
      let bodyDefault (t0:TAG.tag) : MethodSpecClause :=
        match t0 with
        | ensuresT => ensuresC false (NotSpecified:optional Expression)
        | signalsT => signalsC false (Exception_e, NotSpecified)
        | signalsOnlyT => signalsOnlyC false (filterCheckedExceptions (METHOD.throws this))
        | divergesT    => divergesC false (: false' :)%jml
        | whenT        => whenC false NotSpecified
        | assignableT  => assignableC false NotSpecified
        | accessibleT  => accessibleC false NotSpecified
        | callableT    => callableC false NotSpecified
        | measuredByT  => measuredByC false (NotSpecified, None)
        | capturesT    => capturesC false NotSpecified
        | workingSpaceT => workingSpaceC false (NotSpecified, None)
        | durationT     => durationC false (NotSpecified, None)
        end in
      Build_FullSpecCaseDefaults headerDefault bodyDefault.

    (**
      heavyweightDefaults sc m
      Generates a FullSpecCaseDefaults record value representing the default clause values
      for a heavyweight specification case.
      Method /m/ is needed to determine the defaults for the signals_only clause.
     
      @see JML RM Section 9: Method Specifications for the different default values
     *)
    Definition heavyweightDefaults (spec:FULL_SPEC_CASE.t) (this:METHOD.t) : FullSpecCaseDefaults :=
      let codeContract := FULL_SPEC_CASE.isCodeContract spec in
      let headerDefault := requiresSH false (: true' :)%jml in (* requires default *)
      let bodyDefault (t0:TAG.tag) :=
        match t0 with
        | ensuresT => ensuresC false (: true' :)%jml
        | signalsT => signalsC false (Exception_e, (: true' :)%jml)
        | signalsOnlyT => signalsOnlyC false (filterCheckedExceptions (METHOD.throws this))
        | divergesT    => divergesC false (: false' :)%jml
        | whenT        => whenC false (: true' :)%jml
        | assignableT  => assignableC false (: \everything :)%jml
        | accessibleT  => accessibleC false (if codeContract then (: \everything :)%jml else NotSpecified)
        | callableT    => callableC false   (if codeContract then (: METHODSPEC.EveryMethod :)%jml else NotSpecified)
        | measuredByT  => measuredByC false (NotSpecified, None)
        | capturesT    => capturesC false (: \everything :)%jml
        | workingSpaceT => workingSpaceC false (NotSpecified, None)
        | durationT     => durationC false (NotSpecified, None)
        end in
      Build_FullSpecCaseDefaults headerDefault bodyDefault.

    (** 
      addDefaults sc m defaults
      Helper function that adds default clauses from /defaults/ to sc for every kind of clause that
      is missing in sc.
      Valid only on flattened specification cases (after desugaring step 3.5).
     *)
    Definition addDefaults (spec0:FULL_SPEC_CASE.t) (m:METHOD.t) (defaults:FullSpecCaseDefaults) : FULL_SPEC_CASE.t :=    
      let (sct,v,r,cc,case0) := spec0 in
      let (fvd,ovd,sh0,body) := case0 in

      let clauses0 := 
        match body with
        | inl cls => cls
        | inr _ => nil (* error *)
        end in

      let addDefault (tag:ClauseTag) (clauses:list MethodSpecClause) : list MethodSpecClause :=
        match TAG.filterTag tag clauses with
        | nil => (bodyDefault defaults tag) :: clauses
        | _   => clauses
        end in 

      let sh1 := match sh0 with nil => (headerDefault defaults) :: nil | _ => sh0 end in
      let clauses1 := addDefault durationT clauses0 in
      let clauses2 := addDefault workingSpaceT clauses1 in
      let clauses3 := addDefault capturesT clauses2 in
      let clauses4 := addDefault measuredByT clauses3 in
      let clauses5 := addDefault callableT clauses4 in
      let clauses6 := addDefault accessibleT clauses5 in
      let clauses7 := addDefault assignableT clauses6 in
      let clauses8 := addDefault whenT clauses7 in
      let clauses9 := addDefault divergesT clauses8 in
      let clauses10 := addDefault signalsOnlyT clauses9 in
      let clauses11 := addDefault signalsT clauses10 in
      let clauses12 := addDefault ensuresT clauses11 in

      FULL_SPEC_CASE.Build_t sct v r cc (GENERIC_SPEC_CASE.Build_t fvd ovd sh1 (inl _ clauses12)).

    (** 
      Desugaring 3.6 of TR 00-03e: Desugaring Lightweight, Normal, and Exceptional Specifications
      This desugaring depends on desugaring 3.5 (see addDefaults).
     
      desugarBehaviour scs m
        for all spec case types:
          - sets the spec case type to behaviour
     
        for a lightweight specification case:
          - set the visibility of the spec case to the visibility of m
          - adds the defaults for omitted clause types
     
        for a heavyweight specification case:
          - sets the visibilty to package visibilty if omitted
     
        for a normal_behaviour specification case:
          - adds a signals clause (signals Exception false)
     
        for an exceptional_behaviour specification case:
          - adds an ensures clause (ensures false)
     *)
    Definition desugarBehaviour (specs:list FULL_SPEC_CASE.t) (m:METHOD.t) : list FULL_SPEC_CASE.t :=
      let setSpecCaseType (spec:FULL_SPEC_CASE.t) (sct:SpecCaseType) : FULL_SPEC_CASE.t :=
        let (_,v,r,cc,case) := spec in FULL_SPEC_CASE.Build_t sct v r cc case in
      
      let setVisibility (spec:FULL_SPEC_CASE.t) (vo:option Visibility) : FULL_SPEC_CASE.t :=
        let (sct,_,r,cc,case) := spec in FULL_SPEC_CASE.Build_t sct vo r cc case in

      let desugar1 (spec0:FULL_SPEC_CASE.t) : FULL_SPEC_CASE.t :=
	let vis := 
	  match FULL_SPEC_CASE.visibility spec0, FULL_SPEC_CASE.specCaseType spec0 with
	  | Some v', _        => v' (* case only possible for heavyweight case *)
	  | None, lightweight => METHOD.visibility m
	  | None, _           => Package (* default visibility for heavyweight case *)
	  end in

        match FULL_SPEC_CASE.specCaseType spec0 with
        | lightweight =>
            let spec1 := setSpecCaseType spec0 behaviour in
            let spec2 := setVisibility spec1 (Some vis) in 
            let spec3 := addDefaults spec2 m (lightweightDefaults spec2 m) in
            spec3
        | normal_behaviour => 
            let spec1 := setSpecCaseType spec0 behaviour in
	    let spec2 := setVisibility spec1 (Some vis) in 
            let spec3 := addBody spec2 (signalsC false (Exception_e, (: false' :)%jml)) in
            spec3
        | exceptional_behaviour =>
            let spec1 := setSpecCaseType spec0 behaviour in
	    let spec2 := setVisibility spec1 (Some vis) in 
            let spec2 := addBody spec2 (ensuresC false (: false' :)%jml) in
            spec2
        | behaviour => setVisibility spec0 (Some vis)
        end in
      map desugar1 specs.

    Module SIGNALS_SUBST.
      (** 
        bool equality between a parameter and an expression:
        Param_Expression_eqb p e = true iff e = (param q) and PARAM.eq_t p q
       *)      
      Definition Param_Expression_eqb p e : bool :=
        match e with
        | param q => PARAM.eq_t p q
        | _ => false
        end.

      (** 
        subst p t e
        Substitute expression /t/ for parameter p in e.
       
        @see PROGRAM_PLUS.expressionSubstitute (implementation)
       *)
      Definition subst p t e := expressionSubstitute (param p) (Param_Expression_eqb p) t e.
    End SIGNALS_SUBST.

    (** Is the given type equals to java.lang.Exception? *)
    Definition isExceptionType (typ:StaticType) : bool :=
      match typ with
      | ReferenceType rt =>
          match rt with
          | TypeDefType en _ => eq_TypeDefName en (java.lang.Exception_)
          | _ => false
          end
      | _ => false
      end.

    (**
      normaliseSignals cl
      Normalises the signals parameter and predicate of the given signals clause /cl/:
      signals (ET n) P ↝ signals (Exception e) (e instanceof ET) ==> [(ET)e / n] P
      If ET=Exception, the normalisation only normalised the signals variable name 
      to Exception_e_name.
     *)
    Definition normaliseSignals (data:{d:MethodSpecClause | signalsT = TAG.tagOf d}) : MethodSpecClause :=
      let (par, oexpr0) := TAG.mapF signalsT data in
      let paramType := PARAMSIGNATURE.type (PARAM.signature par) in
      let oexpr1 := 
        match oexpr0 with
        | NotSpecified => NotSpecified
        | Specified expr0 => 
            if isExceptionType paramType 
              then 
                let expr1 := SIGNALS_SUBST.subst par (param Exception_e) expr0 in
                Specified expr1
              else 
                let expr1 := SIGNALS_SUBST.subst par (Cast paramType (param Exception_e)) expr0 in
                let expr2 := (((param Exception_e) instanceof paramType) ==>' expr1)%jml in
                Specified expr2
        end in
      signalsC false (Exception_e, oexpr1).

    (** 
      Desugaring 3.8 of TR 00-03e: Standardizing Signals Clauses
      signals (ET n) P ↝ signals (Exception e) (e instanceof ET) ==> [(ET)e / n] P
     *)
    Definition desugarSignals : list FULL_SPEC_CASE.t -> list FULL_SPEC_CASE.t . (* (specs:list FULL_SPEC_CASE.t) : list FULL_SPEC_CASE.t := *)
    refine (fun specs => 
      let mapF (tag : ClauseTag) (data : {d:MethodSpecClause | tag = TAG.tagOf d}) := 
        let (d,P) := data in
        match tag as c return (tag = c -> MethodSpecClause) with
        | signalsT => fun P => normaliseSignals _
        | _ => fun _ => d
        end (refl_equal tag) in

      let desugar1 (spec:FULL_SPEC_CASE.t) : FULL_SPEC_CASE.t := 
        let (sct,v,r,cc,case) := spec in
        FULL_SPEC_CASE.Build_t sct v r cc (clausesMap (TAG.mapTag mapF) case) in

      map desugar1 specs).
    Proof.
      rewrite P0 in data.
      exact data.
    Defined.

    (** Merge a list of forall variable declarations into a single forall variable declaration. *)
    Definition mergeForallVarDecl (l:list FORALL_VAR_DECL.t) : option FORALL_VAR_DECL.t :=
      match l with
      | nil => None
      | _ => Some (FORALL_VAR_DECL.Build_t (flat_map FORALL_VAR_DECL.vars l))
      end.

    (** Merge a list of old variable declarations into a single old variable declaration. *)
    Definition mergeOldVarDecl (l:list OLD_VAR_DECL.t) : option OLD_VAR_DECL.t :=
      match l with
      | nil => None
      | _ => Some (OLD_VAR_DECL.Build_t (flat_map OLD_VAR_DECL.varDecls l))
      end.

    (**
      Merge multiple requires clauses into a single requires clause.
      requires P; requires Q ↝ requires P && Q
     
      Wf-predicate has to ensure that l consists of one single same clause or
          a list of Specified/NotSpecified clauses
     
      @see JML RM 9.9.2
     *)
    Definition mergeRequires (l0:list (optionalSame Expression)) :  option (optionalSame Expression) :=
      let liftOptionalSame2 (A:Type) (op:A->A->A) (oa ob:optionalSame A) :  optionalSame A :=
        match oa, ob with
        | SpecifiedOS a,  SpecifiedOS b => SpecifiedOS (op a b)
        | NotSpecifiedOS, b => b
        | a, NotSpecifiedOS => a
        | same, b => same
        | a, same => same
        end in

      match l0 with
      | nil => None
      | _   => Some (fold_left1 (liftOptionalSame2 Expression (BinaryCondBoolExpr ConditionalAnd)) l0 NotSpecifiedOS)
      end.

    (**
      Merge multiple ensures clauses into a single ensures clause.
      ensures P; ensures Q ↝ ensures P && Q
     
      @see JML RM 9.9.3
     *)
    Definition mergeEnsures (l:list (optional Expression)) : option (optional Expression) :=
      let optionalAnd := liftOptional2 (BinaryCondBoolExpr ConditionalAnd)  in
      match l with
      | nil => None
      | _   => Some (fold_left1 optionalAnd l NotSpecified)
      end.

    (**
      Merge multiple signals clauses into a single signals clause.
        signals (Exception e1) P1 ;
        signals (Exception e2) P2;
        ↝
        signals (Exception e3) P1 && P2;
     
      mergeSignals depends on desugarSignals to have standardised the signals type to (Exception).
      
      @see JML RM 9.9.4
     *)
    Definition mergeSignals (l0:list (Param * optional Expression)) : option (Param * optional Expression) :=
      let snd' := snd (A := Param) (B := optional Expression) in
      let l1 := map snd' l0 in
      match mergeEnsures l1 with
      | None => None
      | Some oe => Some (Exception_e, oe)
      end.

    (**
      mergeSignalsOnly l
      As noted in the JML RM, multiple signals_only clauses per specification case are not really sensible,
      so we do not support them.
      \nothing corresponds to the empty list nil.
     
      @see JML RM 9.9.5
     *)
    Definition mergeSignalsOnly (l:list (list StaticType)) : option (list StaticType) :=
      head l.

    (**
      Merge multiple diverges clauses into a single diverges clause.
      diverges P; diverges Q ↝ diverges P && Q
     
      @see JML RM 9.9.7
      The RM does not mention multiple diverges clauses, but this behaviour seems reasonable.
      The JML tools allow multiple diverges clauses, too.
     *)
    Definition mergeDiverges (l:list (optional Expression)) : option (optional Expression) := 
      mergeEnsures l.

    (**
      Merge multiple when clauses into a single when clause.
      when P; when Q ↝ when P && Q
      
      @see JML RM 9.9.8
      The RM does not mention multiple when clauses, but this behaviour seems reasonable.
     *)
    Definition mergeWhen (l:list (optional Expression)) : option (optional Expression) :=
      mergeEnsures l. 
 
    (** Merge multiple accessible clauses into a single accesible clause *)
    Definition mergeAccessible (l:list (optional StoreRefList)) : option (optional StoreRefList) :=
      match l with
      | nil => None
      | _   => Some (fold_left1 (liftOptional2 appLocations) l NotSpecified)
      end.

    (** Merge multiple callable clauses into a single callable clause. *)
    Definition mergeCallable (l:list (optional CallableList)) : option (optional CallableList) :=
      let merge2 (cl1 cl2:CallableList) : CallableList :=
        match cl1, cl2 with
        | METHODSPEC.EveryMethod, _ 
        | _, METHODSPEC.EveryMethod                => METHODSPEC.EveryMethod
        | METHODSPEC.These l1, METHODSPEC.These l2 => METHODSPEC.These (app l1 l2)
        end in
      match l with
      | nil => None
      | _   => Some (fold_left1 (liftOptional2 merge2) l NotSpecified)
      end.

    (**
      mergeMeasuredBy l.
      We do not allow multiple measured_by clauses.
     *)
    Definition mergeMeasuredBy (l:list (optional Expression * option Expression)) : option (optional Expression * option Expression) :=
      head l.

    (** Merge multiple captures clauses into a single captures clause. *)
    Definition mergeCaptures (l:list (optional StoreRefList)) : option (optional StoreRefList) :=
      match l with
      | nil => None
      | _   => Some (fold_left1 (liftOptional2 appLocations) l NotSpecified)
      end.

    (**
      Merge multiple working_space clauses into a single working_space clause.
      working_space DE WSE1 if W1
      working_space WSE2 if W2
      
      working_space Integer.min(W1 ? WSE1 : Integer.MAX_VALUE, W2 ? WSE2 : Integer.MAX_VALUE)
     
      @see TR 00-03e, section 3.9
     *)    
    Definition mergeWorkingSpace (l:list (optional Expression * option Expression)) : option (optional Expression * option Expression) := 
      let cond (ws:optional Expression * option Expression) : Expression :=
        match snd ws with
	| None   => true'%jml
	| Some c => c
        end in

      let rewrite1 (ws:optional Expression * option Expression) : optional Expression :=
	match fst ws with
	| NotSpecified   => NotSpecified
	| Specified expr => Specified ((cond ws) then' expr else' field java.lang.Integer.F_MAX_VALUE None)%jml
        end in

      let merge2 (e1:Expression) (e2:Expression) : Expression :=
        (method java.lang.Integer.M_min_5 None [e1; e2])%jml in

      let or := BinaryCondBoolExpr ConditionalOr in
      let exprs := fold_right1 (liftOptional2 merge2) (map rewrite1 l) NotSpecified in
      let conds := fold_left1 or (map cond l) true'%jml in

      match l with
      | nil     => None
      | ws::nil => Some ws
      | _       => Some (exprs, Some conds)
      end.

    (**
      Merge multiple duration clauses into a single duration clause.
      duration DE1 if D1
      duration D2 if D2
     
      duration Long.min(D1 ? DE1 : Long.MAX_VALUE, D2 ? DE2 : Long.MAX_VALUE)
      
      @see TR 00-03e, section 3.9
     *)
    Definition mergeDuration (l:list (optional Expression * option Expression)) : option (optional Expression * option Expression) := 
      let cond (ws:optional Expression * option Expression) : Expression :=
        match snd ws with
	| None   => true'%jml
	| Some c => c
        end in

      let rewrite1 (ws:optional Expression * option Expression) : optional Expression :=
	match fst ws with
	| NotSpecified   => NotSpecified
	| Specified expr => Specified ((cond ws) then' expr else' field java.lang.Long.F_MAX_VALUE None)%jml
        end in

      let merge2 (e1:Expression) (e2:Expression) : Expression :=
        (method java.lang.Long.M_min_5 None [e1; e2])%jml in

      let or := BinaryCondBoolExpr ConditionalOr in
      let exprs := fold_right1 (liftOptional2 merge2) (map rewrite1 l) NotSpecified in
      let conds := fold_left1 or (map cond l) true'%jml in

      match l with
      | nil     => None
      | ws::nil => Some ws
      | _       => Some (exprs, Some conds)
      end.

    (** Is the given specification header (requires clause) redundant? *)
    Definition specHeaderRedundant (r:SpecHeader) : bool :=
      let (redundant,_) := r in redundant.

    (** 
      Extract either all redundant or all non-redundant requires clauses from the given spec header.
      
      @see extractClauses (same function for simple-spec-body-clauses)
     *)
    Fixpoint extractRequires (redundant:bool) (l:list SpecHeader) {struct l} : list (optionalSame Expression) :=
      match l with
      | nil  => nil
      | (requiresSH r e)::rr => 
          if eqb r redundant
               then e :: extractRequires redundant rr
               else extractRequires redundant rr
      end.

    (** 
      Desugaring 3.9 of TR 00-03e: Desugaring Multiple Clauses of the Same Kind.
      Multiple clauses of the same kind (within the same simple-spec-body) are not allowed for 
      the signals_only and the measured_by clauses.
      
      desugarMultiple scs
      Recursively merges all clauses of the same kind within each simple-spec-body in
      every specification case in /scs/.
     
      See mergeX (X=Ensures, Signals, ...) for the individual merging functions.
     *)
    Definition desugarMultiple (specs:list FULL_SPEC_CASE.t) : list FULL_SPEC_CASE.t :=
      let desugar1Clauses (l:list MethodSpecClause) : list MethodSpecClause :=
        let ens := mergeEnsures     (extractClauses ensuresT false l) in
        let sig := mergeSignals     (extractClauses signalsT false l) in
        let sgo := mergeSignalsOnly (extractClauses signalsOnlyT false l) in
        let div := mergeDiverges    (extractClauses divergesT false l) in
        let whe := mergeWhen        (extractClauses whenT false l) in
        let ass := mergeAssignable  (extractClauses assignableT false l) in
        let acc := mergeAccessible  (extractClauses accessibleT false l) in
        let cal := mergeCallable    (extractClauses callableT false l) in
        let mea := mergeMeasuredBy  (extractClauses measuredByT false l) in
        let cap := mergeCaptures    (extractClauses capturesT false l) in
        let wor := mergeWorkingSpace (extractClauses workingSpaceT false l) in
        let dur := mergeDuration     (extractClauses durationT false l) in
  
        let rens := mergeEnsures     (extractClauses ensuresT true l) in
        let rsig := mergeSignals     (extractClauses signalsT true l) in
        let rsgo := mergeSignalsOnly (extractClauses signalsOnlyT true l) in
        let rdiv := mergeDiverges    (extractClauses divergesT true l) in
        let rwhe := mergeWhen        (extractClauses whenT true l) in
        let rass := mergeAssignable  (extractClauses assignableT true l) in
        let racc := mergeAccessible  (extractClauses accessibleT true l) in
        let rcal := mergeCallable    (extractClauses callableT true l) in
        let rmea := mergeMeasuredBy  (extractClauses measuredByT true l) in
        let rcap := mergeCaptures    (extractClauses capturesT true l) in
        let rwor := mergeWorkingSpace (extractClauses workingSpaceT true l) in
        let rdur := mergeDuration     (extractClauses durationT true l) in
  
        let optionClauses :=
  	optionMap (ensuresC false) ens ::
  	optionMap (signalsC false) sig ::
  	optionMap (signalsOnlyC false) sgo ::
  	optionMap (divergesC false) div ::
  	optionMap (whenC false) whe ::
  	optionMap (assignableC false) ass ::
  	optionMap (accessibleC false) acc ::
  	optionMap (callableC false) cal ::
  	optionMap (measuredByC false) mea ::
  	optionMap (capturesC false) cap ::
  	optionMap (workingSpaceC false) wor ::
  	optionMap (durationC false) dur ::
  
  	optionMap (ensuresC true) rens ::
  	optionMap (signalsC true) rsig ::
  	optionMap (signalsOnlyC true) rsgo ::
  	optionMap (divergesC true) rdiv ::
  	optionMap (whenC true) rwhe ::
  	optionMap (assignableC true) rass ::
  	optionMap (accessibleC true) racc ::
  	optionMap (callableC true) rcal ::
  	optionMap (measuredByC true) rmea ::
  	optionMap (capturesC true) rcap ::
  	optionMap (workingSpaceC true) rwor ::
  	optionMap (durationC true) rdur ::
  	nil in
        optionList2list optionClauses in      
  
      let fix desugar1Case (case:GENERIC_SPEC_CASE.t) : GENERIC_SPEC_CASE.t :=
        let (fvd0,ovd0,sh0,body0) := case in
        let fvd1 := option2list (mergeForallVarDecl fvd0) in 
  	let ovd1 := option2list (mergeOldVarDecl ovd0) in 
  	let sh0r  := extractRequires true sh0 in 
  	let sh0nr := extractRequires false sh0 in 
  	let sh1r  := optionMap (requiresSH true) (mergeRequires sh0r) in 
        let sh1nr := optionMap (requiresSH false) (mergeRequires sh0nr) in 
        let sh1   := optionList2list (sh1nr :: sh1r :: nil) in
  
        let body1 := 
          match body0 with
          | inl cl     => inl _ (desugar1Clauses cl)
          | inr nested => inr _ (map desugar1Case nested)
          end in
        GENERIC_SPEC_CASE.Build_t fvd1 ovd1 sh1 body1 in
  
      let desugar1 (spec:FULL_SPEC_CASE.t) : FULL_SPEC_CASE.t := 
        let (sct,v,r,cc,case) := spec in
        FULL_SPEC_CASE.Build_t sct v r cc (desugar1Case case) in
  
      map desugar1 specs.

    (** @see FULL2BASIC.desugarAll *)
    Definition desugarAll (specs0:list FULL_SPEC_CASE.t) (m:METHOD.t) (enc:TYPEDEF.t) : list FULL_SPEC_CASE.t := 
      let specs1 := desugarNonNullArguments specs0 m in
      let specs2 := desugarNonNullResult specs1 m in
      let specs3 := desugarPure specs2 m in
      let specs4 := desugarEmptySpecification specs3 m enc in
      let specs5 := desugarNested specs4 in
      let specs6 := desugarBehaviour specs5 m in
      let specs8 := desugarSignals specs6 in
      let specs9 := desugarMultiple specs8 in 
      specs9.

    (* Error default clause values used in the implementation of rewriteFullSpecification.
      In a correct implementation, these values are guaranteed not to appear in the
      result of rewriteFullSpecification.
     *)
    Parameter errorRequires : optionalSame Expression.
    Parameter errorEnsures : TAG.mapType ensuresT.
    Parameter errorSignals : TAG.mapType signalsT.
    Parameter errorSignalsOnly : TAG.mapType signalsOnlyT.
    Parameter errorDiverges : TAG.mapType divergesT.
    Parameter errorWhen : TAG.mapType whenT.
    Parameter errorAssignable : TAG.mapType assignableT.
    Parameter errorAccessible : TAG.mapType accessibleT.
    Parameter errorCallable : TAG.mapType callableT.
    Parameter errorMeasuredBy : TAG.mapType measuredByT.
    Parameter errorCaptures : TAG.mapType capturesT.
    Parameter errorWorkingSpace : TAG.mapType workingSpaceT.
    Parameter errorDuration : TAG.mapType durationT.

    (** 
      Explicit conversion from optionalSame to REQUIRES.t
     *)
    Definition optionalSame2Requires (os:optionalSame Expression) :=
      match os with
      | SpecifiedOS p  => REQUIRES.Build_t (Specified p) false
      | NotSpecifiedOS => REQUIRES.Build_t NotSpecified false
      | same           => REQUIRES.Build_t NotSpecified true
      end.

    (** Convenience definitions for \not_specified clause type values. *)
    Definition requiresNotSpecified := optionalSame2Requires NotSpecified.
    Definition ensuresNotSpecified := TAG.mkBasicClause ensuresT NotSpecified.
    Definition signalsNotSpecified := TAG.mkBasicClause signalsT (Exception_e, NotSpecified).
    Definition signalsOnlyNotSpecified := TAG.mkBasicClause signalsOnlyT nil.
    Definition divergesNotSpecified := TAG.mkBasicClause divergesT NotSpecified.
    Definition whenNotSpecified := TAG.mkBasicClause whenT NotSpecified.
    Definition assignableNotSpecified := TAG.mkBasicClause assignableT NotSpecified.
    Definition accessibleNotSpecified := TAG.mkBasicClause accessibleT NotSpecified.
    Definition callableNotSpecified := TAG.mkBasicClause callableT NotSpecified.
    Definition measuredByNotSpecified := TAG.mkBasicClause measuredByT (NotSpecified, None).
    Definition capturesNotSpecified := TAG.mkBasicClause capturesT NotSpecified.
    Definition workingSpaceNotSpecified := TAG.mkBasicClause workingSpaceT (NotSpecified, None).
    Definition durationNotSpecified := TAG.mkBasicClause durationT (NotSpecified, None).
    
    (**
      rewriteFullSpecs scs m e
      Performs all rewritings (desugarAll) on the list of spec cases scs and
      transforms the full syntax data type FULL_SPEC_CASE.t into the basic syntax type SpecificationCase.
      Note that TR 00-03e does not fill in default values for heavyweight cases in desugaring 3.6,
      so this is necessarily done here.
     *)
    Definition rewriteFullSpecification (specs0:list FULL_SPEC_CASE.t) (m:METHOD.t) (enc:TYPEDEF.t) : list SpecificationCase := 
      let specs1 := desugarAll specs0 m enc in
      let specs2 := map (fun spec => addDefaults spec m (heavyweightDefaults spec m)) specs1 in 

      let rewrite1 (spec:FULL_SPEC_CASE.t) : SpecificationCase :=
        let (sct,v,r,cc,case) := spec in
        let (fvd,ovd,sh,body) := case in
        let vis := match v with None => Public | Some v' => v' end in 
        let clauses := 
          match body with
          | inl cl => cl
          | inr _ => nil (* error *)
          end in 
        CASE.Build_t 
          vis
          (hd (FORALL_VAR_DECL.Build_t nil) fvd)
          (hd (OLD_VAR_DECL.Build_t nil) ovd)
          (optionalSame2Requires (hd errorRequires (extractRequires false sh)))
          (TAG.mkBasicClause ensuresT (hd errorEnsures (extractClauses ensuresT false clauses)))
          (TAG.mkBasicClause signalsT (hd errorSignals (extractClauses signalsT false clauses)))
          (TAG.mkBasicClause signalsOnlyT (hd errorSignalsOnly (extractClauses signalsOnlyT false clauses)))
          (TAG.mkBasicClause divergesT (hd errorDiverges (extractClauses divergesT false clauses)))
          (TAG.mkBasicClause whenT (hd errorWhen (extractClauses whenT false clauses)))
          (TAG.mkBasicClause assignableT (hd errorAssignable (extractClauses assignableT false clauses)))
          (TAG.mkBasicClause accessibleT (hd errorAccessible (extractClauses accessibleT false clauses)))
          (TAG.mkBasicClause callableT (hd errorCallable (extractClauses callableT false clauses)))
          (TAG.mkBasicClause measuredByT (hd errorMeasuredBy (extractClauses measuredByT false clauses)))
          (TAG.mkBasicClause capturesT (hd errorCaptures (extractClauses capturesT false clauses)))
          (TAG.mkBasicClause workingSpaceT (hd errorWorkingSpace (extractClauses workingSpaceT false clauses)))
          (TAG.mkBasicClause durationT (hd errorDuration (extractClauses durationT false clauses)))
	  (* redundant clauses *)
          (optionalSame2Requires (hd (NotSpecified:optionalSame Expression) (extractRequires true sh)))
          (TAG.mkBasicClause ensuresT (hd NotSpecified (extractClauses ensuresT true clauses)))
          (TAG.mkBasicClause signalsT (hd (Exception_e, NotSpecified) (extractClauses signalsT true clauses)))
          (TAG.mkBasicClause signalsOnlyT (hd nil (extractClauses signalsOnlyT true clauses)))
          (TAG.mkBasicClause divergesT (hd NotSpecified (extractClauses divergesT true clauses)))
          (TAG.mkBasicClause whenT (hd NotSpecified (extractClauses whenT true clauses)))
          (TAG.mkBasicClause assignableT (hd NotSpecified (extractClauses assignableT true clauses)))
          (TAG.mkBasicClause accessibleT (hd NotSpecified (extractClauses accessibleT true clauses)))
          (TAG.mkBasicClause callableT (hd NotSpecified (extractClauses callableT true clauses)))
          (TAG.mkBasicClause measuredByT (hd (NotSpecified, None) (extractClauses measuredByT true clauses)))
          (TAG.mkBasicClause capturesT (hd NotSpecified (extractClauses capturesT true clauses)))
          (TAG.mkBasicClause workingSpaceT (hd (NotSpecified, None) (extractClauses workingSpaceT true clauses)))
          (TAG.mkBasicClause durationT (hd (NotSpecified, None) (extractClauses durationT true clauses)))
          r cc in
      map rewrite1 specs2. 

  End METHODSPEC_REWRITINGS.
  Export METHODSPEC_REWRITINGS.

  Module TYPESPEC_REWRITINGS <: TYPESPEC_REWRITINGS_TYPE.
    Import TYPESPEC.

    (**
      fieldNonNullInvariant entityName f
      For the given field /f/ of visibilty v
      the result is an invariant (f != null) of visibility v 
      if f is of reference type and declared to be non_null.
     *)
    Definition fieldNonNullInvariant (entityName:ClassName) (f:Field) : option INVARIANT.t :=
      let target := if FIELD.isStatic f then None else Some (this%jml) in

      if FIELD.isNullable f || negb (isReferenceType (FIELDSIGNATURE.type (FIELD.signature f)))
        then None
        else let fExpr := field (entityName, (FIELD.signature f)) target in 
             Some (INVARIANT.Build_t (fExpr != null)%jml (FIELD.visibility f) (FIELD.isStatic f) false).

    (** @see fieldNonNullInvariant *)
    Definition fieldNonNullInvariants (entityName:ClassName) (l:list Field) : list TYPESPEC.INVARIANT.t :=
      optionList2list (map (fieldNonNullInvariant entityName) l).

    (**
      modelFieldNonNullInvariant entityName f
      For the given model field /f/ of visibility v,
      the result is an invariant (f != null) of visibility v if f is declared non_null.
     *)
    Definition modelFieldNonNullInvariant (entityName:ClassName) (f:ModelField) : option INVARIANT.t :=
      if MODELFIELD.isNullable f || negb (isReferenceType (FIELDSIGNATURE.type (MODELFIELD.signature f)))
        then None
        else let fExpr := field (entityName, (MODELFIELD.signature f)) None in 
             Some (INVARIANT.Build_t (fExpr != null)%jml (MODELFIELD.visibility f) (MODELFIELD.isStatic f) false).

    (** @see modelFieldNonNullInvariant *)
    Definition modelFieldNonNullInvariants (entityName:ClassName) (l:list ModelField) : list INVARIANT.t :=
      optionList2list (map (modelFieldNonNullInvariant entityName) l).

    (** @see FULL2BASIC.rewriteInvariants *)
    Definition rewriteInvariants (invs:list INVARIANT.t) (enc:TYPEDEF.t) : list INVARIANT.t :=
      let fieldInvs := fieldNonNullInvariants (TYPEDEF.name enc) (TYPEDEF.fields enc) in 
      let modelFieldInvs := modelFieldNonNullInvariants (TYPEDEF.name enc) (TYPEDEF.modelFields enc) in 
      invs +++ fieldInvs +++ modelFieldInvs.

    (**
      mergeInvariants invs
      Merge all invariants in /invs/ into a single &&-conjoined invariant.
      Note that visibility and static/instance modifiers are ignored.
      The result invariant is non-static and public.
     *)
    Definition mergeInvariants (invs:list INVARIANT.t) : INVARIANT.t :=
      let and := BinaryCondBoolExpr ConditionalAnd in
      let lPred := map INVARIANT.pred invs in 
      INVARIANT.Build_t (fold_right and true'%jml lPred) Public false false.

    (** @see FULL2BASIC.rewriteTypeSpecs *)
    Definition rewriteTypeSpecs (ts:TYPESPEC.t) (enc:TYPEDEF.t) : TYPESPEC.t :=
      let invs0 := TYPESPEC.invariant ts in
      let invs1 := rewriteInvariants invs0 enc in
      (* let invs1 := mergeInvariants invs0 in *)
      TYPESPEC.setInvariant ts invs1.

  End TYPESPEC_REWRITINGS.

  Module ALL_REWRITINGS <: ALL_REWRITINGS_TYPE.
    Import METHODSPEC_REWRITINGS.
    Import TYPESPEC_REWRITINGS.

    (** @see FULL2BASIC.rewriteMethod *)
    Definition rewriteMethod (m:Method) (enc:TYPEDEF.t) : Method := 
      let specs0 := rewriteFullSpecification (METHOD.fullSpecs m) m enc in
      METHOD.setSpecs m specs0.

    (** @see FULL2BASIC.rewriteTypeDef *)
    Definition rewriteTypeDef (e0:TYPEDEF.t) : TYPEDEF.t :=
      let ts1 := rewriteTypeSpecs (TYPEDEF.typeSpec e0) e0 in
      let methods1 := map (fun m => rewriteMethod m e0) (TYPEDEF.methods e0) in
      let e1 := TYPEDEF.setTypeSpec e0 ts1 in
      let e2 := TYPEDEF.setMethods e1 methods1 in
      e2.
    
  End ALL_REWRITINGS.
  Import ALL_REWRITINGS.

  Module EXPRESSION_REWRITINGS <: EXPRESSION_REWRITINGS_TYPE.
    Export FULL2BASIC_P.EXPRESSION_REWRITINGS.

    (** @see FULL2BASIC.rewriteVariant *)
    Definition rewriteVariant (lbl:Label) (e:Expression) : Expression :=
      let lit0 := literal (IntLiteral 0%Z) in
      ( (lit0 <= e) &&' (e < \oldl e at lbl) )%jml.

    (** @see rewriteFullQuantifier *)
    Fixpoint rewriteFullQuantifier_rec (q:Quantifier) (l:list Var) (range: Expression) (expr:Expression) {struct l} : Expression := 
      match l with 
      | nil      => false'%jml (* error *)
      | (v::nil) => Quantification q v range expr
      | (v::vs)  => Quantification q v (true')%jml (rewriteFullQuantifier_rec q vs range expr)
      end.

    (** @see FULL2BASIC.rewriteFullQuantifier *)
    Definition rewriteFullQuantifier (fq:FullQuantifier) : Expression := 
      let (q,l,range,expr) := fq in rewriteFullQuantifier_rec q l range expr.
  End EXPRESSION_REWRITINGS.
  Export EXPRESSION_REWRITINGS.

  Module DECLARATION_REWRITINGS <: DECLARATION_REWRITINGS_TYPE.
    Export DECLARATIONS. 

  Module LOOP_ANNOTATION_TAG.
      Definition tag : Set := LoopAnnotationTag.
      Definition data : Type := (tag * Expression).

      (** Equality on LoopAnnotationTag's is decidable. *)
      Definition tag_eq_dec (x y:tag) : {x=y}+{x<>y}.
      Proof.
        case x; case y; (left; reflexivity) || (right; discriminate).
      Defined.
  
      (** tagOf (t,expr) is t *)
      Definition tagOf (d:data) : tag := let (t,_) := d in t.
  
      (**
         filterTag t annos
        Filter all loop annotations in /annos/ with the given loop annotation tag /t/.
       *)
      Definition filterTag (t:tag) (l:list data) : list Expression := 
        let f := fun x => match x with exist (_,d) _ => d end in
        map f (filterTag tag tag_eq_dec data tagOf t l).
    End LOOP_ANNOTATION_TAG.

    (** bool equality on modifiers *)
    Definition eqb_Modifier (x y:Modifier) := 
      match x, y with
      | public, public => true
      | protected, protected => true
      | private, private => true
      | abstract, abstract => true
      | static, static     => true
      | final, final       => true
      | native, native	 => true
      | spec_public, spec_public       => true
      | spec_protected, spec_protected => true
      | model, model => true
      | ghost, ghost => true
      | pure, pure   => true
      | instance, instance => true
      | helper, helper => true
      | non_null, non_null => true
      | nullable, nullable => true
      | nullable_by_default, nullable_by_default => true
      | monitored, monitored         => true
      | uninitialized, uninitialized => true
      | code, code => true
      | implicit_constructor, implicit_constructor => true
      | _, _ => false
      end.
  
    (** 
      hasModifiers mods m
      Is the given modifier /m/ part of modifier list /mods/?
     *)
    Definition hasModifier (mods:list Modifier) (m:Modifier) : bool := existsb (eqb_Modifier m) mods.
  
    (** bool equality on TypeDefKind *)
    Definition eqb_TypeDefKind (x y:TypeDefKind) := 
      match x, y with 
      | ClassEK, ClassEK         => true
      | InterfaceEK, InterfaceEK => true
      | _, _ => false
      end.
  
    Open Scope bool_scope.
  
    (**
      javaVisibilityOption mods
      Extract a possibly present (Java) visibility modifier from a given 
      modifiers list /mods/.
      The result is undefined if /mods/ contains more then one visibility modifier.
     *)
    Fixpoint javaVisibilityOption (mods:list Modifier) : option Visibility := 
        match mods with
        | public::_    => Some Public
        | protected::_ => Some Protected
        | private::_   => Some Private
        | _::xs        => javaVisibilityOption xs
        | nil          => None
        end.
  
    (**
      javaVisibilty ek mods
      Java visibility is either the explicitly specificed visibility (in the modifier list /mods/)
      or defaults to package visibility within a class or public visibility within an interface.
     *)
    Definition javaVisibility (ek:TypeDefKind) (mods:list Modifier) : Visibility :=
      match javaVisibilityOption mods, ek with
      | Some v, _ => v
      | None, ClassEK     => Package
      | None, InterfaceEK => Public
      end.
  
    (**
      JML visibility dependent on modifiers and Java visibility:
         spec_public    `elem` mods => spec_public
         spec_protected `elem` mods => spec_protected
         otherwise                  => Java visibility
     *)
    Definition specVisibility (ek:TypeDefKind) (mods:list Modifier)  : Visibility := 
      let fix specVisibility' (mods':list Modifier) : option Visibility := 
        match mods' with
        | spec_public::_    => Some Spec_Public
        | spec_protected::_ => Some Spec_Protected
        | _::xs             => specVisibility' xs
        | nil               => None
        end in

      match (specVisibility' mods) with
      | Some v => v
      | None => javaVisibility ek mods
      end.

    (** Distinction between fields (FieldEK) and model fields (ModelFieldEK) *)
    Inductive FieldKind  : Set := FieldFK | ModelFieldFK.
  
    (** bool equality on FieldKind *)
    Definition eqb_FieldKind (x y:FieldKind) := 
      match x, y with 
      | FieldFK, FieldFK           => true
      | ModelFieldFK, ModelFieldFK => true
      | _, _ => false
      end.

    (**
      fieldModifierValue ek fk mods m
      Value of modifier /m/ within a field/model field declaration 
      based on entity kind, field kind and the given list of explicitly specified modifiers.
      Modifier m must be one of final, static, ghost, nullable or monitored
      
      Modifier m  | Condition for value true 
      --------------------------------------
      final       | m in mods or the declaration is a (non-ghost) field within an interface
      static      | m in mods or the declaration is within an interface and the instance modifier is not in mods
      ghost       | m in mods
      nullable    | m in mods
      monitored   | m in mods
     *)
    Definition fieldModifierValue (ek:TypeDefKind) (fk:FieldKind) (mods:list Modifier) (m:Modifier) : bool := 
      let m_present        := existsb (eqb_Modifier m) mods in
      let instance_present := existsb (eqb_Modifier instance) mods in 
      let ghost_present    := existsb (eqb_Modifier ghost) mods in
        match m with
          (* fields (not ghost, not model) in interfaces implicitly final, JLS 9.3, RM 6.2.5, RM 6.2.6 *)
        | final         => m_present || ((eqb_FieldKind fk FieldFK) && (eqb_TypeDefKind ek InterfaceEK) && (negb ghost_present))
          (* fields (+ghost, +model) in interfaces implicitly static, JLS 9.3, RM 6.2.5, RM 6.2.6 unless instance modifier present *)
        | static        => m_present || ((eqb_TypeDefKind ek InterfaceEK) && (negb instance_present))
        | ghost         => m_present
        | nullable      => m_present (* nullable_by_default handled by Java translation frontend *)
        | monitored     => m_present
        | _             => false (* error *)
        end.

    (** 
      typeSpec_isStatic ek mods
      Value of the static modifier within a type specification declaration:
      
      Modifier m  | Condition for value true 
      --------------------------------------
      static      | m in mods or the declaration is within an interface and the instance modifier is not in mods
     *)
    Definition typeSpec_isStatic (ek:TypeDefKind) (mods:list Modifier) : bool :=
      let static_present   := existsb (eqb_Modifier static) mods in
      let instance_present := existsb (eqb_Modifier instance) mods in
        static_present || ((eqb_TypeDefKind ek InterfaceEK) && (negb instance_present)).
 
    (** @see FULL2BASIC.methodSpecDecl *)
    Definition methodSpecDecl (redundant:bool) (mods:list Modifier) (sct:SpecCaseType) (case:GENERIC_SPEC_CASE.t) : FULL_SPEC_CASE.t :=
	FULL_SPEC_CASE.Build_t sct (javaVisibilityOption mods) redundant (hasModifier mods code) case.

    (** Explicit conversion from ReturnType to the isomorphic option type. *)
    Definition returnType2option (rt:ReturnType) : option StaticType := 
      match rt with
      | Void     => None
      | Return t => Some t
      end.

    (** @see FULL2BASIC.methodDecl *)
    Definition methodDecl (ek:TypeDefKind) (mk:MethodKind) (fullSpecs:list FULL_SPEC_CASE.t) (super:option MethodSignature) 
                            (mods:list Modifier) 
                            (rt:ReturnType) (name:ShortMethodName) (params:list Param) (throws:list ExceptionType)
                            (block:option BLOCK.t) : Method :=
      let signature  := METHODSIGNATURE.Build_t name params (returnType2option rt) in
      let body       := match block with (Some block') => Some (METHODBODY.Build_t block' nil) | _ => None end in

        METHOD.Build_t
          signature
          throws
	  body
          super
          mk (* MethodKind *)
          (hasModifier mods final) (* isFinal *)
          (hasModifier mods static) (* isStatic *)
          (hasModifier mods native) (* isNative *)
          (javaVisibility ek mods) (* visibility *)
          (specVisibility ek mods) (* spec visibility*)
          (hasModifier mods pure) (* isPure *)
          (hasModifier mods helper) (* isHelper *)
          (hasModifier mods nullable) (* isNullable *)
          (hasModifier mods implicit_constructor) (* is this the implicit zero-arg ctor? *)
          nil (* specs *)
          fullSpecs.

    (** @see FULL2BASIC.varDecl *)
    Definition varDecl (mods:list Modifier) (t:StaticType) (name:VarName) : Var := 
        VAR.Build_t
          (VARSIGNATURE.Build_t name t)
          (hasModifier mods final)
          (negb (hasModifier mods non_null))
          (hasModifier mods ghost)
          (hasModifier mods uninitialized).

    (** @see FULL2BASIC.paramDecl *)
    Definition paramDecl (mods:list Modifier) (t:StaticType) (name:ParamName) : Param := 
        PARAM.Build_t 
          (PARAMSIGNATURE.Build_t name t)
          (hasModifier mods final)
          (hasModifier mods nullable).

    (** @see FULL2BASIC.fieldDecl *)
    Definition fieldDecl (ek:TypeDefKind) (mods:list Modifier) (t:StaticType) (name:ShortFieldName) (val:option Expression) (data_groups:list DATA_GROUP.t): Field := 
      let concreteModifierValue := fieldModifierValue ek FieldFK mods in 
      let signature := FIELDSIGNATURE.Build_t name t in
        FIELD.Build_t 
          signature
          (concreteModifierValue final) (* isFinal *)
          (javaVisibility ek mods) (* visibility *)
          (specVisibility ek mods) (* specVisibility *)
          (concreteModifierValue static) (* isStatic *)
          (concreteModifierValue ghost) (* isGhost *)
          (concreteModifierValue nullable) (* isNullable *)
          (concreteModifierValue monitored) (* isMonitored *)
          val
          data_groups.

    (** @see FULL2BASIC.modelFieldDecl *)
    Definition modelFieldDecl (ek:TypeDefKind) (mods:list Modifier) (t:StaticType) (name:ShortModelFieldName)  (data_groups:list DATA_GROUP.t) : ModelField := 
      let concreteModifierValue := fieldModifierValue ek ModelFieldFK mods in 
      let signature := FIELDSIGNATURE.Build_t name t in
        MODELFIELD.Build_t 
          signature
          (javaVisibility ek mods) (* visibility *)
	  (concreteModifierValue static) (* isStatic *)
          (concreteModifierValue nullable) (* isNullable *)
          data_groups.

    (**
      implementsList impls
      Extract all non-weakly interfaces from the given list /impls/.
     *)
    Fixpoint implementsList (l:list Implements) : list Interface :=
      match l with
      | (implements i)::xs        => i :: (implementsList xs)
      | (implements_weakly _)::xs => (implementsList xs)
      | nil => nil
      end.

    (**
      implementsList impls
      Extract all weakly interfaces from the given list /impls/.
     *)
    Fixpoint weaklyImplementsList (l:list Implements) : list Interface :=
      match l with
      | (implements _)::xs        => (weaklyImplementsList xs)
      | (implements_weakly i)::xs => i :: (weaklyImplementsList xs)
      | nil => nil
      end.

    (** Helper function that unifies classDecl and interfaceDecl *)
    Definition typeDecl (isClass:bool) (mods:list Modifier) (name:ClassName) (ext:Extends)
                        (impls:list Implements)
                        (fields:list Field) (modelFields:list ModelField) (methods:list Method) (ts:TypeSpec) :=
      let (superClass, weaklyExtends) :=
        match ext with
        | extends name => (Some name, false)
        | extends_weakly name => (Some name, true)
	| no_extends => (None, true) (* weakly extends irrelevant in this case *)
        end in

      let type0 :=
        TYPEDEF.Build_t
          isClass
  	  name
	  (javaVisibility ClassEK mods)
          (specVisibility ClassEK mods)
          superClass
          weaklyExtends
          (implementsList impls)
          (weaklyImplementsList impls)
          fields
          modelFields
          methods
          (hasModifier mods final)
          (hasModifier mods abstract)
          ts in

      rewriteTypeDef type0.

    (** @see FULL2BASIC.classDecl *)
    Definition classDecl (mods:list Modifier) (name:ClassName) (ext:Extends)
                         (impls:list Implements)
                         (fields:list Field) (modelFields:list ModelField) 
                         (methods:list Method) (ts:TypeSpec) : Class :=
      typeDecl true mods name ext impls fields modelFields methods ts.

    (** @see FULL2BASIC.interfaceDecl *)
    Definition interfaceDecl (mods:list Modifier) (name:ClassName)
                         (impls:list Implements) (fields:list Field) (modelFields:list ModelField) 
                         (methods:list Method) (ts:TypeSpec) : Interface :=
      typeDecl false mods name no_extends impls fields modelFields methods ts.

    (** @see FULL2BASIC.invariantDecl *)
    Definition invariantDecl redundant ek mods pred := 
      TYPESPEC.INVARIANT.Build_t pred (javaVisibility ek mods) (typeSpec_isStatic ek mods) redundant.

    (** @see FULL2BASIC.constraintDecl *)
    Definition constraintDecl redundant ek mods pred constraintFor := 
      TYPESPEC.CONSTRAINT.Build_t pred (javaVisibility ek mods) constraintFor (typeSpec_isStatic ek mods) redundant.
  
    (** @see FULL2BASIC.representsDecl *)
    Definition representsDecl redundant ek mods modelField representsKind pred :=
      let relational := 
        match representsKind with
        | Functional => false
        | Relational => true
        end in
  
      TYPESPEC.REPRESENTS.Build_t (javaVisibility ek mods) modelField pred relational (typeSpec_isStatic ek mods) redundant.

    (** @see FULL2BASIC.initiallyDecl *)
    Definition initiallyDecl ek mods pred := TYPESPEC.INITIALLY.Build_t (javaVisibility ek mods) pred.
   
    (** @see FULL2BASIC.axiomDecl *)
    Definition axiomDecl pred := TYPESPEC.AXIOM.Build_t pred.

    (** @see FULL2BASIC.readableIfDecl *)
    Definition readableIfDecl ek mods field pred := TYPESPEC.READABLE_IF.Build_t field (javaVisibility ek mods) pred.

    (** @see FULL2BASIC.writableIfDecl *)
    Definition writableIfDecl ek mods field pred := TYPESPEC.WRITABLE_IF.Build_t field (javaVisibility ek mods) pred.

    (** @see FULL2BASIC.monitorsForDecl *)
    Definition monitorsForDecl ek mods field exprL := TYPESPEC.MONITORS_FOR.Build_t field (javaVisibility ek mods) exprL.
   
    (** @see FULL2BASIC.loopAnnotationDecl *)
    Definition loopAnnotationDecl (lbl:Label) (annotations:list LOOP_ANNOTATION_TAG.data) : LOOP_ANNOTATION.t :=
      let invs0    := LOOP_ANNOTATION_TAG.filterTag INVARIANT_TAG annotations in
      let invsRed0 := LOOP_ANNOTATION_TAG.filterTag INVARIANT_REDUNDANTLY_TAG annotations in
      let vars0    := LOOP_ANNOTATION_TAG.filterTag VARIANT_TAG annotations in
      let varsRed0 := LOOP_ANNOTATION_TAG.filterTag VARIANT_REDUNDANTLY_TAG annotations in  
  
      let optionalAnd := liftOptional2 (BinaryCondBoolExpr ConditionalAnd) in
      let SpecifiedE := Specified (A := Expression) in 
  
      let invs1    := fold_left1 optionalAnd (map SpecifiedE invs0) NotSpecified in
      let invsRed1 := fold_left1 optionalAnd (map SpecifiedE invsRed0) NotSpecified in
  
      let vars1    := map (rewriteVariant lbl) vars0 in
      let varsRed1 := map (rewriteVariant lbl) varsRed0 in
  
      let vars2    := fold_left1 optionalAnd (map SpecifiedE vars1) NotSpecified in
      let varsRed2 := fold_left1 optionalAnd (map SpecifiedE varsRed1) NotSpecified in
  
      LOOP_ANNOTATION.Build_t (optionalAnd invs1 vars2) (optionalAnd invsRed1 varsRed2) 
        invs0 invsRed0 vars0 varsRed0.

  End DECLARATION_REWRITINGS.
  Export DECLARATION_REWRITINGS.

