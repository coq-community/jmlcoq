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

(**
  JMLSyntaxImpl contains implementation dependent Notation shorthands
  for statements (JML/Java), blocks and  and blocks.
 *)

Require Import List.
Require Import ListHelpers.

Require Import JMLExpressionNotations.

Require Import JMLProgramPlusImpl.
Import P. (* PROGRAM module *)

Module EXPRESSION_NOTATIONS_P := EXPRESSION_NOTATIONS P.Program.
Export EXPRESSION_NOTATIONS_P.

Require Export JMLFull2BasicImpl.

(** Full syntax quantifiers with multiple variables *)
Notation "\forall vs ; r ; e"  := (rewriteFullQuantifier (FullQuantification Forall vs r e)) (at level 0, e at level 200) : jml_scope.
Notation "\exists vs ; r ; e"  := (rewriteFullQuantifier (FullQuantification Exists vs r e)) (at level 0, e at level 200) : jml_scope.
Notation "\max vs ; r ; e"     := (rewriteFullQuantifier (FullQuantification Max vs r e)) (at level 0, e at level 200) : jml_scope.
Notation "\min vs ; r ; e"     := (rewriteFullQuantifier (FullQuantification Min vs r e)) (at level 0, e at level 200) : jml_scope.
Notation "\num_of vs ; r ; e"  := (rewriteFullQuantifier (FullQuantification NumOf vs r e)) (at level 0, e at level 200) : jml_scope.
Notation "\product vs ; r ; e" := (rewriteFullQuantifier (FullQuantification Product vs r e)) (at level 0, e at level 200) : jml_scope.
Notation "\sum vs ; r ; e"     := (rewriteFullQuantifier (FullQuantification Sum vs r e)) (at level 0, e at level 200) : jml_scope.

(** Statent notations *)

(** StatementType tailered to implementation *)
Definition StmtType : Type := StatementType (Statement := STATEMENT.t) (Block := STATEMENT.b).

(**
  Notation to make a statement for a given pc and statement type:
    e.g. 2%N :> nop. 
 *)
Notation "pc :> stmt" := (STATEMENT.Build_t pc None stmt) (at level 97) : jml_scope.
Notation "pc_lbl :-> stmt" := (STATEMENT.Build_t (fst pc_lbl) (Some (snd pc_lbl)) stmt) (at level 97) : jml_scope.

(**
  Labels a given statement:
    e.g. label bla (1%N :> nop) 
 *)
Definition label (lbl:Label) (stmt:STATEMENT.t) : STATEMENT.t := 
  STATEMENT.Build_t (STATEMENT.pc stmt) (Some lbl) (STATEMENT.type stmt).

(* Notation to set the label in a given statement:
    e.g. (2%N :> nop) <<: 27%N. 
 *)
(* Notation "stmt <<: lbl" := (STATEMENT.Build_t (STATEMENT.pc stmt) lbl (STATEMENT.type stmt)) (at level 98) : jml_scope. *)

(** Creates a statement type from a given expression *)
Definition stmt (e:Expression) : StmtType := ExprStmt e.

(** Creates a for loop statement type  *) 
Definition for_ (anno:LOOP_ANNOTATION.t) (init:list STATEMENT.t) (test:Expression) (step:list Expression) (body:STATEMENT.t) :=
  ForLoop (Block := BLOCK.t) anno init test step body.

(** Creates a while statement type *)
Definition while (anno:LOOP_ANNOTATION.t) (test:Expression) (body:STATEMENT.t) :=
  WhileLoop (Block := BLOCK.t) anno test body.


(** Creates a do statement:
    do {
      ..
    } while_ (expr) 
 *)
Inductive While_ : Set := while_.
Definition do_ (anno:LOOP_ANNOTATION.t) (body:STATEMENT.t) (_:While_) (test:Expression) :=
  DoLoop (Block := BLOCK.t) anno body test.

(** Creates an if statement type (without else) *)
Definition if_ (test:Expression) (_then:STATEMENT.t) := 
  IfStmt (Block := BLOCK.t) test _then None.

(** Dummy type to mimic java if (test) { // then } else { // else } syntax *)
Inductive Else_ : Set := else_.

(**
  Creates an if statement (with else):
   ife (expr) {
     ..
   } else_ {
     ..
   } 
 *)
Definition ife (test:Expression) (_then:STATEMENT.t) (_:Else_) (_else:STATEMENT.t) := 
  IfStmt (Block := BLOCK.t) test _then (Some _else).

(**
  Notational convenience for cases within a switch statment:
   case A:                   
   case B:             -->  cases [A; B] [{ pc :>> blockStatements }]
     blockStatements
 *)
Definition cases (exprList:list Expression) (stmts:list STATEMENT.t) : (list Expression)*(list STATEMENT.t) :=
  (exprList, stmts).

(**
  Notation for the switch statment type:
   switch (expr) {{
    cases [..] { ..
    }
    ..
    default Some (statement)
   }}.
 *)
Notation "'switch' e {{ l 'default' d }}" := 
  (SwitchStmt STATEMENT.t STATEMENT.b e l (Some d)) (at level 0) : jml_scope.

Notation "'switch' e {{ l  }}" := 
  (SwitchStmt STATEMENT.t STATEMENT.b e l None) (at level 0) : jml_scope.

(**
  Notational convenience for catch within a try statement:
   catch (ex) { .. } 
 *)   
Definition catch (param:Param) (block:STATEMENT.t) : (Param * STATEMENT.t) := (param, block).

Inductive Finally := finally.

Definition tryF t catches (_:Finally) fin := TryBlock (Statement := STATEMENT.t) (Block := BLOCK.t) t catches (Some fin).

Definition try t catches := TryBlock (Statement := STATEMENT.t) (Block := BLOCK.t) t catches None.

(**
  Notation for the try statetement type:
   try { .. 
   }; catch (ex) { ..
   }; finally { ..
   }.
 *)
(*
Notation "'try' t ; h ; 'finally' f" := 
  (TryBlock STATEMENT.t STATEMENT.b t h f) (at level 0) : jml_scope.
*)

(** break statement type and breakL statment type to break with label. *)
Definition break : StmtType  := BreakStmt None.
Definition breakL (lbl:Label) : StmtType  := BreakStmt (Some lbl).

(** continue statement type and continueL statment type to continue at a label. *)
Definition continue : StmtType  := ContStmt None.
Definition continueL (lbl:Label) : StmtType  := ContStmt (Some lbl).

(** return_ statement type to return without argument and returnE to return with the given expression *)
Definition return_ : StmtType := ReturnStmt None.
Definition returnE (e:Expression) : StmtType := ReturnStmt (Some e).

(** throw statement type to throw a given exception expression *)
Definition throw : Expression -> StmtType := ThrowStmt .

(** assert statement types to assert a given expression *)
Definition jassert := JavaAssertion (Statement := STATEMENT.t) (Block := BLOCK.t).

(** @assert statement types to assert a given expression *)
Definition assert (e:Expression) (l:option Expression) := LocalAssertion (Statement := STATEMENT.t) (Block := BLOCK.t) e l false.
Definition assert_redundantly (e:Expression) (l:option Expression) := LocalAssertion (Statement := STATEMENT.t) (Block := BLOCK.t) e l true.

(** @assume statement types to assume the given expression *)
Definition assume (e:Expression) (l:option Expression):= LocalAssumption (Statement := STATEMENT.t) (Block := BLOCK.t) e l false.
Definition assume_redundantly (e:Expression) (l:option Expression):= LocalAssumption (Statement := STATEMENT.t) (Block := BLOCK.t) e l true.

(** @set statement type to assign an expression to a ghost variable *)
Definition set : Expression -> StmtType := SetGhost.

(** @unreachable assertion: control flow never reaches this statement. *)
Definition unreachable : StmtType := Unreachable.


(** @debug statement type to execute a jml expression that can refer to jml entities also *)
Definition debug : Expression -> StmtType := Debug.

Definition var_decl_stmtM mods typ name val := varDeclStmt (Statement := STATEMENT.t) (Block := BLOCK.t) (varDecl mods typ name) val.
Definition var_decl_stmt typ name val     := varDeclStmt (Statement := STATEMENT.t) (Block := BLOCK.t) (varDecl nil  typ name) val.

(** 
  @hence_by statement type: 
   [RM:]
   The hence_by statement is used to record reasoning when writing a proof by intermittent assertions. 
   It would normally be used between two assert statements 
 *)
Definition hence_by (e:Expression) : StmtType := HenceBy e false.
Definition hence_by_redundantly (e:Expression) : StmtType := HenceBy e true.

(** Nop statement type (= empty statement ;) *)
Definition nop := Nop (Statement := STATEMENT.t) (Block := BLOCK.t).

Definition super_call := SuperCallStmt (Statement := STATEMENT.t) (Block := BLOCK.t).
Definition this_call  := ThisCallStmt (Statement := STATEMENT.t) (Block := BLOCK.t).

(** Block declarations *)

(**
  Notation for blocks within method bodies:
   {
     locals [var1; var2; ...];
     list_of_statments
   }
 *)
(* Notation "{: 'locals' x ; y :}" := (Some (BLOCK.Build_t x y)) : jml_scope. *)

Notation "{{: x ; .. ; y :}}" := (Some (BLOCK.Build_t (cons x .. (cons y nil) ..))) : jml_scope.
Notation "{{: :}}" := (Some (BLOCK.Build_t nil)) : jml_scope.


Definition no_body : option BLOCK.t := None.

(**
  Notation for block statements (as e.g. then-block within an if_):
   { pc :>>
     locals [var1; var2; ...];
     list_of_statments
   } 
 *)
(*
Notation "{: pc :> 'locals' x ; y :}" := 
  (STATEMENT.Build_t pc None (Compound STATEMENT.t STATEMENT.b (BLOCK.Build_t x y))) : jml_scope.
*)

Notation "{: pc :>> x ; .. ; y :}" := 
  (STATEMENT.Build_t pc None (Compound STATEMENT.t STATEMENT.b (BLOCK.Build_t (cons x .. (cons y nil) ..)))) : jml_scope.

Notation "{: pc_lbl :->> x ; .. ; y :}" := 
  (STATEMENT.Build_t (fst pc_lbl) (Some (snd pc_lbl)) (Compound STATEMENT.t STATEMENT.b (BLOCK.Build_t (cons x .. (cons y nil) ..)))) : jml_scope.

Notation "{: pc :>> :}" := 
  (STATEMENT.Build_t pc None (Compound STATEMENT.t STATEMENT.b (BLOCK.Build_t nil))) : jml_scope.

Notation "{: pc_lbl :->> :}" := 
  (STATEMENT.Build_t (fst pc_lbl) (Some (snd pc_lbl)) (Compound STATEMENT.t STATEMENT.b (BLOCK.Build_t nil))) : jml_scope.


(** Loop annotations *)

(** @maintaining annotation to add the given expression as a loop invariant *)
Definition maintaining (e:Expression) := (INVARIANT_TAG, e).
Definition maintaining_redundantly (e:Expression) := (INVARIANT_REDUNDANTLY_TAG, e).

(** @decreasing annotation to add the given expression as a loop variant *)
Definition decreasing (e:Expression) := (VARIANT_TAG, e).
Definition decreasing_redundantly (e:Expression) := (VARIANT_REDUNDANTLY_TAG, e).

Definition loop_annotation := loopAnnotationDecl.

(** Method specification clauses *)
Definition forall_ := FORALL_VAR_DECL.Build_t.
Definition old := OLD_VAR_DECL.Build_t.

Notation "\same" := (same) : jml_scope.
Definition requires := requiresSH false.
Definition requires_redundantly := requiresSH true.

Definition ensures := ensuresC false.
Definition signals e pred := signalsC false (e, pred).
Definition signals_only := signalsOnlyC false.
Definition diverges := divergesC false.
Definition when := whenC false.
Definition assignable := assignableC false.
Definition accessible := accessibleC false.
Definition callable := callableC false.
Definition measured_by expr cond := measuredByC false (expr, cond).
Definition captures := capturesC false.
Definition working_space expr cond := workingSpaceC false (expr, cond).
Definition duration expr cond := durationC false (expr, cond).

Definition ensures_redundantly := ensuresC true.
Definition signals_redundantly e pred := signalsC true (e, pred).
Definition signals_only_redundantly := signalsOnlyC true.
Definition diverges_redundantly := divergesC true.
Definition when_redundantly := whenC true.
Definition assignable_redundantly := assignableC true.
Definition accessible_redundantly := accessibleC true.
Definition callable_redundantly := callableC true.
Definition measured_by_redundantly expr cond := measuredByC true (expr, cond).
Definition captures_redundantly := capturesC true.
Definition working_space_redundantly expr cond := workingSpaceC true (expr, cond).
Definition duration_redundantly expr cond := durationC true (expr, cond).


(** Notation for a list of NestedBody's *)
Declare Scope jml_nb_scope.
Notation "{| x ; .. ; y |}" := (cons x .. (cons y nil) ..) : jml_nb_scope. 

Bind Scope jml_nb_scope with GENERIC_SPEC_CASE.t.
Delimit Scope jml_nb_scope with jml_nb.

(** Notation for a heavyweight spec case *)
Definition spec_case := methodSpecDecl false.

(** Notation for a redundant heavyweight spec case *)
Definition spec_case_redundantly := methodSpecDecl true.

(** Notation for a lightweight spec case *)
Definition spec_case_lightweight := methodSpecDecl false nil lightweight.

(** Notation for a redundant lightweight spec case *)
Definition spec_case_lightweight_redundantly := methodSpecDecl true nil lightweight.

(** Notation for a nested spec case *)
Definition nested_case forallVarDecl oldVarDecl specHeader (nested:list GENERIC_SPEC_CASE.t) := 
  GENERIC_SPEC_CASE.Build_t forallVarDecl oldVarDecl specHeader (inr _ nested).
 
(** Notation for a simple spec case *)
Definition simple_case forallVarDecl oldVarDecl specHeader (simple:list MethodSpecClause) := 
  GENERIC_SPEC_CASE.Build_t forallVarDecl oldVarDecl specHeader (inl _ simple).

(** Java entity declarations *)

(** Notations for super method declarations within method declarations *)
Definition statically_bound : option MethodSignature := None.
Definition no_override : option MethodSignature := None.
Definition overrides (m:MethodSignature) := Some m.

(** Notations for throws clause *)
Definition throws (exceptions:list ExceptionType) := exceptions.
Definition no_throws : list ExceptionType := nil.

Definition of_class := ClassEK.
Definition of_interface := InterfaceEK.

Definition no_modifiers : list Modifier := nil.
Definition no_implements : list Implements := nil.
Definition no_fields : list Field := nil.
Definition no_model_fields : list ModelField := nil.
Definition no_methods : list Method := nil.

Definition var_declM  := varDecl.
Definition var_decl   := varDecl nil.
Definition param_declM := paramDecl.
Definition param_decl  := paramDecl nil.

(* Notations for data groups *)
Definition in_ (dataGroups : list FieldSignature) := DATA_GROUP.Build_t None dataGroups false.
Definition in_redundantly (dataGroups : list FieldSignature) := DATA_GROUP.Build_t None dataGroups true.

Inductive Into := IntoC.
Notation "\into" := IntoC : jml_scope.

Definition maps (target:DynDgPivotTarget) (_:Into) (dataGroups : list FieldSignature) :=
  DATA_GROUP.Build_t (Some target) dataGroups false.
Definition maps_redundantly (target:DynDgPivotTarget) (_:Into) (dataGroups : list FieldSignature) :=
  DATA_GROUP.Build_t (Some target) dataGroups true.

Definition field_decl ek mods t sfs oe := fieldDecl ek mods t sfs oe nil.
Definition field_declS := fieldDecl.

Definition model_field_decl ek mods t sfs := modelFieldDecl ek mods t sfs nil.
Definition model_field_declS := modelFieldDecl.

Definition method_declS := methodDecl.
Definition method_decl ek := methodDecl ek Default.
Definition class_decl     := classDecl.

Definition interface_decl := interfaceDecl.

(** Declaration of a field signature *)
Definition field_signature_decl (cn:ClassName) (t:StaticType) (n:ShortFieldName) := (cn, FIELDSIGNATURE.Build_t n t).

(** Declaration of a method signature *)
Definition method_signature_decl (cn:ClassName) (rt:ReturnType) (name:ShortMethodName) (params:list Param) :=
  (cn, METHODSIGNATURE.Build_t name params (returnType2option rt)).

Definition type_spec_decl := TYPESPEC.Build_t.

Definition no_invariants := nil (A := INVARIANT.t).
Definition no_constraints := nil (A := CONSTRAINT.t).
Definition no_represents := nil (A := REPRESENTS.t).
Definition no_initially := nil (A := INITIALLY.t).
Definition no_axiom := nil (A := AXIOM.t).
Definition no_readable_if := nil (A := READABLE_IF.t).
Definition no_writable_if := nil (A := WRITABLE_IF.t).
Definition no_monitors_for := nil (A := MONITORS_FOR.t).

Definition invariant := invariantDecl false.
Definition invariant_redundantly := invariantDecl true.
Definition constraint := constraintDecl false.
Definition constraint_redundantly := constraintDecl true.
Notation "\such_that" := (Relational) : jml_scope.
Notation "<-" := (Functional) : jml_scope.
Definition represents := representsDecl false.
Definition represents_redundantly := representsDecl true.
Definition initially := initiallyDecl.
Definition axiom := axiomDecl.
Definition readable_if := readableIfDecl.
Definition writable_if := writableIfDecl.
Definition monitors_for := monitorsForDecl.

