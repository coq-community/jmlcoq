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

Require Export JMLSemantics.
Require Import List.
Require Import Relation_Operators.

  Import Dom.
  Import Prog.
  Import METHODSPEC.

(** * The Java Operational Semantics
As parameter, we pass the module that defines the jml annotations to use (semantics or rac) *) 

Module OperationalSemantics (jml : JML).

  Import jml.
  Import Assignables.
  Import AnnotationTable.

(** Retrieve values from StepValues, abort if no normal step happened *)

  Fixpoint nv2v (nv : list StepValue) : list Value :=
  match nv with
  | ((normal_step_v v)::t) => (v::(nv2v t)) 
  | _ => nil
  end.

(** If the list of values is as long as the list of StepValue
     all step values come from normal steps, used in ExprStep *)

  Lemma nv2v_implication : 
  forall nvl vl, 
  (forall nv, exists v, In nv nvl -> nv = (normal_step_v v))-> 
  nv2v nvl = vl -> 
  length nvl = length vl.
  Proof.
  intros.
  inversion_clear H0.
  induction nvl.
    (* base case *)
    compute;reflexivity.

    (* step *)
    destruct (H a).
    rewrite H0.
      simpl.
      apply f_equal.
      apply IHnvl.
      intros. 
      destruct (H nv).
      exists x0.
      auto with datatypes.
    apply in_eq.
  Qed.

  (** Evaluation of one step of an expression *)
  Inductive ExpressionStep (p : Program): Expression -> State.t -> State.t -> StepValue -> Prop :=
 
  (** Assignment to an instance field: [target.fsig = expr] *)
  | assignment_instance_field_ok:
    forall e v obj fsig expr target st st1 st2 st' st3 loc cn um,
    e = Assignment (field fsig (Some target)) expr ->
    loc = (Heap.InstanceField obj fsig) ->
    ExpressionStep p target st st1 (normal_step_v (Ref obj)) ->
    FieldUpdateCheck p loc st1 ->
    ExpressionStep p expr st1 st2 (normal_step_v v) ->
    Heap.typeof st2@h obj = Some (Heap.ObjectObject cn um) ->
    defined_field p cn fsig ->
    assign_compatible p st2@h v (FIELDSIGNATURE.type (snd fsig)) -> 
    FieldUpdateAction p loc v st2 = st3 ->
    st' = st3[h:= Heap.update st2@h loc v] ->
    ExpressionStep p e st st' (normal_step_v v)

  (** Method call: [target.msig(params)] *)
  | method_vcall_ok:
    forall e st st1 st2 st3 st_c st_c' st' fr_c1 msig 
	o cn um this ps psnv psv v cn' m' c' b body,
    e = method msig (Some o) ps ->
    ExpressionStep p o st st1 (normal_step_v (Ref this)) ->
    Heap.typeof st1@h this = Some (Heap.ObjectObject cn um) ->
    lookup p cn (snd msig) (cn' , m') ->
    PROG.class p cn = Some c' ->
    ListSteps p ps st1 st2 psnv ->
    psv = nv2v psnv ->
    length psv = length psnv ->
    fr_c1 = NewFrame m' (lv2params m' ((Ref this)::psv)) st2 ->
    st3 = st2[fr:=fr_c1] ->
    MethodCallAction p c' m' st3 = st_c ->
    METHOD.body m' = Some body ->
    STATEMENT.type (METHODBODY.compound body) = Compound b ->
    BlockStep p m' b st_c st_c' normal_step ->
    Normal (Some v) = Frame.ret st_c'@fr ->
    MethodReturnAction p st_c' st2 = st' ->
    ExpressionStep p e st st' (normal_step_v v)

  (** Allocate new object: [o = new t] *)
  | new_object_ok: 
    forall e o st st' st1 h' cn um,
    e = new (ReferenceType (TypeDefType cn um)) ->
    Heap.new st@h p (Heap.ObjectObject cn um) = Some (o , h') ->
    NewObjectAction p o st = st1 ->
    st' = st1[h:= h'] ->
    ExpressionStep p e st st' (normal_step_v (Ref o))

  (** ListSteps evaluate a whole list of expressions, used in method calls, circular dependency *)
  with ListSteps (p : Program): list Expression -> State.t -> State.t -> list StepValue -> Prop :=

  | ListSteps_nil:
    forall st st',
    st = st' ->
    ListSteps p nil st st' nil

  | ListSteps_cons_ok: 
    forall e le elist st st1 st' v lr ,
    elist = e::le ->
    ExpressionStep p e st st1 (normal_step_v v) ->
    ListSteps p le st1 st' lr ->
    ListSteps p elist st st' ((normal_step_v v)::lr)

(* Not interesting for the moment
  | ListSteps_cons_err:
    forall e le elist st st' err,
    elist = e::le ->
    ExpressionStep ListSteps e st st' (exception_step err) ->
    ListSteps elist st st' ((exception_step err) :: nil)
*)

  (** Evaluation function for statements *)
  with StatementStep (p : Program) : Method -> BLOCK.t -> State.t -> State.t -> StepValue -> Prop :=

  (** Expression-Statement *)
  | expr_stmt_ok : forall st st' v e,
    forall m b,
    statement_at m (Frame.pc st@fr) = Some (ExprStmt e) ->
    ExpressionStep p e st st' (normal_step_v v) ->
    StatementStep p m b st st' normal_step

(* Not interesting for the moment
  (** Nested Block *)
  | block_stmt : forall h fr fr' h' fr1 fr2 st st' pc pc' b',    
    pc = Frame.pc fr ->
    statement_at m pc = Compound b' ->
    BLOCK.first b' = Some pc' ->
    fr1 = UpdatePc fr pc' ->
    bSteps m b' (h, fr1) (h', fr2) ->
    fr' = UpdatePc fr2 pc ->
    st = (h, fr) ->
    st' = (h', fr') ->
    StatementStep m b st st'
*)

  (** Evaluation of a block, sequencial composition *)
  with BlockStep (p : Program) : Method -> BLOCK.t -> State.t -> State.t -> StepValue-> Prop :=
  
  (** If there is a next instruction, do sequencial composition *)
  | BlockStep_ok_next: forall m b pc' st st1 st' fr2 ,
    BLOCK.next b (Frame.pc st@fr) = Some pc' ->
    StatementStep p m b st st1 normal_step -> 
    fr2 = Frame.set_pc st1@fr pc' ->
    BlockStep p m b st1[fr:=fr2] st' normal_step ->
    BlockStep p m b st st' normal_step

  (** Last statement in block, just evaluate statement *)
  | BlockStep_ok_last: forall m b st st' ,
    BLOCK.next b (Frame.pc st@fr) = None ->
    StatementStep p m b st st' normal_step ->
    BlockStep p m b st st' normal_step.

Scheme expr_step_ind := Minimality for ExpressionStep Sort Prop
  with expr_steps_ind := Minimality for ListSteps Sort Prop
  with stmt_step_ind := Minimality for StatementStep Sort Prop
  with block_step_ind := Minimality for BlockStep Sort Prop.
Combined Scheme mutual_ind from expr_step_ind, expr_steps_ind, stmt_step_ind, block_step_ind.

Theorem OpSem_deterministic:
forall p,
  (forall e st st' r',
  ExpressionStep p e st st' r' ->
  forall st'' r'',
  ExpressionStep p e st st'' r'' ->
  st' = st'' /\ r' = r'')
/\
  (forall l st st' r',
  ListSteps p l st st' r' ->
  forall st'' r'',
  ListSteps p l st st'' r'' ->
  st' = st'' /\ r' = r'')
/\
  (forall m b st st' r',
  StatementStep p m b st st' r' ->
  forall st'' r'',
  StatementStep p m b st st'' r'' ->
  st' = st'' /\ r' = r'')
/\
  (forall m b st st' r',
  BlockStep p m b st st' r' ->
  forall st'' r'',
  BlockStep p m b st st'' r'' ->
  st' = st'' /\ r' = r'').
Proof.

intro p.
apply mutual_ind; intros; simpl in *.
 inversion H11; try (rewrite H12 in H; discriminate H).
 subst.
 inversion H12.
 subst.
 destruct H2 with st4 (normal_step_v (Ref obj0)); trivial.
 inversion H0.
 subst.
 destruct H5 with st5 (normal_step_v v0); trivial.
 inversion H9.
 rewrite H in |- *.
 tauto.
 
 inversion H18; try (rewrite H19 in H; discriminate H).
 subst.
 inversion H19.
 subst.
 destruct H1 with st4 (normal_step_v (Ref this1)); trivial.
 inversion H7.
 subst.
 destruct H6 with st5 psnv0; trivial.
 subst.
 rewrite H2 in H21.
 inversion H21.
 subst.
 assert ((cn', m') = (cn'0, m'0)).
  apply (lookup_deterministic p cn0 (snd msig0) (cn', m') (cn'0, m'0));
   trivial.
  
  inversion H.
  subst.
  rewrite H12 in H30; inversion H30; subst.
  rewrite H13 in H31; inversion H31; subst.
  rewrite H4 in H23; inversion H23; subst.
  destruct H15 with st_c'0 normal_step; trivial.
  subst.
  rewrite <- H16 in H33; inversion H33; subst.
  tauto.
 
 inversion H3; try (rewrite H4 in H; discriminate H).
 rewrite H4 in H.
 inversion H.
 subst.
  
 rewrite H0 in H5; inversion H5; subst.
 tauto.
 
 inversion H0.
  subst.
  tauto.
  
  discriminate H1.
  
 inversion H4; try (rewrite <- H6 in H; discriminate H).
 subst.
 inversion H5.
 subst.
 destruct H1 with st2 (normal_step_v v0); trivial.
 subst.
 inversion H8.
 subst.
 destruct H3 with st'' lr0; trivial.
 subst.
 tauto.
 
 inversion H2; try (rewrite H4 in H; discriminate H).
 subst.
 rewrite H3 in H; inversion H; subst.
 destruct H1 with st'' (normal_step_v v0); trivial.
 tauto.
 
 inversion H5; try (rewrite H6 in H; discriminate H).
 subst.
 destruct H1 with st2 normal_step; trivial.
 subst.
 rewrite H6 in H; inversion H; subst.
 destruct H4 with st'' normal_step; trivial.
 tauto.
 
 inversion H2; try (rewrite H3 in H; discriminate H).
 subst.
 destruct H1 with st'' normal_step; trivial.
 tauto.
Qed.

End OperationalSemantics.
