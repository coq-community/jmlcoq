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
#<pre>#
Correctness Proof of RAC2 <-> RAC3

Sem:  st_rac2 ----- Exec p ------> st'_rac2
        |                           |
        | Corr                      | Corr
        |                           |
RAC1: st_rac3 ----- Exec p ------> st'_rac3

#</pre>#
*)

Require Export JMLRac3.
Require Export JMLOpSem.

Import Dom.
Import Prog.
Import Sem.Notations.
Import Rac1.Notations.
Import Rac2.Notations.
Import Rac3.Notations.

Module OpRac2 := OperationalSemantics Rac2.
Module OpRac3 := OperationalSemantics Rac3.

Import Rac3.
Import Assignables.

Open Scope rac3_scope.

Theorem rac3_rac2_correct:
forall p,
  (forall e st_rac3 st'_rac3 r,
  OpRac3.ExpressionStep p e st_rac3 st'_rac3 r ->
  forall st_rac2,
  CorrespondingState p st_rac2 st_rac3 ->
  exists st'_rac2,
  CorrespondingState p st'_rac2 st'_rac3 /\
  OpRac2.ExpressionStep p e st_rac2 st'_rac2 r)
/\
  (forall l st_rac3 st'_rac3 r,
  OpRac3.ListSteps p l st_rac3 st'_rac3 r ->
  forall st_rac2,
  CorrespondingState p st_rac2 st_rac3 ->
  exists st'_rac2,
  CorrespondingState p st'_rac2 st'_rac3 /\
  OpRac2.ListSteps p l st_rac2 st'_rac2 r)
/\
  (forall m b st_rac3 st'_rac3 r,
  OpRac3.StatementStep p m b st_rac3 st'_rac3 r ->
  forall st_rac2,
  CorrespondingState p st_rac2 st_rac3 ->
  exists st'_rac2,
  CorrespondingState p st'_rac2 st'_rac3 /\
  OpRac2.StatementStep p m b st_rac2 st'_rac2 r)
/\
  (forall m b st_rac3 st'_rac3 r,
  OpRac3.BlockStep p m b st_rac3 st'_rac3 r ->
  forall st_rac2,
  CorrespondingState p st_rac2 st_rac3->
  exists st'_rac2,
  CorrespondingState p st'_rac2 st'_rac3 /\
  OpRac2.BlockStep p m b st_rac2 st'_rac2 r).
Proof.

intro p.
apply OpRac3.mutual_ind; intros; simpl in *.



(* Case assignment_instance_field_ok *)

 apply H2 in H11.
destruct H11 as[st1_rac2 H11].
destruct H11.
destruct H5 with st1_rac2 as [st2_rac2 H13];trivial.
destruct H13.
set (st3_rac2 := Rac2.Assignables.FieldUpdateAction p loc v st2_rac2).
exists ((st3_rac2[h := Heap.update st2_rac2@h loc v])%rac2).
split.
rewrite H10.
apply FieldUpdateAction_Correct with cn um obj fsig;trivial.
inversion H13.
  apply
   (OpRac2.assignment_instance_field_ok p e v obj fsig expr target st_rac2
      st1_rac2 st2_rac2 st3_rac2[h := Heap.update st2_rac2@h loc v]%rac2
      st3_rac2 loc cn um); trivial.

   apply
    (FieldUpdateCheck_Correct loc p st1_rac2 st1);
    trivial.    

rewrite H16;trivial.

rewrite H16;trivial.

   
(* Case method_vcall_ok *)

 destruct H1 with st_rac2 as (st1_rac2, Htmp); trivial.
 destruct Htmp.
 clear H1.
 destruct H6 with st1_rac2 as (st2_rac2, Htmp); trivial.
 destruct Htmp.
 clear H6.
 set (fr_c1_rac2 := Rac2.NewFrame m' (lv2params m' (Ref this0 :: psv)) st2_rac2)
  in |- *.
 set (st3_rac2 := st2_rac2[fr := fr_c1_rac2]%rac2) in |- *.
 set (st_c_rac2 := Rac2.Assignables.MethodCallAction p c' m' st3_rac2) in |- *.
 destruct H15 with st_c_rac2 as (st_c'_rac2, Htmp).
  assert (CorrespondingState p st3_rac2 st3).

   unfold st3_rac2 in |- *.
   rewrite H10 in |- *.
   
   apply
    NewFrame_Correct
     with
       (m := m')
       (param := lv2params m' (Ref this0 :: psv))
       (st_rac2 := st2_rac2)
       (st_rac3 := st2); trivial.
   
   unfold st_c_rac2 in |- *.
   rewrite <- H11.
    apply
     MethodCallAction_Correct
      with (c := c') (m := m') (st_rac2 := st3_rac2) (st_rac3 := st3); 
     trivial.
    
  destruct Htmp.

  set
   (st'_rac2 :=
    Rac2.Assignables.MethodReturnAction p st_c'_rac2 st2_rac2) 
   in |- *.
  exists st'_rac2.
  split.
   unfold st'_rac2 in |- *.
   rewrite <- H17 in |- *.

    apply
     MethodReturnAction_Correct
      with
        st2_rac2 st_c'_rac2
        st2 st_c'; trivial.
   
   apply
    (OpRac2.method_vcall_ok p e st_rac2 st1_rac2 st2_rac2 st3_rac2 st_c_rac2
       st_c'_rac2 st'_rac2 fr_c1_rac2 msig o cn um this0 ps
       psnv psv v cn' m' c' b body); trivial.
    inversion H19.
    rewrite H24;trivial.
    
    inversion H6.
    inversion H23.
    rewrite H31.
    trivial.

(* new_object_ok *)

 set (st1_rac2 := Rac2.Assignables.NewObjectAction p o st_rac2) in |- *.
 exists st1_rac2[h := h']%rac2.
 split.
  rewrite H2 in |- *.
  assert (CorrespondingState p st1_rac2 st1).
   unfold st1_rac2 in |- *.
   rewrite <- H1 in |- *.
   apply NewObjectAction_Correct with o st_rac2 st; trivial.
   replace st@h with st1@h in H0.

   destruct H4.
   split;simpl;trivial.

  rewrite <- CorrectBacklinks_new with cn um o;trivial.

  destruct H1.   
  unfold NewObjectAction.
  simpl.
  trivial.

  apply
   OpRac2.new_object_ok
    with (st1 := st1_rac2) (h' := h') (cn := cn) (um := um);
   trivial.
  destruct H3.
  rewrite H4; trivial.

(* ListSteps_nil *)

 exists st_rac2.
 rewrite <- H in |- *.
 split; trivial.
 apply OpRac2.ListSteps_nil; trivial.

(* ListSteps_cons_ok *)

 destruct H1 with st_rac2 as (st1_rac2, Htmp); trivial.
 destruct Htmp.
 destruct H3 with st1_rac2 as (st'_rac2, Htmp); trivial.
 destruct Htmp.
 exists st'_rac2.
 split; trivial.
 apply OpRac2.ListSteps_cons_ok with (e := e) (le := le) (st1 := st1_rac2);
  trivial.

(* expr_stmt_ok *)
 
 destruct H1 with st_rac2 as (st'_rac2, Htmp); trivial.
 destruct Htmp.
 exists st'_rac2.
 split; trivial.
 apply OpRac2.expr_stmt_ok with (v := v) (e := e); trivial.
 destruct H2.
 destruct H2.
 rewrite H8 in |- *; trivial.

(* BlockStep_ok_next *)
 
 destruct H1 with st_rac2 as (st1_rac2, Htmp); trivial.
 destruct Htmp.
 set (fr2_rac2 := Rac2.State.Frame.set_pc st1_rac2@fr%rac2 pc') in |- *.
 destruct H4 with st1_rac2[fr := fr2_rac2]%rac2 as (st'_rac2, Htmp); trivial.
  destruct H6.
  rewrite H2 in |- *.
  unfold fr2_rac2 in |- *.
  split; trivial.

  inversion H6.
  split;simpl;trivial.
  
  destruct Htmp.
  exists st'_rac2.
  split; trivial.
  apply
   OpRac2.BlockStep_ok_next
    with (pc' := pc') (st1 := st1_rac2) (fr2 := fr2_rac2); 
   trivial.
  destruct H5.
  destruct H5.
  rewrite H13 in |- *.
  trivial.

(* BlockStep_ok_last *)
  
 destruct H1 with st_rac2 as (st'_rac2, Htmp); trivial.
 destruct Htmp.
 exists st'_rac2.
 split; trivial.
 apply OpRac2.BlockStep_ok_last; trivial.
 destruct H2.
 destruct H2.
 rewrite H8 in |- *; trivial.
Qed.


Open Scope rac2_scope.

Theorem rac2_rac3_correct:
forall p,
  (forall e st_rac2 st'_rac2 r,
  OpRac2.ExpressionStep p e st_rac2 st'_rac2 r ->
  forall st_rac3,
  CorrespondingState p st_rac2 st_rac3 ->
  exists st'_rac3,
  CorrespondingState p st'_rac2 st'_rac3 /\
  OpRac3.ExpressionStep p e st_rac3 st'_rac3 r)
/\
  (forall l st_rac2 st'_rac2 r,
  OpRac2.ListSteps p l st_rac2 st'_rac2 r ->
  forall st_rac3,
  CorrespondingState p st_rac2 st_rac3 ->
  exists st'_rac3,
  CorrespondingState p st'_rac2 st'_rac3 /\
  OpRac3.ListSteps p l st_rac3 st'_rac3 r)
/\
  (forall m b st_rac2 st'_rac2 r,
  OpRac2.StatementStep p m b st_rac2 st'_rac2 r ->
  forall st_rac3,
  CorrespondingState p st_rac2 st_rac3 ->
  exists st'_rac3,
  CorrespondingState p st'_rac2 st'_rac3 /\
  OpRac3.StatementStep p m b st_rac3 st'_rac3 r)
/\
  (forall m b st_rac2 st'_rac2 r,
  OpRac2.BlockStep p m b st_rac2 st'_rac2 r ->
  forall st_rac3,
  CorrespondingState p st_rac2 st_rac3->
  exists st'_rac3,
  CorrespondingState p st'_rac2 st'_rac3 /\
  OpRac3.BlockStep p m b st_rac3 st'_rac3 r).
Proof.
intro p.
apply OpRac2.mutual_ind; intros; simpl in *.

(* Case assignment_instance_field_ok *)

apply H2 in H11.
destruct H11 as[st1_rac3 H11].
destruct H11.
destruct H5 with st1_rac3 as [st2_rac3 H13];trivial.
destruct H13.
set (st3_rac3 := Rac3.Assignables.FieldUpdateAction p loc v st2_rac3).
exists ((st3_rac3[h := Heap.update st2_rac3@h loc v])%rac3).
split.
rewrite H10.
destruct H13.
apply FieldUpdateAction_Correct with cn um obj fsig;trivial.
rewrite <- H15;trivial.
rewrite <- H15;trivial.
split;trivial.
inversion H13.
  apply
   (OpRac3.assignment_instance_field_ok p e v obj fsig expr target st_rac3
      st1_rac3 st2_rac3 st3_rac3[h := Heap.update st2_rac3@h loc v]%rac3
      st3_rac3 loc cn um); trivial.

   apply
    (FieldUpdateCheck_Correct loc p st1 st1_rac3);
    trivial.

rewrite <- H16;trivial.

rewrite <- H16;trivial.

   
(* Case method_vcall_ok *)

 destruct H1 with st_rac3 as (st1_rac3, Htmp); trivial.
 destruct Htmp.
 clear H1.
 destruct H6 with st1_rac3 as (st2_rac3, Htmp); trivial.
 destruct Htmp.
 clear H6.
 set (fr_c1_rac3 := Rac3.NewFrame m' (lv2params m' (Ref this0 :: psv)) st2_rac3)
  in |- *.
 set (st3_rac3 := st2_rac3[fr := fr_c1_rac3]%rac3) in |- *.
 set (st_c_rac3 := Rac3.Assignables.MethodCallAction p c' m' st3_rac3) in |- *.
 destruct H15 with st_c_rac3 as (st_c'_rac3, Htmp).
  assert (CorrespondingState p st3 st3_rac3).

   unfold st3_rac3 in |- *.
   rewrite H10 in |- *.
   
   apply
    NewFrame_Correct
     with
       (m := m')
       (param := lv2params m' (Ref this0 :: psv))
       (st_rac2 := st2)
       (st_rac3 := st2_rac3); trivial.
   
   unfold st_c_rac3 in |- *.
   rewrite <- H11.
    apply
     MethodCallAction_Correct
      with (c := c') (m := m') (st_rac2 := st3) (st_rac3 := st3_rac3); 
     trivial.
    
  destruct Htmp.

  set
   (st'_rac3 :=
    Rac3.Assignables.MethodReturnAction p st_c'_rac3 st2_rac3) 
   in |- *.
  exists st'_rac3.
  split.
   unfold st'_rac3 in |- *.
   rewrite <- H17 in |- *.

    apply
     MethodReturnAction_Correct
      with
        st2 st_c'
        st2_rac3 st_c'_rac3; trivial.
   
   apply
     (OpRac3.method_vcall_ok p e st_rac3 st1_rac3 st2_rac3 st3_rac3 st_c_rac3
       st_c'_rac3 st'_rac3 fr_c1_rac3 msig o cn um this0 ps
       psnv psv v cn' m' c' b body); trivial.
    inversion H19.
    rewrite <- H24;trivial.
    
    inversion H6.
    inversion H23.
    rewrite <- H31.
    trivial.

(* new_object_ok *)

 set (st1_rac3 := Rac3.Assignables.NewObjectAction p o st_rac3) in |- *.
 exists st1_rac3[h := h']%rac3.
 split.
  rewrite H2 in |- *.
  assert (CorrespondingState p st1 st1_rac3).
   unfold st1_rac3 in |- *.
   rewrite <- H1 in |- *.
   apply NewObjectAction_Correct with o st st_rac3; trivial.
   replace st@h with st1@h in H0.

   destruct H4.
   split;simpl;trivial.

  rewrite <- CorrectBacklinks_new with cn um o;trivial.
  rewrite <- H5;trivial.

  destruct H1.   
  unfold Rac2.Assignables.NewObjectAction.
  simpl.
  trivial.

  apply
   OpRac3.new_object_ok
    with (st1 := st1_rac3) (h' := h') (cn := cn) (um := um);
   trivial.
  destruct H3.
  rewrite <- H4; trivial.

(* ListSteps_nil *)

 exists st_rac3.
 rewrite <- H in |- *.
 split; trivial.
 apply OpRac3.ListSteps_nil; trivial.

(* ListSteps_cons_ok *)

 destruct H1 with st_rac3 as (st1_rac3, Htmp); trivial.
 destruct Htmp.
 destruct H3 with st1_rac3 as (st'_rac3, Htmp); trivial.
 destruct Htmp.
 exists st'_rac3.
 split; trivial.
 apply OpRac3.ListSteps_cons_ok with (e := e) (le := le) (st1 := st1_rac3);
  trivial.

(* expr_stmt_ok *)
 
 destruct H1 with st_rac3 as (st'_rac3, Htmp); trivial.
 destruct Htmp.
 exists st'_rac3.
 split; trivial.
 apply OpRac3.expr_stmt_ok with (v := v) (e := e); trivial.
 destruct H2.
 destruct H2.
 rewrite <- H8 in |- *; trivial.

(* BlockStep_ok_next *)
 
 destruct H1 with st_rac3 as (st1_rac3, Htmp); trivial.
 destruct Htmp.
 set (fr2_rac3 := Rac3.State.Frame.set_pc st1_rac3@fr%rac3 pc') in |- *.
 destruct H4 with st1_rac3[fr := fr2_rac3]%rac3 as (st'_rac3, Htmp); trivial.
  destruct H6.
  rewrite H2 in |- *.
  unfold fr2_rac3 in |- *.
  split; trivial.

  inversion H6.
  split;simpl;trivial.
  
  destruct Htmp.
  exists st'_rac3.
  split; trivial.
  apply
   OpRac3.BlockStep_ok_next
    with (pc' := pc') (st1 := st1_rac3) (fr2 := fr2_rac3); 
   trivial.
  destruct H5.
  destruct H5.
  rewrite <- H13 in |- *.
  trivial.

(* BlockStep_ok_last *)
  
 destruct H1 with st_rac3 as (st'_rac3, Htmp); trivial.
 destruct Htmp.
 exists st'_rac3.
 split; trivial.
 apply OpRac3.BlockStep_ok_last; trivial.
 destruct H2.
 destruct H2.
 rewrite <- H8 in |- *; trivial.
Qed.
