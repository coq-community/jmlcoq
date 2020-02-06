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
Correctness Proof of SEM <-> RAC1

Sem:  st_sem ----- Exec p ------> st'_sem
        |                           |
        | Corr                      | Corr
        |                           |
RAC1: st_rac ----- Exec p ------> st'_rac

Theorem sem_rac1_correct_sem_rac:
forall st_sem, st_rac, st_sem', p,
   Exec p st_sem st'_sem ->
   Corr st_sem st_rac ->
   exists st'_rac,
     Exec p st_rac st'_rac /\
     Corr st'_sem st'_rac.

Theorem sem_rac1_correct_rac_sem:
forall st_rac, st_sem, st_rac', p,
   Exec p st_rac st'_rac ->
   Corr st_sem st_rac ->
   exists st'_sem,
     Exec p st_sem st'_sem /\
     Corr st'_sem st'_rac.
#</pre>#
*)

Require Export JMLRac.
Require Export JMLOpSem.
Require Import List.

Import Dom.
Import Prog.
Import Sem.Notations.

Module OpSem := OperationalSemantics Sem.

Import Rac1.
Import Rac1.Notations.


Module OpRac1 := OperationalSemantics Rac1.

Open Scope rac1_scope.

Theorem sem_rac1_correct_sem_rac:
forall p,
  (forall e st_sem st_sem' s,
  OpSem.ExpressionStep p e st_sem st_sem' s ->
  forall st_rac,
  CorrespondingState p st_rac st_sem ->
  exists st_rac',
  CorrespondingState p st_rac' st_sem' /\
  OpRac1.ExpressionStep p e st_rac st_rac' s)
/\
  (forall l st_sem st_sem' s,
  OpSem.ListSteps p l st_sem st_sem' s ->
  forall st_rac,
  CorrespondingState p st_rac st_sem ->
  exists st_rac',
  CorrespondingState p st_rac' st_sem' /\
  OpRac1.ListSteps p l st_rac st_rac' s)
/\
  (forall m b st_sem st_sem' s,
  OpSem.StatementStep p m b st_sem st_sem' s ->
  forall st_rac,
  CorrespondingState p st_rac st_sem ->
  exists st_rac',
  CorrespondingState p st_rac' st_sem' /\
  OpRac1.StatementStep p m b st_rac st_rac' s)
/\
  (forall m b st_sem st_sem' s,
  OpSem.BlockStep p m b st_sem st_sem' s ->
  forall st_rac,
  CorrespondingState p st_rac st_sem ->
  exists st_rac',
  CorrespondingState p st_rac' st_sem' /\
  OpRac1.BlockStep p m b st_rac st_rac' s).

Proof.

intro p.
apply OpSem.mutual_ind; intros; simpl in *.

(* Case assignment_instance_field_ok *)

 rewrite <- H9 in H10.
 destruct H2 with (st_rac := st_rac) as (st1_rac, H21); trivial.
 destruct H21.
 destruct H5 with (st_rac := st1_rac) as (st2_rac, H61); trivial.
 destruct H61.
 exists (st2_rac) [h := Heap.update (st2_rac) @h loc v].
 split.
  rewrite H10 in |- *.
  unfold CorrespondingState in H14.
  destruct H14.
  split; trivial.
  rewrite H14 in |- *; trivial.
  destruct H14.
  apply
   (OpRac1.assignment_instance_field_ok p e v obj fsig expr target st_rac
      st1_rac st2_rac (st2_rac) [h := Heap.update (st2_rac) @h loc v]
     st2_rac loc cn um); trivial.
   apply
    (Assignables.FieldUpdateCheck_Correct loc p st1_rac st1);
    trivial.
  rewrite <- H14;trivial.
  rewrite <- H14;trivial.
   
(* Case method_vcall_ok *)

 destruct H1 with st_rac as (st1_rac, Htmp); trivial.
 destruct Htmp.
 clear H1.
 destruct H6 with st1_rac as (st2_rac, Htmp); trivial.
 destruct Htmp.
 clear H6.
 set (fr_c1_rac := NewFrame m' (lv2params m' (Ref this0 :: psv)) st2_rac)
  in |- *.
 set (st3_rac := (st2_rac) [fr := fr_c1_rac]) in |- *.
 set (st_c_rac := Assignables.MethodCallAction p c' m' st3_rac) in |- *.
 destruct H15 with st_c_rac as (st_c'_rac, Htmp).
  assert (CorrespondingState p st3_rac st3).
   unfold st3_rac in |- *.
   rewrite H10 in |- *.
   destruct H1.
   split; trivial.
   simpl in |- *.
   apply
    Assignables.NewFrame_Correct
     with
       (m := m')
       (param := lv2params m' (Ref this0 :: psv))
       (st_rac := st2_rac)
       (st_sem := st2); trivial.
   split; trivial.
   
   unfold st_c_rac in |- *.
   rewrite <- H11 in |- *.
   unfold NewFrame in fr_c1_rac.
   unfold Sem.NewFrame in H9.
    apply
     Assignables.MethodCallAction_Correct
      with (c := c') (m := m') (st_rac := st3_rac) (st_sem := st3)
                (st_rac_assignables := st2_rac@fr@assignables)
                (st_rac_fresh := st2_rac@fr@fresh); 
     trivial.
intuition.
rewrite H9 in H10.
rewrite H10.
trivial.

  destruct Htmp.
  set
   (st'_rac :=
    Assignables.MethodReturnAction p st_c'_rac st2_rac) 
   in |- *.
  exists st'_rac.
  split.
   unfold st'_rac in |- *.
   rewrite <- H17 in |- *.
    
    apply
     Assignables.MethodReturnAction_Correct
      with
        st2_rac st_c'_rac
        st2 st_c';trivial.
     
   apply
    (OpRac1.method_vcall_ok p e st_rac st1_rac st2_rac st3_rac st_c_rac
       st_c'_rac st'_rac fr_c1_rac msig o cn um this0 ps
       psnv psv v cn' m' c' b body); trivial.
    destruct H19.
    rewrite <- H19 in |- *.
    trivial.
    
    destruct H6.
    destruct H23.
    rewrite <- H26 in |- *.
    trivial.

(* new_object_ok *)

 set (st1_rac := Assignables.NewObjectAction p o st_rac) in |- *.
 exists (st1_rac) [h := h'].
 split.
  assert (CorrespondingState p st1_rac st1).
   unfold st1_rac in |- *.
   rewrite <- H1 in |- *.
   apply Assignables.NewObjectAction_Correct with  o st_rac st; trivial.
   
  rewrite H2. 
  destruct H4.
   split; trivial.
   
  apply
   OpRac1.new_object_ok
    with (st1 := st1_rac) (h' := h') (cn := cn) (um := um);
   trivial.
  destruct H3.
  rewrite H3 in H0; trivial.

(* ListSteps_nil *)

 exists st_rac.
 rewrite <- H in |- *.
 split; trivial.
 apply OpRac1.ListSteps_nil; trivial.

(* ListSteps_cons_ok *)

 destruct H1 with st_rac as (st1_rac, Htmp); trivial.
 destruct Htmp.
 destruct H3 with st1_rac as (st'_rac, Htmp); trivial.
 destruct Htmp.
 exists st'_rac.
 split; trivial.
 apply OpRac1.ListSteps_cons_ok with (e := e) (le := le) (st1 := st1_rac);
  trivial.

(* expr_stmt_ok *)
 
 destruct H1 with st_rac as (st'_rac, Htmp); trivial.
 destruct Htmp.
 exists st'_rac.
 split; trivial.
 apply OpRac1.expr_stmt_ok with (v := v) (e := e); trivial.
 destruct H2.
 destruct H5.
 rewrite <- H7 in |- *; trivial.

(* BlockStep_ok_next *)
 
 destruct H1 with st_rac as (st1_rac, Htmp); trivial.
 destruct Htmp.
 set (fr2_rac := State.Frame.set_pc (st1_rac) @fr pc') in |- *.
 destruct H4 with (st1_rac) [fr := fr2_rac] as (st'_rac, Htmp); trivial.
  destruct H6.
  split; trivial.
  simpl in |- *.
  rewrite H2 in |- *.
  unfold fr2_rac in |- *.
  destruct H8.
  split; trivial.
  
  destruct Htmp.
  exists st'_rac.
  split; trivial.
  apply
   OpRac1.BlockStep_ok_next
    with (pc' := pc') (st1 := st1_rac) (fr2 := fr2_rac); 
   trivial.
  destruct H5.
  destruct H10.
  rewrite <- H12 in |- *.
  trivial.

(* BlockStep_ok_last *)
  
 destruct H1 with st_rac as (st'_rac, Htmp); trivial.
 destruct Htmp.
 exists st'_rac.
 split; trivial.
 apply OpRac1.BlockStep_ok_last; trivial.
 destruct H2.
 destruct H5.
 rewrite <- H7 in |- *; trivial.
Qed.

Open Scope sem_scope.

Theorem sem_rac1_correct_rac_sem:
forall p,
  (forall e st_rac st_rac' s,
  OpRac1.ExpressionStep p e st_rac st_rac' s ->
  forall st_sem,
  CorrespondingState p st_rac st_sem ->
  exists st_sem',
  CorrespondingState p st_rac' st_sem' /\
  OpSem.ExpressionStep p e st_sem st_sem' s)
/\
  (forall l st_rac st_rac' s,
  OpRac1.ListSteps p l st_rac st_rac' s ->
  forall st_sem,
  CorrespondingState p st_rac st_sem ->
  exists st_sem',
  CorrespondingState p st_rac' st_sem' /\
  OpSem.ListSteps p l st_sem st_sem' s)
/\
  (forall m b st_rac st_rac' s,
  OpRac1.StatementStep p m b st_rac st_rac' s ->
  forall st_sem,
  CorrespondingState p st_rac st_sem ->
  exists st_sem',
  CorrespondingState p st_rac' st_sem' /\
  OpSem.StatementStep p m b st_sem st_sem' s)
/\
  (forall m b st_rac st_rac' s,
  OpRac1.BlockStep p m b st_rac st_rac' s ->
  forall st_sem,
  CorrespondingState p st_rac st_sem ->
  exists st_sem',
  CorrespondingState p st_rac' st_sem' /\
  OpSem.BlockStep p m b st_sem st_sem' s).
Proof.
intro p.
apply OpRac1.mutual_ind; intros; simpl in *.

(* Case assignment_instance_field_ok *)

 unfold Sem.Assignables.FieldUpdateAction in H6.
 rewrite <- H9 in H10.
 replace (st2) [fr := (st2) @fr]%rac1 with st2 in H5 
  by (destruct st2; trivial).
 destruct H2 with (st_sem := st_sem) as (st1_sem, H21); trivial.
 destruct H21.
 destruct H5 with (st_sem := st1_sem) as (st2_sem, H61); trivial.
 destruct H61.
 exists (st2_sem) [h := Heap.update (st2_sem) @h loc v].
 split.
  rewrite H10 in |- *.
  unfold CorrespondingState in H14.
  destruct H14.
  split; trivial.
  rewrite H14 in |- *; trivial.
  destruct H14.
  apply
   (OpSem.assignment_instance_field_ok p e v obj fsig expr target st_sem
      st1_sem st2_sem (st2_sem) [h := Heap.update (st2_sem) @h loc v]
      st2_sem loc cn um); trivial.
   apply (Assignables.FieldUpdateCheck_Correct loc p st1 st1_sem); trivial.
   rewrite H14;trivial.
   rewrite H14;trivial.
   
(* Case method_vcall_ok *)
   
 destruct H1 with st_sem as (st1_sem, Htmp); trivial.
 destruct Htmp.
 clear H1.
 destruct H6 with st1_sem as (st2_sem, Htmp); trivial.
 destruct Htmp.
 clear H6.
 set (fr_c1_sem := Sem.NewFrame m' (lv2params m' (Ref this0 :: psv)) st2_sem)
  in |- *.
 set (st3_sem := (st2_sem) [fr := fr_c1_sem]) in |- *.
 set (st_c_sem := Sem.Assignables.MethodCallAction p c' m' st3_sem)
  in |- *.
 destruct H15 with st_c_sem as (st_c'_sem, Htmp).
  assert (CorrespondingState p st3 st3_sem).
   unfold st3_sem in |- *.
   rewrite H10 in |- *.
   destruct H1.
   split; trivial.
   simpl in |- *.
   apply
    Assignables.NewFrame_Correct
     with
       (m := m')
       (param := lv2params m' (Ref this0 :: psv))
       (st_rac := st2)
       (st_sem := st2_sem); trivial.
   split; trivial.

   unfold st_c_sem in |- *.
   rewrite <- H11 in |- *.
   unfold NewFrame in H9.
   unfold Sem.NewFrame in fr_c1_sem.
    apply
    Assignables.MethodCallAction_Correct
      with (c := c') (m := m') (st_rac := st3) (st_sem := st3_sem) 
                (st_rac_assignables := st2@fr@assignables%rac1)
                (st_rac_fresh := st2@fr@fresh%rac1); 
     trivial.

intuition.
rewrite H9 in H10.
rewrite H10.
trivial.
rewrite H9 in H10.
rewrite H10.
trivial.
    
  destruct Htmp.
  set
   (st'_sem :=
    Sem.Assignables.MethodReturnAction p st_c'_sem st2_sem) 
   in |- *.
  exists st'_sem.
  split.
   unfold st'_sem in |- *.
   rewrite <- H17 in |- *.
    
    apply
     Assignables.MethodReturnAction_Correct
      with
        st2 st_c'
        st2_sem st_c'_sem; trivial.
     
   apply
    (OpSem.method_vcall_ok p e st_sem st1_sem st2_sem st3_sem st_c_sem
       st_c'_sem st'_sem fr_c1_sem msig o cn um this0 ps
       psnv psv v cn' m' c' b body); trivial.
    destruct H19.
    rewrite H19 in |- *.
    trivial.
    
    destruct H6.
    destruct H23.
    rewrite H26 in |- *.
    trivial.

(* new_object_ok *)

 set (st1_sem := Sem.Assignables.NewObjectAction p o st_sem) in |- *.
 exists (st1_sem) [h := h'].
 split.
  rewrite H2.
  assert (CorrespondingState p st1 st1_sem).
   unfold st1_sem in |- *.
   rewrite <- H1.
   apply Assignables.NewObjectAction_Correct with o st st_sem; trivial.
   
   destruct H4.
   split; trivial.

  apply
   OpSem.new_object_ok
    with (st1 := st1_sem) (h' := h') (cn := cn) (um := um);
   trivial.
  destruct H3.
  rewrite <- H3 in H0; trivial.

(* ListSteps_nil *)

 exists st_sem.
 rewrite <- H in |- *.
 split; trivial.
 apply OpSem.ListSteps_nil; trivial.

(* ListSteps_cons_ok *)

 destruct H1 with st_sem as (st1_sem, Htmp); trivial.
 destruct Htmp.
 destruct H3 with st1_sem as (st'_sem, Htmp); trivial.
 destruct Htmp.
 exists st'_sem.
 split; trivial.
 apply OpSem.ListSteps_cons_ok with (e := e) (le := le) (st1 := st1_sem);
  trivial.

(* expr_stmt_ok *)

 destruct H1 with st_sem as (st'_sem, Htmp); trivial.
 destruct Htmp.
 exists st'_sem.
 split; trivial.
 apply OpSem.expr_stmt_ok with (v := v) (e := e); trivial.
 destruct H2.
 destruct H5.
 rewrite H7 in |- *; trivial.

(* BlockStep_ok_next *)

 destruct H1 with st_sem as (st1_sem, Htmp); trivial.
 destruct Htmp.
 set (fr2_sem := Sem.State.Frame.set_pc (st1_sem) @fr pc') in |- *.
 destruct H4 with (st1_sem) [fr := fr2_sem] as (st'_sem, Htmp); trivial.
  destruct H6.
  split; trivial.
  simpl in |- *.
  rewrite H2 in |- *.
  unfold fr2_sem in |- *.
  destruct H8.
  split; trivial.
  
  destruct Htmp.
  exists st'_sem.
  split; trivial.
  apply
   OpSem.BlockStep_ok_next
    with (pc' := pc') (st1 := st1_sem) (fr2 := fr2_sem); 
   trivial.
  destruct H5.
  destruct H10.
  rewrite H12 in |- *.
  trivial.

(* BlockStep_ok_last *)

 destruct H1 with st_sem as (st'_sem, Htmp); trivial.
 destruct Htmp.
 exists st'_sem.
 split; trivial.
 apply OpSem.BlockStep_ok_last; trivial.
 destruct H2.
 destruct H5.
 rewrite H7 in |- *; trivial.
Qed.
