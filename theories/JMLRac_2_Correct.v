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
Correctness Proof of RAC1 <-> RAC2

Sem:  st_rac1 ----- Exec p ------> st'_rac1
        |                           |
        | Corr                      | Corr
        |                           |
RAC1: st_rac2 ----- Exec p ------> st'_rac2

#</pre>#
*)

Require Export JMLRac2.
Require Export JMLOpSem.
Require Import List.
Require Import Min.

Import Dom.
Import Prog.
Import Sem.Notations.
Import Rac1.Notations.
Import Rac2.Notations.
Import Stack.

Module OpRac1 := OperationalSemantics Rac1.
Module OpRac2 := OperationalSemantics Rac2.

Import Rac2.
Import Assignables.

Open Scope rac2_scope.

Theorem rac2_length_assignables_correct:
forall p,
  (forall e st st' s,
  OpRac2.ExpressionStep p e st st' s ->
  (length st@fr@assignables) = (length st'@fr@assignables))
/\
  (forall l st st' s,
  OpRac2.ListSteps p l st st' s ->
  (length st@fr@assignables) = (length st'@fr@assignables))
/\
  (forall m b st st' s,
  OpRac2.StatementStep p m b st st' s ->
  (length st@fr@assignables) = (length st'@fr@assignables))
/\
  (forall m b st st' s,
  OpRac2.BlockStep p m b st st' s ->
  (length st@fr@assignables) = (length st'@fr@assignables)).
Proof.
intro p.
apply OpRac2.mutual_ind; intros; simpl in *; subst; trivial.
 simpl.
 unfold Assignables.FieldUpdateAction.
 case isPivot.
  simpl.
  rewrite map_length.
  rewrite H2.
  assumption.
  
  rewrite H2.
  assumption.
  
 simpl.
 rewrite H1.
 rewrite H6.
 simpl in H15.
 apply eq_add_S.
 rewrite H15.
 unfold pop.
 destruct st_c' @fr @assignables.
  discriminate H15.
  
  trivial.
  
 rewrite H1.
 assumption.
 
 rewrite H1.
 assumption.
Qed.

Theorem rac2_equiv_assignables_correct:
forall p,
  (forall e st st' s,
  OpRac2.ExpressionStep p e st st' s ->
  EquivAssignables p st st')
/\
  (forall l st st' s,
  OpRac2.ListSteps p l st st' s ->
  EquivAssignables p st st')
/\
  (forall m b st st' s,
  OpRac2.StatementStep p m b st st' s ->
  EquivAssignables p st st')
/\
  (forall m b st st' s,
  OpRac2.BlockStep p m b st st' s ->
  EquivAssignables p st st').
Proof.
generalize rac2_length_assignables_correct.
intros.
specialize H with p.
destruct H.
destruct H0.
destruct H1.
apply OpRac2.mutual_ind; intros; simpl in *.
 apply EquivAssignables_trans with st1; trivial.
  apply EquivAssignables_trans with st2; trivial.
   rewrite H14.
   apply FieldUpdateAction_Equiv; auto.
   
   rewrite H14.
   rewrite <- H13.
   simpl.
   unfold FieldUpdateAction.
   case isPivot.
    simpl.
    rewrite map_length.
    apply le_min_r.
    
    apply le_min_r.
    
  apply H in H5.
  rewrite H5.
  apply le_min_l.
  
 apply EquivAssignables_trans with st1; trivial.
  apply EquivAssignables_trans with st2; trivial.

   assert (EquivAssignables p st2 st_c).

unfold NewFrame in H13.
unfold MethodCallAction in H15.
unfold EquivAssignables.
rewrite H13 in H14.
rewrite H14 in H15.
simpl in H15.
rewrite <- H15.
simpl.
unfold level.
simpl.
rewrite nat_compare_n_Sn.
rewrite truncate_same.
apply EquivAssignables_ind_refl.

    apply EquivAssignables_trans with st_c'; trivial.
     apply EquivAssignables_trans with st_c; trivial.
      
     apply H2 in H18.
     rewrite H18.
     apply le_min_r.
      
     rewrite <- H21.
     apply MethodReturnAction_Equiv with st2; auto.
     
     rewrite <- H21.
     unfold MethodReturnAction.
     simpl.
     unfold pop.
     case st_c' @fr @assignables.
      auto with *.
      
      intros.
      simpl.
      auto with *.
      
   apply H0 in H9.
   rewrite H9.
   apply le_min_l.
   
  apply H in H4.
  rewrite H4.
  apply le_min_l.

 apply EquivAssignables_trans with (st' := st1); trivial.
  apply NewObjectAction_Equiv with o; auto.
  
  rewrite H6.
  apply EquivAssignables_3 with (Heap.ObjectObject cn um) o.
  replace st1 @h with st @h ; trivial.
  rewrite <- H5.
  trivial.
  
  rewrite H6.
  simpl.
  apply le_min_r.
  
 rewrite H3.
 apply EquivAssignables_refl.
 
 apply EquivAssignables_trans with st1; trivial.
 apply H0 in H6.
 rewrite H6.
 apply le_min_r.
 
 trivial.
 
 apply EquivAssignables_trans with st1; trivial.
  apply EquivAssignables_trans with st1 [fr := fr2]; trivial.
   unfold EquivAssignables.
   rewrite H6.
   simpl.
   unfold level.
   rewrite nat_compare_n_n.
   apply EquivAssignables_ind_refl.
   
   rewrite H6.
   simpl.
   apply le_min_l.
   
  apply H1 in H4.
  rewrite H4.
  apply le_min_l.
  
 trivial.
Qed.


Theorem rac2_rac1_correct:
forall p,
  (forall e st_rac2 st'_rac2 r,
  OpRac2.ExpressionStep p e st_rac2 st'_rac2 r ->
  forall st_rac1,
  CorrespondingState p st_rac1 st_rac2 ->
  exists st'_rac1,
  CorrespondingState p st'_rac1 st'_rac2 /\
  OpRac1.ExpressionStep p e st_rac1 st'_rac1 r)
/\
  (forall l st_rac2 st'_rac2 r,
  OpRac2.ListSteps p l st_rac2 st'_rac2 r ->
  forall st_rac1,
  CorrespondingState p st_rac1 st_rac2 ->
  exists st'_rac1,
  CorrespondingState p st'_rac1 st'_rac2 /\
  OpRac1.ListSteps p l st_rac1 st'_rac1 r)
/\
  (forall m b st_rac2 st'_rac2 r,
  OpRac2.StatementStep p m b st_rac2 st'_rac2 r ->
  forall st_rac1,
  CorrespondingState p st_rac1 st_rac2 ->
  exists st'_rac1,
  CorrespondingState p st'_rac1 st'_rac2 /\
  OpRac1.StatementStep p m b st_rac1 st'_rac1 r)
/\
  (forall m b st_rac2 st'_rac2 r,
  OpRac2.BlockStep p m b st_rac2 st'_rac2 r ->
  forall st_rac1,
  CorrespondingState p st_rac1 st_rac2->
  exists st'_rac1,
  CorrespondingState p st'_rac1 st'_rac2 /\
  OpRac1.BlockStep p m b st_rac1 st'_rac1 r).
Proof.

intro p.
apply OpRac2.mutual_ind; intros; simpl in *.



(* Case assignment_instance_field_ok *)

 apply H2 in H11.
destruct H11 as[st1_rac1 H11].
destruct H11.
destruct H5 with st1_rac1 as [st2_rac1 H13];trivial.
destruct H13.
set (st'_rac1 := Rac1.Assignables.FieldUpdateAction p loc v st2_rac1).
exists ((st'_rac1[h := Heap.update st2_rac1@h loc v])%rac1).
split.
rewrite H10.
apply FieldUpdateAction_Correct;trivial.
inversion H13.
  apply
   (OpRac1.assignment_instance_field_ok p e v obj fsig expr target st_rac1
      st1_rac1 st2_rac1 st2_rac1[h := Heap.update st2_rac1@h loc v]%rac1
      st2_rac1 loc cn um); trivial.
   apply
    (FieldUpdateCheck_Correct loc p st1_rac1 st1);
    trivial.
rewrite H23;trivial.
rewrite H23;trivial.

   
(* Case method_vcall_ok *)

 destruct H1 with st_rac1 as (st1_rac1, Htmp); trivial.
 destruct Htmp.
 clear H1.
 destruct H6 with st1_rac1 as (st2_rac1, Htmp); trivial.
 destruct Htmp.
 clear H6.
 set (fr_c1_rac1 := Rac1.NewFrame m' (lv2params m' (Ref this0 :: psv)) st2_rac1)
  in |- *.
 set (st3_rac1 := st2_rac1[fr := fr_c1_rac1]%rac1) in |- *.
 set (st_c_rac1 := Rac1.Assignables.MethodCallAction p c' m' st3_rac1) in |- *.
 destruct H15 with st_c_rac1 as (st_c'_rac1, Htmp).
  assert (CorrespondingState p st3_rac1 st3).

   unfold st3_rac1 in |- *.
   rewrite H10 in |- *.
   
   apply
    NewFrame_Correct
     with
       (m := m')
       (param := lv2params m' (Ref this0 :: psv))
       (st_rac1 := st2_rac1)
       (st_rac2 := st2); trivial.
   
   unfold st_c_rac1 in |- *.
   rewrite <- H11.
    apply
     MethodCallAction_Correct
      with (c := c') (m := m') (st_rac1 := st3_rac1) (st_rac2 := st3); 
     trivial.
    
  destruct Htmp.

  set
   (st'_rac1 :=
    Rac1.Assignables.MethodReturnAction p st_c'_rac1 st2_rac1) 
   in |- *.
  exists st'_rac1.
  split.
   unfold st'_rac1 in |- *.
   rewrite <- H17 in |- *.
    
generalize rac2_length_assignables_correct.
intros.
specialize H23 with p.
      destruct H23.
      destruct H24.
      destruct H25.


    apply
     MethodReturnAction_Correct
      with
        st2_rac1 st_c'_rac1
        st2 st_c'; trivial.
        assert (EquivAssignables p st2 st_c).
   
    unfold NewFrame in H9.
unfold MethodCallAction in H11.
unfold EquivAssignables.
rewrite H9 in H10.
rewrite H10 in H11.
simpl in H11.
rewrite <- H11.
simpl.
unfold level.
simpl.
rewrite nat_compare_n_Sn.
rewrite truncate_same.
apply EquivAssignables_ind_refl.

     apply EquivAssignables_trans with st_c; trivial.
      generalize rac2_equiv_assignables_correct.
      intros.
      specialize H28 with p.
      destruct H28.
      destruct H29.
      destruct H30.
      apply H31 in H14.
      trivial.
apply H26 in H14.
rewrite H14.
apply le_min_r.

apply H26 in H14.
rewrite <- H14.
rewrite <- H11.
rewrite H10.
rewrite H9.
simpl.
trivial.
   apply
    (OpRac1.method_vcall_ok p e st_rac1 st1_rac1 st2_rac1 st3_rac1 st_c_rac1
       st_c'_rac1 st'_rac1 fr_c1_rac1 msig o cn um this0 ps
       psnv psv v cn' m' c' b body); trivial.
    destruct H19.
    rewrite H30;trivial.
    
    destruct H6.
    rewrite H25.
    trivial.

(* new_object_ok *)

 set (st1_rac1 := Rac1.Assignables.NewObjectAction p o st_rac1) in |- *.
 exists st1_rac1[h := h']%rac1.
 split.
  rewrite H2 in |- *.
  assert (CorrespondingState p st1_rac1 st1).
   unfold st1_rac1 in |- *.
   rewrite <- H1 in |- *.
   apply NewObjectAction_Correct with o st_rac1 st; trivial.

   destruct H4.
   split;simpl;trivial.
destruct H11.
split.
trivial.
intros.

  generalize UnfoldDatagroups_rac_intersect_new.
  intros.
specialize H11 with p st_rac2@h (Heap.ObjectObject cn um) st_rac2@fr o h' n.
replace st@h with st_rac2@h in H0.
apply H11 in H0.
generalize H0.
specialize e1 with n.
generalize e1.
apply LocSet.eq_trans.
rewrite <- H1.
simpl.
trivial.

  apply
   OpRac1.new_object_ok
    with (st1 := st1_rac1) (h' := h') (cn := cn) (um := um);
   trivial.
  destruct H3.
  rewrite H11; trivial.

(* ListSteps_nil *)

 exists st_rac1.
 rewrite <- H in |- *.
 split; trivial.
 apply OpRac1.ListSteps_nil; trivial.

(* ListSteps_cons_ok *)

 destruct H1 with st_rac1 as (st1_rac1, Htmp); trivial.
 destruct Htmp.
 destruct H3 with st1_rac1 as (st'_rac1, Htmp); trivial.
 destruct Htmp.
 exists st'_rac1.
 split; trivial.
 apply OpRac1.ListSteps_cons_ok with (e := e) (le := le) (st1 := st1_rac1);
  trivial.

(* expr_stmt_ok *)
 
 destruct H1 with st_rac1 as (st'_rac1, Htmp); trivial.
 destruct Htmp.
 exists st'_rac1.
 split; trivial.
 apply OpRac1.expr_stmt_ok with (v := v) (e := e); trivial.
 destruct H2.
 destruct H5.
 rewrite H6 in |- *; trivial.

(* BlockStep_ok_next *)
 
 destruct H1 with st_rac1 as (st1_rac1, Htmp); trivial.
 destruct Htmp.
 set (fr2_rac1 := Rac1.State.Frame.set_pc st1_rac1@fr%rac1 pc') in |- *.
 destruct H4 with st1_rac1[fr := fr2_rac1]%rac1 as (st'_rac1, Htmp); trivial.
  destruct H6.
  rewrite H2 in |- *.
  unfold fr2_rac1 in |- *.
  split; trivial.
  
  destruct Htmp.
  exists st'_rac1.
  split; trivial.
  apply
   OpRac1.BlockStep_ok_next
    with (pc' := pc') (st1 := st1_rac1) (fr2 := fr2_rac1); 
   trivial.
  destruct H5.
  rewrite H11 in |- *.
  trivial.

(* BlockStep_ok_last *)
  
 destruct H1 with st_rac1 as (st'_rac1, Htmp); trivial.
 destruct Htmp.
 exists st'_rac1.
 split; trivial.
 apply OpRac1.BlockStep_ok_last; trivial.
 destruct H2.
 rewrite H6 in |- *; trivial.
Qed.

Theorem rac1_rac2_correct:
forall p,
  (forall e st_rac1 st'_rac1 r,
  OpRac1.ExpressionStep p e st_rac1 st'_rac1 r ->
  forall st_rac2,
  CorrespondingState p st_rac1 st_rac2 ->
  exists st'_rac2,
  CorrespondingState p st'_rac1 st'_rac2 /\
  OpRac2.ExpressionStep p e st_rac2 st'_rac2 r)
/\
  (forall l st_rac1 st'_rac1 r,
  OpRac1.ListSteps p l st_rac1 st'_rac1 r ->
  forall st_rac2,
  CorrespondingState p st_rac1 st_rac2 ->
  exists st'_rac2,
  CorrespondingState p st'_rac1 st'_rac2 /\
  OpRac2.ListSteps p l st_rac2 st'_rac2 r)
/\
  (forall m b st_rac1 st'_rac1 r,
  OpRac1.StatementStep p m b st_rac1 st'_rac1 r ->
  forall st_rac2,
  CorrespondingState p st_rac1 st_rac2 ->
  exists st'_rac2,
  CorrespondingState p st'_rac1 st'_rac2 /\
  OpRac2.StatementStep p m b st_rac2 st'_rac2 r)
/\
  (forall m b st_rac1 st'_rac1 r,
  OpRac1.BlockStep p m b st_rac1 st'_rac1 r ->
  forall st_rac2,
  CorrespondingState p st_rac1 st_rac2->
  exists st'_rac2,
  CorrespondingState p st'_rac1 st'_rac2 /\
  OpRac2.BlockStep p m b st_rac2 st'_rac2 r).
Proof.

intro p.
apply OpRac1.mutual_ind; intros; simpl in *.



(* Case assignment_instance_field_ok *)

apply H2 in H11.
destruct H11 as[st1_rac2 H11].
destruct H11.
destruct H5 with st1_rac2 as [st2_rac2 H13];trivial.
destruct H13.
set (st'_rac2 := FieldUpdateAction p loc v st2_rac2).
exists ((st'_rac2[h := Heap.update st2_rac2@h loc v])).
split.
rewrite H10.
apply FieldUpdateAction_Correct;trivial.
inversion H13.
  apply
   (OpRac2.assignment_instance_field_ok p e v obj fsig expr target st_rac2
      st1_rac2 st2_rac2 st'_rac2[h := Heap.update st2_rac2@h loc v]
      st'_rac2 loc cn um); trivial.
   apply
    (FieldUpdateCheck_Correct loc p st1 st1_rac2);
    trivial.
rewrite <- H23;trivial.
rewrite <- H23;trivial.
   
(* Case method_vcall_ok *)

 destruct H1 with st_rac2 as (st1_rac2, Htmp); trivial.
 destruct Htmp.
 clear H1.
 destruct H6 with st1_rac2 as (st2_rac2, Htmp); trivial.
 destruct Htmp.
 clear H6.
 set (fr_c1_rac2 := NewFrame m' (lv2params m' (Ref this0 :: psv)) st2_rac2)
  in |- *.
 set (st3_rac2 := st2_rac2[fr := fr_c1_rac2]) in |- *.
 set (st_c_rac2 := MethodCallAction p c' m' st3_rac2) in |- *.
 destruct H15 with st_c_rac2 as (st_c'_rac2, Htmp).
  assert (CorrespondingState p st3 st3_rac2).

   unfold st3_rac2 in |- *.
   rewrite H10 in |- *.
   
   apply
    NewFrame_Correct
     with
       (m := m')
       (param := lv2params m' (Ref this0 :: psv))
       (st_rac1 := st2)
       (st_rac2 := st2_rac2); trivial.
   
   unfold st_c_rac2 in |- *.
   rewrite <- H11.
    apply
     MethodCallAction_Correct
      with (c := c') (m := m') (st_rac1 := st3) (st_rac2 := st3_rac2); 
     trivial.
    
  destruct Htmp.

  set
   (st'_rac2 :=
    MethodReturnAction p st_c'_rac2 st2_rac2) 
   in |- *.
  exists st'_rac2.
  split.
   unfold st'_rac2 in |- *.
   rewrite <- H17 in |- *.
    
generalize rac2_length_assignables_correct.
intros.
specialize H23 with p.
      destruct H23.
      destruct H24.
      destruct H25.


    apply
     MethodReturnAction_Correct
      with
        st2 st_c'
        st2_rac2 st_c'_rac2; trivial.
        assert (EquivAssignables p st2_rac2 st_c_rac2).
   unfold fr_c1_rac2 in st3_rac2.
unfold st3_rac2 in st_c_rac2.
unfold st_c_rac2.
unfold EquivAssignables.
unfold MethodCallAction.
unfold NewFrame.
simpl.
unfold level.
simpl.
rewrite nat_compare_n_Sn.
rewrite truncate_same.
apply EquivAssignables_ind_refl.

     apply EquivAssignables_trans with st_c_rac2; trivial.
      generalize rac2_equiv_assignables_correct.
      intros.
      specialize H28 with p.
      destruct H28.
      destruct H29.
      destruct H30.
      apply H31 in H22.
      trivial.
apply H26 in H22.
rewrite H22.
apply le_min_r.

apply H26 in H22.
rewrite <- H22.
unfold st_c_rac2.
unfold st3_rac2.
simpl.
trivial.
   apply
    (OpRac2.method_vcall_ok p e st_rac2 st1_rac2 st2_rac2 st3_rac2 st_c_rac2
       st_c'_rac2 st'_rac2 fr_c1_rac2 msig o cn um this0 ps
       psnv psv v cn' m' c' b body); trivial.
    destruct H19.
    rewrite <- H30;trivial.
    
    destruct H6.
    rewrite <- H25.
    trivial.

(* new_object_ok *)

 set (st1_rac2 := NewObjectAction p o st_rac2) in |- *.
 exists st1_rac2[h := h'].
 split.
  assert (CorrespondingState p st1 st1_rac2).
   unfold st1_rac2 in |- *.
   rewrite <- H1 in |- *.
   apply NewObjectAction_Correct with o st st_rac2; trivial.
   rewrite H2.
   destruct H4.
   split;simpl;trivial.
destruct H11.
split;trivial.
intros.
  generalize UnfoldDatagroups_rac_intersect_new.
  intros.
specialize H11 with p st_rac0@h (Heap.ObjectObject cn um) st_rac0@fr o h' n.
replace st@h%rac1 with st_rac1@h%rac1 in H0.
rewrite H12 in H0.
apply H11 in H0.
generalize H0.
specialize e1 with n.
generalize e1.
apply LocSet.eq_trans.
rewrite <- H1.
simpl.
trivial.

  apply
   OpRac2.new_object_ok
    with (st1 := st1_rac2) (h' := h') (cn := cn) (um := um);
   trivial.
  destruct H3.
  rewrite <- H11; trivial.

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
 destruct H5.
 rewrite <- H6 in |- *; trivial.

(* BlockStep_ok_next *)
 
 destruct H1 with st_rac2 as (st1_rac2, Htmp); trivial.
 destruct Htmp.
 set (fr2_rac2 := Frame.set_pc st1_rac2@fr pc') in |- *.
 destruct H4 with st1_rac2[fr := fr2_rac2] as (st'_rac2, Htmp); trivial.
  destruct H6.
  rewrite H2 in |- *.
  unfold fr2_rac2 in |- *.
  split; trivial.
  
  destruct Htmp.
  exists st'_rac2.
  split; trivial.
  apply
   OpRac2.BlockStep_ok_next
    with (pc' := pc') (st1 := st1_rac2) (fr2 := fr2_rac2); 
   trivial.
  destruct H5.
  rewrite <- H11 in |- *.
  trivial.

(* BlockStep_ok_last *)
  
 destruct H1 with st_rac2 as (st'_rac2, Htmp); trivial.
 destruct Htmp.
 exists st'_rac2.
 split; trivial.
 apply OpRac2.BlockStep_ok_last; trivial.
 destruct H2.
 rewrite <- H6 in |- *; trivial.
Qed.
