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

Require Export JMLRac.
Require Import Min.
Require Import List.
Require Import Stack.
Require Import ListSet.
Require Import Bool.
Require Import ZArith.
Require Import Relation_Operators.
Require Import ListHelpers.
Require Import Classical.

  Import Dom.
  Import Prog.
  Import JmlNotations.
  Import METHODSPEC.
  Import TYPESPEC.

  Open Scope jml_scope.

(** * The JML Runtime Assertion Checker Rac2
This module describes the runtime assertions checks for suported JML-Level 0 constructs *)

Module Rac2 <: JML.

(** ** Implementation of the JML Frame for Rac2 *)

Module FrameAdds <: ADDS.

  Record t_rec : Type := make {
                     (* invalid pivots * assignable locations *)
    assignables: stack (LocSet.t * LocSet.t);
    fresh : stack ObjSet.t;
    pre : Heap.t * ParamDict.t;
    quants : VarDict.t
  }.

  Definition t := t_rec.

  Parameter empty : t.

  Definition set_pre (fr : t) (h : Heap.t) (p : ParamDict.t) : t :=
    make (assignables fr) (fresh fr) (h, p) (quants fr).

  Definition set_assignables (fr : t) (x : stack (LocSet.t * LocSet.t)) : t :=
    make x (fresh fr) (pre fr) (quants fr).

  Definition replace_top_assignables (fr : t) (elem : LocSet.t * LocSet.t) : t :=
    set_assignables fr (replace_top elem (assignables fr)).

  Definition pop_assignables (fr : t) : t :=
    set_assignables fr (pop (assignables fr)).

  Definition set_fresh (fr : t) (x : stack ObjSet.t) : t :=
    make (assignables fr) x (pre fr) (quants fr).
  Definition add_fresh (fr : t) (x : Object) : t :=
    set_fresh fr (apply_top (ObjSet.add x) (fresh fr)).
  Definition union_fresh (fr : t) (x : ObjSet.t) : t :=
    set_fresh fr (apply_top (ObjSet.union x) (fresh fr)).

  Definition set_quants (fr : t) (x : VarDict.t) : t :=
    make (assignables fr) (fresh fr) (pre fr) x.
  Definition quant (fr : t) (x : Var) : option Value :=
    VarDict.get (quants fr) x.
  Definition set_quant (fr : t) (x : Var) (v : Value) : t :=
    set_quants fr (VarDict.update (quants fr) x v).

  Definition pre_heap (fr : t) : Heap.t :=
    fst (pre fr).

End FrameAdds.

Module Adds := Sem.Adds.

Declare Module Frame : FRAME with Module Adds := FrameAdds.
Declare Module State : STATE 
  with Module Frame := Frame 
  with Module Adds := Adds.

Module Notations.

  Declare Scope rac2_scope.
  Delimit Scope rac2_scope with rac2.

  Open Scope rac2_scope.

  Notation "st '@h'" := (State.h st) (at level 1, left associativity): rac2_scope.
  Notation "st '@fr'" := (State.fr st) (at level 1, left associativity) : rac2_scope.
  Notation "st '@adds'" := (State.adds st) (at level 1, left associativity) : rac2_scope.

  Notation "st '[h' ':=' h ']'" := (State.set_h st h) (at level 1, left associativity): rac2_scope.
  Notation "st '[fr' ':=' fr ']'" := (State.set_fr st fr) (at level 1, left associativity) : rac2_scope.
  Notation "st '[adds' ':=' adds ']'" := (State.set_adds st adds) (at level 1, left associativity) : rac2_scope.

  Notation "[ h , fr , adds ]" := (State.build h fr adds) : rac2_scope.

  Notation "fr '@params'" := (Frame.params fr) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@vars'" := (Frame.vars fr) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@pc'" := (Frame.pc fr) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@ret'" := (Frame.ret fr) (at level 1, left associativity) : rac2_scope.

  Notation "fr '@fradds'" := (Frame.adds fr) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@pre'" := (FrameAdds.pre (Frame.adds fr)) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@preheap'" := (fst (fr@pre)) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@preparams'" := (snd (fr@pre)) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@assignables'" := (FrameAdds.assignables (Frame.adds fr)) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@fresh'" := (FrameAdds.fresh (Frame.adds fr)) (at level 1, left associativity) : rac2_scope.
  Notation "fr '@quants'" := (FrameAdds.quants (Frame.adds fr)) (at level 1, left associativity) : rac2_scope.

  Notation "fr '[fradds' ':=' adds ']'" := (Frame.set_adds fr adds) (at level 1, left associativity): rac2_scope.
  Notation "fr '[quants' ':=' q ']'" := ( fr[fradds := (FrameAdds.set_quants fr@fradds q)]) (at level 1, left associativity) : rac2_scope.
  Notation "fr '[assignables' ':=' a ']'" := ( fr[fradds := (FrameAdds.set_assignables fr@fradds a)]) (at level 1, left associativity) : rac2_scope.
  Notation "fr '[assignables' ':+' elem ']'" := ( fr[fradds := (FrameAdds.replace_top_assignables fr@fradds elem)]) (at level 1, left associativity) : rac2_scope.
  Notation "fr '[assignables' '--' ']'" := ( fr[fradds := (FrameAdds.pop_assignables fr@fradds)]) (at level 1, left associativity) : rac2_scope. 
  Notation "fr '[fresh' ':=' f ']'" := ( fr[fradds := (FrameAdds.set_fresh fr@fradds f)]) (at level 1, left associativity) : rac2_scope.
  Notation "fr '[fresh' ':\/' f ']'" := ( fr[fradds := (FrameAdds.union_fresh fr@fradds f)]) (at level 1, left associativity) : rac2_scope.
  Notation "fr '[fresh' ':+' f ']'" := ( fr[fradds := (FrameAdds.add_fresh fr@fradds f)]) (at level 1, left associativity) : rac2_scope.

End Notations.

Import Sem.Notations.
Import Rac1.Notations.
Import Notations.

Open Scope nat_scope.

(** A new JML Frame is initialized with the assignable locations from the caller *)
Definition NewFrame (m : Method) (p : ParamDict.t) (st : State.t) : Frame.t :=
  let adds := FrameAdds.make  ((LocSet.empty,LocSetAll)::st@fr@assignables)  (ObjSet.empty::st@fr@fresh) (st@h , p) VarDict.empty in
  Frame.build m p adds.

Inductive FieldInDg_rac (p : Program) (h : Heap.t) (ep : LocSet.t): (* field *) Location -> (* dg *) Location -> Prop :=
  | FieldInDg_rac_step : forall field dg dg',
    FieldInDg_rac p h ep dg' dg ->
    FieldInDg_rac p h ep field dg' ->
    FieldInDg_rac p h ep field dg
  | FieldInDg_rac_static : forall field dg,
    direct_FieldInDg_static p field dg ->
    FieldInDg_rac p h ep field dg
  | FieldInDg_rac_dynamic : forall field dg pivot,
    direct_FieldInDg_dynamic p h field dg pivot ->
    ~ LocSet.In pivot ep ->
    FieldInDg_rac p h ep field dg
  | FieldInDg_rac_same : forall field dg, 
    field = dg ->  
    FieldInDg_rac p h ep field dg.

Lemma FieldInDg_rac_1:
  forall p h f dg,
  FieldInDg p h f dg <-> FieldInDg_rac p h LocSet.empty f dg.
Proof.

intros.
split; intro.
 induction H.
  apply FieldInDg_rac_step with dg';trivial.
  apply FieldInDg_rac_static; trivial.
  apply FieldInDg_rac_dynamic with pivot; trivial.
  apply LocSet.empty_1.
  apply FieldInDg_rac_same; trivial.
  
 induction H.
  apply FieldInDg_step with dg';trivial.
  apply FieldInDg_static; trivial.
  apply FieldInDg_dynamic with pivot; trivial.
  apply FieldInDg_same; trivial.
Qed.

Lemma init_value_not_ref:
forall f r,
init_value (FIELDSIGNATURE.type (FIELD.signature f))
     <> Ref r.
Proof.
intros.
intro.
unfold init_value in H.
destruct (FIELDSIGNATURE.type (FIELD.signature f)).
 discriminate H.
 
 destruct pt; discriminate H.
Qed.

Lemma init_field_value_not_ref:
forall f r,
init_field_value f <> Ref r.
Proof.
intros.
intro.
unfold init_field_value in H.
destruct (FIELD.initValue f).
 destruct e; try discriminate H; try destruct l; try discriminate H;
  try destruct b; try discriminate H; elim init_value_not_ref with f r;
  trivial.
 
 elim init_value_not_ref with f r; trivial.
Qed.

Lemma new_object_field_not_ref:
forall h p lt obj fsig loc h' r,
Heap.new h p lt = Some (obj, h') ->
loc = Heap.InstanceField obj fsig ->
Heap.get h' loc  <> Some (Ref r).
Proof.
intros.
destruct lt.
 elim classic with (defined_field p c fsig).
  intros.
  destruct H1 as (f, H1).
  generalize Heap.new_defined_object_field.
  intro.
  specialize H2 with h p c u fsig f obj h'.
  rewrite H0.
  rewrite H2; trivial.
  intro.
  inversion H3.
  elim init_field_value_not_ref with f r; trivial.
  
  intro.
  generalize Heap.new_undefined_object_field.
  intro.
  specialize H2 with h p c u fsig obj h'.
  rewrite H0.
  rewrite H2; trivial.
  intro.
  discriminate H3.
  
 intro.
 generalize Heap.get_uncompat.
 intro.
 specialize H2 with h' loc.
 rewrite H2 in H1.
  discriminate H1.
  
  clear H2.
  intro.
  destruct H2.
   discriminate H0.
   
   inversion H0.
   subst.
   generalize Heap.new_typeof.
   intro.
   apply H3 in H.
   rewrite H in H2.
   inversion H2.
   
   discriminate H0.
Qed.

Lemma FieldInDg_rac_2:
forall p h h' lt obj pivots a dg,
Heap.new h p lt = Some (obj, h') ->
(FieldInDg_rac p h pivots a dg 
  <->
FieldInDg_rac p h' pivots a dg).
Proof.
split; intros.
 induction H0.
  apply FieldInDg_rac_step with dg'; trivial.
  
  apply FieldInDg_rac_static; trivial.
  
  apply FieldInDg_rac_dynamic with pivot; trivial.
  destruct H0.
  split
   with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg;
   trivial.
  rewrite <- H4.
  destruct lt.
   apply Heap.new_object_no_change with p c u obj; trivial.
   intro.
   intro.
   rewrite H3 in H11.
   inversion H11.
   subst.
   generalize Heap.new_fresh_location.
   intro.
   apply H0 in H.
   clear H0.
   generalize Heap.get_uncompat.
   intro.
   assert (~Heap.Compat h (Heap.InstanceField obj fs)).
    intro.
    inversion H2.
    subst.
    rewrite H in H10.
    discriminate H10.
    
    apply H0 in H2.
    rewrite H4 in H2.
    discriminate H2.
    
   apply Heap.new_array_no_change with p t s u obj; trivial.
   intros.
   rewrite H3.
   intro.
   discriminate H11.
   
  subst.
  apply FieldInDg_rac_same.
  trivial.
  
 induction H0.
  apply FieldInDg_rac_step with dg'; trivial.
  
  apply FieldInDg_rac_static; trivial.
  
  apply FieldInDg_rac_dynamic with pivot; trivial.
  destruct H0.
  split
   with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg;
   trivial.
  elim classic with (obj = pivot_obj); intro.
   generalize new_object_field_not_ref.
   intro.
   specialize H12 with h p lt obj pivot_fsig pivot_loc h' field_obj.
   apply H12 in H.
    elim H; trivial.
    
    rewrite H11; trivial.
    
   rewrite <- H4.
   symmetry .
   destruct lt.
    apply Heap.new_object_no_change with p c u obj; trivial.
    intros.
    rewrite H3.
    intro.
    elim H11.
    inversion H12.
    trivial.
    
    apply Heap.new_array_no_change with p t s u obj; trivial.
    intros.
    rewrite H3.
    intro.
    discriminate H12.
    
  subst.
  apply FieldInDg_rac_same.
  trivial.
Qed.

Parameter UnfoldDatagroup_rac: Program -> Heap.t ->(* excl pivots *) LocSet.t -> Location -> LocSet.t.
  Axiom UnfoldDatagroup_rac_def:  forall p h ep dg f, 
    LocSet.In f (UnfoldDatagroup_rac p h ep dg) <-> 
    FieldInDg_rac p h ep f dg.

Lemma UnfoldDatagroup_rac_1:
  forall p h dg f,
  LocSet.In f (UnfoldDatagroup p h dg) <->
  LocSet.In f (UnfoldDatagroup_rac p h LocSet.empty dg).
Proof.
intros.
split; intros.
 apply <- UnfoldDatagroup_rac_def.
 apply UnfoldDatagroup_def in H.
 rewrite <- FieldInDg_rac_1 in |- *; trivial.
 
 apply <- UnfoldDatagroup_def.
 apply UnfoldDatagroup_rac_def in H.
 rewrite FieldInDg_rac_1 in |- *; trivial.
Qed.

Parameter UnfoldDatagroups_rac: Program -> Heap.t -> (*excl pivots *) LocSet.t -> LocSet.t -> LocSet.t.
  Axiom UnfoldDatagroups_rac_def: forall p h ep dgs f,
    LocSet.In f (UnfoldDatagroups_rac p h ep dgs) <-> 
    exists dg, LocSet.In dg dgs /\ LocSet.In f (UnfoldDatagroup_rac p h ep dg).   


Lemma UnfoldDatagroups_rac_1:
  forall p h dgs f,
  LocSet.In f (UnfoldDatagroups p h dgs) <->
  LocSet.In f (UnfoldDatagroups_rac p h LocSet.empty dgs).
Proof.
intros.
split;intros.
  apply <- UnfoldDatagroups_rac_def.
  apply UnfoldDatagroups_def in H.
  destruct H as [dg H].
  destruct H.
  exists dg.
  split;trivial.

  rewrite <- UnfoldDatagroup_rac_1;trivial.
  apply <- UnfoldDatagroups_def.
  apply UnfoldDatagroups_rac_def in H.
  destruct H as [dg H].
  destruct H.
  exists dg.
  split;trivial.
  rewrite UnfoldDatagroup_rac_1;trivial.
Qed.

Definition EquivAssignableHeap (p : Program) (h h' : Heap.t) (pivots : LocSet.t) : Prop :=
forall loc,
  PivotField p loc -> 
  ~ LocSet.In loc pivots -> 
  Heap.get h loc = Heap.get h' loc.

Lemma UnfoldDatagroups_rac_2:
  forall p h h' pivots assignables,
  EquivAssignableHeap p h h' pivots ->
  UnfoldDatagroups_rac p h pivots assignables [=]
  UnfoldDatagroups_rac p h' pivots assignables.
Proof.
unfold EquivAssignableHeap.
split; intros; apply <- UnfoldDatagroups_rac_def;
 apply UnfoldDatagroups_rac_def in H0.
 destruct H0 as (dg, H0).
 exists dg.
 destruct H0.
 split; trivial.
 apply <- UnfoldDatagroup_rac_def.
 apply UnfoldDatagroup_rac_def in H1.
 clear assignables H0.
 induction H1.
  apply FieldInDg_rac_step with dg'; trivial.
  
  apply FieldInDg_rac_static; trivial.
  
  apply FieldInDg_rac_dynamic with pivot.
   destruct H0.
   apply
    direct_FieldInDg_dynamic_def
     with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg;
    trivial.
   
   rewrite <- H in |- *; trivial.
   
   split with pivot_fsig pivot_obj pivot_f dg; trivial.
   
   trivial.
   
  subst.
  apply FieldInDg_rac_same; trivial.
  
 destruct H0 as (dg, H0).
 exists dg.
 destruct H0.
 split; trivial.
 apply <- UnfoldDatagroup_rac_def.
 apply UnfoldDatagroup_rac_def in H1.
 clear assignables H0.
 induction H1.
  apply FieldInDg_rac_step with dg'; trivial.
  
  apply FieldInDg_rac_static; trivial.
  
  apply FieldInDg_rac_dynamic with pivot.
   destruct H0.
   apply
    direct_FieldInDg_dynamic_def
     with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg;
    trivial.
   rewrite H in |- *; trivial.
   split with pivot_fsig pivot_obj pivot_f dg; trivial.
   
   trivial.
   
  subst.
  apply FieldInDg_rac_same; trivial.
Qed.


Lemma UnfoldDatagroups_rac_3:
  forall p h h' lt obj pivots assignables,
  Heap.new h p lt = Some (obj, h') ->
  UnfoldDatagroups_rac p h pivots assignables [=]
  UnfoldDatagroups_rac p h' pivots assignables.
Proof.
generalize FieldInDg_rac_2.
intro.
split; intros; rewrite UnfoldDatagroups_rac_def;
 apply UnfoldDatagroups_rac_def in H1.
 destruct H1 as (dg, H1).
 destruct H1.
 exists dg.
 split; trivial.
 clear H1.
 rewrite UnfoldDatagroup_rac_def in *.
 specialize H with p h h' lt obj pivots a dg.
 rewrite <- H; trivial.
 
 destruct H1 as (dg, H1).
 destruct H1.
 exists dg.
 split; trivial.
 clear H1.
 rewrite UnfoldDatagroup_rac_def in *.
 specialize H with p h h' lt obj pivots a dg.
 rewrite H; trivial.
Qed.


Lemma UnfoldDatagroups_rac_intersect_update:
forall p h a loc v,
isPivot p loc = false ->
(forall n,
  UnfoldDatagroups_rac p h
  (fst (nth n a (LocSet.empty,LocSet.empty)))
  (snd (nth n a (LocSet.empty,LocSet.empty)))
[=]
  UnfoldDatagroups_rac p (Heap.update h loc v)
  (fst (nth n a (LocSet.empty,LocSet.empty)))
  (snd (nth n a (LocSet.empty,LocSet.empty)))).
Proof.
intros.
generalize n;clear n.
induction a.
simpl.
 destruct n; split; rewrite UnfoldDatagroups_rac_def; simpl; intros;
  destruct H0 as (dg, H0); destruct H0; elim LocSet_empty with dg; 
  trivial.
destruct n.
clear IHa.
apply UnfoldDatagroups_rac_2.

unfold EquivAssignableHeap.
intros.
simpl in H1.
elim classic with (loc = loc0);intros.
subst.
rewrite <- isPivot_PivotField in H0.
rewrite H in H0.
discriminate H0.
rewrite Heap.get_update_old;trivial.
simpl;trivial.
Qed.

Lemma UnfoldDatagroups_rac_intersect_new:
forall p h lt fr obj h',
Heap.new h p lt = Some (obj, h') ->
(forall n,
  UnfoldDatagroups_rac p h
  (fst (nth n fr@assignables (LocSet.empty,LocSet.empty)))
  (snd (nth n fr@assignables (LocSet.empty,LocSet.empty)))
[=]
  UnfoldDatagroups_rac p h'
  (fst (nth n fr@assignables (LocSet.empty,LocSet.empty)))
  (snd (nth n fr@assignables (LocSet.empty,LocSet.empty)))).
Proof.
intros.
generalize n ; clear n.
induction fr@assignables.
simpl.
 destruct n; split; rewrite UnfoldDatagroups_rac_def; simpl; intros;
  destruct H0 as (dg, H0); destruct H0; elim LocSet_empty with dg; 
  trivial.
destruct n.
simpl.
clear IHs.
apply UnfoldDatagroups_rac_3 with lt obj;trivial.
simpl;trivial.
Qed.

  Parameter AssignablePivotTargets: Program -> Heap.t -> 
                                (* pivot *) Location ->
                                (LocSet.t * LocSet.t) -> (* Fields *) LocSet.t.
  Axiom AssignablePivotTargets_def: forall p h pivots aset pivot f,
    LocSet.In f (AssignablePivotTargets p h pivot (pivots, aset))
      <->
    exists dg', direct_FieldInDg_dynamic p h f dg' pivot /\ 
    exists dg, FieldInDg_rac p h pivots dg' dg /\ LocSet.In dg aset .

  Definition SavePreState (p : Program) 
                          (h : Heap.t) 
                          (pivot : Location)
                          (assignable: LocSet.t * LocSet.t) : (LocSet.t * LocSet.t) :=
  if LocSet.mem pivot (fst assignable) then
    assignable
  else
    let fields := AssignablePivotTargets p h pivot assignable in
    (LocSet.add pivot (fst assignable), LocSet.union fields (snd assignable)).

Lemma SavePreState_HeapUpdate:
forall p h loc a v,
EquivAssignableHeap p h (Heap.update h loc v)
       (fst (SavePreState p h loc a )).
Proof.
intros.
unfold EquivAssignableHeap.
intros.
unfold SavePreState in H0.
case_eq (LocSet.mem loc (fst a)).
intros.
rewrite H1 in H0.
apply LocSet.mem_2 in H1.
assert (loc <> loc0).
intuition.
elim H0.
rewrite <- H2;trivial.
symmetry.
apply Heap.get_update_old;trivial.
intros.
rewrite H1 in H0.
simpl in H0.
assert (loc0 <> loc).
auto with *.
symmetry.
apply Heap.get_update_old.
auto.
Qed.


  Lemma eq_false_not_true:
    forall b : bool,
    b = false -> b <> true.
  Proof.
  intuition.
  subst.
  discriminate H0.
  Qed.
  

  Lemma not_mem_not_in :
  forall a x,
  LocSet.mem x a = false -> ~ LocSet.In x a.
  Proof.
  intros.
  intro.
  apply LocSet.mem_1 in H0.
  rewrite H0 in H.
  discriminate H.
  Qed.


Lemma LocSetExistsEquals: forall x, exists y, x [=] y.
intros.
exists x.
split;trivial.
Qed.


  Lemma FieldInDg_rac_pivots_1: 
    forall p h pivot pivots f dg,
    FieldInDg_rac p h (LocSet.add pivot pivots) f dg ->
    FieldInDg_rac p h pivots f dg.
    Proof.
    intuition.
    induction H.
    apply FieldInDg_rac_step with dg';trivial.
    apply FieldInDg_rac_static;trivial.
    apply FieldInDg_rac_dynamic with pivot0;trivial.
    auto with *.
    apply FieldInDg_rac_same;trivial.
  Qed.

  Lemma FieldInDg_rac_pivots_2:
    forall p h f dg pivots pivot,
    FieldInDg_rac p h pivots f dg ->
    ~ FieldInDg_rac p h (LocSet.add pivot pivots) f dg ->
    
    exists dg1, FieldInDg_rac p h (LocSet.add pivot pivots) f dg1 /\
    exists dg', direct_FieldInDg_dynamic p h dg1 dg' pivot /\
    FieldInDg_rac p h pivots dg' dg.
  Proof.
intros.
induction H.
 set (pivots' := LocSet.add pivot pivots) in |- *.
 replace (LocSet.add pivot pivots) with pivots' in *  by trivial.
 elim classic with (FieldInDg_rac p h pivots' field0 dg'); intro.
  elim classic with (FieldInDg_rac p h pivots' dg' dg); intro.
   elim H0.
   apply FieldInDg_rac_step with dg'; trivial.
   
   apply IHFieldInDg_rac1 in H3.
   destruct H3.
   destruct H3.
   destruct H4.
   exists x.
   split.
    apply FieldInDg_rac_step with dg'; trivial.
    
    exists x0; trivial.
    
  apply IHFieldInDg_rac2 in H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  exists x.
  split; trivial.
  exists x0.
  split; trivial.
  apply FieldInDg_rac_step with dg'; trivial.
  
 elim H0.
 apply FieldInDg_rac_static; trivial.
 
 elim classic with (pivot0 = pivot); intro.
  subst.
  exists field0.
  split.
   apply FieldInDg_rac_same; trivial.
   
   exists dg.
   split; trivial.
   apply FieldInDg_rac_same; trivial.

  elim H0.
  apply FieldInDg_rac_dynamic with pivot0; trivial.
  intro.
  elim H1.
  apply LocSet.add_3 in H3; trivial.
  intro.
  elim H2.
  progress auto.
  
 subst.
 elim H0.
 apply FieldInDg_rac_same; trivial.
Qed.

  Lemma SavePreState_1:
  forall p h pivot pivots assignable,
  let a' := SavePreState p h pivot (pivots, assignable) in
  UnfoldDatagroups_rac p h pivots assignable [=]
  UnfoldDatagroups_rac p h (fst a') (snd a').
  Proof.
intuition.
unfold LocSet.Equal in |- *.
intro.
unfold SavePreState in |- *.
simpl in |- *.
case_eq (LocSet.mem pivot pivots); simpl in |- *; intro.
 tauto.

 split; intuition.
  rewrite UnfoldDatagroups_rac_def in |- *.
  rewrite UnfoldDatagroups_rac_def in H0.
  destruct H0 as (dg, H0); destruct H0.
  rewrite UnfoldDatagroup_rac_def in H1.
  set (P := FieldInDg_rac p h (LocSet.add pivot pivots) a dg) in |- *.
  elim classic with P; unfold P in |- *; intro; clear P.
   exists dg.
   split.
    apply LocSet.union_3; trivial.
    
    rewrite UnfoldDatagroup_rac_def in |- *; trivial.
    
   elim FieldInDg_rac_pivots_2 with p h a dg pivots pivot;trivial.
    intros.
    exists x.
    split;trivial.
     apply LocSet.union_2; trivial.
     rewrite AssignablePivotTargets_def in |- *.
     destruct H3.
     destruct H4.
     destruct H4.
     exists x0; trivial.
     split; trivial.
     exists dg.
     auto.
     
     destruct H3.
     rewrite UnfoldDatagroup_rac_def in |- *; trivial.
     
  rewrite UnfoldDatagroups_rac_def in H0 |- *.
  destruct H0.
  destruct H0.
  apply LocSet.union_1 in H0.
  destruct H0.
   apply AssignablePivotTargets_def in H0.
   destruct H0 as (dg', H0).
   destruct H0.
   destruct H2 as (dg, H2).
   destruct H2.
   exists dg.
   split; trivial.
   rewrite UnfoldDatagroup_rac_def in |- *.
   apply UnfoldDatagroup_rac_def in H1.
   apply FieldInDg_rac_pivots_1 in H1.
   apply FieldInDg_rac_step with x; trivial.
   apply FieldInDg_rac_step with dg'; trivial.
   apply FieldInDg_rac_dynamic with pivot; trivial.
   intro.
   apply LocSet.mem_1 in H4.
   rewrite H in H4.
   discriminate H4.
   
   exists x; split; trivial.
   rewrite UnfoldDatagroup_rac_def in H1 |- *.
   apply FieldInDg_rac_pivots_1 in H1; trivial.
Qed.


Lemma SavePreState_2:
forall p h a pivot v,
(forall n,
  UnfoldDatagroups_rac p h
  (fst (nth n a (LocSet.empty,LocSet.empty)))
  (snd (nth n a (LocSet.empty,LocSet.empty)))
[=]
UnfoldDatagroups_rac p (Heap.update h pivot v)
  (fst (nth n (map (SavePreState p h pivot) a)
     (LocSet.empty,LocSet.empty)))
  (snd (nth n (map (SavePreState p h pivot) a)
     (LocSet.empty,LocSet.empty)))).
Proof.
induction a.
 simpl.
 destruct n; split; rewrite UnfoldDatagroups_rac_def; simpl; intros;
  destruct H as (dg, H); destruct H; elim LocSet_empty with dg; 
  trivial.
 
 destruct n.
  simpl.
  clear IHa.
  destruct a as (pivots, assignables).
  simpl.
  pose proof (SavePreState_1 p h pivot pivots assignables) as H.
  simpl in H.
  generalize UnfoldDatagroups_rac_2.
  intro.
  specialize
   H0
    with
      p
      h
      (Heap.update h pivot v)
      (fst (SavePreState p h pivot (pivots, assignables) ))
      (snd (SavePreState p h pivot (pivots, assignables) )).
  generalize SavePreState_HeapUpdate.
  intro.
  apply H0 in H1.
  generalize H1.
  generalize H.
  apply LocSet.eq_trans.
  
  simpl.
  trivial.
Qed.

Inductive EquivAssignables_ind (p : Program) (h h' : Heap.t) (a a' : stack (LocSet.t * LocSet.t)) : Prop :=
| EquivAssignables_base:
  a = nil ->
  a' = nil ->
  EquivAssignables_ind p h h' a a'
| EquivAssignables_step:
  forall head tail head' tail',
  a = head::tail ->
  a' = (head'::tail') ->
  length tail = length tail' ->
  EquivAssignables_ind p h h' tail tail' ->
  UnfoldDatagroups_rac p h (fst head) (snd head) [=] UnfoldDatagroups_rac p h' (fst head') (snd head') ->
  EquivAssignables_ind p h h' a a'.

Lemma EquivAssignables_ind_1: 
forall p h h' a a',
EquivAssignables_ind p h h' a a' ->
(forall n,
  UnfoldDatagroups_rac p h
  (fst (nth n a (LocSet.empty,LocSet.empty)))
  (snd (nth n a (LocSet.empty,LocSet.empty)))
[=]
  UnfoldDatagroups_rac p h'
  (fst (nth n a' (LocSet.empty,LocSet.empty)))
  (snd (nth n a' (LocSet.empty,LocSet.empty)))).
Proof.
intros.
generalize n.
clear n.
induction H.
 subst.
 simpl.
 destruct n; split; rewrite UnfoldDatagroups_rac_def; simpl; intros;
  destruct H as (dg, H); destruct H; elim LocSet_empty with dg; 
  trivial.
 
 subst.
 destruct n.
  simpl.
  trivial.
  
  simpl.
  trivial.
Qed.



Lemma SavePreState_3:
forall p loc st v,
let (a, a') :=
    level st @fr @assignables
      (map (SavePreState p st @h loc) st @fr @assignables) in
EquivAssignables_ind p st@h (Heap.update st@h loc v) a a'.
Proof.
intros.
unfold level.
rewrite map_length.
rewrite nat_compare_n_n.
induction st@fr@assignables.
simpl.
apply EquivAssignables_base;trivial.
simpl.
apply EquivAssignables_step
  with a s (SavePreState p st@h loc a) (map (SavePreState p st@h loc) s);
  trivial.
rewrite map_length;trivial.
pose proof (SavePreState_1 p st@h loc (fst a) (snd a)) as H.
simpl in H.
replace ((fst a), (snd a)) with a in H by (destruct a;trivial).
generalize UnfoldDatagroups_rac_2.
intros.
specialize H0 with 
  p 
  st@h 
  (Heap.update st@h loc v) 
  (fst (SavePreState p st@h loc a )) 
  (snd (SavePreState p st@h loc a )).
generalize SavePreState_HeapUpdate.
intros.
apply H0 in H1.
generalize H1.
generalize H.
apply LocSet.eq_trans.
Qed.

Definition EquivAssignables (p : Program) (st st' : State.t) : Prop :=
let (a, a') := level st@fr@assignables st'@fr@assignables in
EquivAssignables_ind p st@h st'@h a a'.

Lemma EquivAssignables_2:
forall p st loc v,
isPivot p loc = false ->
EquivAssignables p st st[h:=Heap.update st@h loc v].
Proof.
intros.
unfold EquivAssignables.
simpl.
unfold level.
rewrite nat_compare_n_n.
induction (st@fr@assignables).
apply EquivAssignables_base;trivial.
apply EquivAssignables_step with a s a s ;trivial.
apply UnfoldDatagroups_rac_2.
unfold EquivAssignableHeap.
intros.
apply isPivot_PivotField in H0.
assert (loc0 <> loc).
intro.
rewrite H2 in H0.
rewrite H in H0.
discriminate H0.
symmetry.
apply Heap.get_update_old;trivial.
auto.
Qed.

Lemma EquivAssignables_3:
forall p st lt obj h',
Heap.new st@h p lt = Some (obj, h') ->
EquivAssignables p st st[h:=h'].
Proof.
intros.
unfold EquivAssignables.
unfold level.
rewrite nat_compare_n_n.
simpl.
induction st @fr @assignables.
 apply EquivAssignables_base; trivial.
 
 apply EquivAssignables_step with a s a s; trivial.
 apply UnfoldDatagroups_rac_3 with lt obj; trivial.
Qed.

Lemma EquivAssignables_ind_refl:
forall p h a,
EquivAssignables_ind p h h a a.
Proof.
intros.
induction a.
apply EquivAssignables_base;trivial.
apply EquivAssignables_step with a a0 a a0;trivial.
apply LocSet.eq_refl.
Qed.

Lemma EquivAssignables_refl:
forall p st,
EquivAssignables p st st.
Proof.
intros.
unfold EquivAssignables.
unfold level.
rewrite nat_compare_n_n.
apply EquivAssignables_ind_refl.
Qed.

Lemma EquivAssignables_ind_sym:
forall p h h' a a',
EquivAssignables_ind p h h' a a' -> EquivAssignables_ind p h' h a' a.
Proof.
intros.
induction H.
subst.
apply EquivAssignables_base;trivial.
apply EquivAssignables_step with head' tail' head tail;trivial.
symmetry;trivial.
apply LocSet.eq_sym.
trivial.
Qed.

Lemma EquivAssignables_sym:
forall p st st',
EquivAssignables p st st' ->
EquivAssignables p st' st.
Proof.
intros.
 unfold EquivAssignables in *.
 unfold level in *.
 case_eq (Nat.compare (length st @fr @assignables) (length st' @fr @assignables)); intros;
  rewrite H0 in H.
  apply nat_compare_eq_sym in H0.
  rewrite H0 in |- *.
  apply EquivAssignables_ind_sym;trivial.
    
  apply nat_compare_lt_gt_sym in H0.
  rewrite H0 in |- *.
  apply EquivAssignables_ind_sym;trivial.
    
  apply nat_compare_lt_gt_sym in H0.
  rewrite H0 in |- *.
  apply EquivAssignables_ind_sym;trivial.
Qed.

Lemma EquivAssignables_ind_truncated:
forall p h h' a a' n,
length a = length a' ->
EquivAssignables_ind p h h' a a' ->
EquivAssignables_ind p h h' (truncate n a) (truncate n a').
Proof.
intros.
induction H0.
 subst.
 apply EquivAssignables_base.
  unfold truncate in |- *.
  destruct Nat.compare; trivial.
  
  unfold truncate in |- *.
  destruct Nat.compare; trivial.
  
 apply IHEquivAssignables_ind in H2.
 subst.
 case_eq (Nat.compare n (length (head::tail))).
  intros.
  unfold truncate.
  rewrite H0.
  rewrite H in H0.
  rewrite H0.
  apply EquivAssignables_step with head tail head' tail';auto.
  intro.
   unfold truncate in |- *.
   rewrite H0 in |- *.
   rewrite H in H0.
   rewrite H0 in |- *.
   apply IHEquivAssignables_ind.
   progress auto.
   
  intro.
  unfold truncate in |- *.
  rewrite H0 in |- *.
  rewrite H in H0.
  rewrite H0 in |- *.
  apply EquivAssignables_step with head tail head' tail'; auto.
Qed.

Lemma EquivAssignables_ind_tail:
forall p h h' a t a' t',
length t = length t' ->
EquivAssignables_ind p h h' (a::t) (a'::t') ->
EquivAssignables_ind p h h' t t'.
intros.
replace t with (pop (a :: t)) by trivial.
replace t' with (pop (a' :: t')) by trivial.
rewrite <- truncate_pop with (LocSet.t * LocSet.t)%type (length t ) (a :: t).
 rewrite <- truncate_pop with (LocSet.t * LocSet.t)%type (length t' ) (a' :: t').
  rewrite <- H.
  apply EquivAssignables_ind_truncated.
   simpl; auto.
   
   trivial.
   
  trivial.
  
 trivial.
Qed.

Lemma EquivAssignables_ind_trans:
forall p h h' h'' a a' a'',
length a = length a' ->
EquivAssignables_ind p h h' a a' ->
length a' = length a'' ->
EquivAssignables_ind p h' h'' a' a'' ->
EquivAssignables_ind p h h'' a a''.
Proof.
intros p h h' h''.
induction a.
 destruct a'.
  simpl in |- *.
  destruct a''.
   simpl in |- *.
   intros.
   apply EquivAssignables_base; trivial.
   
   intros.
   discriminate H1.
   
  intros.
  discriminate H.
  
 destruct a'.
  intros.
  discriminate H.
  
  destruct a''.
   intros.
   discriminate H1.
   
   intros.
   apply EquivAssignables_step with a a0 p1 a''; trivial.
    rewrite H1 in H.
    auto.
    
    apply IHa with a'.
     auto.
     
     apply EquivAssignables_ind_tail with a p0.
      auto.
      
      trivial.
      
     auto.
     
     apply EquivAssignables_ind_tail with p0 p1.
      auto.
      
      trivial.
      
    destruct H0.
     discriminate H0.
     
     destruct H2.
      discriminate H2.
      
      inversion H0.
      inversion H3.
      inversion H2.
      inversion H7.
      subst.
      inversion H2.
      subst.
      generalize H10.
      generalize H6.
      apply LocSet.eq_trans.
Qed.

Lemma min_L: forall x y, min x y = x <-> x <= y.
Proof.
split;intros.
destruct H.
apply le_min_r.
apply min_l;trivial.
Qed.

Lemma min_R : forall x y , min x y = y <-> y <= x.
Proof.
split;intros.
destruct H.
apply le_min_l.
apply min_r;trivial.
Qed.

Lemma EquivAssignables_trans:
forall p st st' st'',
let x := st@fr@assignables in
let x' := st'@fr@assignables in
let x'' := st''@fr@assignables in
EquivAssignables p st st' ->
EquivAssignables p st' st'' ->
min (length x) (length x'') <= length x'  ->
EquivAssignables p st st''.
Proof.
intros.
unfold EquivAssignables in *;
 replace (FrameAdds.assignables (State.Frame.adds (State.fr st))) with x in *
   by trivial;
 replace (FrameAdds.assignables (State.Frame.adds (State.fr st'))) with x' in
  *  by trivial;
 replace (FrameAdds.assignables (State.Frame.adds (State.fr st''))) with x''
  in *  by trivial.
elim min_dec with (length x) (length x''); intro.
 rewrite a in H1.
 apply min_L in a.
 generalize H1.
 generalize a.
 intros.
 apply level_le in a0.
 apply level_le in H2.
 rewrite <- a0 in |- *.
 rewrite <- H2 in H.
 unfold level in H0.
 case_eq (Nat.compare (length x') (length x'')); intros; rewrite H3 in H0.
  apply EquivAssignables_ind_truncated with (n := length x) in H0.
   apply
    EquivAssignables_ind_trans
     with (h' := State.h st') (a' := truncate (length x) x'); 
    trivial.
    apply truncate_1.
    trivial.
    
    rewrite <- truncate_1 in |- *; trivial.
    apply truncate_1; trivial.
    
   apply nat_compare_Eq in H3; trivial.
   
  apply EquivAssignables_ind_truncated with (n := length x) in H0.
   rewrite <- truncate_truncate in H0.
    apply
     EquivAssignables_ind_trans
      with (h' := State.h st') (a' := truncate (length x) x'); 
     trivial.
     apply truncate_1.
     trivial.
     
     rewrite <- truncate_1 in |- *; trivial.
     apply truncate_1; trivial.
     
    trivial.
    
   apply truncate_1.
   apply nat_compare_lt in H3; auto with *.
   
  apply EquivAssignables_ind_truncated with (n := length x) in H0.
   rewrite <- truncate_truncate in H0.
    apply
     EquivAssignables_ind_trans
      with (h' := State.h st') (a' := truncate (length x) x'); 
     trivial.
     apply truncate_1.
     trivial.
     
     rewrite <- truncate_1 in |- *; trivial.
     apply truncate_1; trivial.
     
    trivial.
    
   symmetry  in |- *.
   apply truncate_1.
   apply nat_compare_gt in H3; auto with *.
   
 rewrite b in H1.
 apply min_R in b.
 generalize H1.
 generalize b.
 intros.
 rewrite le_ge in b0.
 rewrite le_ge in H2.
 apply level_ge in b0.
 apply level_ge in H2.
 rewrite <- b0 in |- *.
 rewrite <- H2 in H0.
 unfold level in H.
 case_eq (Nat.compare (length x) (length x')); intros; rewrite H3 in H.
  apply EquivAssignables_ind_truncated with (n := length x'') in H.
   apply
    EquivAssignables_ind_trans
     with (h' := State.h st') (a' := truncate (length x'') x'); 
    trivial.
    repeat rewrite <- truncate_1 in |- *; trivial.
    
    symmetry  in |- *.
    apply truncate_1; trivial.
    
   apply nat_compare_Eq in H3; trivial.
   
  apply EquivAssignables_ind_truncated with (n := length x'') in H.
   rewrite <- truncate_truncate in H.
    apply
     EquivAssignables_ind_trans
      with (h' := State.h st') (a' := truncate (length x'') x'); 
     trivial.
     repeat rewrite <- truncate_1 in |- *; trivial.
     
     symmetry  in |- *.
     apply truncate_1; trivial.
     
    trivial.
    
   apply truncate_1.
   apply nat_compare_lt in H3; auto with *.
   
  apply EquivAssignables_ind_truncated with (n := length x'') in H.
   rewrite <- truncate_truncate in H.
    apply
     EquivAssignables_ind_trans
      with (h' := State.h st') (a' := truncate (length x'') x'); 
     trivial.
     repeat rewrite <- truncate_1 in |- *; trivial.
     
     symmetry  in |- *.
     apply truncate_1.
     trivial.
     
    apply nat_compare_gt in H3; auto with *.
    
   symmetry  in |- *.
   apply truncate_1.
   apply nat_compare_gt in H3; auto with *.
Qed.

Inductive CorrespondingAssignables (p : Program) (h : Heap.t) (rac : stack (Heap.t * LocSet.t)) (rac2 : stack (LocSet.t * LocSet.t)) :=
CorrespondingAssignables_def:
length rac = length rac2 ->
(forall n,
  UnfoldDatagroups p (fst (nth n  rac (InitHeap, LocSet.empty))) (snd (nth n  rac (InitHeap, LocSet.empty))) [=]
  UnfoldDatagroups_rac p h (fst (nth n  rac2 (LocSet.empty, LocSet.empty))) (snd (nth n  rac2 (LocSet.empty,LocSet.empty)))) ->
CorrespondingAssignables p h rac rac2.

Inductive EqualFresh (f1 f2: stack ObjSet.t) :=
EqualFresh_def:
length f1 = length f2 ->
(forall n d,
  (nth n  f1 d) [[=]] (nth n  f2 d)) ->
EqualFresh f1 f2.

Inductive CorrespondingState (p : Program): Rac1.State.t -> State.t -> Prop :=
| CorrespondingState_def:
  forall st_rac1 st_rac2,
  st_rac1@fr@params %rac1         = st_rac2@fr@params ->
  st_rac1@fr@vars %rac1           = st_rac2@fr@vars ->
  st_rac1@fr@pc %rac1             = st_rac2@fr@pc ->
  st_rac1@fr@ret %rac1            = st_rac2@fr@ret ->
  st_rac1@fr@pre %rac1            = st_rac2@fr@pre ->
  st_rac1@fr@quants %rac1         = st_rac2@fr@quants ->
  EqualFresh st_rac1@fr@fresh%rac1  st_rac2@fr@fresh ->
  CorrespondingAssignables p st_rac2@h st_rac1@fr@assignables%rac1 st_rac2@fr@assignables ->
  st_rac1@h %rac1 = st_rac2@h ->
  st_rac1@adds %rac1 = st_rac2@adds ->
  CorrespondingState p st_rac1 st_rac2.

(** Postpone this ... *)
Declare Module AnnotationTable : ANNOTATION_TABLE State.

Module Assignables <: ASSIGNABLES State.

(** Simply find the location in the list of assignable locations *)

  Lemma NewFrame_Correct: forall p m param st_rac1 st_rac2 fr'_rac1 fr'_rac2,
  CorrespondingState p st_rac1 st_rac2 ->
  fr'_rac1 = Rac1.NewFrame m param st_rac1 ->
  fr'_rac2 = NewFrame m param st_rac2 ->
  CorrespondingState p st_rac1[fr:=fr'_rac1]%rac1 st_rac2[fr:=fr'_rac2].
  Proof.
  intuition.
  rewrite H0.
  rewrite H1.
  unfold NewFrame.
  unfold Rac1.NewFrame.
  destruct H.
  split;trivial.
  simpl in * |- *.
  rewrite H9.
  trivial.
  simpl.
  split.
  destruct H7.
  simpl.
  rewrite e.
  trivial.
  destruct H7.
  simpl.
  destruct n.
  intros.
  apply ObjSet.eq_refl.
  trivial.
  simpl.
  split.
  destruct H8.
  simpl.
  rewrite e.
  trivial.
  destruct H8.
  simpl.
  destruct n.
split;
rewrite UnfoldDatagroups_def;
rewrite UnfoldDatagroups_rac_def;intros.
exists a.
split.
apply LocSetAll_def.
rewrite UnfoldDatagroup_rac_def.
apply FieldInDg_rac_same;trivial.
exists a.
split.
apply LocSetAll_def.
rewrite UnfoldDatagroup_def.
apply FieldInDg_same;trivial.
trivial.
  Qed.

  Definition FieldUpdateCheck (p : Program) (loc : Location) (st : State.t): Prop :=
  forall n,
  (n < length st@fr@assignables)%nat ->
       (exists m, 
        (m <= n /\ m < length st@fr@fresh)%nat /\ LocSet.In loc (ObjSet2LocSet (nth m st@fr@fresh ObjSet.empty)))
    \/
        exists dg, LocSet.In dg (snd (nth n st@fr@assignables (LocSet.empty,LocSet.empty))) /\ 
        FieldInDg_rac p st@h (fst (nth n st@fr@assignables (LocSet.empty,LocSet.empty))) loc dg.


  Lemma FieldUpdateCheck_Correct: 
    forall loc p st_rac1 st_rac2,
    CorrespondingState p st_rac1 st_rac2 ->
    ( Rac1.Assignables.FieldUpdateCheck p loc st_rac1
    <->
    FieldUpdateCheck p loc st_rac2).
Proof.
intros.
destruct H.
clear H H0 H1 H2 H3 H4.
unfold FieldUpdateCheck.
unfold Rac1.Assignables.FieldUpdateCheck.
intuition.
 destruct H6.
 destruct H with (n).
  rewrite e.
  trivial.
  
  left.
  destruct H1 as (m0, H1).
  destruct H1.
   exists m0.
   split.

   inversion H5.
   rewrite <- H3.
   trivial.
   rewrite ObjSet2LocSet_def in H2 |- * .
   unfold LocInObjSet in H2 |- *.
   destruct loc.
   inversion H2.
   unfold ObjSet.Equal in e0.
   apply ObjSet.mem_1.
   apply ObjSet.mem_2 in H2.
   inversion H5.
   apply H4 in H2.
   trivial.
   unfold ObjSet.Equal in e0.
   apply ObjSet.mem_1.
   apply ObjSet.mem_2 in H2.
   inversion H5.
   apply H4 in H2.
   trivial.

  right.
  specialize e0 with n.
  unfold LocSet.Equal in e0.
  specialize e0 with loc.
  rewrite UnfoldDatagroups_def in e0.
  rewrite UnfoldDatagroups_rac_def in e0.
  destruct e0.
  clear H3.
  destruct H2.
  destruct H1.
  exists x.
  destruct H1.
  split;trivial.
  rewrite UnfoldDatagroup_def.
  trivial.
  exists x.
  destruct H2.
  split;trivial.
  rewrite UnfoldDatagroup_rac_def in H3.
  trivial.

 destruct H6.
 destruct H with (n).
  rewrite <- e.
  trivial.
  
  left.
  destruct H1 as (m0, H1).
  destruct H1.
 
   exists m0.
   split.
   inversion H5.
   rewrite H3.
   trivial.
   rewrite ObjSet2LocSet_def in H2 |- * .
   unfold LocInObjSet in H2 |- *.
   destruct loc.
   inversion H2.
   unfold ObjSet.Equal in e0.
   apply ObjSet.mem_1.
   apply ObjSet.mem_2 in H2.
   inversion H5.
   apply H4 in H2.
   trivial.
   unfold ObjSet.Equal in e0.
   apply ObjSet.mem_1.
   apply ObjSet.mem_2 in H2.
   inversion H5.
   apply H4 in H2.
   trivial.

  right.
  specialize e0 with n.
  unfold LocSet.Equal in e0.
  specialize e0 with loc.
  rewrite UnfoldDatagroups_def in e0.
  rewrite UnfoldDatagroups_rac_def in e0.
  destruct e0.
  clear H2.
  destruct H3.
  destruct H1.
  exists x.
  destruct H1.
  split;trivial.
  rewrite UnfoldDatagroup_rac_def.
  trivial.
  exists x.
  destruct H2.
  split;trivial.
  rewrite UnfoldDatagroup_def in H3.
  trivial.
Qed.

  (* Don't bother for now, just assume that this function yields the same assignable locations than in the semantics.*)
  Parameter EvalAssignableClause : Program -> Class -> Method -> State.t -> LocSet.t.
  Parameter EvalAssignableClause_def : 
    forall p c m st_rac1 st_rac2,
    CorrespondingState p st_rac1 st_rac2 ->
    (EvalAssignableClause p c m st_rac2 [=] Rac1.Assignables.EvalAssignableClause p c m st_rac1).

  Definition MethodCallAction (p : Program) (c : Class) (m : Method) (st : State.t) : State.t :=
  let locs := EvalAssignableClause p c m st in
  st[fr:=st@fr[assignables :+ (LocSet.empty, locs)]].

  Lemma MethodCallAction_Correct:
    forall p c m st_rac1 st_rac1' st_rac2 st_rac2',
    CorrespondingState p st_rac1 st_rac2 ->
    Rac1.Assignables.MethodCallAction p c m st_rac1 = st_rac1' ->
    MethodCallAction p c m st_rac2 = st_rac2' ->
    CorrespondingState p st_rac1' st_rac2'.
Proof.
intuition.
subst.
generalize H.
intro H'.
destruct H'.
split; try trivial.
unfold MethodCallAction.
unfold Rac1.Assignables.MethodCallAction.
simpl.
assert
 (EvalAssignableClause p c m st_rac2[=]
  Rac1.Assignables.EvalAssignableClause p c m st_rac1).
 apply EvalAssignableClause_def; trivial.
 
 split; intros.
  unfold replace_top.
    destruct H7.
  destruct st_rac1@fr@assignables%rac1;
  destruct st_rac2@fr@assignables;trivial.
 
  destruct n.
  unfold replace_top.
  destruct H7.
  destruct st_rac1@fr@assignables%rac1;
  destruct st_rac2@fr@assignables;trivial.
  inversion e.
  inversion e.
  simpl in * |- *.
   split.
    rewrite <- UnfoldDatagroups_rac_1.
    rewrite H8.
    rewrite UnfoldDatagroups_def.
    rewrite UnfoldDatagroups_def.
    intros.
    destruct H7 as (dg, H7).
    exists dg.
    unfold LocSet.eq in H10.
    unfold LocSet.Equal in H10.
    destruct H10 with dg.
    tauto.
    
    rewrite <- UnfoldDatagroups_rac_1.
    rewrite H8.
    rewrite UnfoldDatagroups_def.
    rewrite UnfoldDatagroups_def.
    intros.
    destruct H7 as (dg, H7).
    exists dg.
    unfold LocSet.eq in H10.
    unfold LocSet.Equal in H10.
    destruct H10 with dg.
    tauto.
    
   unfold replace_top.
   destruct H7.
  destruct st_rac1@fr@assignables%rac1;
  destruct st_rac2@fr@assignables;trivial.
  inversion e.
  inversion e.
    simpl.
    specialize e0 with (S n).
    simpl in e0.
   trivial.
Qed.

(** Add all fields of a newly created object to the list of fresh locations, as well
to the assignable list *)

  Definition NewObjectAction (p : Program) (obj : Object) (st : State.t) : State.t :=
    st[fr:=st@fr[fresh :+ obj]].

  Lemma NewObjectAction_Equiv:
  forall p l st st',
  st' = NewObjectAction p l st ->
  EquivAssignables p st st'.
Proof.
intros.
unfold NewObjectAction in H.
subst.
unfold EquivAssignables.
simpl.
apply EquivAssignables_refl.
Qed.

  Lemma NewObjectAction_Correct:
    forall p l st_rac1 st_rac1' st_rac2 st_rac2',
    CorrespondingState p st_rac1 st_rac2 ->
    NewObjectAction p l st_rac2 = st_rac2' ->
    Rac1.Assignables.NewObjectAction p l st_rac1%rac1 = st_rac1' ->
    CorrespondingState p st_rac1' st_rac2'.
  Proof.
intuition.
subst.
inversion H.
split; trivial.
subst.
simpl in *.
unfold apply_top.
destruct H6.
destruct st_rac1 @fr @fresh%rac1; destruct st_rac2 @fr @fresh.
 split.
  trivial.
  
  trivial.
  
 inversion e.
 
 inversion e.
 
 split; simpl.
  trivial.
  
  intros.
  destruct n.
   specialize e0 with 0 d.
   simpl in e0.
   unfold ObjSet.Equal in * |- *.
split;intros.
case_eq(ObjDec.eq_dec l a);intros.
apply ObjSet.add_1;trivial.
apply ObjSet.add_2;trivial.
apply ObjSet.add_3 in H6;trivial.
rewrite <- e0;trivial.
case_eq(ObjDec.eq_dec l a);intros.
apply ObjSet.add_1;trivial.
apply ObjSet.add_2;trivial.
apply ObjSet.add_3 in H6;trivial.
rewrite e0;trivial.
   
   specialize e0 with (S n) d.
   simpl in e0.
   trivial.
Qed.
(** Upon method return, add all freshly created locations to the list of fresh locations from the caller *)

  Definition MethodReturnAction (p : Program) (st_c : State.t) (st : State.t) : State.t :=
    st_c[fr:=st@fr[fresh :\/ (peekd st_c@fr@fresh ObjSet.empty)][assignables := pop st_c@fr@assignables]].
    
  Lemma MethodReturnAction_Equiv:
  forall p st st_c st_c',
  st_c' = MethodReturnAction p st_c st -> 
  EquivAssignables p st_c st_c'.
  Proof.
  intros.
  subst.
  unfold MethodReturnAction.
  unfold EquivAssignables.
  simpl.
  unfold pop.
  case_eq (st_c@fr@assignables).
  intro.
  simpl.
  apply EquivAssignables_ind_refl.
  intros.
  unfold level.
  replace (length (p0::l)) with (S (length l)) by auto.
  rewrite nat_compare_Sn_n.
  rewrite truncate_pop by auto.
  simpl.
  apply EquivAssignables_ind_refl.
Qed.

  Lemma MethodReturnAction_Correct:
    forall p st_rac1 st_rac1_c st_rac1_c' st_rac2 st_rac2_c st_rac2_c',
    
    CorrespondingState p st_rac1_c st_rac2_c ->
    CorrespondingState p st_rac1 st_rac2 ->
    Rac1.Assignables.MethodReturnAction p st_rac1_c st_rac1 = st_rac1_c' ->
    MethodReturnAction p st_rac2_c st_rac2 = st_rac2_c' ->
    EquivAssignables p st_rac2 st_rac2_c ->
    S (length st_rac2@fr@assignables) = length st_rac2_c@fr@assignables ->
    CorrespondingState p st_rac1_c' st_rac2_c'.
  Proof.
  intuition.
  subst.
  unfold MethodReturnAction.
  unfold Rac1.Assignables.MethodReturnAction.
  destruct H.
  rename st_rac0 into st_rac1_c.
  rename st_rac3 into st_rac2_c.
  destruct H0.
  split;trivial.
  simpl.
  unfold apply_top.
  destruct H17.
    destruct st_rac1@fr@fresh%rac1;
    destruct st_rac2@fr@fresh;trivial.
    split;simpl;trivial.
    inversion e.
inversion e.
    split;simpl.
    trivial.
    intros.
    destruct n.
specialize e0 with O d.
simpl in e0.
destruct H8.
destruct st_rac1_c@fr@fresh%rac1;
destruct st_rac2_c@fr@fresh;simpl;trivial.
apply UnionEqual.
apply ObjSet.eq_refl.
trivial.
inversion e1.
inversion e1.
specialize e2 with O d.
simpl in e2.
apply UnionEqual;trivial.
specialize e0 with (S n) d.
simpl in e0.
trivial.
split.
simpl.
unfold pop.
destruct st_rac2_c@fr@assignables.
simpl in H4.
inversion H4.
destruct H18.
rewrite e.
auto.
intros.
simpl.
unfold EquivAssignables in H3.
  unfold level in H3.
  assert (Nat.compare (length st_rac2@fr@assignables) (length st_rac2_c@fr@assignables )= Lt).
rewrite <- H4.
simpl.
  apply nat_compare_n_Sn.
  rewrite H21 in H3.
  rewrite truncate_pop in H3.
  apply EquivAssignables_ind_1 with (n:= n) in H3 .
  destruct H18.
  specialize e0 with n.
  generalize H3.
  generalize e0.
  apply LocSet.eq_trans.
  symmetry;trivial.
Qed.

  Definition FieldUpdateAction (p : Program) (pivot : Location) (new_loc : Value) (st : State.t) : State.t :=
    if (isPivot p pivot) then
      st[fr:=st@fr[assignables := map (SavePreState p st@h pivot) st@fr@assignables]]
    else
      st.


  Lemma FieldUpdateAction_Equiv:
    forall p loc st v st',
    st' = FieldUpdateAction p loc v st ->
    EquivAssignables p st st'[h:=Heap.update st@h loc v].
Proof.
intros.
unfold FieldUpdateAction in H.
case_eq(isPivot p loc);intro;rewrite H0 in H.

subst.
unfold EquivAssignables.
simpl.
apply SavePreState_3.
unfold EquivAssignables.
simpl.
rewrite H.

generalize EquivAssignables_2.
intros.
specialize H1 with p st loc v.
apply H1 in H0.
trivial.
Qed.

  Lemma FieldUpdateAction_Correct:
    forall p loc st_rac1 v st_rac1' st_rac2 st_rac2',
    CorrespondingState p st_rac1 st_rac2 ->
    FieldUpdateAction p loc v st_rac2 = st_rac2' ->
    Rac1.Assignables.FieldUpdateAction p loc v st_rac1 = st_rac1' ->
    CorrespondingState p 
      st_rac1'[h:=Heap.update st_rac1@h loc v]%rac1 
      st_rac2'[h:=Heap.update st_rac2@h loc v].
Proof.
intuition.
inversion H.
subst.
unfold Rac1.Assignables.FieldUpdateAction.
unfold FieldUpdateAction.
case_eq (isPivot p loc); intro.
 split; simpl; trivial.
 
 split.
 rewrite map_length.
 destruct H9.
 trivial.
 generalize SavePreState_2.
  intros.
  specialize H1 with p st_rac2 @h st_rac2 @fr@assignables loc v n.
  destruct H9.
  generalize H1.
  specialize e0 with n.
  generalize e0.
  apply LocSet.eq_trans.
  
  rewrite H10.
  trivial.
  
 split; trivial.
  simpl.
  split.
  destruct H9;trivial.
  generalize UnfoldDatagroups_rac_intersect_update.
  intro.
  intros.
  specialize H1 with p st_rac2 @h st_rac2 @fr@assignables loc v n.
  apply H1 in H0.
  clear H1.
  destruct H9.
  specialize e0 with n.
  generalize H0.
  generalize e0.
  apply LocSet.eq_trans.
  
  simpl.
  rewrite H10.
  trivial.
Qed.

End Assignables.

End Rac2.












