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

From JML Require Export JMLSemantics.
From Coq Require Import List.
From JML Require Import Stack.
From Coq Require Import ListSet.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Relation_Operators.
From JML Require Import ListHelpers.
From Coq Require Import Lia.

Import Dom.
Import Prog.
Import JmlNotations.
Import METHODSPEC.
Import TYPESPEC.

Open Scope jml_scope.

(** * The JML Runtime Assertion Checker Rac1
This module describes the runtime assertions checks for suported JML-Level 0 constructs *)

Module Rac1 <: JML.

(** ** Implementation of the JML Frame for Rac1 *)

Module FrameAdds <: ADDS.

  Record t_rec : Type := make {
    assignables: stack (Heap.t * LocSet.t);
    fresh : stack ObjSet.t;
    pre : Heap.t * ParamDict.t;
    quants : VarDict.t
  }.

  Definition t := t_rec.

  Parameter empty : t.

  Definition set_pre (fr : t) (h : Heap.t) (p : ParamDict.t) : t :=
    make (assignables fr) (fresh fr) (h, p) (quants fr).

  Definition set_assignables (fr : t) (x : stack (Heap.t * LocSet.t)) : t :=
    make x (fresh fr) (pre fr) (quants fr).

  Definition replace_top_assignables (fr : t) (elem : Heap.t * LocSet.t) : t :=
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

  Declare Scope rac1_scope.
  Delimit Scope rac1_scope with rac1.

  Open Scope rac1_scope.

  Notation "st '@h'" := (State.h st) (at level 1, left associativity): rac1_scope.
  Notation "st '@fr'" := (State.fr st) (at level 1, left associativity) : rac1_scope.
  Notation "st '@adds'" := (State.adds st) (at level 1, left associativity) : rac1_scope.

  Notation "st '[h' ':=' h ']'" := (State.set_h st h) (at level 1, left associativity): rac1_scope.
  Notation "st '[fr' ':=' fr ']'" := (State.set_fr st fr) (at level 1, left associativity) : rac1_scope.
  Notation "st '[adds' ':=' adds ']'" := (State.set_adds st adds) (at level 1, left associativity) : rac1_scope.

  Notation "[ h , fr , adds ]" := (State.build h fr adds) : rac1_scope.

  Notation "fr '@params'" := (Frame.params fr) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@vars'" := (Frame.vars fr) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@pc'" := (Frame.pc fr) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@ret'" := (Frame.ret fr) (at level 1, left associativity) : rac1_scope.

  Notation "fr '@fradds'" := (Frame.adds fr) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@pre'" := (FrameAdds.pre (Frame.adds fr)) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@preheap'" := (fst (fr@pre)) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@preparams'" := (snd (fr@pre)) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@assignables'" := (FrameAdds.assignables (Frame.adds fr)) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@fresh'" := (FrameAdds.fresh (Frame.adds fr)) (at level 1, left associativity) : rac1_scope.
  Notation "fr '@quants'" := (FrameAdds.quants (Frame.adds fr)) (at level 1, left associativity) : rac1_scope.

  Notation "fr '[fradds' ':=' adds ']'" := (Frame.set_adds fr adds) (at level 1, left associativity): rac1_scope.
  Notation "fr '[quants' ':=' q ']'" := ( fr[fradds := (FrameAdds.set_quants fr@fradds q)]) (at level 1, left associativity) : rac1_scope.
  Notation "fr '[assignables' ':=' a ']'" := ( fr[fradds := (FrameAdds.set_assignables fr@fradds a)]) (at level 1, left associativity) : rac1_scope.
  Notation "fr '[assignables' ':+' elem ']'" := ( fr[fradds := (FrameAdds.replace_top_assignables fr@fradds elem)]) (at level 1, left associativity) : rac1_scope.
  Notation "fr '[assignables' '--' ']'" := ( fr[fradds := (FrameAdds.pop_assignables fr@fradds)]) (at level 1, left associativity) : rac1_scope. 
  Notation "fr '[fresh' ':=' f ']'" := ( fr[fradds := (FrameAdds.set_fresh fr@fradds f)]) (at level 1, left associativity) : rac1_scope.
  Notation "fr '[fresh' ':\/' f ']'" := ( fr[fradds := (FrameAdds.union_fresh fr@fradds f)]) (at level 1, left associativity) : rac1_scope.
  Notation "fr '[fresh' ':+' f ']'" := ( fr[fradds := (FrameAdds.add_fresh fr@fradds f)]) (at level 1, left associativity) : rac1_scope.

End Notations.

Import Sem.Notations.

Import Notations.

(** A new JML Frame is initialized with the assignable locations from the caller *)
Definition NewFrame (m : Method) (p : ParamDict.t) (st : State.t) : Frame.t :=
  let adds := FrameAdds.make ((InitHeap,LocSetAll)::st@fr@assignables) (ObjSet.empty::st@fr@fresh)  (st@h , p) VarDict.empty in
  Frame.build m p adds.

Definition CorrespondingFreshAssignables (p: Program) (asem : LocSet.t) (fsem : ObjSet.t) (arac: stack (Heap.t * LocSet.t)) (fresh : stack ObjSet.t) : Prop :=
forall loc,
  LocSet.In loc asem \/ (LocInObjSet loc fsem = true)
  <-> 
  (forall n,
  (n < length arac)%nat ->
       (exists m, 
        (m <= n /\ m < length fresh)%nat /\ LocSet.In loc (ObjSet2LocSet (nth m fresh ObjSet.empty)))
    \/
      LocSet.In loc (UnfoldDatagroups p (fst (nth n arac (InitHeap,LocSet.empty))) (snd (nth n arac (InitHeap,LocSet.empty))))).

Inductive CorrespondingFrame (p : Program) : Frame.t -> Sem.Frame.t -> Prop :=
| CorrespondingFrame_def:
  forall fr_rac fr_sem,
  fr_sem@params %sem         = fr_rac@params ->
  fr_sem@vars %sem           = fr_rac@vars ->
  fr_sem@pc %sem             = fr_rac@pc ->
  fr_sem@ret %sem            = fr_rac@ret ->
  fr_sem@pre %sem            = fr_rac@pre ->
  fr_sem@quants %sem         = fr_rac@quants ->
  fr_sem@fresh %sem  [[=]] (peekd fr_rac@fresh ObjSet.empty) ->
  CorrespondingFreshAssignables p fr_sem@assignables%sem fr_sem@fresh%sem fr_rac@assignables fr_rac@fresh ->
  fr_rac@fresh <> nil ->
  CorrespondingFrame p fr_rac fr_sem.

Definition CorrespondingState (p : Program) (st_rac : State.t) (st_sem : Sem.State.t) : Prop :=
  st_sem@h %sem = st_rac@h /\ CorrespondingFrame p st_rac@fr st_sem@fr %sem.

(** Postpone this ... *)
Declare Module AnnotationTable : ANNOTATION_TABLE State.

Module Assignables <: ASSIGNABLES State.

(** Simply find the location in the list of assignable locations *)

  Lemma NewFrame_Correct: forall p m param st_rac st_sem fr'_rac fr'_sem,
  CorrespondingState p st_rac st_sem ->
  fr'_rac =NewFrame m param st_rac ->
  fr'_sem = Sem.NewFrame m param st_sem ->
  CorrespondingFrame p fr'_rac fr'_sem.
  Proof.
intuition.
rewrite H0.
rewrite H1.
unfold NewFrame.
unfold Sem.NewFrame.
destruct H.
destruct H2.
rename H10 into Hfresh.
unfold Sem.Frame.build.
unfold Frame.build.
split; trivial; simpl.
 rewrite H.
 trivial.
 
 apply ObjSet.eq_refl.
 
 split.
  intros.
  destruct n.
   right.
   simpl.
   rewrite UnfoldDatagroups_def.
   exists loc.
   split.
    apply LocSetAll_def.
    
    rewrite UnfoldDatagroup_def.
    apply FieldInDg_same.
    trivial.
    
   destruct H9 with loc.
   clear H13.
   destruct H10.
    apply LocSet.union_1 in H10.
    destruct H12 with n.
     rewrite ObjSet2LocSet_def in H10.
     trivial.
     
     simpl in H11.
     lia.
     
     left.
     destruct H13 as (m0, H13).
     exists (S m0).
     simpl.
     intuition auto with arith.
     
     right.
     simpl.
     trivial.
     
    generalize LocInObjSet_empty.
    intros.
    specialize H13 with loc.
    rewrite H10 in H13.
    elim H13; trivial.
    
  intros.
  destruct H9 with loc.
  clear H11.
  destruct H12.
   intros.
   destruct H10 with (S n).
    simpl.
    lia.
    
    destruct H12 as (m0, H12).
    destruct H12.
    destruct m0.
     simpl in H13.
     generalize LocInObjSet_empty.
     intros.
     specialize H14 with loc.
     apply ObjSet2LocSet_def in H13.
     rewrite H13 in H14.
     elim H14; trivial.
     
     left.
     exists m0.
     destruct H12.
     simpl in H14.
     simpl in H13.
     split.
      split.
       lia.
       
       lia.
       
      trivial.
      
    right.
    simpl in H12.
    trivial.
    
   left.
   apply LocSet.union_2; trivial.
   
   left.
   apply LocSet.union_3; trivial.
   apply ObjSet2LocSet_def.
   trivial.
   
 auto with *.
Qed.

  Definition FieldUpdateCheck (p : Program) (loc : Location) (st : State.t): Prop :=
  forall n,
  (n < length st@fr@assignables)%nat ->
       (exists m, 
        (m <= n /\ m < length st@fr@fresh)%nat /\ LocSet.In loc (ObjSet2LocSet (nth m st@fr@fresh ObjSet.empty)))
    \/
        exists dg, LocSet.In dg (snd (nth n st@fr@assignables (InitHeap,LocSet.empty))) /\ 
        FieldInDg p (fst (nth n st@fr@assignables (InitHeap,LocSet.empty))) loc dg.

  Lemma FieldUpdateCheck_Correct: 
    forall loc p st_rac st_sem,
    CorrespondingState p st_rac st_sem ->
    ( FieldUpdateCheck p loc st_rac <->  Sem.Assignables.FieldUpdateCheck p loc st_sem).
  Proof.
intros loc p stRac stSem H0.
destruct H0.
inversion_clear H0 as (t1, t2, _, _, _, _, _, _, HC0, HC1, HC2).
unfold FieldUpdateCheck; unfold Sem.Assignables.FieldUpdateCheck.
unfold CorrespondingFreshAssignables in HC1.
destruct HC1 with loc.
split; intros.
 apply H1.
 intros.
 rewrite UnfoldDatagroups_def.
 destruct H2 with n; trivial.
  left; trivial.
  
  destruct H4 as (dg, H4).
  right.
  exists dg.
  rewrite UnfoldDatagroup_def.
  trivial.
  
 destruct H0 with n; trivial.
  destruct H4 as (fset, H4).
  left.
  exists fset.
  trivial.
  
  right.
  rewrite UnfoldDatagroups_def in H4.
  destruct H4 as (dg, H4).
  exists dg.
  rewrite UnfoldDatagroup_def in H4.
  trivial.
Qed.

  (* Don't bother for now, just assume that this function yields the same assignable locations than in the semantics.*)
  Parameter EvalAssignableClause : Program -> Class -> Method -> State.t -> LocSet.t.
  Parameter EvalAssignableClause_def : 
    forall p c m st_sem st_rac,
    CorrespondingState p st_rac st_sem ->
    (EvalAssignableClause p c m st_rac [=] Sem.Assignables.EvalAssignableClause p c m st_sem).

  Definition MethodCallAction (p : Program) (c : Class) (m : Method) (st : State.t) : State.t :=
  let locs := EvalAssignableClause p c m st in 
  st[fr:=st@fr[assignables :+ (st@h, locs)]].
  
  Lemma MethodCallAction_Correct:
    forall p c m st_rac st_rac' st_sem st_sem' st_rac_assignables st_rac_fresh,
    (st_sem@fr@fresh%sem = ObjSet.empty /\ 
     st_rac@fr@assignables = ((InitHeap,LocSetAll) :: st_rac_assignables) /\
     st_rac@fr@fresh = (ObjSet.empty::st_rac_fresh)) ->
    CorrespondingState p st_rac st_sem ->
    Sem.Assignables.MethodCallAction p c m st_sem = st_sem' ->
    Rac1.Assignables.MethodCallAction p c m st_rac = st_rac' ->
    CorrespondingState p st_rac' st_sem'.
  Proof.
intros.
subst.
rename H into Hinit.
rename H0 into H.
inversion H.
inversion H1.
rename H10 into Hfresh.
subst.
split; trivial.
simpl in *.
split; trivial.
simpl.
split.
 intros.
 destruct n.
  destruct H10.
   apply LocSet.inter_2 in H10.
   right.
   unfold replace_top.
   destruct st_rac @fr @assignables.
    unfold replace_top in H11.
    inversion H11.
    
    simpl.
    assert
     (EvalAssignableClause p c m st_rac[=]
      Sem.Assignables.EvalAssignableClause p c m st_sem).
     apply EvalAssignableClause_def; trivial.
     
     rewrite UnfoldDatagroups_def in H10 |- *.
     unfold LocSet.Equal in H12.
     destruct H10 as (dg, H10).
     exists dg.
     rewrite H12.
     rewrite <- H0.
     trivial.
     
   destruct Hinit.
   rewrite H12 in H10.
   elim LocInObjSet_empty with loc; trivial.
   
  unfold replace_top in *.
  destruct st_rac @fr @assignables.
   inversion H11.
   
   destruct H9 with loc.
   clear H13.
   destruct H12 with (S n).
    destruct H10.
     left.
     apply LocSet.inter_1 in H10.
     trivial.
     
     right; trivial.
     
    trivial.
    
    destruct H13 as (Sm, H13).
    left.
    exists Sm.
    trivial.
    
    right.
    simpl in *.
    trivial.
    
 intros.
 destruct H9 with loc.
 clear H11.
 unfold replace_top in *.
 left.
 apply LocSet.inter_3.
  destruct H12.
   intros.
   destruct H10 with n.
    destruct st_rac @fr @assignables.
     inversion H11.
     
     trivial.
     
    left; trivial.
    
    destruct st_rac @fr @assignables.
     inversion H11.
     
     right.
     destruct Hinit.
     destruct H14.
     inversion H14.
     subst.
     destruct n.
      simpl in *.
      rewrite UnfoldDatagroups_def.
      exists loc.
      split.
       apply LocSetAll_def.
       
       rewrite UnfoldDatagroup_def.
       apply FieldInDg_same.
       trivial.
       
      simpl in *.
      trivial.
      
   trivial.
   
   destruct Hinit.
   rewrite H12 in H11.
   elim LocInObjSet_empty with loc.
   trivial.
   
  destruct H10 with 0%nat.
   destruct st_rac @fr @assignables.
    destruct Hinit.
    destruct H13.
    inversion H13.
    
    simpl.
    lia.
    
   destruct H11 as (m0, H11).
   destruct m0.
    destruct H11.
    destruct H11.
    destruct Hinit.
    destruct H16.
    rewrite H17 in H13.
    simpl in H13.
    rewrite ObjSet2LocSet_def in H13.
    elim LocInObjSet_empty with loc.
    trivial.
    
    destruct H11.
    destruct H11.
    inversion H11.
    
   destruct Hinit.
   destruct H14.
   rewrite H14 in H11.
   simpl in H11.
   assert
    (EvalAssignableClause p c m st_rac[=]
     Sem.Assignables.EvalAssignableClause p c m st_sem).
    apply EvalAssignableClause_def; trivial.
    
    rewrite UnfoldDatagroups_def in H11 |- *.
    unfold LocSet.Equal in H16.
    destruct H11 as (dg, H11).
    exists dg.
    rewrite <- H16.
    rewrite H0.
    trivial.
Qed.

(** Add all fields of a newly created object to the list of fresh locations, as well
to the assignable list *)

  Definition NewObjectAction (p : Program) (obj : Object) (st : State.t) : State.t :=
    st[fr:=st@fr[fresh :+ obj]].

  Lemma NewObjectAction_Correct:
    forall p l st_rac st_rac' st_sem st_sem',
    CorrespondingState p st_rac st_sem ->
    NewObjectAction p l st_rac = st_rac' ->
    Sem.Assignables.NewObjectAction p l st_sem = st_sem' ->
    CorrespondingState p st_rac' st_sem'.
  Proof.
intuition.
subst.
inversion H.
split; trivial.
inversion H1.
split; trivial.
 subst.
 unfold Sem.Assignables.NewObjectAction.
 unfold NewObjectAction.
 simpl in *.
 destruct st_rac @fr @fresh.
  simpl.
  destruct H10; trivial.
  
  simpl.
  simpl in H8.
  unfold ObjSet.Equal in *.
  split; intros.
   case_eq (ObjDec.eq_dec l a); intros.
    apply ObjSet.add_1; trivial.
    
    apply ObjSet.add_2; trivial.
    apply ObjSet.add_3 in H11; trivial.
    rewrite <- H8; trivial.
    
   case_eq (ObjDec.eq_dec l a); intros.
    apply ObjSet.add_1; trivial.
    
    apply ObjSet.add_2; trivial.
    apply ObjSet.add_3 in H11; trivial.
    rewrite H8; trivial.
    
 unfold Sem.Assignables.NewObjectAction.
 unfold NewObjectAction.
 simpl in *.
 split; intuition.
  destruct H9 with loc.
  clear H16.
  apply H15 in H13.
   destruct H13.
    destruct H13 as (fset, H13).
    left.
    destruct st_rac @fr @fresh.
     elim H10; trivial.
     
     simpl.
     rename fset into m0.
     exists m0.
     destruct m0.
      simpl in *.
      split.
       tauto.
       
       destruct H13.
       rewrite ObjSet2LocSet_def in H16 |- *.
       unfold LocInObjSet in H16 |- *.
       destruct loc.
        inversion H16.
        
        apply ObjSet.mem_1.
        apply ObjSet.add_2.
        apply ObjSet.mem_2 in H16; trivial.
        
        apply ObjSet.mem_1.
        apply ObjSet.add_2.
        apply ObjSet.mem_2 in H16; trivial.
        
      destruct H13.
      split; trivial.
      
    right; trivial.
    
   left; trivial.
   
  left.
  destruct st_rac @fr @fresh.
   elim H10; trivial.
   
   simpl in *.
   exists 0%nat.
   split.
    lia.
    
    rewrite ObjSet2LocSet_def.
    unfold ObjSet.Equal in *.
    unfold LocInObjSet in H14 |- *.
    destruct loc.
     inversion H14.
     
     apply ObjSet.mem_2 in H14.
     apply ObjSet.mem_1.
     case_eq (ObjDec.eq_dec l o); intros.
      apply ObjSet.add_1; trivial.
      
      apply ObjSet.add_2; trivial.
      apply ObjSet.add_3 in H14; trivial.
      rewrite <- H8; trivial.
      
     apply ObjSet.mem_2 in H14.
     apply ObjSet.mem_1.
     case_eq (ObjDec.eq_dec l o); intros.
      apply ObjSet.add_1; trivial.
      
      apply ObjSet.add_2; trivial.
      apply ObjSet.add_3 in H14; trivial.
      rewrite <- H8; trivial.
      
  case_eq (LocInObj loc l); intros.
   right.
   apply LocInObj_ObjSet with (obj := l); trivial.
   apply ObjSet.add_1; trivial.
   
   destruct H9 with loc.
   clear H15.
   destruct H16.
    intros.
    apply H13 in H15.
    destruct H15.
     destruct H15 as (m0, H15).
     left.
     destruct st_rac @fr @fresh.
      elim H10; trivial.
      
      simpl in H15.
      exists m0.
      destruct m0.
       simpl in *.
       split.
        tauto.
        
        destruct H15.
        rewrite ObjSet2LocSet_def in H16 |- *.
        unfold LocInObjSet in H16 |- *.
        unfold LocInObj in H14.
        destruct loc.
         inversion H16.
         
         case_eq (ObjDec.eq_dec o l); intros.
          rewrite H17 in H14.
          inversion H14.
          
          apply ObjSet.mem_2 in H16.
          apply ObjSet.add_3 in H16.
           apply ObjSet.mem_1; trivial.
           
           auto.
           
         case_eq (ObjDec.eq_dec o l); intros.
          rewrite H17 in H14.
          inversion H14.
          
          apply ObjSet.mem_2 in H16.
          apply ObjSet.add_3 in H16.
           apply ObjSet.mem_1; trivial.
           
           auto.
           
       destruct H15.
       split; trivial.
       
     right; trivial.
     
    left; trivial.
    
    right.
    unfold LocInObjSet in H15 |- *.
    destruct loc.
     inversion H15.
     
     apply ObjSet.mem_2 in H15.
     apply ObjSet.mem_1.
     apply ObjSet.add_2; trivial.
     
     apply ObjSet.mem_2 in H15.
     apply ObjSet.mem_1.
     apply ObjSet.add_2; trivial.
     
 unfold NewObjectAction.
 simpl.
 destruct st_rac @fr @fresh.
  elim H10; trivial.
  
  simpl.
  auto with *.
Qed.

(** Upon method return, add all freshly created locations to the list of fresh locations from the caller *)

  Definition MethodReturnAction (p : Program) (st_c : State.t) (st : State.t) : State.t :=
    st_c[fr:=st@fr[fresh :\/ (peekd st_c@fr@fresh ObjSet.empty) ]].

  Lemma MethodReturnAction_Correct:
    forall p st_rac st_rac_c st_rac' st_sem st_sem_c st_sem',
    CorrespondingState p st_rac_c st_sem_c ->
    CorrespondingState p st_rac st_sem ->
    MethodReturnAction p st_rac_c st_rac = st_rac' ->
    Sem.Assignables.MethodReturnAction p st_sem_c st_sem = st_sem' ->
    CorrespondingState p st_rac' st_sem'.
  Proof.
intuition.
subst.
unfold MethodReturnAction.
unfold Sem.Assignables.MethodReturnAction.
destruct H.
destruct H0.
destruct H1.
rename fr_sem into fr_sem_c.
rename fr_rac into fr_rac_c.
destruct H2.
split; trivial; simpl in *.
split; trivial.
 simpl.
 destruct fr_rac_c @fresh.
  elim H10; trivial.
  
  simpl.
  destruct fr_rac @fresh.
   elim H18; trivial.
   
   simpl.
   simpl in H8.
   simpl in H16.
   apply UnionEqual; trivial.
   
 simpl in *.
 destruct fr_rac_c @fresh.
  elim H10; trivial.
  
  simpl.
  destruct fr_rac @fresh.
   elim H18; trivial.
   
   simpl in *.
   split; intros.
    rename t into fr_rac_c_top.
    rename t0 into fr_rac_top.
    rename s0 into fr_rac_tail.
    destruct H17 with loc.
    clear H22.
    destruct H19.
     destruct H21 with n; trivial.
      left; trivial.
      
      destruct H22 as (m0, H22).
      left.
      exists m0.
      destruct H22.
      split; simpl; trivial.
      destruct m0.
       simpl in *.
       rewrite ObjSet2LocSet_def in H23 |- *.
       unfold LocInObjSet in H23 |- *.
       destruct loc.
        inversion H23.
        
        apply ObjSet.mem_1.
        apply ObjSet.union_3.
        apply ObjSet.mem_2 in H23; trivial.
        
        apply ObjSet.mem_1.
        apply ObjSet.union_3.
        apply ObjSet.mem_2 in H23; trivial.
        
       simpl; trivial.
       
      right; trivial.
      
     unfold LocInObjSet in H19.
     destruct loc.
      inversion H19.
      
      apply ObjSet.mem_2 in H19.
      apply ObjSet.union_1 in H19.
      destruct H19.
       left.
       exists 0%nat.
       split.
        split.
         lia.
         
         simpl.
         intuition auto with arith.
         
        simpl.
        rewrite ObjSet2LocSet_def.
        unfold LocInObjSet.
        apply ObjSet.mem_1.
        apply ObjSet.union_2.
        unfold ObjSet.Equal in H8.
        rewrite <- H8.
        trivial.
        
       destruct H21 with n; trivial.
        right.
        unfold LocInObjSet.
        apply ObjSet.mem_1; trivial.
        
        destruct H22 as (m0, H22).
        unfold ObjSet.Equal in H16.
        apply H16 in H19.
        left.
        exists m0.
        destruct H22.
        split.
         simpl in *.
         trivial.
         
         destruct m0.
          simpl in *.
          rewrite ObjSet2LocSet_def in H23 |- *.
          unfold LocInObjSet in H23 |- *.
          apply ObjSet.mem_1.
          apply ObjSet.union_3.
          apply ObjSet.mem_2 in H23; trivial.
          
          simpl; trivial.
          
        right; trivial.
        
      apply ObjSet.mem_2 in H19.
      apply ObjSet.union_1 in H19.
      destruct H19.
       left.
       exists 0%nat.
       split.
        split.
         lia.
         
         simpl.
         intuition auto with arith.
         
        simpl.
        rewrite ObjSet2LocSet_def.
        unfold LocInObjSet.
        apply ObjSet.mem_1.
        apply ObjSet.union_2.
        unfold ObjSet.Equal in H8.
        rewrite <- H8.
        trivial.
        
       destruct H21 with n; trivial.
        right.
        unfold LocInObjSet.
        apply ObjSet.mem_1; trivial.
        
        destruct H22 as (m0, H22).
        unfold ObjSet.Equal in H16.
        apply H16 in H19.
        left.
        exists m0.
        destruct H22.
        split.
         simpl in *.
         trivial.
         
         destruct m0.
          simpl in *.
          rewrite ObjSet2LocSet_def in H23 |- *.
          unfold LocInObjSet in H23 |- *.
          apply ObjSet.mem_1.
          apply ObjSet.union_3.
          apply ObjSet.mem_2 in H23; trivial.
          
          simpl; trivial.
          
        right; trivial.
        
    rename t into fr_rac_c_top.
    rename t0 into fr_rac_top.
    rename s0 into fr_rac_tail.
    case_eq (LocInObjSet loc fr_rac_c_top); intros.
     right.
     unfold LocInObjSet in H20 |- *.
     destruct loc.
      inversion H20.
      
      apply ObjSet.mem_1.
      apply ObjSet.union_2.
      unfold ObjSet.Equal in H8.
      rewrite H8.
      apply ObjSet.mem_2 in H20; trivial.
      
      apply ObjSet.mem_1.
      apply ObjSet.union_2.
      unfold ObjSet.Equal in H8.
      rewrite H8.
      apply ObjSet.mem_2 in H20; trivial.
      
     destruct H17 with loc.
     clear H21.
     destruct H22.
      intros.
      apply H19 in H21.
      destruct H21.
       destruct H21 as (m0, H21).
       destruct H21.
       left.
       exists m0.
       split.
        simpl in *.
        trivial.
        
        destruct m0.
         simpl in *.
         rewrite ObjSet2LocSet_def in H22 |- *.
         unfold LocInObjSet in H22 |- *.
         destruct loc.
          inversion H22.
          
          unfold LocInObjSet in H20.
          apply ObjSet.mem_2 in H22.
          apply ObjSet.union_1 in H22.
          destruct H22.
           apply ObjSet.mem_1 in H22.
           rewrite H20 in H22.
           inversion H22.
           
           apply ObjSet.mem_1.
           trivial.
           
          unfold LocInObjSet in H20.
          apply ObjSet.mem_2 in H22.
          apply ObjSet.union_1 in H22.
          destruct H22.
           apply ObjSet.mem_1 in H22.
           rewrite H20 in H22.
           inversion H22.
           
           apply ObjSet.mem_1.
           trivial.
           
         simpl; trivial.
         
       right; trivial.
       
      left; trivial.
      
      right.
      unfold LocInObjSet in H21 |- *.
      destruct loc.
       inversion H21.
       
       auto with *.
       
       auto with *.
       
 destruct fr_rac_c @fresh.
  elim H10; trivial.
  
  simpl.
  destruct fr_rac @fresh.
   elim H18; trivial.
   
   simpl.
   auto with *.
Qed.

(** No action needed in the semantics (this function will be used in RAC3) *)

  Definition FieldUpdateAction (p : Program) (loc : Location) (v : Value) (st : State.t) : State.t :=
    st.

  Lemma FieldUpdateAction_Correct:
    forall p loc st_rac st_rac' st_sem st_sem' v,
    CorrespondingState p st_rac st_sem ->
    FieldUpdateAction p loc v st_rac = st_rac' ->
    Sem.Assignables.FieldUpdateAction p loc v st_sem = st_sem' ->
    CorrespondingState p st_rac' st_sem'.
  Proof.
  intuition.
  unfold FieldUpdateAction in H0.
  unfold Sem.Assignables.FieldUpdateAction in H1.
  subst.
  trivial.
Qed.

End Assignables.

End Rac1.
