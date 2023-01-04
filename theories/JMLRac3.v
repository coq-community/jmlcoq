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

From JML Require Export JMLRac2.
From Coq Require Import List.
From JML Require Import Stack.
From Coq Require Import ListSet.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Relation_Operators.
From JML Require Import ListHelpers.
From Coq Require Import Classical.
From Coq Require Import DecidableType.
From Coq Require Import FSetInterface.
From Coq Require Import FSetProperties.
From Coq Require Import FSetEqProperties.
From Coq Require Import FSetFacts.
From Coq Require Import Sumbool.
From Coq Require Import Lia.

Import Dom.
Import Prog.
Import JmlNotations.
Import METHODSPEC.
Import TYPESPEC.

Module LocSetProp := Properties LocSet.
Import LocSetProp.
Module LocSetPropEq := EqProperties LocSet.
Import LocSetPropEq.
Module LocSetFacts := Facts LocSet.
Import LocSetFacts.

Open Scope jml_scope.

(** * The JML Runtime Assertion Checker Rac3
This module describes the runtime assertions checks for suported JML-Level 0 constructs *)

Module Rac3 <: JML.

(** ** Implementation of the JML Frame for Rac3 *)

  Declare Module LocDict: DICT 
    with Definition Key := (* pivot *) Location
    with Definition Val := (* dg *) LocSet.t.


  Declare Module Backlinks : DICT 
    with Definition Key := (* field *) Location
    with Definition Val := LocDict.t.



Definition StaticDGs (p : Program) (f : Location) : list Location :=
  match f with
  | Heap.InstanceField obj fsig =>
    match findField p fsig with
    | Some f =>
      let dgs := FIELD.dataGroups f in
      let dgs_static := filter (fun dg => negb (DATA_GROUP.isDynamic dg)) dgs in
      let dgfsig := flat_map DATA_GROUP.dataGroups dgs_static in
      map (Heap.InstanceField obj) dgfsig
    | _ => []
    end
  | _ => []
  end.

Lemma StaticDGs_Correct:
forall p field_am dg_am,
In dg_am (StaticDGs p field_am) <-> direct_FieldInDg_static p field_am dg_am.
Proof.
intuition.
 unfold StaticDGs in H.
 case_eq field_am; intros; subst; try inversion H.
 case_eq (findField p f); intros; rewrite H0 in H; try inversion H.
 apply in_map_iff in H.
 destruct H as [dg_fsig H].
 destruct H.
 apply in_flat_map in H1.
 destruct H1 as [dg H1].
 destruct H1.
 apply filter_In in H1.
 destruct H1.
 split with o dg_fsig o f f0 dg; auto.
 case_eq (DATA_GROUP.isDynamic dg); intros.
  rewrite H4 in H3; inversion H3.
  
  trivial.
  
 destruct H.
 unfold StaticDGs.
 rewrite H0.
 rewrite H2.
 apply in_map_iff.
 exists dg_fsig.
 rewrite <- H1.
 split; auto.
 apply in_flat_map.
 exists dg.
 rewrite filter_In.
 split.
  split.
   trivial.
   
   rewrite H4.
   simpl; trivial.
   
  trivial.
Qed.


Fixpoint option_list2list {A : Type} (l: list (option A)) : list A :=
match l with
| nil => nil
| (h::t) =>
    match h with
    | Some a => (a :: option_list2list t)
    | _ => option_list2list t
    end
 end.

Lemma some_list_list:
forall {A : Type} (l : list (option A)) x,
In (Some x) l <-> In x (option_list2list l).
Proof.
induction l.
 simpl.
 tauto.
 
 intros.
 simpl.
 split; intro.
  destruct H.
   rewrite H.
   auto with *.
   
   rewrite IHl in H.
   destruct a.
    auto with *.
    
    trivial.
    
  case_eq a.
   intros.
   rewrite H0 in H.
   simpl in H.
   destruct H.
    rewrite H.
    tauto.
    
    right.
    rewrite IHl; trivial.
    
   intros.
   right.
   rewrite IHl.
   rewrite H0 in H.
   trivial.
Qed.

Declare Module FsigDec : DecidableType with Definition t := FieldSignature
	                                with Definition eq := eq (A := FieldSignature).

Definition DynamicDGs (p : Program) (f_fsig : FieldSignature) (pivot : Location) : list Location :=
  match pivot with
  | Heap.InstanceField pivot_obj pivot_fsig =>
    match findField p pivot_fsig with
    | Some pivot_f =>
      let dgs_dyn := filter (fun dg => DATA_GROUP.isDynamic dg) (FIELD.dataGroups pivot_f) in
                let dgs_f_target := filter (fun dg => 
                  match DATA_GROUP.pivotTarget dg with
                  | Some (FieldDg fsig) => if FsigDec.eq_dec fsig f_fsig then true else false
                  | _ => false
                  end        
                  ) dgs_dyn in
                let dg_fsig := flat_map DATA_GROUP.dataGroups dgs_f_target in
                map (Heap.InstanceField pivot_obj) dg_fsig
      | _ => []
    end
  | _ => []
  end.

Lemma DynamicDGs_Correct:
forall p h f_obj f_fsig pivot dg,
Heap.get h pivot = Some (Ref f_obj) ->
(In dg (DynamicDGs p f_fsig pivot) <-> direct_FieldInDg_dynamic p h (Heap.InstanceField f_obj f_fsig) dg pivot).
Proof.
intuition.
 unfold DynamicDGs in H0.
 case_eq pivot; intros; rewrite H1 in H0; try inversion H0.
 rename o into pivot_obj.
 rename f into pivot_fsig.
 case_eq (findField p pivot_fsig); intros; rewrite H2 in H0; try inversion H0.
 rename f into pivot_f.
  apply in_map_iff in H0.
  destruct H0 as (dg_fsig, H0).
  destruct H0.
  apply in_flat_map in H3.
  destruct H3 as (dgt, H3).
  destruct H3.
  apply filter_In in H3.
  destruct H3.
  apply filter_In in H3.
  destruct H3.
  case_eq (DATA_GROUP.pivotTarget dgt); intros; rewrite H7 in H5.
   case_eq d; intros.
   rewrite H8 in H5.
   rewrite H8 in H7.
   clear d H8.
   case_eq (FsigDec.eq_dec fsig f_fsig); intros.
    unfold FsigDec.eq in e.
    rewrite e in H7.
    clear H5 H8.
    clear fsig e.
    split
     with pivot_obj dg_fsig f_obj f_fsig pivot_obj pivot_fsig pivot_f dgt;
     trivial.
     auto.
     
     rewrite <- H1; trivial.
     
    rewrite H8 in H5; inversion H5.
    
   inversion H5.
   
 inversion H0.
 unfold DynamicDGs.
 rewrite H3.
 rewrite H5.
 inversion H2.
 rewrite <- H16.
  
   apply in_map_iff.
   exists dg_fsig.
   split.
    rewrite <- H10; auto.
    
    apply in_flat_map.
    exists dg0.
    rewrite filter_In.
    split.
     split.
      rewrite filter_In.
      split.
       trivial.
       
       trivial.
       
      rewrite H8.
    destruct FsigDec.eq_dec.
     trivial.
     
     elim n.
     auto.
     
   trivial.
Qed.

Definition PivotTargets (p : Program) (pivot : Location) : list FieldSignature :=
  match pivot with 
  | Heap.InstanceField pivot_obj pivot_fsig =>
    match findField p pivot_fsig with
    | Some pivot_f =>
      let dgs_dyn := filter (fun dg => DATA_GROUP.isDynamic dg) (FIELD.dataGroups pivot_f) in
      let fsigs_option := (map (fun dg => match (DATA_GROUP.pivotTarget dg) with 
                                                            | Some (FieldDg fsig) => Some fsig
                                                            | _ => None end) dgs_dyn) in
       option_list2list fsigs_option
    | _ => []
    end
  | _ => []
  end.

Lemma PivotTargets_Correct:
forall p h f_fsig f_obj pivot,
Heap.get h pivot = Some (Ref f_obj) ->
(In f_fsig (PivotTargets p pivot) <-> exists dg, direct_FieldInDg_dynamic p h (Heap.InstanceField f_obj f_fsig) dg pivot).
Proof.
intuition.
 unfold PivotTargets in H0.
 case_eq pivot; intros; rewrite H1 in H0; try inversion H0.
 rename o into pivot_obj.
 rename f into pivot_fsig.
 case_eq (findField p pivot_fsig); intros; rewrite H2 in H0; try inversion H0.
 apply some_list_list in H0.
 apply in_map_iff in H0.
 destruct H0 as (dg, H0).
 destruct H0.
 case_eq (DATA_GROUP.pivotTarget dg); intros; rewrite H4 in H0.
  case_eq d; intros; rewrite H5 in H0.
  apply filter_In in H3.
  destruct H3.
  generalize DATA_GROUP.dataGroups_not_nil.
  intro.
  specialize H7 with dg.
  case_eq (DATA_GROUP.dataGroups dg); intros.
   elim H7; trivial.
   
   exists (Heap.InstanceField pivot_obj f0).
   split with pivot_obj f0 f_obj f_fsig pivot_obj pivot_fsig f dg; trivial.
    rewrite <- H1; trivial.
    
    inversion H0.
    rewrite H10 in H5.
    rewrite <- H5.
    trivial.
    
    rewrite H8.
    auto with *.
    
     inversion H0.
   
 destruct H0 as (dg, H0).
 inversion H0.
 unfold PivotTargets.
 rewrite H3.
 rewrite H5.
  
  apply some_list_list.
   apply in_map_iff.
   exists dg0.
   rewrite H8.
   inversion H2.
   split;auto.
   apply filter_In.
   split.
   trivial.
   trivial.
Qed.

Lemma PivotTargets_not_nil:
forall p pivot,
PivotField p pivot ->
exists fsig , In fsig (PivotTargets p pivot).
Proof.
intros.
inversion H.
unfold PivotTargets.
rewrite H0.
rewrite H1.
case_eq (DATA_GROUP.pivotTarget dg);intros.
 destruct d.
 exists fsig0.
 apply some_list_list.
 apply in_map_iff.
 exists dg.
 rewrite H4.
 split; trivial.
 apply filter_In.
 tauto.
unfold DATA_GROUP.isDynamic in H3.
rewrite H4 in H3.
inversion H3.
Qed.


  Definition set_backlink (bl :Backlinks.t) (f : Location) (pivot : Location) (dgs: LocSet.t) : Backlinks.t :=
    match Backlinks.get bl f with
    | None => 
      Backlinks.update bl f (LocDict.singleton pivot dgs)
    | Some amdict => 
      let amdict' := LocDict.update amdict pivot dgs in 
      Backlinks.update bl f amdict'
    end.

  Definition remove_backlink (bl : Backlinks.t) (f : Location) (pivot: Location) : Backlinks.t :=
    match Backlinks.get bl f with
    | None => bl
    | Some amdict =>
      let amdict' := LocDict.remove amdict pivot in
      Backlinks.update bl f amdict'
    end.

  Definition get_backlinks (bl : Backlinks.t) (f: Location) : LocDict.t :=
  match Backlinks.get bl f with
  | None => LocDict.empty
  | Some am => am
  end.

Module Adds <: ADDS.

  Record t_rec : Type := make {
    backlinks: Backlinks.t
  }.

  Definition t := t_rec.

End Adds.

Module FrameAdds := Rac2.FrameAdds.

Module Frame := Rac2.Frame.
Declare Module State : STATE 
  with Module Frame := Frame 
  with Module Adds := Adds.

Module Notations.

  Declare Scope rac3_scope.
  Delimit Scope rac3_scope with rac3.

  Open Scope rac3_scope.

  Notation "st '@h'" := (State.h st) (at level 1, left associativity): rac3_scope.
  Notation "st '@fr'" := (State.fr st) (at level 1, left associativity) : rac3_scope.
  Notation "st '@adds'" := (State.adds st) (at level 1, left associativity) : rac3_scope.
  Notation "st '@bl'" := (Adds.backlinks st@adds) (at level 1, left associativity) : rac3_scope.

  Notation "st '[h' ':=' h ']'" := (State.set_h st h) (at level 1, left associativity): rac3_scope.
  Notation "st '[fr' ':=' fr ']'" := (State.set_fr st fr) (at level 1, left associativity) : rac3_scope.
  Notation "st '[adds' ':=' adds ']'" := (State.set_adds st adds) (at level 1, left associativity) : rac3_scope.
  Notation "st '[bl' ':=' bl ']'" := (st[adds := Adds.make bl]) (at level 1, left associativity) : rac3_scope.
  Notation "[ h , fr , adds ]" := (State.build h fr adds) : rac3_scope.

End Notations.


Import Sem.Notations.
Import Rac1.Notations.
Import Rac2.Notations.
Import Notations.

Open Scope nat_scope.

(** A new JML Frame is initialized with the assignable locations from the caller *)
Definition NewFrame (m : Method) (p : ParamDict.t) (st : State.t) : Frame.t :=
  let adds := FrameAdds.make ((LocSet.empty,LocSetAll)::st@fr@assignables) (ObjSet.empty::st@fr@fresh) (st@h , p) VarDict.empty in
  Frame.build m p adds.

Inductive DGTree :=  DGNode (am : Location) (dgs: list DGTree).

Section correct_dgtree_ind.
Variables (P : DGTree ->  Prop) (Q : list DGTree ->  Prop).
Hypotheses
   (H : forall (a : Location) (l : list DGTree), Q l ->  P (DGNode a l))
   (H0 : Q nil)
   (H1 : forall (t : DGTree),
         P t -> forall (l : list DGTree ), Q l ->  Q (cons t l)).

Fixpoint DGTree_ind2 (t : DGTree) : P t :=
 match t as x return P x with
    DGNode a l =>
      H a l ((fix l_ind (l' : list DGTree) : Q l' :=
                     match l' as x return Q x with
                     | nil => H0
                     | cons t1 tl => H1 t1 (DGTree_ind2 t1) tl (l_ind tl)
                     end) l)
 end.
End correct_dgtree_ind.

Inductive InDG (dg : Location) (tree : DGTree) : Prop :=
| InDG_base: 
  forall kids,
  tree = (DGNode dg kids) ->
  InDG dg tree
| InDG_step:
  forall kids f tree',
  tree = (DGNode f kids) ->
  dg <> f ->
  In tree' kids ->
  InDG dg tree' ->
  InDG dg tree.

Fixpoint InDGTree (dg : Location) (tree : DGTree) : bool :=
match tree with
| DGNode f kids =>
  if LocDec.eq_dec dg f then true
  else fold_right (fun tree' => (orb (InDGTree dg tree'))) false kids
end.

Definition DGSubTree (t1 t2: DGTree) : Prop :=
forall a,
InDG a t1 -> InDG a t2.

Lemma fold_right_andb:
forall (A : Type) (l : list A) f,
fold_right (fun elem b => (f elem) && b) true l = true <-> (forall elem, In elem l -> f elem = true).
Proof.
split; intros.
 induction l.
  inversion H0.
  
  simpl in H0.
  simpl in H.
  rewrite andb_true_iff in H.
  destruct H.
  destruct H0.
   rewrite <- H0; trivial.
   
   apply IHl; trivial.
   
 induction l.
  simpl; trivial.
  
  simpl.
  rewrite andb_true_iff.
  split.
   apply H.
   auto with *.
   
   apply IHl.
   intros.
   apply H.
   auto with *.
Qed.

Lemma fold_right_orb:
forall (A : Type) (l : list A) f,
fold_right (fun elem b => (f elem) || b) false l = true <-> (exists elem, In elem l /\ f elem = true).
Proof.
split;intros.
induction l.
 simpl in H.
 discriminate H.
 
 simpl in H.
 apply orb_prop in H.
 destruct H.
  exists a.
  auto with *.
  
  apply IHl in H.
  destruct H.
  exists x.
  intuition auto with datatypes.

 destruct H as (elem, H).
 destruct H.
 induction l.
  inversion H.
  
  simpl.
  apply orb_true_intro.
  destruct H.
   left.
   rewrite H.
   trivial.
   
   right.
   apply IHl.
   trivial.
Qed.

Lemma LocSet_fold_orb:
forall f s,  LocSet.fold (fun e b => (f e) || b) s false = true <-> exists e, LocSet.In e s /\ f e = true.
Proof.
intros.
rewrite LocSet.fold_1.
rewrite <- fold_left_rev_right.
rewrite fold_right_orb.
split; intros.
 destruct H as (e, H).
 rewrite <- in_rev in H.
 exists e.
 destruct H.
 split.
  apply LocSet.elements_2.
  unfold LocSet.E.eq.
  clear H0.
  induction (LocSet.elements s).
   inversion H.
   
   simpl in H.
   destruct H.
    apply InA_cons_hd.
    auto.
    
    apply InA_cons_tl.
    apply IHl; trivial.
    
  trivial.
  
 destruct H as (e, H).
 exists e.
 split.
  destruct H.
  rewrite <- in_rev.
  apply LocSet.elements_1 in H.
  unfold LocSet.E.eq in H.
  induction H.
   left; auto.
   
   right.
   trivial.
   
  tauto.
Qed.

Lemma fold_right_union:
forall e l,
LocSet.In e (fold_right LocSet.union LocSet.empty l) 
<->
exists s, In s l /\ LocSet.In e s.
Proof.
induction l.
 intuition.
  simpl in H.
  apply LocSet.empty_1 in H.
  tauto.
  
  destruct H.
  tauto.
  
 simpl.
 intuition.
  apply LocSet.union_1 in H1.
  destruct H1.
   exists a.
   split; tauto.
   
   apply H in H1.
   destruct H1.
   exists x.
   split; tauto.
   
  destruct H1.
  destruct H1.
  destruct H1.
   apply LocSet.union_2.
   rewrite H1.
   trivial.
   
   apply LocSet.union_3.
   apply H0.
   exists x.
   tauto.
Qed.

Lemma In_InA: 
forall x l,
InA LocSet.E.eq x l <-> In x l.
Proof.
intros.
induction l.
simpl.
intuition.
inversion H.
simpl.
intuition.
inversion H1.
subst.
left.
auto.
subst.
right.
apply H;trivial.
Qed.

Lemma InDGTree_Correct:
forall tree dg,
InDG dg tree <-> InDGTree dg tree = true.
Proof.
split;intros.
induction H.
 subst.
 simpl.
 case_eq (LocDec.eq_dec dg dg); intro; trivial.
 elim n; trivial.
 
 unfold InDGTree.
 rewrite H.
 destruct LocDec.eq_dec; trivial.
fold InDGTree.
 apply fold_right_orb.
 exists tree'.
 tauto.

generalize dg H.
clear dg H.
elim tree using
 DGTree_ind2
  with
    (Q := fun kids =>
          forall dg tree',
          In tree' kids -> InDGTree dg tree' = true -> InDG dg tree').
 intros.
 unfold InDGTree in H0.
 case_eq (LocDec.eq_dec dg a).
  intros.
  apply InDG_base with l.
  unfold LocDec.eq in e.
  rewrite e.
  trivial.
  
  intros.
  unfold LocDec.eq in n.
  rewrite H1 in H0.
  apply fold_right_orb in H0.
  destruct H0 as (tree', H0).
  destruct H0.
  apply InDG_step with l a tree'; trivial.
  apply H; trivial.
  
 intros.
 inversion H.
 
 intros.
 simpl in H1.
 destruct H1.
  rewrite <- H1.
  rewrite <- H1 in H2.
  apply H; trivial.
  
  apply H0; trivial.
Qed.


Definition FieldOfNode (n : DGTree) : LocSet.elt :=
match n with
| DGNode f _ => f
end.

Inductive ValidDGTree (p : Program) (bl : Backlinks.t) (ep : LocSet.t) 
                 (f : Location) (m : LocSet.t) : DGTree -> Prop :=
| ValidDGTree_def:
  forall  dg dgs ad f'list f'list',
  dg = DGNode f dgs ->
  get_backlinks bl f = ad ->
  (LocSet.elements (fold_right (LocSet.union) 
        LocSet.empty 
        (LocDict.filter ad (fun f'' => ~ LocSet.In f'' ep))))  
        +++ (StaticDGs p f) = f'list' ->
  filter (fun f'' => LocSet.mem f'' m) f'list' = f'list ->
  length dgs = length f'list ->
  (forall n f'' f' dgs', 
    n < length dgs ->
    nth n  f'list f'' = f' ->
    nth n dgs (DGNode f'' []) = dgs' ->
    ValidDGTree p bl ep f' (LocSet.remove f' m) dgs') ->
  ValidDGTree p bl ep f m dg.

Lemma ValidDGTree_func: forall p bl ep tree f m,
ValidDGTree p bl ep f m tree ->
forall tree',
ValidDGTree p bl ep f m tree' -> 
tree = tree'.
Proof.
intros p bl ep tree.
elim tree using
 DGTree_ind2
  with
    (Q := fun kids =>
          forall k f m,
          In k kids ->
          ValidDGTree p bl ep f (LocSet.remove f m) k ->
          forall k', ValidDGTree p bl ep f (LocSet.remove f m) k' -> eq k k').
 intros.
 inversion H0.
 inversion H1.
 rewrite H9.
 inversion H2.
 rewrite H18 in H.
 assert (eq dgs dgs0).
  rewrite H3 in H10.
  rewrite <- H10 in H11.
  rewrite H4 in H11.
  rewrite <- H11 in H12.
  rewrite H5 in H12.
  rewrite <- H12 in H13.
  rewrite <- H12 in H14.
  rewrite <- H6 in H13.
  clear a l H0 tree' H1 dg ad f'list' H2 H3 H4 H5 H8 dg0 ad0 f'list0 f'list'0
   H9 H10 H11 H12 H15 H17 H18.
  assert
   (forall n f'',
    (nth n dgs (DGNode f'' nil)) = (nth n dgs0 (DGNode f'' nil))).
   intros.
   case_eq (Nat.compare n (length dgs)); intros.
    assert (le (length dgs) n).
     rewrite nat_compare_Eq in H0.
     lia.
     
     generalize H1; intro.
     apply nth_overflow with (d := DGNode f'' nil) in H1.
     rewrite <- H13 in H2.
     apply nth_overflow with (d := DGNode f'' nil) in H2.
     rewrite H1; rewrite H2; trivial.
     
    rewrite <- nat_compare_lt in H0.
    apply H with (nth n f'list f'') m.
     apply nth_In; trivial.
     
     apply H7 with n f''; trivial.
     
     apply H14 with n f''; trivial.
     rewrite H13; trivial.
     
    assert (le (length dgs) n).
     rewrite <- nat_compare_gt in H0.
     lia.
     
     generalize H1; intro.
     apply nth_overflow with (d := DGNode f'' nil) in H1.
     rewrite <- H13 in H2.
     apply nth_overflow with (d := DGNode f'' nil) in H2.
     rewrite H1; rewrite H2; trivial.
     
   clear p bl ep tree H f m f'list H6 H7 H14.
   symmetry  in H13.
   generalize dgs0, H13, H0.
   clear dgs0 H13 H0.
   induction dgs.
    intros.
    destruct dgs0; trivial.
    inversion H13.
    
    intros.
    destruct dgs0.
     inversion H13.
     
     assert (eq a d).
      destruct a.
      specialize H0 with O am.
      simpl in H0; trivial.
      
      assert (eq dgs dgs0).
       apply IHdgs.
        auto.
        
        intros.
        specialize H0 with (S n) f''.
        simpl in H0; trivial.
        
       rewrite H; rewrite H1; trivial.
       
  rewrite H16; trivial.
  
 intros.
 inversion H.
 
 intros.
 simpl in H1.
 destruct H1.
  rewrite <- H1.
  rewrite <- H1 in H2.
  apply H with f (LocSet.remove f m); trivial.
  
  apply H0 with f m; trivial.
Qed.

Lemma ValidDGTree_exists: forall p bl ep m,
forall f, exists dg, ValidDGTree p bl ep f m dg.
Proof.
intros p bl ep m.
assert (exists n , n = LocSet.cardinal m).
exists (LocSet.cardinal m);trivial.
destruct H as [n H].
generalize n m H.
clear m n H.
induction n.

 intros.
 set (ad := get_backlinks bl f).
 set
  (f'list' :=
    (LocSet.elements (fold_right (LocSet.union) LocSet.empty (LocDict.filter ad (fun f'' => ~ LocSet.In f'' ep))))  +++ (StaticDGs p f)).
 exists (DGNode f nil).
 apply
  ValidDGTree_def
   with (dgs := nil) (ad := ad) (f'list' := f'list') (f'list := nil); 
  trivial.
  induction f'list'.
   simpl; trivial.
   
   simpl.
   symmetry  in H.
   rewrite <- LocSetProp.cardinal_Empty in H.
   replace (LocSet.mem a m) with false .
    trivial.
    
    case_eq (LocSet.mem a m); intro; trivial.
    apply LocSet.mem_2 in H0.
    unfold LocSet.Empty in H.
    destruct H with a; trivial.
    
  intros.
  simpl in H0.
  inversion H0.
  
 intros.
 set (ad := get_backlinks bl f).
 set
  (f'list' :=
    (LocSet.elements (fold_right (LocSet.union) LocSet.empty (LocDict.filter ad (fun f'' => ~ LocSet.In f'' ep))))  +++ (StaticDGs p f)).
 set (f'list := filter (fun f'' => LocSet.mem f'' m) f'list').
 set (dgsEx := (exists dgs, length dgs = length f'list /\ forall n f'' f' dgs', n < length dgs ->
    nth n  f'list f'' = f' ->
    nth n dgs (DGNode f'' []) = dgs' ->
    ValidDGTree p bl ep f' (LocSet.remove f' m) dgs')).
unfold ad in f'list'.

 elim classic with dgsEx; intros.
  destruct H0 as (dgs, H0).
  clear dgsEx.
  destruct H0.
  exists (DGNode f dgs).
  apply
   ValidDGTree_def
    with (dgs := dgs) (ad := ad) (f'list' := f'list') (f'list := f'list);
   trivial.
  
  elim H0.
unfold dgsEx.
  apply not_all_not_ex.
  intro.
  clear H0 dgsEx.
  induction f'list'.
   specialize H1 with (nil (A:=DGTree)).
   destruct H1.
   split.
    trivial.
    
    intros.
    inversion H0.
    
   apply IHf'list'.
   clear IHf'list'.
   intro.
   intro.
   case_eq (LocSet.mem a m); intro.
    specialize IHn with (m := LocSet.remove a m).
    destruct IHn with a.
     apply eq_add_S.
     rewrite H.
     symmetry .
     apply LocSetProp.remove_cardinal_1.
     apply LocSet.mem_2; trivial.
     apply H1 with (cons x n0).
     split.
      unfold f'list.
      simpl.
      rewrite H2.
      simpl.
      lia.
      
      destruct H0.
      intros.
      unfold f'list in H6.
      simpl in H6.
      rewrite H2 in H6.
      case_eq n1; intros.
       simpl in H7.
       rewrite H8 in H7.
       simpl in H6.
       rewrite H8 in H6.
       rewrite <- H6.
       rewrite <- H7.
       trivial.
       
       simpl in H7.
       apply H4 with n2 f''.
        rewrite H8 in H5.
        simpl in H5.
        auto with *.
        
        rewrite H8 in H6.
        simpl in H6.
        trivial.
        
        rewrite H8 in H7.
        trivial.

    apply H1 with n0.
    unfold f'list.
    simpl.
    rewrite H2.
    trivial.
Qed.

Lemma ValidDGTree_1:
forall p bl ep f m dg,
ValidDGTree p bl ep f m dg ->
exists dgs, dg = DGNode f dgs.
Proof.
intros.
inversion H.
exists dgs.
trivial.
Qed.

Lemma ValidDGTree_EqualSets:
forall p bl ep n f tree  s1 s2 ,
s1 [=] s2 ->
n = LocSet.cardinal s1 ->
ValidDGTree p bl ep f s1 tree ->
ValidDGTree p bl ep f s2 tree.
Proof.
intros p bl ep.
induction n.
 intros.
 inversion H1.
 symmetry  in H0.
 apply LocSetProp.cardinal_Empty in H0.
 assert (f'list = []).
  clear H4 H7 H6.
  generalize f'list, H5.
  clear f'list H5.
  induction f'list'.
   intros.
   simpl in H5.
   auto.
   
   intros.
   simpl in H5.
   assert (LocSet.mem a s1 = false).
    unfold LocSet.Empty in H0.
    specialize H0 with a.
    apply LocSetPropEq.mem_3; trivial.
    
    rewrite H4 in H5.
    intros.
    apply IHf'list'.
    trivial.
    
  rewrite H9 in H5.
  rewrite H9 in H7.
  apply ValidDGTree_def with dgs ad [] f'list'; trivial.
   assert (LocSet.Empty s2).
    unfold LocSet.Empty.
    intros.
    unfold LocSet.Empty in H0.
    unfold LocSet.Equal in H.
    intro.
    apply H in H10.
    elim H0 with a; trivial.
    
    clear H4 H5 H6 H7 H9.
    induction f'list'.
     simpl; trivial.
     
     assert (LocSet.mem a s2 = false).
      apply LocSetPropEq.mem_3; trivial.
      
      simpl.
      rewrite H4.
      trivial.
      
   rewrite H6.
   rewrite H9.
   trivial.
   
   intros.
   rewrite H6 in H10.
   rewrite H9 in H10.
   simpl in H10; inversion H10.
   
 intros.
 inversion H1.
 apply ValidDGTree_def with dgs ad f'list f'list'; trivial.
  generalize f'list, H5.
  clear f'list H4 H5 H6 H7.
  induction f'list'.
   simpl.
   trivial.
   
   simpl.
   intros.
   case_eq (LocSet.mem a s1); intros.
    rewrite H4 in H5.
    rewrite H in H4.
    rewrite H4.
    destruct f'list.
     inversion H5.
     
     specialize IHf'list' with f'list.
     rewrite IHf'list'.
      inversion H5.
      trivial.
      
      inversion H5; trivial.
      
    rewrite H4 in H5.
    rewrite H in H4.
    rewrite H4.
    rewrite IHf'list' with f'list; trivial.
    
  intros.
  specialize IHn with f' dgs' (LocSet.remove f' s1) (LocSet.remove f' s2).
  case_eq (LocSet.mem f' s1); intros.
   apply IHn.
    apply LocSetProp.Equal_remove; trivial.
    
    apply eq_add_S.
    rewrite H0.
    symmetry .
    apply LocSetPropEq.remove_cardinal_1; trivial.
    
    apply H7 with n0 f''; trivial.
    
   assert (LocSet.mem f' s1 = true).
    generalize nth_In.
    intros.
    assert (In f' f'list).
     rewrite <- H10.
     apply H13.
     rewrite <- H6.
     trivial.
     
     rewrite <- H5 in H14.
     clear H4.
     generalize f'list, H5.
     clear f'list H5 H10 H6 H7.
     induction f'list'.
      intros.
      simpl in *.
      inversion H14.
      
      intros.
      simpl in H5.
      case_eq (LocSet.mem a s1); intros.
       rewrite H4 in H5.
       simpl in H14.
       rewrite H4 in H14.
       case_eq (LocDec.eq_dec a f').
        intros.
        unfold LocDec.eq in e.
        rewrite <- e.
        trivial.
        
        intros.
        simpl in H14.
        destruct H14.
         elim n1.
         unfold LocDec.eq.
         trivial.
         
         destruct f'list.
          inversion H5.
          
          apply IHf'list' with f'list in H7; trivial.
          inversion H5.
          trivial.
          
       rewrite H4 in H5.
       simpl in H14.
       rewrite H4 in H14.
       apply IHf'list' with f'list in H14; trivial.
       
    rewrite H12 in H13.
    inversion H13.
Qed.

Parameter BuildDGTree: Program -> Backlinks.t -> (* excluded pivots *) LocSet.t -> (* field *) Location -> LocSet.t -> DGTree.
Axiom BuildDGTree_def: forall p bl ep f tree m,
ValidDGTree p bl ep f m tree <-> BuildDGTree p bl ep f m  = tree.

Definition FieldInDg_rac3 (p : Program) (bl : Backlinks.t) 
      ((* excluded pivots *) ep : LocSet.t) (f : Location) 
      (dg : Location) : bool :=
  InDGTree dg (BuildDGTree p bl ep f (LocSetAll \ (LocSet.singleton f))).


Definition CorrectBacklink (p : Program) (st : State.t) (f dg pivot : Location) : Prop :=
direct_FieldInDg_dynamic p st@h f dg pivot
<->
exists ams,  LocDict.get (get_backlinks st@bl f) pivot = Some ams /\ LocSet.In dg ams.

Definition CorrectBacklinks (p : Program) (st : State.t) : Prop :=
forall f dg pivot , CorrectBacklink p st f dg pivot.

Lemma LocDict_get_some:
forall bl f pivot ams,
LocDict.get (get_backlinks bl f) pivot = Some ams ->
exists ad, Backlinks.get bl f = Some ad.
Proof.
intros.
unfold get_backlinks in H.
case_eq (Backlinks.get bl f);intros.
exists v;trivial.
rewrite H0 in H.
rewrite LocDict.get_empty in H.
inversion H.
Qed.

Inductive EqualAssignables (a1 a2: list (LocSet.t * LocSet.t)) :=
EqualAssignables_def:
length a1 = length a2 ->
(forall n a,
  fst (nth n  a1 a) [=] fst (nth n  a2 a) /\
  snd (nth n  a1 a) [=] snd (nth n  a2 a)) ->
EqualAssignables a1 a2.

Inductive EqualFresh (f1 f2: stack ObjSet.t) :=
EqualFresh_def:
length f1 = length f2 ->
(forall n d,
  (nth n  f1 d) [[=]] (nth n  f2 d)) ->
EqualFresh f1 f2.

Inductive CorrespondingFrame : Rac2.Frame.t -> Frame.t -> Prop :=
| CorrespondingFrame_def:
  forall fr_rac2 fr_rac3,
  fr_rac2@params         = fr_rac3@params ->
  fr_rac2@vars           = fr_rac3@vars ->
  fr_rac2@pc             = fr_rac3@pc ->
  fr_rac2@ret            = fr_rac3@ret ->
  fr_rac2@pre            = fr_rac3@pre ->
  fr_rac2@quants         = fr_rac3@quants ->
  EqualFresh fr_rac2@fresh fr_rac3@fresh ->
  EqualAssignables fr_rac2@assignables fr_rac3@assignables -> 
  CorrespondingFrame fr_rac2 fr_rac3.

Inductive CorrespondingState (p : Program): Rac2.State.t -> State.t -> Prop :=
| CorrespondingState_def:
  forall st_rac2 st_rac3,
  CorrespondingFrame st_rac2@fr%rac2 st_rac3@fr ->
  st_rac2@h%rac2 = st_rac3@h ->
  CorrectBacklinks p st_rac3 ->
  CorrespondingState p st_rac2 st_rac3.

Lemma nil_length:
forall A (l : list A),
0 = length l -> l = nil.
Proof.
intuition.
unfold length in H.
destruct l;trivial.
inversion H.
Qed.

Lemma FieldInDg_rac_EqualSets:
forall p h s1 f dg,
Rac2.FieldInDg_rac p h s1 f dg ->
forall s2,
s1 [=] s2 ->
Rac2.FieldInDg_rac p h s2 f dg.
Proof.
intros p h s1 f dg H.
induction H; intros.
 apply Rac2.FieldInDg_rac_step with dg'.
  apply IHFieldInDg_rac1; trivial.
  
  apply IHFieldInDg_rac2; trivial.
  
 apply Rac2.FieldInDg_rac_static; trivial.
 
 apply Rac2.FieldInDg_rac_dynamic with pivot; trivial.
 intro.
 elim H0.
 apply H1; trivial.
 
 apply Rac2.FieldInDg_rac_same; trivial.
Qed.

(* field in rac as in second refinement, but terminating *)
Inductive FieldInDg_rac2 (p : Program) (h : Heap.t) (ep : LocSet.t) (s : LocSet.t): (* field *) Location -> (* dg *) Location -> Prop :=
  | FieldInDg_rac2_static : forall f dg dg',
    direct_FieldInDg_static p f dg' ->
    ~ LocSet.In dg' s ->
    FieldInDg_rac2 p h ep (LocSet.add dg' s) dg' dg ->
    FieldInDg_rac2 p h ep s f dg
  | FieldInDg_rac2_dynamic : forall f dg pivot dg',
    direct_FieldInDg_dynamic p h f dg' pivot ->
    ~ LocSet.In pivot ep ->
    ~ LocSet.In dg' s ->
    FieldInDg_rac2 p h ep (LocSet.add dg' s) dg' dg ->
    FieldInDg_rac2 p h ep s f dg
  | FieldInDg_rac2_base : forall f dg, 
    f = dg ->
    FieldInDg_rac2 p h ep s f dg.

Lemma FieldInDg_rac2_Correct:
forall p h ep1 ep2 f dg,
ep1 [=] ep2 ->
(Rac2.FieldInDg_rac p h ep1 f dg 
<->
FieldInDg_rac2 p h ep2 (LocSet.singleton f) f dg).
Admitted. (* Pen and paper proof *)

Lemma FieldInDg_rac2_EqualSet:
forall p h ep s1 f dg,
FieldInDg_rac2 p h ep s1 f dg -> 
forall s2, s1 [=] s2 ->
FieldInDg_rac2 p h ep s2 f dg.
Proof.
intros p h ep s1 f dg H.
induction H.
 intros.
 apply FieldInDg_rac2_static with dg'; trivial.
  intro; elim H0.
  apply H2.
  trivial.
  
  apply IHFieldInDg_rac2.
  auto with *.
  
 intros.
 apply FieldInDg_rac2_dynamic with pivot dg'; trivial.
  intro; elim H1.
  apply H3.
  trivial.
  
  apply IHFieldInDg_rac2.
  auto with *.
  
 intros.
 apply FieldInDg_rac2_base; trivial.
Qed.

Lemma LocSet_remove_diff_remove_add:
forall x y e,
LocSet.In e x ->
x \ (y \ {e})  [=] LocSet.add e (x \ y).
Proof.
split; intros.
 case_eq (MP.FM.eq_dec e a); intros.
  apply LocSet.add_1; trivial.
  
  apply LocSet.add_2.
  apply LocSet.diff_3.
   apply LocSet.diff_1 in H0; trivial.
   
   apply LocSet.diff_2 in H0.
   intro; elim H0.
   apply LocSet.remove_2; trivial.
   
 case_eq (MP.FM.eq_dec e a); intros.
  unfold LocDec.eq in e0; subst.
  apply LocSet.diff_3; trivial.
  apply LocSet.remove_1; trivial.
  
  apply LocSet.add_3 in H0; trivial.
  apply LocSet.diff_3.
   apply LocSet.diff_1 in H0; trivial.
   
   apply LocSet.diff_2 in H0.
   intro; elim H0.
   apply LocSet.remove_3 in H2; trivial.
Qed.

Lemma LocSet_diff_remove_diff_add:
forall x y e,
(x \ y) \ {e} [=] x \ (LocSet.add e y).
Proof.
split; intros.
 apply LocSet.diff_3.
  apply LocSet.remove_3 in H.
  apply LocSet.diff_1 in H.
  trivial.
  
  intro.
  apply LocSet.add_3 in H0.
   apply LocSet.remove_3 in H.
   apply LocSet.diff_2 in H.
   elim H; trivial.
   
   intro.
   unfold LocSet.E.eq in H1.
   rewrite H1 in H.
   apply LocSet.remove_1 in H.
    elim H.
    
    trivial.
    
 apply LocSet.remove_2.
  intro.
  unfold LocSet.E.eq in H0.
  rewrite H0 in H.
  apply LocSet.diff_2 in H.
  elim H.
  apply LocSet.add_1.
  trivial.
  
  apply LocSet.diff_3.
   apply LocSet.diff_1 in H.
   trivial.
   
   apply LocSet.diff_2 in H.
   intro; elim H.
   apply LocSet.add_2.
   trivial.
Qed.

Lemma FieldInDg_rac3_Correct:
forall p ep st f dg ,
CorrectBacklinks p st ->
(FieldInDg_rac2 p st@h ep (LocSet.singleton f) f dg 
<->
FieldInDg_rac3 p st@bl ep f dg = true).
Proof.
split;intros.
 unfold FieldInDg_rac3 in *.
 apply InDGTree_Correct.
 induction H0.
  elim
   ValidDGTree_exists
    with p st@bl ep (LocSetAll \ s) f; 
   trivial.
  intro tree.
  intro.
  replace (BuildDGTree p st@bl ep f (LocSetAll \ s)) with tree .
   destruct tree.
   inversion H3.
   assert (In dg' f'list').
    rewrite <- H6.
    apply in_or_app.
    right.
    apply StaticDGs_Correct; trivial.
    
    assert (In dg' f'list).
     clear H6.
     generalize f'list, H7, H11.
     clear f'list H7 H11 H8 H9.
     assert (LocSet.mem dg' (LocSetAll \ s) = true).
      rewrite LocSetPropEq.diff_mem.
      apply andb_true_iff.
      split.
       apply LocSet.mem_1.
       apply LocSetAll_def.
       
       apply negb_true_iff.
       apply LocSetPropEq.mem_3; trivial.
       
      induction f'list'.
       intros.
       inversion H11.
       
       intros.
       simpl in H11.
       destruct H11.
        subst.
        simpl.
        rewrite H6.
        simpl; left; trivial.
        
        simpl in H7.
        case_eq (LocSet.mem a (LocSetAll \ s)); intros; rewrite H9 in H7.
         destruct f'list.
          inversion H7.
          
          specialize IHf'list' with f'list.
          inversion H7.
          rewrite H13.
          apply IHf'list' in H13.
           auto with *.
           
           trivial.
           
         apply IHf'list'.
          trivial.
          
          trivial.
     
     apply in_nth with (d:=f) in H12.
      destruct H12 as [n H12].
      destruct H12.
      inversion H4.
      set (tree' := nth n dgs0 (DGNode f [])).
      specialize H9 with n f dg' tree'.
      case_eq (LocDec.eq_dec dg f); intros.
       unfold LocDec.eq in e.
       apply InDG_base with dgs0.
       rewrite e; trivial.
       
       apply InDG_step with dgs0 f tree'; trivial.
        unfold tree'.
        apply nth_In.
        rewrite H8; trivial.
        
        assert (BuildDGTree p st@bl ep dg' (LocSetAll \ (LocSet.add dg' s)) = tree').
         rewrite <- BuildDGTree_def.
         apply
          ValidDGTree_EqualSets
           with
             (n := LocSet.cardinal ((LocSetAll \ s) \ {dg'}))
             (s1 := (LocSetAll \ s) \ {dg'}); trivial.
             
             apply LocSet_diff_remove_diff_add.
             
          apply H9; trivial.
          rewrite H8; trivial.
          
         rewrite <- H17.
         trivial.

   symmetry .
   apply BuildDGTree_def; trivial.

  elim
   ValidDGTree_exists
    with p st@bl ep (LocSetAll \ s) f; 
   trivial.
  intro tree.
  intro.
  replace (BuildDGTree p st@bl ep f (LocSetAll \ s)) with tree .
  destruct tree.
   inversion H4.
   assert (In dg' f'list').
    rewrite <- H7.
    apply in_or_app.
    left.
    unfold CorrectBacklinks in H.
    unfold CorrectBacklink in H.
    unfold get_backlinks in H6.
    rewrite H in H0.
    destruct H0 as [amd H0].
    destruct H0.
    rewrite <- In_InA.
    apply LocSet.elements_1.
    apply fold_right_union.
    elim LocDict_get_some with st@bl f pivot amd;trivial.
    intros.
    rewrite H13 in H6.
    rewrite <- H6.
    exists amd.
    split;trivial.
    apply LocDict.filter_1.
    exists pivot.
    unfold get_backlinks in H0.
    rewrite H13 in H0.
    tauto.

    assert (In dg' f'list).
     clear H7.
     generalize f'list, H8, H12.
     clear f'list H8 H12 H9 H10.
     assert (LocSet.mem dg' (LocSetAll \ s) = true).
      rewrite LocSetPropEq.diff_mem.
      apply andb_true_iff.
      split.
       apply LocSet.mem_1.
       apply LocSetAll_def.
       
       apply negb_true_iff.
       apply LocSetPropEq.mem_3; trivial.
       
      induction f'list'.
       intros.
       inversion H12.
       
       intros.
       simpl in H12.
       destruct H12.
        subst.
        simpl.
        rewrite H7.
        simpl; left; trivial.
        
        simpl in H8.
        case_eq (LocSet.mem a (LocSetAll \ s)); intros; rewrite H10 in H8.
         destruct f'list.
          inversion H8.
          
          specialize IHf'list' with f'list.
          inversion H8.
          rewrite H14.
          apply IHf'list' in H14.
           auto with *.
           
           trivial.
           
         apply IHf'list'.
          trivial.
          
          trivial.
          
     apply in_nth with (d := f) in H13.
      destruct H13 as [n H13].
      destruct H13.
      inversion H4.
      set (tree' := nth n dgs0 (DGNode f [])).
      specialize H10 with n f dg' tree'.
      case_eq (LocDec.eq_dec dg f); intros.
       unfold LocDec.eq in e.
       apply InDG_base with dgs0.
       rewrite e; trivial.
       
       apply InDG_step with dgs0 f tree'; trivial.
        unfold tree'.
        apply nth_In.
        rewrite H9; trivial.
        
        assert (BuildDGTree p st@bl ep dg' (LocSetAll \ (LocSet.add dg' s)) = tree').
         rewrite <- BuildDGTree_def.
         apply
          ValidDGTree_EqualSets
           with
             (n := LocSet.cardinal ((LocSetAll \ s) \ {dg'}))
             (s1 := (LocSetAll \ s) \ {dg'}); trivial.
             
             apply LocSet_diff_remove_diff_add.
             
          apply H10; trivial.
          rewrite H9; trivial.
          
         rewrite <- H23.
         trivial.
      
   symmetry .
   apply BuildDGTree_def; trivial.

  assert(exists tree, BuildDGTree p st@bl ep f (LocSetAll \s) = tree).
  exists (BuildDGTree p st@bl ep f (LocSetAll \s)).
  trivial.
  destruct H1 as [tree H1].
  apply BuildDGTree_def in H1.
  replace (BuildDGTree p st@bl ep f (LocSetAll \s)) with tree.
  inversion H1.
  apply InDG_base with dgs.
  rewrite <- H0.
  trivial.
  symmetry.
  apply BuildDGTree_def;trivial.

apply FieldInDg_rac2_EqualSet with (LocSetAll \ (LocSetAll \ (LocSet.singleton f))).
unfold FieldInDg_rac3 in *.
apply InDGTree_Correct in H0.
assert
 (exists tree, BuildDGTree p st@bl ep f (LocSetAll \ LocSet.singleton f) = tree).
 exists (BuildDGTree p st@bl ep f (LocSetAll \ LocSet.singleton f)).
 trivial.
 
 destruct H1 as (tree, H1).
 rewrite H1 in H0.
 apply BuildDGTree_def in H1.
 induction H1.
 destruct H0.
  rewrite H0 in H1.
  inversion H1.
  apply FieldInDg_rac2_base.
  trivial.
  
  rewrite H0 in H1.
  inversion H1.
  apply in_nth with (d := DGNode f []) in H9.
  destruct H9 as (n, H9).
  destruct H9.
  set (f' := nth n f'list f).
  assert (In f' f'list).
   apply nth_In.
   rewrite <- H5.
   rewrite <- H13; trivial.
   assert (LocSet.In f' m).
    clear H3.
    generalize f'list, H4, f', H14.
    clear f'list H4 f' H14 H5 H6 H7.
    induction f'list'.
     intros.
     simpl in H4.
     rewrite <- H4 in H14.
     inversion H14.
     
     intros.
     simpl in H4.
     case_eq (LocSet.mem a m); intros; rewrite H3 in H4.
      destruct f'list.
       inversion H4.
       
       simpl in H14.
       destruct H14.
        rewrite <- H5.
        inversion H4.
        rewrite <- H7.
        apply LocSet.mem_2; trivial.
        
        apply IHf'list' with f'list.
         inversion H4; trivial.
         
         trivial.
         
      apply IHf'list' with f'list; trivial.
      
    specialize H6 with n f f' tree'.
    specialize H7 with n f f' tree'.
    assert (In f' f'list').
     rewrite <- H4 in H14.
     rewrite filter_In in H14.
     destruct H14; trivial.
     
     rewrite <- H3 in H16.
     apply in_app_or in H16.
     destruct H16.
      unfold CorrectBacklinks in H.
      unfold CorrectBacklink in H.
      apply In_InA in H16.
      apply LocSet.elements_2 in H16.
      apply fold_right_union in H16.
      destruct H16 as (ams, H16).
      rewrite LocDict.filter_1 in H16.
      destruct H16.
      destruct H16 as (pivot, H16).
      destruct H16.
      apply FieldInDg_rac2_dynamic with pivot f'; trivial.
       rewrite H.
       exists ams.
       split;trivial.
         rewrite H2;trivial.

       intro.
       apply LocSet.diff_2 in H19.
       elim H19;trivial.

       apply FieldInDg_rac2_EqualSet with (LocSetAll \ (m \ {f'})).
        rewrite <- H13 in H7.
        apply H7; trivial.
        
        apply LocSet_remove_diff_remove_add.
        apply LocSetAll_def.
        
      apply StaticDGs_Correct in H16.
      apply FieldInDg_rac2_static with f'; trivial.
       intro.
       apply LocSet.diff_2 in H17.
       elim H17; trivial.
       
       apply FieldInDg_rac2_EqualSet with (LocSetAll \ (m \ {f'})).
        rewrite <- H13 in H7.
        apply H7; trivial.
        
        apply LocSet_remove_diff_remove_add.
        apply LocSetAll_def.

  split; intros.
   apply LocSet.diff_2 in H1.
   assert (LocSet.In a LocSetAll).
    apply LocSetAll_def.
    
    assert (~ LocSet.In a (LocSetAll \ {f})).
     intro; elim H1.
     apply remove_diff_singleton; trivial.
     
     apply LocSet.singleton_2.
     unfold LocSet.E.eq.
     case_eq (MP.FM.eq_dec f a); intros.
      auto.
      
      elim H3.
      apply LocSet.remove_2.
       trivial.
       
       trivial.
       
   apply LocSet.diff_3.
    apply LocSetAll_def.
    
    intro.
    apply LocSet.diff_2 in H2.
    elim H2; trivial.
Qed.


Definition St3to2 (st: State.t) : Rac2.State.t :=
Rac2.State.build st@h st@fr Rac2.Adds.singleton.

(** Postpone this ... *)
Declare Module AnnotationTable : ANNOTATION_TABLE State.

Module Assignables <: ASSIGNABLES State.	

  Lemma NewFrame_Correct: forall p m param st_rac2 st_rac3 fr'_rac2 fr'_rac3,
  CorrespondingState p st_rac2 st_rac3 ->
  fr'_rac2 = Rac2.NewFrame m param st_rac2 ->
  fr'_rac3 = NewFrame m param st_rac3 ->
  CorrespondingState p st_rac2[fr:=fr'_rac2]%rac2 st_rac3[fr:=fr'_rac3].
  Proof.
intuition.
destruct H.
split.
 rewrite H0.
 rewrite H1.
 unfold NewFrame.
 unfold Rac2.NewFrame.
 destruct H.
 split; trivial.
  simpl.
  rewrite H2.
  trivial.
  
  simpl.
  split.
   destruct H9.
   simpl.
   rewrite e.
   trivial.
   
   destruct H9.
   simpl.
   destruct n.
    intros.
    apply ObjSet.eq_refl.
    
    trivial.
    
  simpl.
  split.
   destruct H10.
   simpl.
   rewrite e.
   trivial.
   
   destruct H10.
   simpl.
   destruct n.
    intros.
    split; simpl; apply LocSet.eq_refl.
    
    specialize a with (n := n).
    trivial.
    
 simpl; trivial.
 
 unfold CorrectBacklinks.
 intros.
 split; intros.
  unfold CorrectBacklinks in H3.
  simpl.
  apply H3.
  rewrite H1 in H4.
  unfold NewFrame in H4.
  simpl in H4; trivial.
  
  unfold CorrectBacklinks in H3.
  simpl in H4.
  apply H3 in H4.
  rewrite H1.
  unfold NewFrame.
  simpl.
  trivial.
Qed.

  Definition Assignable (p : Program) (bl : Backlinks.t) (f : Location) (a : LocSet.t * LocSet.t) : bool :=
      LocSet.fold
         (fun dg b => (FieldInDg_rac3 p bl (fst a) f dg) || b)
         (snd a)
         false.

  Definition FieldUpdateCheck (p : Program) (loc : Location) (st : State.t): Prop :=
  forall n,
  (n < length st@fr@assignables)%nat ->
       (exists m, 
        (m <= n /\ m < length st@fr@fresh)%nat /\ LocSet.In loc (ObjSet2LocSet (nth m st@fr@fresh ObjSet.empty)))
    \/
        Assignable p st@bl loc (nth n st@fr@assignables (LocSet.empty,LocSet.empty)) = true.

  Lemma FieldUpdateCheck_Correct:
    forall am p st_rac2 st_rac3,
    CorrespondingState p st_rac2 st_rac3 ->
    ( Rac2.Assignables.FieldUpdateCheck p am st_rac2 <-> FieldUpdateCheck p am st_rac3).
Proof.
intros.
destruct H.
rename H1 into Hcorr.
inversion H.
clear H H1 H2 H3 H4 H5 H6.
subst.
rename H8 into H6.
rename H7 into H5.
rename H0 into H7.
unfold FieldUpdateCheck.
unfold Rac2.Assignables.FieldUpdateCheck.
intuition.
  destruct (H n).  
  inversion H6.
  rewrite H1.
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
   destruct am; trivial.
   inversion H5.
   unfold ObjSet.Equal in H4.
   apply ObjSet.mem_1.
   apply ObjSet.mem_2 in H2.
   apply H4.
   trivial.
   inversion H5.
   unfold ObjSet.Equal in H4.
   apply ObjSet.mem_1.
   apply ObjSet.mem_2 in H2.
   apply H4.
   trivial.

  right.
  unfold Assignable.
  apply LocSet_fold_orb.
  destruct H1.
  destruct H1.
  inversion H6.  
  specialize H4 with n (LocSet.empty, LocSet.empty).
  unfold LocSet.Equal in H4.
  destruct H4.  
  exists x.
  split; [apply H8; trivial|].
  rewrite <- FieldInDg_rac3_Correct; trivial.
  rewrite <- FieldInDg_rac2_Correct with (ep1 := fst (nth n st_rac2 @fr%rac2 @assignables (LocSet.empty, LocSet.empty) )); trivial.
  rewrite <- H7;trivial.
    
 destruct H with n.

  inversion H6.
  rewrite <- H1.
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
   destruct am; trivial.
   inversion H5.
   unfold ObjSet.Equal in H4.
   apply ObjSet.mem_1.
   apply ObjSet.mem_2 in H2.
   rewrite H4.
   trivial.
   inversion H5.
   unfold ObjSet.Equal in H4.
   apply ObjSet.mem_1.
   apply ObjSet.mem_2 in H2.
   rewrite H4.
   trivial.

  right.
  unfold Assignable in H1.
  apply LocSet_fold_orb in H1.

  inversion H6.
  specialize H3 with n (LocSet.empty, LocSet.empty).
  unfold LocSet.Equal in H3.
  destruct H3.
  destruct H1.
  exists x.
  destruct H1.
  split; [apply H4; trivial|].
  rewrite  FieldInDg_rac2_Correct with (ep2 := fst (nth n st_rac3 @fr@assignables (LocSet.empty, LocSet.empty) )); trivial.
  rewrite H7;trivial.    
  rewrite  FieldInDg_rac3_Correct; trivial.
Qed.

  Definition AssignablePivotTargets ( p : Program) (bl : Backlinks.t) (pivot : Location) (a : LocSet.t * LocSet.t) : LocSet.t :=
    list2LocSet (
      filter
        (fun f => 
	   match LocDict.get (get_backlinks bl f) pivot with
	   | Some dgs => if LocSet.fold (fun dg b => (Assignable p bl dg a) || b) dgs false  then true else false
	   | None => false
           end)
        (Backlinks.keys bl)).

  Lemma AssignablePivotTargets_Correct:
    forall p  st  a1 a2 pivot,
    CorrectBacklinks p st ->
    (fst a1) [=] (fst a2) ->
    (snd a1) [=] (snd a2) ->
    Rac2.AssignablePivotTargets p st@h pivot a1   [=]
    AssignablePivotTargets p st@bl pivot a2.
  Proof.
intros.
unfold CorrectBacklinks in H.
split; intros.
 destruct a1.
 destruct a2.
 simpl in *.
 rewrite Rac2.AssignablePivotTargets_def in H2.
 destruct H2 as (dg', H2).
 destruct H2.
 destruct H3 as (dg, H3).
 destruct H3.
 unfold AssignablePivotTargets.
 apply list2LocSet_1.
 apply filter_In.
 apply H in H2.
 destruct H2 as (dgs, H2).
 destruct H2.
 split.
  apply Backlinks.keys_1.
  intro.
  apply LocDict_get_some in H2.
  destruct H2.
  rewrite H2 in H6.
  inversion H6.
  
  rewrite H2.
  case_eq
   (LocSet.fold
      (fun (elem : LocSet.elt) (b : bool) =>
       Assignable p st @bl elem (t1, t2) || b) dgs false); 
   intro.
   trivial.
   
   rewrite <- not_true_iff_false in H6.
   rewrite LocSet_fold_orb in H6.
   elim H6.
   clear H6.
   exists dg'.
   split; trivial.
   unfold Assignable.
   simpl.
   rewrite LocSet_fold_orb.
   exists dg.
   split; trivial.
    rewrite <- H1; trivial.
    
    rewrite <- FieldInDg_rac3_Correct.
     rewrite <- FieldInDg_rac2_Correct with (ep1 := t); trivial.
     
     auto with *.
     
 destruct a1.
 destruct a2.
 simpl in *.
 rewrite Rac2.AssignablePivotTargets_def.
 unfold AssignablePivotTargets in H2.
 apply list2LocSet_1 in H2.
 apply filter_In in H2.
 destruct H2 as (H', H2).
 case_eq (LocDict.get (get_backlinks st @bl a) pivot); intros.
  rewrite H3 in H2.
  case_eq
   (LocSet.fold
      (fun (dg : LocSet.elt) (b : bool) =>
       Assignable p st @bl dg (t1, t2) || b) v false); 
   intros.
   apply LocSet_fold_orb in H4.
   destruct H4.
   destruct H4.
   exists x.
   split.
    apply H.
    exists v.
    auto.
    
    unfold Assignable in H5.
    apply LocSet_fold_orb in H5.
    simpl in H5.
    destruct H5 as (dg, H5).
    exists dg.
    rewrite H1.
    rewrite FieldInDg_rac2_Correct with (ep2 := t1); trivial.
    rewrite FieldInDg_rac3_Correct; trivial.
    destruct H5.
    auto.
    
   rewrite H4 in H2.
   inversion H2.
   
  rewrite H3 in H2.
  inversion H2.
Qed.

  Definition SavePreState (p : Program) 
                          (bl : Backlinks.t) 
                          (pivot : Location)
                          (assignable: LocSet.t * LocSet.t) : (LocSet.t * LocSet.t) :=
  if LocSet.mem pivot (fst assignable) then
    assignable
  else
    let fields := AssignablePivotTargets p bl pivot assignable in
    (LocSet.add pivot (fst assignable), LocSet.union fields (snd assignable)).

  Lemma SavePreState_same:
  forall p st pivot a3 a2,
  CorrectBacklinks p st ->
  (fst a2) [=] (fst a3) ->
  (snd a2) [=] (snd a3) ->
  (fst (Rac2.SavePreState p st@h pivot a2) [=] fst (SavePreState p st@bl pivot a3) /\
  snd (Rac2.SavePreState p st@h pivot a2) [=] snd (SavePreState p st@bl pivot a3)).
  Proof.
intros.
unfold SavePreState.
unfold Rac2.SavePreState.
case_eq (LocSet.mem pivot (fst a2 )); case_eq (LocSet.mem pivot (fst a3 )); intros;
 try rewrite <- not_true_iff_false in H2;
 try rewrite <- not_true_iff_false in H3; try apply LocSet.mem_2 in H2;
 try apply LocSet.mem_2 in H3.
 tauto.
 
 elim H2.
 apply LocSet.mem_1.
 rewrite <- H0.
 trivial.
 
 elim H3.
 apply LocSet.mem_1.
 rewrite H0.
 trivial.
 
 split; split; simpl.
  intros.
  apply add_iff in H4.
  destruct H4.
   apply LocSet.add_1.
   trivial.
   
   apply LocSet.add_2.
   rewrite <- H0; trivial.
   
  intros.
  apply add_iff in H4.
  destruct H4.
   apply LocSet.add_1.
   trivial.
   
   apply LocSet.add_2.
   rewrite H0; trivial.
   
  intros.
  rewrite <- AssignablePivotTargets_Correct with (a1 := a2); auto with *.
  apply LocSet.union_1 in H4.
  destruct H4.
   apply LocSet.union_2; trivial.
   
   apply LocSet.union_3.
   rewrite <- H1; trivial.
   
  intros.
  rewrite AssignablePivotTargets_Correct with (a2 := a3); auto with *.
  apply LocSet.union_1 in H4.
  destruct H4.
   apply LocSet.union_2; trivial.
   
   apply LocSet.union_3.
   rewrite H1; trivial.
Qed.

  (* Don't bother for now, just assume that this function yields the same assignable locations than in the semantics.*)
  Parameter EvalAssignableClause : Program -> Class -> Method -> State.t -> LocSet.t.
  Parameter EvalAssignableClause_def : 
    forall p c m st_rac2 st_rac3,
    CorrespondingState p st_rac2 st_rac3 ->
    (EvalAssignableClause p c m st_rac3 [=] Rac2.Assignables.EvalAssignableClause p c m st_rac2).

  Definition MethodCallAction (p : Program) (c : Class) (m : Method) (st : State.t) : State.t :=
  let ams := EvalAssignableClause p c m st in
  st[fr:=st@fr[assignables :+ (LocSet.empty, ams)]].

  Lemma MethodCallAction_Correct:
    forall p c m st_rac2 st_rac2' st_rac3 st_rac3',
    CorrespondingState p st_rac2 st_rac3 ->
    Rac2.Assignables.MethodCallAction p c m st_rac2 = st_rac2' ->
    MethodCallAction p c m st_rac3 = st_rac3' ->
    CorrespondingState p st_rac2' st_rac3'.
Proof.
intuition.
inversion H.
subst.
unfold MethodCallAction.
unfold Rac2.Assignables.MethodCallAction.
split; simpl.
 destruct H2.
 split; simpl; trivial.
 split.
  destruct H9.
  unfold replace_top.
  destruct fr_rac2@assignables; destruct fr_rac3@assignables;trivial.
  
  destruct H9.
  intros.
  unfold replace_top.
  destruct fr_rac2@assignables; destruct fr_rac3@assignables;trivial.
  inversion e.
  inversion e.
  destruct n.
  simpl.
  split.
  apply LocSet.eq_refl.
  rewrite EvalAssignableClause_def with (st_rac2 := st_rac2);trivial.
  apply LocSet.eq_refl.
    simpl.
    specialize a with (S n) a0.
    simpl in a.
    trivial.
    
 trivial.
 
 unfold CorrectBacklinks.
 simpl.
 trivial.
Qed.

(** Add all fields of a newly created object to the list of fresh locations, as well
to the assignable list *)

  Definition NewObjectAction (p : Program) (obj : Object) (st : State.t) : State.t :=
    st[fr:=st@fr[fresh :+ obj]].


  Lemma NewObjectAction_Correct:
    forall p l st_rac2 st_rac2' st_rac3 st_rac3',
    CorrespondingState p st_rac2 st_rac3 ->
    NewObjectAction p l st_rac3 = st_rac3' ->
    Rac2.Assignables.NewObjectAction p l st_rac2 = st_rac2' ->
    CorrespondingState p st_rac2' st_rac3'.
  Proof.
intuition.
subst.
inversion H.
split; trivial.
subst.
simpl in *.
destruct H0.
split; simpl; trivial.
subst.
unfold apply_top.
destruct H8.
destruct fr_rac2 @fresh; destruct fr_rac3 @fresh.
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
apply ObjSet.add_3 in H8;trivial.
rewrite <- e0;trivial.
case_eq(ObjDec.eq_dec l a);intros.
apply ObjSet.add_1;trivial.
apply ObjSet.add_2;trivial.
apply ObjSet.add_3 in H8;trivial.
rewrite e0;trivial.
   
   specialize e0 with (S n) d.
   simpl in e0.
   trivial.
Qed.

(** Upon method return, add all freshly created locations to the list of fresh locations from the caller *)

  Definition MethodReturnAction (p : Program) (st_c : State.t) (st : State.t) : State.t :=
    st_c[fr:=st@fr[fresh :\/ (peekd st_c@fr@fresh ObjSet.empty)][assignables := pop st_c@fr@assignables]].
    

  Lemma MethodReturnAction_Correct:
    forall p st_rac2 st_rac2_c st_rac2_c' st_rac3 st_rac3_c st_rac3_c',
    CorrespondingState p st_rac2_c st_rac3_c ->
    CorrespondingState p st_rac2 st_rac3 ->
    Rac2.Assignables.MethodReturnAction p st_rac2_c st_rac2 = st_rac2_c' ->
    MethodReturnAction p st_rac3_c st_rac3 = st_rac3_c' ->
    CorrespondingState p st_rac2_c' st_rac3_c'.
  Proof.
intuition.
subst.
unfold MethodReturnAction.
unfold Rac2.Assignables.MethodReturnAction.
inversion H.
inversion H1.
inversion H0.
inversion H16.
split; trivial.
split; simpl; trivial.

  unfold apply_top.
  destruct H27.
  destruct st_rac2 @fr%rac2 @fresh ; destruct  st_rac3 @fr @fresh;trivial.
      split;simpl;trivial.
    inversion e.
inversion e.
    split;simpl.
    trivial.
    intros.
    destruct n.
specialize e0 with O d.
simpl in e0.
 destruct H12.
 unfold peekd.
 destruct st_rac2_c @fr@fresh%rac2; destruct  st_rac3_c @fr @fresh ; simpl;trivial.
 apply UnionEqual.
 apply ObjSet.eq_refl.
 trivial.
 inversion e1.
inversion e1.
specialize e2 with O d.
simpl in e2.
apply  UnionEqual;trivial.
specialize e0 with (S n) d.
simpl in e0.
trivial.
 destruct H13.
 split.
  unfold pop.
  destruct st_rac2_c @fr%rac2 @assignables;
   destruct st_rac3_c @fr @assignables; trivial.
   inversion e.
   
   inversion e.
   
   simpl in e.
   auto.
   
  intros.
  unfold pop.
  destruct st_rac2_c @fr%rac2 @assignables;
   destruct st_rac3_c @fr @assignables; trivial.
   inversion e.
   
   inversion e.
   
   specialize a with (S n) a0.
   simpl in a.
   trivial.
Qed.

Definition RemoveBacklinks (p : Program) (pivot : Location) (st : State.t) : Backlinks.t :=
  match Heap.get st@h pivot with
  | Some (Ref obj) => 
    fold_right (fun f bl => remove_backlink bl (Heap.InstanceField obj f) pivot) st@bl (PivotTargets p pivot)
  | _ => st@bl
  end.

Definition SetBacklinks (p : Program) (pivot : Location) (v : Value) (bl : Backlinks.t) : Backlinks.t :=
match v with
| Ref obj => 
    fold_right (fun f bl' => set_backlink bl' (Heap.InstanceField obj f) pivot (list2LocSet (DynamicDGs p f pivot))) bl (PivotTargets p pivot)
| _ => bl
end.

Lemma get_remove_old_f_uncompat:
forall f p pivot st, 
(forall f_obj f_fsig , f <> Heap.InstanceField f_obj f_fsig) ->
get_backlinks st@bl f = get_backlinks (RemoveBacklinks p pivot st) f.
Proof.
intros.
destruct f.
 unfold RemoveBacklinks.
 destruct (Heap.get st @h pivot); trivial.
 destruct v; trivial.
 induction (PivotTargets p pivot); trivial.
 simpl.
 unfold remove_backlink at 1.
 destruct Backlinks.get.
  simpl.
  unfold get_backlinks.
  rewrite Backlinks.get_update_old; trivial.
  intuition.
  inversion H0; trivial.
  
  trivial.
  
 elim H with o f.
 trivial.
 
 unfold RemoveBacklinks.
 destruct (Heap.get st @h pivot); trivial.
 destruct v; trivial.
 induction (PivotTargets p pivot); trivial.
 simpl.
 unfold remove_backlink at 1.
 destruct Backlinks.get.
  simpl.
  unfold get_backlinks.
  rewrite Backlinks.get_update_old; trivial.
  intuition.
  inversion H0; trivial.
  
  trivial.
Qed.

Lemma get_set_old_f_uncompat:
forall f p pivot bl v, 
(forall f_obj f_fsig , f <> Heap.InstanceField f_obj f_fsig) ->
get_backlinks bl f = get_backlinks (SetBacklinks p pivot v bl) f.
Proof.
intros.
destruct f.
 unfold SetBacklinks.
 destruct v; trivial.
 induction (PivotTargets p pivot); trivial.
 simpl.
 unfold set_backlink at 1.
 destruct Backlinks.get.
  simpl.
  unfold get_backlinks.
  rewrite Backlinks.get_update_old; trivial.
  intuition.
  inversion H0; trivial.
  
  unfold get_backlinks.
  rewrite Backlinks.get_update_old; trivial.
  intuition.
  inversion H0; trivial.
  
 elim H with o f.
 trivial.
 
 unfold SetBacklinks.
 destruct v; trivial.
 induction (PivotTargets p pivot); trivial.
 simpl.
 unfold set_backlink at 1.
 destruct Backlinks.get.
  simpl.
  unfold get_backlinks.
  rewrite Backlinks.get_update_old; trivial.
  intuition.
  inversion H0; trivial.
  
  unfold get_backlinks.
  rewrite Backlinks.get_update_old; trivial.
  intuition.
  inversion H0; trivial.
 Qed.


Lemma get_remove_old:
forall p loc pivot st x f,
pivot <> loc ->
(LocDict.get (get_backlinks st@bl f) pivot = Some x <->
LocDict.get (get_backlinks  (RemoveBacklinks p loc st) f) pivot = Some x).
Proof.
split;intros.
unfold RemoveBacklinks.
case_eq (Heap.get st @h loc); intros; trivial.
destruct v; trivial.
induction (PivotTargets p loc).
 simpl; trivial.
 
 simpl.
 unfold remove_backlink at 1.
 case_eq
  (Backlinks.get
     (fold_right
        (fun (f0 : FieldSignature) (bl : Backlinks.t) =>
         remove_backlink bl (Heap.InstanceField o f0) loc) 
        st @bl l) (Heap.InstanceField o a)); intros.
  simpl.
  unfold get_backlinks.
  case_eq (eq_dec (Heap.InstanceField o a) f); intros.
   rewrite <- e.
   rewrite Backlinks.get_update_same.
   unfold get_backlinks in IHl.
   rewrite e in H2.
   rewrite H2 in IHl.
   rewrite LocDict.get_remove_old; auto.
   
   rewrite Backlinks.get_update_old; trivial.
   
  case_eq (eq_dec (Heap.InstanceField o a) f); intros.
   rewrite e in H2.
   unfold get_backlinks in IHl.
   rewrite H2 in IHl.
   rewrite LocDict.get_empty in IHl.
   inversion IHl.
   
   trivial.

unfold RemoveBacklinks in H0.
case_eq (Heap.get st @h loc); intros; trivial.
rewrite H1 in H0.
destruct v; trivial.
induction (PivotTargets p loc).
 simpl; trivial.
 
 simpl in H0.
 unfold remove_backlink at 1 in H0.
 case_eq
  (Backlinks.get
     (fold_right
        (fun (f0 : FieldSignature) (bl : Backlinks.t) =>
         remove_backlink bl (Heap.InstanceField o f0) loc) 
        st @bl l) (Heap.InstanceField o a)); intros.
  rewrite H2 in H0.
  simpl in * |- *.
  unfold get_backlinks in H0.
  case_eq (eq_dec (Heap.InstanceField o a) f); intros.
   rewrite <- e in H0.
   rewrite Backlinks.get_update_same in H0.
   unfold get_backlinks in IHl.
   rewrite e in H2.
   rewrite H2 in IHl.
   rewrite LocDict.get_remove_old in H0; auto.
   
   rewrite Backlinks.get_update_old in H0; trivial.
   
   apply IHl.
   trivial.
   apply IHl.
   rewrite H2 in H0.
   trivial.
   rewrite H1 in H0.
   trivial.
Qed.

Lemma get_set_old:
forall p loc pivot bl x f v,
pivot <> loc ->
(LocDict.get (get_backlinks bl f) pivot = Some x <->
LocDict.get (get_backlinks  (SetBacklinks p loc v bl) f)
  pivot = Some x).
Proof.
split; intros.
 unfold SetBacklinks.
 destruct v; trivial.
 induction (PivotTargets p loc).
  simpl; trivial.
  
  simpl.
  unfold set_backlink at 1.
  case_eq
   (Backlinks.get
      (fold_right
         (fun (f0 : FieldSignature) (bl' : Backlinks.t) =>
          set_backlink bl' (Heap.InstanceField o f0) loc
            (list2LocSet (DynamicDGs p f0 loc))) bl l) 
      (Heap.InstanceField o a)); intros.
   simpl.
   unfold get_backlinks.
   case_eq (eq_dec (Heap.InstanceField o a) f); intros.
    rewrite <- e.
    rewrite Backlinks.get_update_same.
    unfold get_backlinks in IHl.
    rewrite e in H1.
    rewrite H1 in IHl.
    rewrite LocDict.get_update_old; auto.
    
    rewrite Backlinks.get_update_old; trivial.
    
   case_eq (eq_dec (Heap.InstanceField o a) f); intros.
    rewrite e in H1.
    unfold get_backlinks in IHl.
    rewrite H1 in IHl.
    rewrite LocDict.get_empty in IHl.
    inversion IHl.
    
    unfold LocDict.singleton.
    unfold get_backlinks.
    rewrite Backlinks.get_update_old; trivial.
    
 unfold SetBacklinks in H0.
 destruct v; trivial.
 induction (PivotTargets p loc).
  simpl; trivial.
  
  simpl in H0.
  unfold set_backlink at 1 in H0.
  case_eq
   (Backlinks.get
      (fold_right
         (fun (f : FieldSignature) (bl' : Backlinks.t) =>
          set_backlink bl' (Heap.InstanceField o f) loc
            (list2LocSet (DynamicDGs p f loc))) bl l) 
      (Heap.InstanceField o a)); intros.
   rewrite H1 in H0.
   simpl in H0.
   unfold get_backlinks in H0.
   case_eq (eq_dec (Heap.InstanceField o a) f); intros.
    rewrite <- e in H0.
    rewrite Backlinks.get_update_same in H0.
    unfold get_backlinks in IHl.
    rewrite e in H1.
    rewrite H1 in IHl.
    rewrite LocDict.get_update_old in H0; auto.
    
    rewrite Backlinks.get_update_old in H0; trivial.
    apply IHl.
    trivial.
    
   rewrite H1 in H0.
   unfold get_backlinks in H0.
   case_eq (eq_dec (Heap.InstanceField o a) f); intros.
    rewrite e in H0.
    rewrite Backlinks.get_update_same in H0.
    unfold LocDict.singleton in H0.
    rewrite LocDict.get_update_old in H0.
     rewrite LocDict.get_empty in H0.
     inversion H0.
     
     auto.
     
    rewrite Backlinks.get_update_old in H0.
     apply IHl.
     trivial.
     
     trivial.
Qed.

Lemma get_remove_none:
forall p st obj f pivot dg,
CorrectBacklink p st (Heap.InstanceField obj f) dg pivot ->
PivotField p pivot ->
   ~ (exists locs,  LocDict.get
       (get_backlinks (RemoveBacklinks p pivot st) (Heap.InstanceField obj f))
       pivot = Some locs /\ (LocSet.In dg locs)).
Proof.
unfold CorrectBacklink.
intros.
unfold RemoveBacklinks.
case_eq (Heap.get st@h pivot);intros.
destruct v.
intro.
rewrite <- H in H2.
inversion H2.
rewrite H6 in H1.
inversion H1.
intro.
rewrite <- H in H2.
inversion H2.
rewrite H6 in H1.
inversion H1.
case_eq (ObjDec.eq_dec o obj).
 intros.
 rewrite e.
 rewrite e in H1.
 clear o e H2.
 elim
  classic
   with
     (exists dg,
      direct_FieldInDg_dynamic p st @h (Heap.InstanceField obj f) dg pivot).
  intros.
  generalize H2; intro.
  rewrite <- PivotTargets_Correct in H3; trivial.
  induction (PivotTargets p pivot).
   inversion H3.
   
   simpl in H3.
   destruct H3.
    clear IHl.
    rewrite H3.
    clear a H3.
    simpl.
    unfold get_backlinks.
    unfold remove_backlink at 1.
    case_eq
     (Backlinks.get
        (fold_right
           (fun (f0 : FieldSignature) (bl : Backlinks.t) =>
            remove_backlink bl (Heap.InstanceField obj f0) pivot) 
           st @bl l) (Heap.InstanceField obj f)).
     intros.
     simpl.
     rewrite Backlinks.get_update_same.
     rewrite LocDict.get_remove_none.
     intro.
     destruct H4.
     destruct H4.
     inversion H4.
     
     intros.
     rewrite H3.
     intro.
     rewrite LocDict.get_empty in H4.
     destruct H4.
     destruct H4.
     inversion H4.
     
    simpl.
    case_eq (FsigDec.eq_dec a f).
     intros.
     rewrite e.
     unfold get_backlinks.
     unfold remove_backlink at 1.
     case_eq
      (Backlinks.get
         (fold_right
            (fun (f0 : FieldSignature) (bl : Backlinks.t) =>
             remove_backlink bl (Heap.InstanceField obj f0) pivot) 
            st @bl l) (Heap.InstanceField obj f)).
      simpl.
      intros.
      rewrite Backlinks.get_update_same.
      rewrite LocDict.get_remove_none.
      intro.
      destruct H6.
      destruct H6.
      inversion H6.
      
      intro.
      rewrite H5.
      intro.
      rewrite LocDict.get_empty in H6.
      destruct H6.
      destruct H6.
      inversion H6.
      
     intros.
     unfold get_backlinks.
     unfold remove_backlink at 1.
     case_eq
      (Backlinks.get
         (fold_right
            (fun (f0 : FieldSignature) (bl : Backlinks.t) =>
             remove_backlink bl (Heap.InstanceField obj f0) pivot) 
            st @bl l) (Heap.InstanceField obj a)).
      intros.
      simpl.
      rewrite Backlinks.get_update_old.
       apply IHl.
       trivial.
       
       intro.
       elim n.
       inversion H6; trivial.
       
      intro.
      apply IHl.
      trivial.
      
  intros.
  intro.
  elim H2.
  exists dg.
  apply H.
  rewrite <- PivotTargets_Correct in H2.
   induction (PivotTargets p pivot).
    simpl.
    intros.
    destruct H3 as [ams H3].
    exists ams.
    trivial.
    
    intros.
    simpl in H3.
    unfold remove_backlink at 1 in H3.
    case_eq
     (Backlinks.get
        (fold_right
           (fun (f : FieldSignature) (bl : Backlinks.t) =>
            remove_backlink bl (Heap.InstanceField obj f) pivot) 
           st @bl l) (Heap.InstanceField obj a)); intros; 
     rewrite H4 in H3.
     simpl in H3.
     simpl in H2.
     assert (a <> f).
      intro.
      elim H2.
      left; trivial.
      
      unfold get_backlinks in H3.
      rewrite Backlinks.get_update_old in H3.
       apply IHl.
        intro.
        elim H2.
        right.
        trivial.
        
        trivial.
        
       intro.
       elim H5.
       inversion H6.
       trivial.
       
     apply IHl.
      intro.
      elim H2.
      right; trivial.
      
      trivial.
      
   trivial.
   
 intros.
 assert (~ direct_FieldInDg_dynamic p st @h (Heap.InstanceField obj f) dg pivot).
  intro.
  inversion H3.
  inversion H5.
  rewrite H7 in H1.
  inversion H1.
  rewrite <- H18 in H20.
  elim n.
  symmetry.
  trivial.
  
  rewrite H in H3.
  intro.
  elim H3.
  induction (PivotTargets p pivot).
   simpl in H4.
   trivial.
   
   apply IHl.
   clear IHl.
   simpl in H4.
   unfold remove_backlink at 1 in H4.
   case_eq
    (Backlinks.get
       (fold_right
          (fun (f : FieldSignature) (bl : Backlinks.t) =>
           remove_backlink bl (Heap.InstanceField o f) pivot) 
          st @bl l) (Heap.InstanceField o a)); intros; 
    rewrite H5 in H4.
    simpl.
    unfold get_backlinks in H4.
    rewrite Backlinks.get_update_old in H4.
     trivial.
     
     intro.
     elim n.
     inversion H6; trivial.
     
    trivial.
    intro.
rewrite <- H in H2.
inversion H2.
rewrite H6 in H1.
inversion H1.
intro.
rewrite <- H in H2.
inversion H2.
rewrite H6 in H1.
inversion H1.
Qed.


Lemma SetRemoveBacklinks_Correct:
forall p loc st st' f dg pivot v cn um loc_obj loc_fsig,
PivotField p loc ->
loc = Heap.InstanceField loc_obj loc_fsig ->
Heap.typeof st@h loc_obj = Some (Heap.ObjectObject cn um) ->
defined_field p cn loc_fsig ->
assign_compatible p st@h v (FIELDSIGNATURE.type (snd loc_fsig)) ->
st' = st[h := (Heap.update st@h loc v)]
              [bl := (SetBacklinks p loc v (RemoveBacklinks p loc st))] ->
CorrectBacklink p st f dg pivot ->
CorrectBacklink p st' f dg pivot.
Proof.
unfold CorrectBacklink.
intros.
rewrite H4.
simpl.
clear H4.
rename H5 into H4.
split; intros.
 inversion H5.
 case_eq (LocSet.E.eq_dec pivot_loc loc); intros.
  intros.
  rewrite e in H18.
  rewrite H18 in H5.
  rewrite H18 in H9.
  set (h' := Heap.update (State.h st) pivot v).
  assert (Heap.Compat (State.h st) pivot).
   rewrite H18 in H0.
   rewrite H0.
   apply Heap.CompatObject with cn um; trivial.
   
   generalize H9; intros.
   rewrite Heap.get_update_same in H21; trivial.
   inversion H21.
   fold h' in H5.
   fold h' in H9.
   rewrite H18.
   exists (list2LocSet (DynamicDGs p field_fsig pivot)).
   generalize H9; intro.
   apply PivotTargets_Correct with (p := p) (f_fsig := field_fsig) in H9.
   destruct H9.
   rewrite <- H7 in H24.
   assert (ex (fun dg => direct_FieldInDg_dynamic p h' f dg pivot)).
    exists dg; trivial.
    unfold SetBacklinks.
    apply H24 in H25.
    clear H9 H24.
    rewrite H7.
    induction (PivotTargets p pivot).
     inversion H25.
     
     split.
      case_eq (FsigDec.eq_dec a field_fsig); intros.
       simpl in H25.
       destruct H25.
        clear IHl.
        rewrite H24.
        simpl.
        unfold set_backlink at 1.
        simpl.
        destruct Backlinks.get.
         unfold get_backlinks.
         rewrite Backlinks.get_update_same.
         rewrite LocDict.get_update_same.
         trivial.
         
         unfold get_backlinks.
         rewrite Backlinks.get_update_same.
         unfold LocDict.singleton.
         rewrite LocDict.get_update_same.
         trivial.
         
        rewrite e0.
        simpl.
        unfold set_backlink at 1.
        simpl.
        destruct Backlinks.get.
         unfold get_backlinks.
         rewrite Backlinks.get_update_same.
         rewrite LocDict.get_update_same.
         trivial.
         
         unfold get_backlinks.
         rewrite Backlinks.get_update_same.
         unfold LocDict.singleton.
         rewrite LocDict.get_update_same.
         trivial.
         
       simpl in H25.
       destruct H25.
        elim n; trivial.
        
        simpl.
        unfold set_backlink at 1.
        destruct Backlinks.get.
         unfold get_backlinks.
         rewrite Backlinks.get_update_old.
          apply IHl.
          trivial.
          
          intro.
          inversion H25.
          elim n; trivial.
          
         unfold get_backlinks.
         rewrite Backlinks.get_update_old.
          apply IHl.
          trivial.
          
          intro.
          inversion H25.
          elim n; trivial.
          
      apply list2LocSet_1.
      rewrite DynamicDGs_Correct with (h := h') (f_obj := field_obj); trivial.
      rewrite <- H7; trivial.
      
  rewrite Heap.get_update_old in H9.
   destruct H4.
   elim H4.
    intros.
    exists x.
    split; trivial.
     clear H4 H20.
     destruct H21.
     apply get_remove_old with (p := p) (loc := loc) in H4.
      apply get_set_old with (p := p) (loc := loc) (v := v) in H4; trivial.
      rewrite <- H18; trivial.
      
      rewrite <- H18; trivial.
      
     tauto.
     
    split
     with
       dg_obj
       dg_fsig
       field_obj
       field_fsig
       pivot_obj
       pivot_fsig
       pivot_f
       dg0; trivial.
    
   rewrite <- H18; auto.
   
 case_eq (LocSet.E.eq_dec pivot loc); intros.
  rewrite <- e in H5.
  rewrite <- e.
  rewrite <- e in H0.
  rewrite <- e in H.
  clear loc e H6.
  destruct f.
   rewrite <- get_set_old_f_uncompat in H5.
    rewrite <- get_remove_old_f_uncompat in H5.
     apply H4 in H5.
     inversion H5.
     inversion H7.
     
     intros; intro; inversion H6.
     
    intros; intro; inversion H6.
   unfold SetBacklinks in H5.
   inversion H3.
    rewrite <- H6 in H5.
    elim get_remove_none with p st o f pivot dg; trivial.
    
    rewrite <- H8 in H5.
    case_eq (ObjDec.eq_dec o obj).
     intros.
     rewrite e.
     rewrite e in H5.
     repeat rewrite e in H4.
     clear o e H10.
     elim classic with (In f (PivotTargets p pivot)).
      intros.
      induction (PivotTargets p pivot).
       inversion H10.
       
       simpl in H10.
       destruct H10.
        clear IHl.
        rewrite H10 in H5.
        simpl in H5.
        unfold set_backlink at 1 in H5.
        case_eq
         (Backlinks.get
            (fold_right
               (fun (f : FieldSignature) (bl' : Backlinks.t) =>
                set_backlink bl' (Heap.InstanceField obj f) pivot
                  (list2LocSet (DynamicDGs p f pivot)))
               (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj f));
         intros; rewrite H11 in H5.
         simpl.
         unfold get_backlinks in H5.
         rewrite Backlinks.get_update_same in H5.
         rewrite LocDict.get_update_same in H5.
         destruct H5.
         destruct H5.
         inversion H5.
         rewrite <- H14 in H12.
         apply list2LocSet_1 in H12.
         rewrite
          DynamicDGs_Correct
           with
             (h := Heap.update (State.h st) pivot (Ref obj))
             (f_obj := obj) in H12.
          trivial.
          
          apply Heap.get_update_same.
          rewrite H0.
          apply Heap.CompatObject with cn um; trivial.
          
         unfold LocDict.singleton in H5.
         unfold get_backlinks in H5.
         rewrite Backlinks.get_update_same in H5.
         rewrite LocDict.get_update_same in H5.
         destruct H5.
         destruct H5.
         inversion H5.
         rewrite <- H14 in H12.
         apply list2LocSet_1 in H12.
         rewrite
          DynamicDGs_Correct
           with
             (h := Heap.update (State.h st) pivot (Ref obj))
             (f_obj := obj) in H12.
          trivial.
          
          apply Heap.get_update_same.
          rewrite H0.
          apply Heap.CompatObject with cn um; trivial.
          
        case_eq (FsigDec.eq_dec a f).
         intros.
         rewrite e in H5.
         clear IHl.
         clear a e H11.
         simpl in H5.
         unfold set_backlink at 1 in H5.
         case_eq
          (Backlinks.get
             (fold_right
                (fun (f : FieldSignature) (bl' : Backlinks.t) =>
                 set_backlink bl' (Heap.InstanceField obj f) pivot
                   (list2LocSet (DynamicDGs p f pivot)))
                (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj f));
          intros; rewrite H11 in H5.
          unfold get_backlinks in H5.
          rewrite Backlinks.get_update_same in H5.
          rewrite LocDict.get_update_same in H5.
          destruct H5.
          destruct H5.
          inversion H5.
          rewrite <- H14 in H12.
          apply list2LocSet_1 in H12.
          rewrite
           DynamicDGs_Correct
            with
              (h := Heap.update (State.h st) pivot (Ref obj))
              (f_obj := obj) in H12.
           trivial.
           
           apply Heap.get_update_same.
           rewrite H0.
           apply Heap.CompatObject with cn um; trivial.
           
          unfold LocDict.singleton in H5.
          unfold get_backlinks in H5.
          rewrite Backlinks.get_update_same in H5.
          rewrite LocDict.get_update_same in H5.
          destruct H5.
          destruct H5.
          inversion H5.
          rewrite <- H14 in H12.
          apply list2LocSet_1 in H12.
          rewrite
           DynamicDGs_Correct
            with
              (h := Heap.update (State.h st) pivot (Ref obj))
              (f_obj := obj) in H12.
           trivial.
           
           apply Heap.get_update_same.
           rewrite H0.
           apply Heap.CompatObject with cn um; trivial.
           
         intros.
         simpl in H5.
         unfold set_backlink at 1 in H5.
         case_eq
          (Backlinks.get
             (fold_right
                (fun (f : FieldSignature) (bl' : Backlinks.t) =>
                 set_backlink bl' (Heap.InstanceField obj f) pivot
                   (list2LocSet (DynamicDGs p f pivot)))
                (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj a));
          intros; rewrite H12 in H5.
          unfold get_backlinks in H5.
          rewrite Backlinks.get_update_old in H5.
           apply IHl; trivial.
           
           intro.
           inversion H13.
           elim n; trivial.
           
          unfold LocDict.singleton in H5.
          unfold get_backlinks in H5.
          rewrite Backlinks.get_update_old in H5.
           apply IHl; trivial.
           
           intro.
           inversion H13.
           elim n; trivial.
           
      intros.
      induction (PivotTargets p pivot).
       simpl in H5.
       intros.
       elim get_remove_none with p st obj f pivot dg; trivial.
       
       simpl in H5.
       unfold set_backlink at 1 in H5.
       case_eq
        (Backlinks.get
           (fold_right
              (fun (f : FieldSignature) (bl' : Backlinks.t) =>
               set_backlink bl' (Heap.InstanceField obj f) pivot
                 (list2LocSet (DynamicDGs p f pivot)))
              (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj a));
        intros; rewrite H11 in H5.
        simpl in H5.
        unfold get_backlinks in H5.
        rewrite Backlinks.get_update_old in H5.
         apply IHl; trivial.
         intro; elim H10; auto with *.
         
         intro; elim H10.
         inversion H12.
         auto with *.
         
        unfold get_backlinks in H5.
        rewrite Backlinks.get_update_old in H5.
         apply IHl; trivial.
         intro; elim H10; auto with *.
         
         intro; elim H10.
         inversion H12.
         auto with *.
         
     intros.
     induction (PivotTargets p pivot).
      simpl in H5.
      elim get_remove_none with p st o f pivot dg; trivial.
      
      simpl in H5.
      unfold set_backlink at 1 in H5.
      case_eq
       (Backlinks.get
          (fold_right
             (fun (f : FieldSignature) (bl' : Backlinks.t) =>
              set_backlink bl' (Heap.InstanceField obj f) pivot
                (list2LocSet (DynamicDGs p f pivot)))
             (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj a));
       intros; rewrite H11 in H5.
       simpl in H5.
       unfold get_backlinks in H5.
       rewrite Backlinks.get_update_old in H5.
        apply IHl; trivial.
        
        intro; elim n.
        inversion H12; trivial.
        
       unfold get_backlinks in H5.
       rewrite Backlinks.get_update_old in H5.
        apply IHl; trivial.
        
        intro; elim n.
        inversion H12; trivial.
        
    rewrite <- H8 in H5.
    case_eq (ObjDec.eq_dec o obj).
     intros.
     rewrite e.
     rewrite e in H5.
     repeat rewrite e in H4.
     clear o e H10.
     elim classic with (In f (PivotTargets p pivot)).
      intros.
      induction (PivotTargets p pivot).
       inversion H10.
       
       simpl in H10.
       destruct H10.
        clear IHl.
        rewrite H10 in H5.
        simpl in H5.
        unfold set_backlink at 1 in H5.
        case_eq
         (Backlinks.get
            (fold_right
               (fun (f : FieldSignature) (bl' : Backlinks.t) =>
                set_backlink bl' (Heap.InstanceField obj f) pivot
                  (list2LocSet (DynamicDGs p f pivot)))
               (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj f));
         intros; rewrite H11 in H5.
         simpl.
         unfold get_backlinks in H5.
         rewrite Backlinks.get_update_same in H5.
         rewrite LocDict.get_update_same in H5.
         destruct H5.
         destruct H5.
         inversion H5.
         rewrite <- H14 in H12.
         apply list2LocSet_1 in H12.
         rewrite
          DynamicDGs_Correct
           with
             (h := Heap.update (State.h st) pivot (Ref obj))
             (f_obj := obj) in H12.
          trivial.
          
          apply Heap.get_update_same.
          rewrite H0.
          apply Heap.CompatObject with cn um; trivial.
          
         unfold LocDict.singleton in H5.
         unfold get_backlinks in H5.
         rewrite Backlinks.get_update_same in H5.
         rewrite LocDict.get_update_same in H5.
         destruct H5.
         destruct H5.
         inversion H5.
         rewrite <- H14 in H12.
         apply list2LocSet_1 in H12.
         rewrite
          DynamicDGs_Correct
           with
             (h := Heap.update (State.h st) pivot (Ref obj))
             (f_obj := obj) in H12.
          trivial.
          
          apply Heap.get_update_same.
          rewrite H0.
          apply Heap.CompatObject with cn um; trivial.
          
        case_eq (FsigDec.eq_dec a f).
         intros.
         rewrite e in H5.
         clear IHl.
         clear a e H11.
         simpl in H5.
         unfold set_backlink at 1 in H5.
         case_eq
          (Backlinks.get
             (fold_right
                (fun (f : FieldSignature) (bl' : Backlinks.t) =>
                 set_backlink bl' (Heap.InstanceField obj f) pivot
                   (list2LocSet (DynamicDGs p f pivot)))
                (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj f));
          intros; rewrite H11 in H5.
          unfold get_backlinks in H5.
          rewrite Backlinks.get_update_same in H5.
          rewrite LocDict.get_update_same in H5.
          destruct H5.
          destruct H5.
          inversion H5.
          rewrite <- H14 in H12.
          apply list2LocSet_1 in H12.
          rewrite
           DynamicDGs_Correct
            with
              (h := Heap.update (State.h st) pivot (Ref obj))
              (f_obj := obj) in H12.
           trivial.
           
           apply Heap.get_update_same.
           rewrite H0.
           apply Heap.CompatObject with cn um; trivial.
           
          unfold LocDict.singleton in H5.
          unfold get_backlinks in H5.
          rewrite Backlinks.get_update_same in H5.
          rewrite LocDict.get_update_same in H5.
          destruct H5.
          destruct H5.
          inversion H5.
          rewrite <- H14 in H12.
          apply list2LocSet_1 in H12.
          rewrite
           DynamicDGs_Correct
            with
              (h := Heap.update (State.h st) pivot (Ref obj))
              (f_obj := obj) in H12.
           trivial.
           
           apply Heap.get_update_same.
           rewrite H0.
           apply Heap.CompatObject with cn um; trivial.
           
         intros.
         simpl in H5.
         unfold set_backlink at 1 in H5.
         case_eq
          (Backlinks.get
             (fold_right
                (fun (f : FieldSignature) (bl' : Backlinks.t) =>
                 set_backlink bl' (Heap.InstanceField obj f) pivot
                   (list2LocSet (DynamicDGs p f pivot)))
                (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj a));
          intros; rewrite H12 in H5.
          unfold get_backlinks in H5.
          rewrite Backlinks.get_update_old in H5.
           apply IHl; trivial.
           
           intro.
           inversion H13.
           elim n; trivial.
           
          unfold LocDict.singleton in H5.
          unfold get_backlinks in H5.
          rewrite Backlinks.get_update_old in H5.
           apply IHl; trivial.
           
           intro.
           inversion H13.
           elim n; trivial.
           
      intros.
      induction (PivotTargets p pivot).
       simpl in H5.
       intros.
       elim get_remove_none with p st obj f pivot dg; trivial.
       
       simpl in H5.
       unfold set_backlink at 1 in H5.
       case_eq
        (Backlinks.get
           (fold_right
              (fun (f : FieldSignature) (bl' : Backlinks.t) =>
               set_backlink bl' (Heap.InstanceField obj f) pivot
                 (list2LocSet (DynamicDGs p f pivot)))
              (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj a));
        intros; rewrite H11 in H5.
        simpl in H5.
        unfold get_backlinks in H5.
        rewrite Backlinks.get_update_old in H5.
         apply IHl; trivial.
         intro; elim H10; auto with *.
         
         intro; elim H10.
         inversion H12.
         auto with *.
         
        unfold get_backlinks in H5.
        rewrite Backlinks.get_update_old in H5.
         apply IHl; trivial.
         intro; elim H10; auto with *.
         
         intro; elim H10.
         inversion H12.
         auto with *.
         
     intros.
     induction (PivotTargets p pivot).
      simpl in H5.
      elim get_remove_none with p st o f pivot dg; trivial.
      
      simpl in H5.
      unfold set_backlink at 1 in H5.
      case_eq
       (Backlinks.get
          (fold_right
             (fun (f : FieldSignature) (bl' : Backlinks.t) =>
              set_backlink bl' (Heap.InstanceField obj f) pivot
                (list2LocSet (DynamicDGs p f pivot)))
             (RemoveBacklinks p pivot st) l) (Heap.InstanceField obj a));
       intros; rewrite H11 in H5.
       simpl in H5.
       unfold get_backlinks in H5.
       rewrite Backlinks.get_update_old in H5.
        apply IHl; trivial.
        
        intro; elim n.
        inversion H12; trivial.
        
       unfold get_backlinks in H5.
       rewrite Backlinks.get_update_old in H5.
        apply IHl; trivial.
        
        intro; elim n.
        inversion H12; trivial.
        
    rewrite <- H7 in H5.
    elim get_remove_none with p st o f pivot dg; trivial.
    
   rewrite <- get_set_old_f_uncompat in H5.
    rewrite <- get_remove_old_f_uncompat in H5.
     apply H4 in H5.
     inversion H5.
     inversion H7.
     
     intros; intro; inversion H6.
     
    intros; intro; inversion H6.
    
  destruct H5.
  destruct H5.
  apply get_set_old in H5.
   apply get_remove_old in H5.
    destruct H4.
    assert
     (ex
        (fun ams  =>
         and
           (eq
              (LocDict.get (get_backlinks (Adds.backlinks (State.adds st)) f)
                 pivot) (Some ams)) (LocSet.In dg ams))).
     exists x; auto.
     
     apply H8 in H9.
     inversion H9.
     split
      with
        dg_obj
        dg_fsig
        field_obj
        field_fsig
        pivot_obj
        pivot_fsig
        pivot_f
        dg0; trivial.
     rewrite Heap.get_update_old.
      trivial.
      
      auto.
      
    trivial.
    
   trivial.
Qed.


Definition FieldUpdateAction (p : Program) (pivot : Location) (v : Value) (st : State.t) : State.t :=
    if (isPivot p pivot) then
       let bl1 := RemoveBacklinks p pivot st in
       let bl' := SetBacklinks p pivot v bl1 in
        st[fr := st@fr[assignables := map (SavePreState p st@bl pivot) st@fr@assignables]][bl := bl']
    else
      st.


Lemma not_isPivot_direct_FieldInDg:
forall p h f dg pivot loc v,
isPivot p loc = false ->
(direct_FieldInDg_dynamic p h f dg pivot <->
direct_FieldInDg_dynamic p (Heap.update h loc v) f dg pivot).
Proof.
intros.
apply not_true_iff_false in H.
rewrite isPivot_PivotField in H.
split; intro.
 destruct H0.
 split
  with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg;
  trivial.
 case_eq (eq_dec loc pivot_loc); intros.
  rewrite e in H.
  elim H.
  split with pivot_fsig pivot_obj pivot_f dg; trivial.
  
  rewrite Heap.get_update_old; trivial.
  
 destruct H0.
 split
  with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg;
  trivial.
 case_eq (eq_dec loc pivot_loc); intros.
  rewrite e in H.
  elim H.
  split with pivot_fsig pivot_obj pivot_f dg; trivial.
  
  rewrite Heap.get_update_old in H3; trivial.
Qed.

  Lemma FieldUpdateAction_Correct:
    forall p loc st_rac2 v st_rac2' st_rac3 st_rac3' cn um loc_obj loc_fsig,
    loc = Heap.InstanceField loc_obj loc_fsig ->
    Heap.typeof st_rac3@h loc_obj = Some (Heap.ObjectObject cn um) ->
    defined_field p cn loc_fsig ->
    assign_compatible p st_rac3@h v (FIELDSIGNATURE.type (snd loc_fsig)) ->
    CorrespondingState p st_rac2 st_rac3 ->
    FieldUpdateAction p loc v st_rac3 = st_rac3' ->
    Rac2.Assignables.FieldUpdateAction p loc v st_rac2 = st_rac2' ->
    CorrespondingState p 
      st_rac2'[h:=Heap.update st_rac2@h loc v]%rac2
      st_rac3'[h:=Heap.update st_rac3@h loc v].
Proof.
intuition.
unfold FieldUpdateAction in H4.
unfold Rac2.Assignables.FieldUpdateAction in H5.
case_eq (isPivot p loc); intros; rewrite H6 in H5;rewrite H6 in H4.
 inversion H3.
 subst.
 split; simpl.

  inversion H7.
  subst.
  split; simpl; trivial.
  destruct H14.
  split.
   repeat rewrite map_length.
   trivial.
   
   intros.
   case_eq (Nat.compare n (length st_rac3 @fr @assignables )).
    intros.
    rewrite nat_compare_Eq in H14.
    repeat rewrite nth_overflow.
     auto with *.
     
     rewrite map_length.
     lia.
     
     rewrite map_length.
     lia.
     
    intros.
    apply nat_compare_lt in H14.
    generalize H14; intros.
    rewrite <- e in H15.
    repeat
     rewrite
      (nth_indep
         (map (Rac2.SavePreState p st_rac2 @h%rac2 (Heap.InstanceField loc_obj loc_fsig))
            st_rac2 @fr%rac2 @assignables) a0
         (Rac2.SavePreState p st_rac2 @h%rac2 (Heap.InstanceField loc_obj loc_fsig) a0)).
     repeat
      rewrite
       (nth_indep
          (map (SavePreState p st_rac3 @bl (Heap.InstanceField loc_obj loc_fsig)) st_rac3 @fr @assignables) a0
          (SavePreState p st_rac3 @bl (Heap.InstanceField loc_obj loc_fsig) a0)).
      rewrite map_nth.
      rewrite map_nth.
      destruct a with n a0.
      repeat rewrite H8.

      apply SavePreState_same; trivial.
      
      rewrite map_length; trivial.
      
     rewrite map_length; trivial.
     
    intros.
    rewrite <- nat_compare_gt in H14.
    repeat rewrite nth_overflow.
     auto with *.
     
     rewrite map_length.
     lia.
     
     rewrite map_length.
     lia.
     
  rewrite H8.
  trivial.
  
  unfold CorrectBacklinks in H9 |- *.
  unfold CorrectBacklink in H9 |- *.
  intros.
  simpl.
  set (st' := st_rac3[h :=(Heap.update st_rac3 @h (Heap.InstanceField loc_obj loc_fsig) v)]
[bl := (SetBacklinks p (Heap.InstanceField loc_obj loc_fsig) v
           (RemoveBacklinks p (Heap.InstanceField loc_obj loc_fsig) st_rac3))]).
  replace (Heap.update st_rac3 @h (Heap.InstanceField loc_obj loc_fsig) v) with st'@h.
  replace ((SetBacklinks p (Heap.InstanceField loc_obj loc_fsig) v
           (RemoveBacklinks p (Heap.InstanceField loc_obj loc_fsig) st_rac3))) with st'@bl.
  apply SetRemoveBacklinks_Correct with (Heap.InstanceField loc_obj loc_fsig) st_rac3 v cn um loc_obj loc_fsig ;trivial.
  apply isPivot_PivotField;trivial.
  unfold CorrectBacklink.
  trivial.
trivial.
trivial.
 split; simpl.
  destruct H.
  subst; trivial.
  
  destruct H3.
  trivial.

  destruct H3.
  rewrite H7.
  trivial.
  
  destruct H3.
  destruct H3.
  unfold CorrectBacklinks in H8 |- *.
  unfold CorrectBacklink in H8 |- *.
  simpl.
  rewrite <- H4.
  intros.
  rewrite <- not_isPivot_direct_FieldInDg.
   trivial.
   
   trivial.
Qed.

Lemma CorrectBacklinks_new:
forall st p cn um obj h' ,
Heap.new st@h p (Heap.ObjectObject cn um) = Some (obj, h') ->
(CorrectBacklinks p st <-> CorrectBacklinks p st [h := h']).
Proof.
intuition.
 intros.
 unfold CorrectBacklinks.
 unfold CorrectBacklink.
 intros.
 destruct H0 with f dg pivot.
 simpl in *.
 intuition.
  apply H1.
  clear H1 H2.
  inversion H3.
  split
   with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg0;
   trivial.
  assert (pivot_obj <> obj).
   intro.
   rewrite H15 in H4.
   apply
    Rac2.new_object_field_not_ref
     with (fsig := pivot_fsig) (loc := pivot) (r := field_obj) 
    in H; trivial.
   elim H; trivial.
   
   rewrite <- H5.
   symmetry .
   apply Heap.new_object_no_change with p cn um obj; trivial.
   intros.
   rewrite H4.
   intro.
   inversion H16.
   elim H15; trivial.
   
  clear H3 H2.
  inversion H4.
  split
   with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg0;
   trivial.
  assert (pivot_obj <> obj).
   intro.
   rewrite H15 in H3.
   apply Heap.new_fresh_location in H.
   assert (~Heap.Compat st @h pivot).
    intro.
    destruct H16.
     inversion H3.
     
     inversion H3.
     rewrite H18 in H16.
     rewrite H in H16.
     inversion H16.
     
     inversion H3.
     
    apply Heap.get_uncompat in H16.
    rewrite H5 in H16.
    inversion H16.
    
   rewrite <- H5.
   apply Heap.new_object_no_change with p cn um obj; trivial.
   intros.
   rewrite H3.
   intro.
   inversion H16.
   elim H15; trivial.
   
 unfold CorrectBacklinks.
 unfold CorrectBacklink.
 intros.
 destruct H0 with f dg pivot.
 simpl in *.
 intuition.
  apply H1.
  clear H1 H2.
  inversion H3.
  split
   with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg0;
   trivial.
  assert (pivot_obj <> obj).
   intro.
   rewrite H15 in H4.
   apply Heap.new_fresh_location in H.
   assert (~Heap.Compat st @h pivot).
    intro.
    destruct H16.
     inversion H4.
     
     inversion H4.
     rewrite H18 in H16.
     rewrite H in H16.
     inversion H16.
     
     inversion H4.
     
    apply Heap.get_uncompat in H16.
    rewrite H5 in H16.
    inversion H16.
    
   rewrite <- H5.
   apply Heap.new_object_no_change with p cn um obj; trivial.
   intros.
   rewrite H4.
   intro.
   inversion H16.
   elim H15; trivial.
   
  clear H3 H2.
  inversion H4.
  split
   with dg_obj dg_fsig field_obj field_fsig pivot_obj pivot_fsig pivot_f dg0;
   trivial.
  assert (pivot_obj <> obj).
   intro.
   rewrite H15 in H3.
   apply
    Rac2.new_object_field_not_ref
     with (fsig := pivot_fsig) (loc := pivot) (r := field_obj) 
    in H; trivial.
   elim H; trivial.
   
   rewrite <- H5.
   symmetry .
   apply Heap.new_object_no_change with p cn um obj; trivial.
   intros.
   rewrite H3.
   intro.
   inversion H16.
   elim H15; trivial.
Qed.

End Assignables.

End Rac3.
