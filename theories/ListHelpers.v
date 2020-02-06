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

Require Import List.
Require Import TheoryList.

(**
  Usefull TheoryList extensions:
  - AllS_x_P
  - Last and corresponding lemmas
  - Suffix and corresponding lemmas
 *)

Section TheoryList.

  (*
  Inductive AllS (A : Type) (P : A -> Prop) : list A -> Prop :=
    | allS_nil  : AllS P nil
    | allS_cons : forall (a : A) (l : list A),
                   P a -> AllS P l -> AllS P (a :: l)
  *)

  (** If AllS P l holds, predicate P holds for every element x in l. *)
  Lemma AllS_x_P : forall A P l (x:A), AllS P l -> In x l -> P x.
    Proof.
      intros.
      induction H.
      (* 1 *)
      simpl in H0.
      elim H0.
      (* 2 *)
      elim H0.
      (* 2.1 *)
      intro eq_a_x.
      rewrite <- eq_a_x; exact H.
      (* 2.2 *)
      assumption.
    Qed.
End TheoryList.

Section In.
  Variable A : Type.

  (** If head l = Some x, x is element of l. *)
  Lemma In_head : forall (x:A) l, head l = Some x -> In x l.
    Proof.
      intros.
      induction l. 
      discriminate H.
      simpl in H.
      unfold In.
      left.
      inversion H.
      reflexivity.
    Qed.

  (** If l=y::nil, In x l -> x=y. *)
  Lemma In_singleton : forall (x y:A),
    In x (y::nil) -> x = y.
  Proof.
    intros.
    case H; intuition.
  Qed.

Lemma in_nth:
forall e (l : list A),
In e l -> forall d, exists n, nth n l d = e /\ (n < length l)%nat.
Proof.
induction l; intros.
 inversion H.
 
 simpl in H.
 destruct H.
  subst.
  exists O.
  simpl.
  auto with *.

  elim IHl with d.
  intros.
  exists (S x).
  simpl.
  intuition.

  trivial.
Qed.

End In.

Section Last.
  Variable A : Type.

  (** Last x l <-> x is the last element of list l. *)
  Inductive Last (x:A) : list A -> Prop :=
    | Last_base : Last x (x::nil)
    | Last_step : forall (y:A) (l:list A), Last x l -> Last x (y::l). 

  (** The empty list nil has no last element. *)
  Lemma Last_nil : forall x:A, Last x nil -> False.
  Proof.
    intros.
    inversion H.
  Qed.

  (** If l is non-empty, the last element x of (y::l) is also the last element of l. *)
  Lemma Last_step_inv : forall (x:A) (l:list A),
    l <> nil -> forall y, Last x (y::l) -> Last x l.
  Proof.
    intros.
    inversion H0.
    rewrite H3 in H; elim H; reflexivity.
    assumption.
  Qed.

  (** The last element x of l2 is also the last element of (l1 ++ l2). *)
  Lemma Last_app : forall (x:A) (l1 l2:list A), Last x l2 -> Last x (l1 ++ l2).
  Proof.
    intros.
    induction l1.
    simpl; assumption.
    change ((a :: l1) ++ l2) with (a :: (l1 ++ l2)).
    apply Last_step; assumption.
  Qed.

  (** If l is non-empty, the last element x of (l1 ++ l2) is also the last element of l2. *)
  Lemma Last_app_inv : forall (x:A) (l1 l2:list A), 
    l2 <> nil -> Last x (l1 ++ l2) -> Last x l2.
  Proof.
    intros.
    induction l1. 
    simpl; assumption.
    apply IHl1.
    apply Last_step_inv with (y := a). 
    destruct l1; [assumption | intuition; discriminate H1].
    assumption.
  Qed.  

  (** The last element Last x l of list l is element of the list l. *)
  Theorem Last_In : forall (x:A) (l:list A),
    Last x l -> In x l.
  Proof.
    intros.
    elim H.
    unfold In.
    left; reflexivity.

    intros y l0 L_x_l0 In_x_l0.
    unfold In. 
    auto.
  Qed.

  (**
    Retrieve the last element x of l.
    The result is either x together with a proof that x is the last element of l,
    or l is the empty list.
   *)
  Definition lastS (l:list A) : {x:A | Last x l}+{l=nil}.
  Proof.
    induction l.
    (* case l = nil *)
    right; reflexivity.

    (* inductive case *)
    case_eq l.
    left.
    exists a.
    apply Last_base.

    left.
    inversion IHl.
    destruct X.
    exists x.
    rewrite <- H.
    apply Last_step; assumption.

    rewrite H in H0.
    discriminate H0.
  Defined.
    
End Last.
Implicit Arguments Last [A].
Implicit Arguments lastS [A].

Section Suffix.
  Variable A : Type.

  (** Suffix s l <-> the list s is a suffix of the list l. *)
  Definition Suffix (s l:list A) : Prop := 
    exists p, p++s = l.

  (** nil is a suffix of every list l. *)
  Lemma Suffix_nil_l : forall l:list A, Suffix nil l.
  Proof.
    intro l.
    exists l; intuition.
  Qed.
  
  (** l is a suffix of itself. *)
  Lemma Suffix_l_l : forall l:list A, Suffix l l.
  Proof.
    intro l.
    exists (nil (A:=A)); intuition.
  Qed.
  
  (** If s is a suffix of l, s is also a suffix of every list (x::l). *)
  Lemma Suffix_step : forall (x:A) (s l:list A), Suffix s l -> Suffix s (x::l).
  Proof.
    intros x s l Hsuff.
    unfold Suffix in * |- *.
    elim Hsuff.
    intros p Heq.
    exists (x::p).
    rewrite <- Heq.
    reflexivity.
  Qed.

  (** 
    If s is a suffix of a list l, 
    every element x that is an element of s is also an element of l. 
   *)
  Lemma Suffix_In : forall s l:list A, Suffix s l -> (forall x:A, In x s -> In x l).
  Proof.
    intros s l Hsuff x Hs.
    elim Hsuff.
    intros p Heq.
    rewrite <- Heq.
    intuition.

  Qed.

  (**
    For any two elements x and y in a list l,
    it holds that either y is in a suffix (x::s) or
    x is in a suffix (y::s).
   *)
  Lemma Suffix_x_y_or_y_x : forall (l:list A) (x y:A),
      In x l -> In y l ->
      (exists s, Suffix (x::s) l /\ In y (x::s)) \/
      (exists s, Suffix (y::s) l /\ In x (y::s)).
    Proof.
      intros.
      induction l.
      (* case l=nil *)
      inversion H.

      (* case a::l *)

      (* 1st case: a = x *)
      case H; intro Hax.
      left.
      exists l.
      split.
      rewrite Hax.
      apply Suffix_l_l.
      rewrite <- Hax; assumption.

      (* 2nd case: a = y *)
      case H0; intro Hay.
      right.
      exists l.
      split.
      rewrite Hay.
      apply Suffix_l_l.
      rewrite <- Hay; assumption.

      (* 3rd case: a <> x, a <> x *)
      change (In x l) in Hax.
      change (In y l) in Hay.
      generalize (IHl Hax Hay); intro H1.

      case H1; intro.
      left.
      elim H2; intros.
      exists x0.
      destruct H3.
      split.
      apply Suffix_step; assumption.
      assumption.

      right.
      elim H2; intros.
      exists x0.
      destruct H3.
      split.
      apply Suffix_step; assumption.
      assumption.
    Qed.

End Suffix.
Implicit Arguments Suffix [A].
