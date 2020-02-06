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
Require Import Coq.Arith.Max.

(**
  Useful functions on lists, not part of the Coq standard library.
  Most functions are taken from the Haskell standard libary module Data.List.
 
 *)

Section ListFunctions.
  Variable A : Type.
  Variable B : Type.

  (** Make a singleton list from the given element a. *)
  Definition singleton (a:A) : list A := a :: nil.

  (** Drop all prefix elements of l that satisfy p. *)
  Fixpoint dropWhile (p:A->bool) (l:list A) {struct l} : list A :=
    match l with
    | nil     => nil
    | (x::xs) => if p x then dropWhile p xs else xs
    end.
  
  (** Concatenate all given lists into a flat list. *)
  Definition concat : list (list A) -> list A := flat_map (fun x:list A => x).

  (** Maximum element of the given list of natural numbers. *)
  Fixpoint maximum (e:nat) (l:list nat) {struct l} : nat :=
    match l with 
    | nil     => e
    | (x::xs) => max x (maximum e xs)
    end.

  (** 
    Like fold_left but take e for the empty list. 
    e is not used for a non-empty list.
   *)
  Definition fold_left1 (op:A->A->A) (l:list A) (e:A) : A :=
    match l with
    | nil   => e
    | x::xs => fold_left op xs x
    end.

  (** 
    Like fold_right but take e for the empty list. 
    e is not used for a non-empty list.
   *)
  Fixpoint fold_right1 (op:A->A->A) (l:list A) (e:A) : A :=
    match l with
    | nil    => e
    | x::nil => x
    | x::xs  => op x (fold_right1 op xs e)
    end.
    
End ListFunctions.

Implicit Arguments singleton [A].
Implicit Arguments dropWhile [A].
Implicit Arguments concat [A].
Implicit Arguments fold_left1 [A].
Implicit Arguments fold_right1 [A].

Inductive Expr : Set :=
    | Lit : nat -> Expr
    | Add : Expr -> Expr -> Expr.

(* Eval compute in fold_right1 Add (Lit 1 :: Lit 2 :: Lit 3 :: nil) (Lit 10). *)

Section Proofs.
  Variable A : Type.
  
  (** 
    For every element y in the result list (concat l),
    there exists a list x in l that contains y.
   *)
  Lemma in_concat : forall (l:list (list A)) (y:A),
    In y (concat l) <-> exists x, In x l /\ In y x.
  Proof.
    apply (in_flat_map (fun x:list A => x)).
  Qed.

  (** e is the maximum of the empty list. *)
  Lemma maximum_e_nil : forall (e:nat) (l:list nat), l=nil -> maximum e l=e.
  Proof.
    intros e l H.
    rewrite H.
    simpl.
    reflexivity.
  Qed.

  (** maximum is composable using max and cons. *)
  Lemma maximum_e_cons : forall (e:nat) (x:nat) (l:list nat), 
    maximum e (x::l) = max x (maximum e l).
  Proof.
    intros e x l.
    simpl.
    reflexivity.
  Qed.

  (** fold_left1 op nil e = e *)
  Lemma fold_left1_e_nil : forall (op:A->A->A) (e:A) (l:list A), 
    l=nil -> 
    fold_left1 op l e = e.
  Proof.
    intros op e l H.
    rewrite H.
    simpl.
    reflexivity.
  Qed.

  (** fold_left1 op (x::l) e = fold_left1 op l x,
     e vanishes for a non-empty list.
    *)
  Lemma fold_left1_fold_left : forall (op:A->A->A) (e:A) (x:A) (l:list A), 
    fold_left1 op (x::l) e = fold_left op l x.
  Proof.
    intros op e x l.
    simpl.
    reflexivity.
  Qed.

  (** The element found by find satisfies predicate p. *)
  Lemma find_def : forall (p:A->bool) (l:list A) (x:A), find p l = Some x -> p x = true.
  Proof.
    intros p l x H.
    induction l.
    (* BC *)
    discriminate H.
    (* IH *)
    simpl in H.
    assert (p a = true \/ p a = false).
    case (p a); auto.

    elim H0; intro Hpa; rewrite Hpa in H. 
    congruence.
    auto.
  Qed.

End Proofs.

