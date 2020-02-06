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
Require Import Arith.
Require Import Min.
Require Import Classical.

Section definitions.

Set Implicit Arguments.

Variable A: Type.

Definition stack := list.

Definition empty (s : stack A) : bool :=
  match s with
  | nil => true
  | _ => false
  end.

Definition singleton (a : A) : stack A :=
  a::nil.


Definition peek (s : stack A) : option A :=
  match s with
  | nil => None
  | a::t => Some a
  end.

Definition peekd (s : stack A) (d : A) : A :=
  match s with
  | nil => d
  | a::t => a
  end.

Definition push (a : A) (s : stack A) : stack A :=
  a :: s.

Definition pop (s : stack A) : stack A :=
  match s with
  | nil => nil
  | a::t => t
  end.

Definition apply_top (f : A -> A) (s : stack A) : stack A :=
  match s with
  | nil => nil
  | a :: t => f a :: t
  end.

Definition replace_top (a : A) (s : stack A) : stack A :=
  match s with
  | nil => nil
  | h :: t => a :: t
  end.

Fixpoint truncate (n : nat) (s : stack A) : stack A :=
    match Nat.compare n (length s) with
    | Lt =>
      match s with
      | _ :: t => truncate n t
      | _ => nil
      end
    | _ => s
    end.

Definition level (s t : stack A) : stack A * stack A :=
  match Nat.compare (length s) (length t) with
  | Lt => (s , truncate (length s) t)
  | Eq => (s, t)
  | Gt => (truncate (length t) s, t)
  end.

End definitions.
                 
(*Notation "⇊ n ( s )" := (truncate n s).*)
Notation "│ s │" := (length s).
Notation "[]" := (nil).

Section proofs.

Set Implicit Arguments.

  Variable A B : Type.
  Lemma nat_compare_n_Sn : forall n,
    Nat.compare n (S n) = Lt.
    Proof.
    intuition.
    rewrite <- nat_compare_lt.
    auto.
Qed.

  Lemma nat_compare_Sn_n : forall n,
    Nat.compare (S n) n = Gt.
    Proof.
    intuition.
    rewrite <- nat_compare_gt.
    auto.
Qed.

Lemma nat_compare_Eq:
forall n m,
Nat.compare n m = Eq <-> n = m.
Proof.
induction n.
 split; intros.
  apply nat_compare_eq; trivial.
  
  unfold Nat.compare.
  destruct m; trivial.
  discriminate H.
  
 intros.
 split.
  intros.
  apply nat_compare_eq; trivial.
  
  intros.
  destruct m.
   discriminate H.
   
   inversion H.
   generalize H1; intro.
   apply IHn in H1.
   unfold Nat.compare.
   subst.
   destruct m; trivial.
Qed.

Lemma nat_compare_n_n:
forall n,
Nat.compare n n = Eq.
Proof.
intros.
rewrite nat_compare_Eq.
trivial.
Qed.

Lemma lt_gt: forall n m, n < m <-> m > n. Proof. split; trivial. Qed.
Lemma le_ge: forall n m , n <= m <-> m>=n. Proof. split;trivial. Qed.

Lemma nat_compare_lt_gt_sym: 
forall n m, Nat.compare n m = Lt <-> Nat.compare m n = Gt.
Proof.
intros;split;intros.
apply nat_compare_lt in H.
rewrite lt_gt in H.
rewrite <- nat_compare_gt;trivial.
apply nat_compare_gt in H.
rewrite <- lt_gt in H.
rewrite <- nat_compare_lt;trivial.
Qed.

Lemma nat_compare_eq_sym: 
forall n m, Nat.compare n m = Eq <-> Nat.compare m n = Eq.
Proof.
intros;split;intros;rewrite nat_compare_Eq;rewrite nat_compare_Eq in H;symmetry;trivial.
Qed.

Lemma truncate_1:
forall n (s : stack A),
n <= length s  ->
n = length ( truncate n s).
Proof.
intros.
unfold truncate in |- *.
induction s.
 simpl in *.
 assert (n = 0) by auto with arith.
 destruct Nat.compare; trivial.
 
 case_eq (Nat.compare n (length (a :: s))); intro.
  apply nat_compare_Eq in H0; trivial.
  
  apply IHs.
  clear IHs.
  apply nat_compare_lt in H0.
  unfold length in H0.
  auto with *.
  
  apply nat_compare_gt in H0.
  apply le_not_lt in H.
  elim H.
  trivial.
Qed.

Lemma truncate_nil:
forall (s : stack A),
truncate 0 s = nil.
Proof.
intros.
induction s.
unfold truncate.
unfold Nat.compare; trivial.
unfold truncate.
replace (Nat.compare 0 (length (a::s))) with Lt by trivial.
trivial.
Qed.

Lemma map_truncate:
forall (f : A -> B) n (s : stack A),
map f (truncate n s) = truncate n (map f s).
Proof.
intros.
induction s.
 unfold truncate in |- *.
 simpl in |- *.
 unfold map in |- *.
 destruct Nat.compare; trivial.
 
 unfold truncate in |- *.
 case_eq (Nat.compare n (length (map f (a :: s)))); intro.
  generalize H; intro.
  rewrite map_length in H0.
  unfold map at 2 in |- *.
  unfold map in H.
  rewrite H in |- *.
  rewrite H0 in |- *.
  trivial.
  
  generalize H; intro.
  rewrite map_length in H0.
  unfold map at 2 in |- *.
  unfold map in H.
  rewrite H in |- *.
  rewrite H0 in |- *.
  assumption.
  
  generalize H; intro.
  rewrite map_length in H0.
  unfold map at 2 in |- *.
  unfold map in H.
  rewrite H in |- *.
  rewrite H0 in |- *.
  trivial.
Qed.

Lemma level_eq:
forall (s t : stack A),
(s, t) = level s t
  <->
length s = length t.
Proof.
intros.
split; intro. 
 unfold level in H.
 case_eq (Nat.compare (length s) (length t)); intro.
  apply nat_compare_Eq in H0; trivial.
  
  rewrite H0 in H.
  inversion H.
  apply truncate_1.
  apply nat_compare_lt in H0.
  auto with *.
  
  rewrite H0 in H.
  inversion H.
  symmetry  in |- *.
  apply truncate_1.
  apply nat_compare_gt in H0.
  progress auto with *.

 unfold level in |- *.
 replace (Nat.compare (length s) (length t)) with Eq ; trivial.
 symmetry  in |- *; rewrite nat_compare_Eq in |- *; trivial.
Qed.

Lemma level_le:
forall (s t : stack A),
(s, truncate (length s) t) = level s t 
  <->
length s <= length t.
Proof.
split;intros.
unfold level in H.
case_eq (Nat.compare (length s) (length t));intros.
apply nat_compare_Eq in H0.
rewrite H0.
trivial.
apply nat_compare_lt in H0.
auto with *.
assert (truncate (length s) t = t).
unfold truncate.
destruct t.
destruct Nat.compare;trivial.
rewrite H0.
trivial.
rewrite H1 in H.
rewrite H0 in H.
inversion H.
generalize truncate_1.
intro.
specialize H2 with (length t) s.
apply nat_compare_lt_gt_sym in H0.
apply nat_compare_lt in H0.
assert ((length t) <= (length s)).
auto with *.
apply H2 in H4.
rewrite <- H4.
trivial.
unfold level.
case_eq(Nat.compare (length s) (length t));intros.
unfold truncate.
destruct t.
destruct Nat.compare;trivial.
rewrite H0;trivial.
trivial.
apply nat_compare_le in H.
elim H;trivial.
Qed.

Lemma level_ge:
forall (s t : stack A),
(truncate (length t) s, t) = level s t 
  <->
length t <= length s.
Proof.
split;intros.
unfold level in H.
case_eq (Nat.compare (length t) (length s));intros.
apply nat_compare_Eq in H0.
rewrite H0.
trivial.
apply nat_compare_lt in H0.
auto with *.
assert (truncate (length t) s = s).
unfold truncate.
destruct s.
simpl.
destruct (Nat.compare (length t) 0);trivial.
rewrite H0.
trivial.
rewrite H1 in H.
apply nat_compare_lt_gt_sym in H0.
rewrite H0 in H.
inversion H.
generalize truncate_1.
intro.
specialize H2 with (length s) t.
apply nat_compare_lt_gt_sym in H0.
apply nat_compare_gt in H0.
assert ((length s) <= (length t)).
auto with *.
apply H2 in H4.
rewrite <- H4.
trivial.
unfold level.
case_eq(Nat.compare (length s) (length t));intros.
unfold truncate.
destruct s.
simpl.
destruct (Nat.compare (length t) 0);trivial.
apply nat_compare_eq_sym in H0.
rewrite H0;trivial.
apply nat_compare_ge in H.
elim H;trivial.
trivial.
Qed.

Lemma level_1: 
forall (s s' t t' : stack A),
(s', t') = level s t ->
length s' = length t'.
Proof.
intros.
unfold level in H.
case_eq (Nat.compare (length s) (length t));intros;rewrite H0 in H.
apply nat_compare_Eq in H0.
inversion H.
trivial.
inversion H;subst.
apply truncate_1.
apply nat_compare_lt in H0.
auto with *.
inversion H;subst.
symmetry.
apply truncate_1.
apply nat_compare_gt in H0.
auto with *.
Qed.

Lemma truncate_pop:
forall n (s : stack A),
  length s = (S n) ->
  truncate n s = pop s.
Proof.
intros.
unfold truncate in |- *.
destruct s.
 destruct Nat.compare; trivial.
 
 rewrite H in |- *.
 rewrite nat_compare_n_Sn in |- *.
 unfold pop in |- *.
 assert (length s = n).
  unfold length in H.
  apply eq_add_S.
  trivial.
  
  destruct s.
   destruct Nat.compare; trivial.
   
   rewrite H0 in |- *.
   replace (Nat.compare n n) with Eq .
   trivial.
   symmetry.
   rewrite nat_compare_Eq.
   trivial.

Qed.

Lemma truncate_same:
forall (s : stack A),
truncate (length s) s = s.
Proof.
intros.
unfold truncate.
destruct s.
destruct Nat.compare;trivial.
rewrite nat_compare_n_n.
trivial.
Qed.

Lemma truncate_n_nil:
forall n,
truncate n nil = nil (A := A).
Proof.
intros. unfold truncate.
destruct Nat.compare;trivial.
Qed.

Lemma truncate_truncate:
forall n m (s : stack A),
  n <= m ->
  truncate n s = truncate n (truncate m s).
Proof.
induction s.
intuition.
repeat rewrite truncate_n_nil;trivial.
intros.
generalize H.
intros.
apply  IHs in H0.
unfold truncate.
case_eq (Nat.compare m (length (a::s))).
case_eq (Nat.compare n (length (a::s))).
trivial.
trivial.
trivial.
unfold truncate in H0.
rewrite <- H0.
clear H0.
intros.
case_eq (Nat.compare n (length (a::s))).
intuition.
apply nat_compare_lt in H0.
apply nat_compare_Eq in H1.
subst.
apply le_not_lt in H.
elim H;trivial.
trivial.
intuition.
apply nat_compare_lt in H0.
apply nat_compare_gt in H1.
assert (m < n).
apply lt_gt in H1.
apply lt_trans with (length (a::s));trivial.
apply le_not_lt in H.
elim H;trivial.
trivial.
Qed.

End proofs.
