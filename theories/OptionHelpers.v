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

From Coq Require Import List.

(**
  Helper functions to work with option types:
  - isSome : option A -> bool.
  - optionMap : (A->B) -> option A -> option B.
  - option2list : option A -> list A.
  - optionList2list : list (option A) -> list A.
 *) 
Section OptionHelpers.
  Variable A : Type.
  Variable B : Type.

  (**
    true  iff exists a, oa = Some a
    false iff oa = None.
   *)
  Definition isSome (oa:option A) : bool :=
    match oa with
    | Some _ => true
    | None => false
    end.

  (**
    [a] iff oa = Some a,
    nil iff oa = None
   *)
  Definition option2list (ox:option A) : list A :=
    match ox with
    | None => nil 
    | Some x => x :: nil
    end.

  (**
    Map function f over a value of type option A.
   *)
  Definition optionMap (f:A->B) (ox:option A) : option B :=
    match ox with 
    | None => None 
    | Some x => Some (f x)
    end.

  (**
    Extract all Some-values from the given list of option A-values
    and return them as a list of A-values.
   *)
  Fixpoint optionList2list (l:list (option A)) : list A :=
    match l with
    | nil => nil
    | (Some x)::xs => x::(optionList2list xs)
    | None::xs     => optionList2list xs
    end.

End OptionHelpers.
Arguments option2list [A].
Arguments optionMap [A B].
Arguments optionList2list [A].


Section Proofs.
  Variable A : Type.

  (** optionList2list retains all non-None elements of the given list l. *)
  Lemma optionList2list_In : forall (x:A) (l:list (option A)), 
    In x (optionList2list l) <-> In (Some x) l.
  Proof.
    intros x l.
    induction l.
      simpl.
      intuition.

      case a.
        intro a0.
        simpl.
        intuition.
        left.
        rewrite H2.
        reflexivity.
        left.
        injection H2.
        intro; assumption.

        simpl.
        intuition.
        discriminate H2.  
  Qed.
End Proofs.
