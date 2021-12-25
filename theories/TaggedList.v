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
From Coq Require Import Decidable.

(**
  Utils to store tagged data in a list.
  A list with tagged data is much like a multi map:
  It allows to retrieve all data with a given tag.
 
  Useful functions:
   taggedFilter : retrieve all data with a given tag t from a list l.
   taggedMap    : apply a function mapF to a list with data with all the same tag t.
 
  The relationship between tag, data, and T:Type is as follows:
   tagOf: data -> tag
   mapF:  forall t:tag, t -> mapType t (T:Type = mapType t)
  
 *)

Section tagged.
  (** tag data type *)
  Variable tag : Set.

  (** tag equality must be decidable *)
  Variable tag_eq_dec : forall t1 t2:tag, {t1=t2}+{t1<>t2}.
  Lemma dec_eq_tag : forall t1 t2:tag, decidable (t1=t2).
  Proof.
    intros t1 t2.
    unfold decidable.
    case (tag_eq_dec t1 t2).
      left; assumption.
      right; assumption.
  Qed.

  (** data data type *)
  Variable data  : Type.

  (** Mapping data to tag *)
  Variable tagOf : data -> tag.

  (**
    Filter out all data d1 from list l that are tagged with t
   *)
  Fixpoint filterTag (t:tag) (l:list data) : list {d:data | t=tagOf d} :=
    match l with
    | nil  => nil
    | d1::ll =>
      let t1 := tagOf d1 in
      match tag_eq_dec t t1 return list {d:data | t=tagOf d} with
      | left Heq => (exist (fun d : data => t = tagOf d) d1 Heq) :: (filterTag t ll)
      | right _  => filterTag t ll
      end
    end. 

  (** Target dependent type for taggedMap *)
  Variable mapType : tag -> Type.

  (** Map function for taggedMap *)
  Variable mapF : forall t:tag, {d:data | t=tagOf d} -> mapType t.

  (** Map a list l of data with tag t using function mapF to a list of element type (mapType t). *)
  Definition mapData2Type : forall t:tag, list {d:data | t=tagOf d} -> list (mapType t) :=
    fun t => map (mapF t).

  (** Normal filter function lifted onto a list of tagged data. *)
  Definition filterTagData (t:tag) (p:data->bool) (l:list {d:data | t=tagOf d}) : list {d:data | t=tagOf d} :=
    filter (fun td:{d:data | t=tagOf d} => let (d,_) := td in p d) l.

  (**
    Normal map function lifted onto a list of tagged data.
    Map function f retrieves a data element together with a proof that the element has a given tag.
   *)
  Definition mapTag (f : forall t:tag, {d:data | t=tagOf d} -> data) (l:list data) : list data :=
    let f' (d:data) : data := f (tagOf d) (exist _ d (refl_equal (tagOf d))) in
    List.map f' l.

End tagged.


(* Deprecated but still nice code ;-)
Section tagged.
  Variable tag   : Set.
  Variable tag_eq_dec : forall t1 t2:tag, {t1=t2}+{t1<>t2}.
  Lemma dec_eq_tag : forall t1 t2:tag, decidable (t1=t2).
  Proof.
    intros t1 t2.
    unfold decidable.
    case (tag_eq_dec t1 t2).
      left; assumption.
      right; assumption.
  Qed.

  Variable data  : Type.
  Variable tagOf : data -> tag.

  Definition taggedData := {td:tag*data | (fst td) = tagOf (snd td)}.
  Definition tdTag (td:taggedData) : tag := match td with exist (t,_) _ => t end.
  Definition tdData (td:taggedData) : data := match td with exist (_,d) _ => d end.
  Definition tdProof (td:taggedData) : tdTag td = tagOf (tdData td) :=
    match td with exist _ P => P end.

  Definition extract1 : forall (t:tag) (td:taggedData), {d:data | d=tdData td /\ t=tagOf d}+{t <> tagOf (tdData td)}.
  refine
    (fun t td =>
    let t1 := tdTag td in
    let d1 := tdData td in
    let Htag := tdProof td in
    match tag_eq_dec t t1 with 
    | left Heq   => inleft (t <> tagOf d1) (exist _ d1 _)
    | right Hneq => inright {d:data | d=d1 /\ t=tagOf d} _
    end).

  Proof.
    split. 
      trivial.
      rewrite Heq.
      apply Htag.

    unfold not.
    intro Hf.
    unfold not in Hneq.
    rewrite <- Htag in Hf.
    apply (Hneq Hf).
  Defined.

  Fixpoint taggedFilter (t:tag) (l:list taggedData) : list {d:data | t=tagOf d} :=
    match l with
    | nil  => nil
    | td::ll =>
      match extract1 t td with
      | inleft (exist d (conj _ P)) => (exist _ d P) :: taggedFilter t ll
      | inright _ => taggedFilter t ll
      end
    end.

  Variable mapType : tag -> Type.
  Variable mapF : forall t:tag, {d:data | t=tagOf d} -> mapType t.
  Definition taggedMap : forall t:tag, list {d:data | t=tagOf d} -> list (mapType t) :=
    fun t => map (mapF t).
End tagged.
*)
