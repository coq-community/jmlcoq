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

Require Export ZArith.
(** Common interface for numerics domains *)
Open Scope Z_scope.

Module Type NUMERIC.
  Parameter t : Set.
  Parameter toZ : t -> Z.
  Parameter power : Z.
  Definition half_base := 2^power.
  Definition base := 2 * half_base.
  Definition range (z : Z) : Prop := -half_base <= z < half_base.
  Parameter range_prop : forall x:t , range (toZ x).
  Parameter num_dec : forall t1 t2:t , {t1 = t2} + {t1 <> t2}.
  Definition smod (x:Z) : Z :=
    let z := x mod base in 
    match Z.compare z half_base  with
    | Lt => z
    | _ => z - base
    end.

  Parameter add : t -> t -> t.
  Parameter add_prop : forall i1 i2 ,
    toZ (add i1 i2) = smod (toZ i1 + toZ i2).

  Parameter sub : t -> t -> t.
  Parameter sub_prop : forall i1 i2 ,
    toZ (sub i1 i2) = smod (toZ i1 - toZ i2).

  Parameter mul : t -> t -> t.
  Parameter mul_prop : forall i1 i2 ,
    toZ (mul i1 i2) = smod (toZ i1 * toZ i2).

  Parameter div : t -> t -> t.
  Parameter div_prop : forall i1 i2 ,
    toZ (div i1 i2) = smod (toZ i1 / toZ i2).

  Parameter rem : t -> t -> t.
  Parameter rem_prop : forall i1 i2 ,
    toZ (rem i1 i2) = smod (toZ i1 mod toZ i2).

  Parameter shr : t -> t -> t.
  Parameter shr_prop : forall i1 i2 ,
    toZ (shr i1 i2) = toZ i1 / 2^(toZ i2 mod 32). (* 5 last bits *)

  Parameter shl : t -> t -> t.
  Parameter shl_prop : forall i1 i2 ,
    toZ (shr i1 i2) = smod (toZ i1 * 2^(toZ i2 mod 32)).

  Parameter ushr : t -> t -> t.
  Parameter ushr_prop1 : forall i1 i2 ,
    toZ i1 < 0 ->
    toZ (ushr i1 i2) = smod ((toZ i1 + base) / 2^(toZ i2 mod 32)).

  Parameter ushr_prop2 : forall i1 i2 ,
    toZ i1 >= 0 ->
    toZ (ushr i1 i2) = toZ i1 / 2^(toZ i2 mod 32).

  (* and, or, xor sould be specified according to Coq library *)
  Parameter and : t -> t -> t.
  Parameter or : t -> t -> t.
  Parameter xor : t -> t -> t.
  Parameter not : t -> t.

  Parameter neg : t -> t.
  Parameter neg_prop : forall i ,
    toZ (neg i) = smod (- toZ i).

  Parameter const : Z -> t.
  Parameter const_prop : forall z ,
    range z -> toZ (const z) = z.

End NUMERIC.
