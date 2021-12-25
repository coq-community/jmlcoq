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

From JML Require Import JMLProgram.

(*#
  BASIC2MINIMAL provides rewritings from the basic syntax into an even smaller syntax set,
  called minimal syntax. The goal is to achieve a minimal syntax set that contains
  no constructs that are rewritable in terms of other syntactical constructs.
 
  Currently, the only basic2minimal rewriting is ...
 *)

Module BASIC2MINIMAL (P:PROGRAM).
  Import P.

  Module Type REWRITINGS_TYPE.
    (**
      rewriteProgram p 
        -> rewriteTYPEDEF for every type declared in program p
     *)
    Parameter rewriteProgram : Program -> Program.

    (**
      rewriteTYPEDEF e
        -> rewriteMethod for every method m declared in e
     *)
    Parameter rewriteTYPEDEF : TYPEDEF.t -> TYPEDEF.t.

    (**
      rewriteMethod m e
        -> rewriteSpecificationCase
     *)
    Parameter rewriteMethod : Method -> Method.

    (**
      rewriteSpecificationCase sc
        -> rewriteSignalsOnly
     *)
    Parameter rewriteSpecificationCase : SpecificationCase -> SpecificationCase.

    (**
      rewriteSignalsOnly sc
      Rewrite the signals_only clause so in sc as a signals clause s' = Tr [so],
      where 
        Tr [signals_only \nothing]    = signals Exception true
        Tr [signals_only E1, ..., En] = signals (Exception e) (e instanceof E1 || ... || e instanceof En)
      The resulting specification case contains a signals clause that is the
      &&-combination of the original signals clause of /sc/ and s'.
     *)
    Parameter rewriteSignalsOnly : SpecificationCase -> SpecificationCase.
  End REWRITINGS_TYPE.

End BASIC2MINIMAL.
