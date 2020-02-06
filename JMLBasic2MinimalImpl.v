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

(**
  Implementation of the basic2minimal rewritings specified in the BASIC2MINIMAL module.
 *)

Require Import JMLBasic2Minimal.
Require Import JMLSyntax.
Require Import List.

Module BASIC2MINIMAL_P := BASIC2MINIMAL P.Program.
Import BASIC2MINIMAL_P.

Module MINIMAL_REWRITINGS <: REWRITINGS_TYPE.

  Definition desugarSignalsOnly (typs:list StaticType) : Expression :=
    let varE := param Exception_e in 
    let desugar1 (typ:StaticType) : Expression := (varE instanceof typ)%jml in 
    fold_right (BinaryCondBoolExpr ConditionalOr) (false'%jml) (map desugar1 typs).

  (*
    In order for this implementation to be correct, it is essential that the 
    exception parameter used by desugarSignalsOnly and the 
    exception parameter of the signals clause of /sc/ refer to the same parameter name.
    In this implementation both parameters refer to Exception_e as parameter name.
    @see SIGNALS.signalsParam_eq_Exception_e
  *)
  Definition rewriteSignalsOnly (sc:SpecificationCase) : SpecificationCase :=
    let soTypes := SIGNALS_ONLY.types (CASE.signalsOnly sc) in 
    let soExpr  := desugarSignalsOnly soTypes in 
    let sExpr   :=
      match SIGNALS.pred (CASE.signals sc) with
      | NotSpecified => true'%jml
      | Specified e  => e
      end in 
    let signals' := SIGNALS.Build_t (: sExpr &&' soExpr :)%jml in 
    CASE.setSignals sc signals'.

  Definition rewriteSpecificationCase (sc:SpecificationCase) : SpecificationCase :=
    rewriteSignalsOnly sc.

  Definition rewriteMethod (m:Method) : Method :=
    let specs' := map rewriteSpecificationCase (METHOD.specs m) in
    METHOD.setSpecs m specs'.

  Definition rewriteTYPEDEF (e:TYPEDEF.t) : TYPEDEF.t :=
    let methods' := map rewriteMethod (TYPEDEF.methods e) in
    TYPEDEF.setMethods e methods'.

  Definition rewriteProgram (p:Program) : Program :=
    let (classes,interfaces) := p in 
    let classes'    := map rewriteTYPEDEF classes in
    let interfaces' := map rewriteTYPEDEF interfaces in
    PROG.Build_t classes' interfaces'.

End MINIMAL_REWRITINGS.

    
