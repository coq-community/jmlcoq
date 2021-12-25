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

From JML Require Import JMLProgramPlusImpl.
From Coq Require Import ZArith.

Module java.
Module lang.
  Definition PKG_lang_ : PackageName := Program.PKG_lang_.

  Definition C_Object_ : ShortClassName := 1%Z.
  Definition Object_ : ClassName := (PKG_lang_, C_Object_).

  Definition C_Integer_ : ShortClassName := 2%Z.
  Definition Integer_ : ClassName := (PKG_lang_, C_Integer_).

  Definition C_String_ : ShortClassName := 3%Z.
  Definition String_ : ClassName := (PKG_lang_, C_String_).

  Definition C_Exception_ : ShortClassName := Program.C_Exception_.
  Definition Exception_ : ClassName := (PKG_lang_, C_Exception_).

  Definition C_CloneNotSupportedException_ : ShortClassName := 5%Z.
  Definition CloneNotSupportedException_ : ClassName := (PKG_lang_, C_CloneNotSupportedException_).

  Definition C_RuntimeException_ : ShortClassName := 6%Z.
  Definition RuntimeException_ : ClassName := (PKG_lang_, C_RuntimeException_).

  Definition C_IllegalArgumentException_ : ShortClassName := 7%Z.
  Definition IllegalArgumentException_ : ClassName := (PKG_lang_, C_IllegalArgumentException_).

  Definition C_Throwable_ : ShortClassName := 8%Z.
  Definition Throwable_ : ClassName := (PKG_lang_, C_Throwable_).

  Definition C_Error_ : ShortClassName := 9%Z.
  Definition Error_ : ClassName := (PKG_lang_, C_Error_).

  Module Object.
    Parameter M_Object_1 : MethodSignature.
    Parameter M_toString_2 : MethodSignature.
    Parameter M_finalize_3 : MethodSignature.
    Parameter M_clone_4 : MethodSignature.
    Parameter M_hashCode_5 : MethodSignature.
  End Object.

  Module Integer.
    Parameter M_Integer_1 : MethodSignature.
    Parameter M_intValue_2 : MethodSignature.
    Parameter M_toString_3 : MethodSignature.
    Parameter M_toString_4 : MethodSignature.
    Parameter M_min_5 : MethodSignature.
    Parameter F_MAX_VALUE : FieldSignature.
  End Integer.

  Module String.
    Parameter M_length_1 : MethodSignature.
  End String.

  Module Long.
    Parameter M_min_5 : MethodSignature.
    Parameter F_MAX_VALUE : FieldSignature.
  End Long.

End lang.
End java.

Module org.
Module jmlspecs.
Module models.
  Definition PKG_models_ : PackageName := 2%Z.
  Definition C_JMLObjectSet_ : ShortClassName := 10%Z.
  Definition JMLObjectSet_ : ClassName := (PKG_models_, C_JMLObjectSet_).

  Module JMLObjectSet.
    Parameter M_has_1 : MethodSignature.
  End JMLObjectSet.
End models.

End jmlspecs.
End org.
