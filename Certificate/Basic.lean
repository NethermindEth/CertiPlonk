import Mathlib.Lean.CoreM

namespace Certificate

-- Some datastructures
structure FFVal where
    val : Nat
    fieldSize: Nat

def Model := List FFVal

open Lean Elab Term

section Syntax

declare_syntax_cat ffval
declare_syntax_cat ffmodel

syntax "FFV(" num "," num ")" : ffval
syntax "SAT(" ffval+ ")" : ffmodel

end Syntax

section Elaborator

def ffvalElab (s: TSyntax `ffval) : Except String FFVal :=
  match s with
  | `(ffval| FFV($n1:num, $n2:num)) => do
    return { val := n1.getNat, fieldSize := n2.getNat}
  | stx => throw s!"Unrecognised finite field value: {stx}"

def ffmodelElab (s: TSyntax `ffmodel) : Except String Model :=
  match s with
  | `(ffmodel| SAT($vs:ffval*)) => do vs.toList.mapM ffvalElab
  | stx => throw s!"Unrecognised model: {stx}"

end Elaborator

end Certificate
