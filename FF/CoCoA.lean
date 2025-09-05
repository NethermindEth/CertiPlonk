import Mathlib.Data.ZMod.Basic

namespace EzPz

namespace CoCoA

namespace Ast

open Lean

structure IndexedTerm where
  i : Nat
  t : ZMod 41
  deriving Inhabited, Repr

inductive Reduction where
  | M (i₁ i₂ : Nat)
  | S (t₁ t₂ : IndexedTerm) (i : Nat)
  | R (i₁ i₂ : Nat) (l : Array IndexedTerm)
  deriving Inhabited, Repr

structure Polynomial where
  P :: i : Nat
       t : ZMod 41
  deriving Inhabited, Repr

structure Cocoa where
  reductions : Array Reduction
  polynomials : Array Polynomial
  deriving Inhabited, Repr

end Ast

end CoCoA

end EzPz
