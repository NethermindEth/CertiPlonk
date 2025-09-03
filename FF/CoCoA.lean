import Mathlib.Data.ZMod.Basic

namespace EzPz

namespace CoCoA

namespace Ast

open Lean

structure IndexedExpr where
  i : Nat
  t : Expr
  deriving Inhabited, Repr

inductive Reduction where
  | M (i₁ i₂ : Nat)
  | S (t₁ t₂ : IndexedExpr) (i : Nat)
  | R (i₁ i₂ : Nat) (l : Array IndexedExpr)
  deriving Inhabited, Repr

structure Polynomial where
  P :: i : Nat
       t : Expr
  deriving Inhabited, Repr

structure Cocoa where
  reductions : Array Reduction
  polynomials : Array Polynomial
  deriving Inhabited, Repr

end Ast

end CoCoA

end EzPz
