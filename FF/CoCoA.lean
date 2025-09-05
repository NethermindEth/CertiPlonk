import Mathlib.Data.ZMod.Basic
import FF.MTacM

namespace EzPz

namespace CoCoA

namespace Ast

open Lean

structure IndexedTerm where
  i : Nat
  t : String
  deriving Inhabited, Repr

inductive Reduction where
  | M (i₁ i₂ : Nat)
  | S (t₁ t₂ : IndexedTerm) (i : Nat)
  | R (i₁ i₂ : Nat) (l : Array IndexedTerm)
  deriving Inhabited, Repr

structure Polynomial where
  P :: i : Nat
       t : String
  deriving Inhabited, Repr

structure Cocoa where
  reductions : Array Reduction
  polynomials : Array Polynomial
  deriving Inhabited, Repr

def Polynomial.toStx (p : Polynomial) : MTacM (Term × Term) := do
  match Parser.runParserCategory (←getEnv) `term p.t with
  | .ok stx => let stx : Term := ⟨stx⟩
               let i : Term := Syntax.mkNatLit p.i
               pure (i, stx)
  | .error e => logError s!"Error: {e}"
                pure default

def IndexedTerm.toStx (it : IndexedTerm) : MTacM (Term × Term) :=
  Polynomial.toStx ⟨it.1, it.2⟩

end Ast

end CoCoA

end EzPz
