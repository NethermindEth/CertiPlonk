import Parser

open Parser Char ASCII

namespace EzPz

namespace CoCoA

namespace Ast

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

end Ast

open Ast

abbrev State (α : Type) := SimpleParser Substring Char α

def parsePolynomial : State Polynomial := do
  discard (char 'P')
  discard (char '(')
  let n₁ ← parseNat
  discard (char ',')
  discard (char ' ')
  let (tokens, _) ← takeUntil (stop := char ')') anyToken
  pure (Polynomial.P n₁ ⟨tokens.toList⟩)

def parseIndexedTerm : State IndexedTerm := do
  let n₁ ← parseNat
  discard (char '{')
  let (tokens, stop) ← takeUntil (stop := char '}') anyToken
  if stop != '}' then throwUnexpectedWithMessage (msg := "Indexed equation must end with '}'.")
  pure ⟨n₁, ⟨tokens.toList⟩⟩

def whiteSpacePoof : State Unit := dropMany (whitespace <|> eol)

def parseReduction : State Reduction := do
  first [
    do discard (char 'M')
       discard (char '(')
       let n₁ ← parseNat
       discard (char ',')
       discard (char ' ')
       let n₂ ← parseNat
       discard (char ')')
       pure (Reduction.M n₁ n₂),
    do discard (char 'S')
       discard (char '(')
       let ti₁ ← parseIndexedTerm
       discard (char ',')
       discard (char ' ')
       let ti₂ ← parseIndexedTerm
       discard (char ',')
       discard (char ' ')
       let n₁ ← parseNat
       discard (char ')')
       pure (Reduction.S ti₁ ti₂ n₁),
    do discard (char 'R')
       discard (char '(')
       let n₁ ← parseNat
       discard (char ';')
       discard (char ' ')
       let (terms, _) ← takeUntil (stop := char ';') (parseIndexedTerm <* optional (char ',' <* char ' '))
       discard (char ' ')
       let n₂ ← parseNat
       discard (char ')')
       pure (Reduction.R n₁ n₂ terms)
  ]

def parseCocoa : State Cocoa := do
  discard (string "UNSAT(")
  whiteSpacePoof
  discard (string "REDUCTIONS(")
  whiteSpacePoof
  let reductions ← takeMany (parseReduction <* whiteSpacePoof)
  whiteSpacePoof
  discard (char ')')
  whiteSpacePoof
  discard (string "POLYNOMIALS(")
  whiteSpacePoof
  let polynomials ← takeMany (parsePolynomial <* whiteSpacePoof)
  discard (char ')')
  whiteSpacePoof
  discard (char ')')
  pure ⟨reductions, polynomials⟩

end CoCoA

end EzPz


-- import Mathlib.Lean.CoreM

-- import Lean

-- open Lean

-- namespace EzPz

-- namespace CoCoA

-- namespace Ast

-- structure IndexedTerm where
--   i : Nat
--   t : Term

-- inductive Reduction where
--   | M (i₁ i₂ : Nat)
--   | S (t₁ t₂ : IndexedTerm) (i : Nat)
--   | R (i₁ i₂ : Nat) (l : Array IndexedTerm)
--   deriving Inhabited

-- structure Polynomial where
--   P :: i : Nat
--        t : Term
--   deriving Inhabited

-- structure Cocoa where
--   reductions : Array Reduction
--   polynomials : Array Polynomial
--   deriving Inhabited

-- end Ast

-- declare_syntax_cat cocoa
-- declare_syntax_cat reduction
-- declare_syntax_cat polynomial

-- abbrev Cocoa := TSyntax `cocoa
-- abbrev Reduction := TSyntax `reduction
-- abbrev Polynomial := TSyntax `polynomial

-- syntax "UNSAT" "(" "REDUCTIONS" "(" reduction* ")" "POLYNOMIALS" "(" polynomial* ")" ")" : cocoa

-- syntax indexedTerm := num noWs "{" term "}"

-- syntax "P(" num "," term ")" : polynomial

-- syntax "M(" num "," num ")" : reduction
-- syntax "S(" indexedTerm "," indexedTerm "," num ")" : reduction
-- syntax "R(" num ";" indexedTerm,* ";" num ")" : reduction 

-- syntax "[CoCoA|" cocoa "]" : term

-- open Ast.Polynomial Ast.Reduction

-- def translatePolynomial : Polynomial → Ast.Polynomial
--   | `(polynomial|P($n, $t)) => P n.getNat t
--   | _                       => default

-- def translateReduction : Reduction → Ast.Reduction
--   | `(reduction|M($n₁, $n₂))                => M n₁.getNat n₂.getNat
--   | `(reduction|S($i₁{$t₁}, $i₂{$t₂}, $n))  => S ⟨i₁.getNat, t₁⟩ ⟨i₂.getNat, t₂⟩ n.getNat
--   | `(reduction|R($n₁; $[$nₖ{$tₖ}],*; $n₂)) => R n₁.getNat n₂.getNat (nₖ.zipWith (⟨·.getNat, ·⟩) tₖ)
--   | _ => default

-- def translateCocoa : Cocoa → Ast.Cocoa
--   | `(cocoa|UNSAT(REDUCTIONS($[$reductions]*) POLYNOMIALS($[$polynomials]*))) =>
--     {
--       reductions := reductions.map translateReduction
--       polynomials := polynomials.map translatePolynomial
--     }
--   | _ => default

-- end CoCoA

-- end EzPz
