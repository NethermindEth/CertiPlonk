import Parser

open Parser Char ASCII

namespace EzPz

namespace CoCoA

namespace AstAlt

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

end AstAlt

open AstAlt

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

def main (args : List String) : IO Unit := do
  let (file :: _) := args | IO.println "No arguments; terminating. Usage: parse <file>"
  let cocoaOutput ← IO.FS.readFile file
  match EzPz.CoCoA.parseCocoa.run cocoaOutput with
  | .ok _ out => IO.println (repr out)
  | .error _ e => IO.println s!"Error parsing the file: {e}"
