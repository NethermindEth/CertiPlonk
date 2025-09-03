import Lean
import Qq

import FF.CoCoA

open Lean Elab Term Qq

namespace EzPz

namespace CoCoA

declare_syntax_cat cocoa
declare_syntax_cat reduction
declare_syntax_cat polynomial

abbrev Cocoa := TSyntax `cocoa
abbrev Reduction := TSyntax `reduction
abbrev Polynomial := TSyntax `polynomial

syntax "UNSAT" "(" "REDUCTIONS" "(" reduction* ")" "POLYNOMIALS" "(" polynomial* ")" ")" : cocoa

syntax indexedTerm := num noWs "{" term "}"

syntax "P(" num "," term ")" : polynomial

syntax "M(" num "," num ")" : reduction
syntax "S(" indexedTerm "," indexedTerm "," num ")" : reduction
syntax "R(" num ";" indexedTerm,* ";" num ")" : reduction 

syntax "[CoCoA|" cocoa "]" : term

open Ast.Polynomial Ast.Reduction

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

def translateIndexedTerm (n : TSyntax `EzPz.CoCoA.indexedTerm) : MacroM Term := do
  let `(indexedTerm|$n{$t}) := n | Macro.throwError "unknown IndexedTerm"
  `(Ast.IndexedTerm.mk $n $t)

def translatePolynomial : Polynomial → MacroM Term
  | `(polynomial|P($n, $t)) => `(P $n q($t : ZMod 41))
  | _                       => Macro.throwError "unknown Polynomial"

def translateReduction : Reduction → MacroM Term
  | `(reduction|M($n₁, $n₂))                => `(M $n₁ $n₂)
  | `(reduction|S($i₁{$t₁}, $i₂{$t₂}, $n))  => `(S ⟨$i₁, $t₁⟩ ⟨$i₂, $t₂⟩ $n)
  | `(reduction|R($n₁; $[$its],*; $n₂)) => do
    let indexedTerms ← its.mapM translateIndexedTerm
    dbg_trace s!"indexedTerms: {indexedTerms}"
    `(R $n₁ $n₂ [$indexedTerms,*])
  | _ => default

def translateCocoa : Cocoa → MacroM Term
  | `(cocoa|UNSAT(REDUCTIONS($[$reductions]*) POLYNOMIALS($[$polynomials]*))) => do
    let reductions ← reductions.mapM translateReduction
    let polynomials ← polynomials.mapM translatePolynomial
    `(Ast.Cocoa.mk #[$reductions,*] #[$polynomials,*])
  | _ => default

macro_rules
  | `([CoCoA|$cocoa]) => do let res ← translateCocoa cocoa
                            dbg_trace s!"res: {res}"
                            pure res

-- UNSAT(
--   REDUCTIONS(
--     M(13, 14)
--   )
--   POLYNOMIALS(
--     P(6, c1 -1)
--   )
-- )



-- macro_rules
--   | `(a) => do let somethingLikeThis := translateCocoa c
--                         logInfo m!"somethingLikeThis: {repr somethingLikeThis}"
--                         _
--   | _ => _
   

end CoCoA

end EzPz

def x : ZMod 41 := default

#check [CoCoA|UNSAT(
                REDUCTIONS(
                  M(13, 14)
                )
                POLYNOMIALS(
                  P(6, x)
                )
              )]
