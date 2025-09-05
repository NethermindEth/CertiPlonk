import FF.LCocoaParser
import FF.Normalise
import Qq

open Lean Qq Elab Term Tactic

namespace EzPz

open CoCoA

def c1 : Fin 41 := default

def test : String :=
  "UNSAT(" ++
  "  REDUCTIONS(" ++
  "    M(13, 14)" ++
  "  )" ++
  "  POLYNOMIALS(" ++
  "    P(6, c1 -1)" ++
  "  )" ++
  ")"

def test' : String :=
  "UNSAT(
     REDUCTIONS(
     )
     POLYNOMIALS(
       P(1, z ^ 3 * x + x * y * 2)
       P(1, x)
       P(1, -2 + z ^ 4 + x ^ 2 * y * 16)
       P(1, z ^ 3 + x ^ 2 * 2)
       P(1, z ^ 3 * x + x * y * 946458 + x ^ 2 * 630972)
       P(1, -262905 - z * 175270 + z * x * y + x)
       P(1, -709842 - z * 473228 + z * x * y + x * 2129526)
       P(1, -920166 - z * 613444 + z * x * y - x)
     )
   )"

set_option hygiene false in
def obtainInfo : MTacM Unit := do
  let fromIo ← IO.FS.readFile "FF/Sample.txt"
  match Parser.runParserCategory (←getEnv) `term s!"[CoCoA|{fromIo}]" with
  | .ok stx => let `([CoCoA|$cocoa]) := stx | throwError "Malformed CoCoA."
               logInfo m!"Parse successful. Omitting result." -- cocoa: {repr cocoa}"
               let CoCoA ← unsafe Elab.Term.evalTerm (Ast.Cocoa) q(Ast.Cocoa) stx
               logInfo m!"CoCoA: {repr CoCoA}"
               let polyStx ← CoCoA.polynomials.mapM Ast.Polynomial.toStx
               let mut i := 0
               for (idx, poly) in polyStx do
                 let iS := mkIdent (.mkSimple s!"H{i}")
                 withMainContext ∘ liftMTac ∘ runTactic' <|
                   (←`(tactic|let $iS := ($idx, $poly)))
                 i := i + 1
  | .error e => Lean.logInfo m!"oops: {e}"

elab "obtainInfo" : tactic => obtainInfo.toTacticM

example {c1 x c2 c3 c4 diseq_0 : ZMod 394357} [Fact (Nat.Prime 394357)]
  : x - 42 = 0 := by
  obtainInfo

-- example {x y z : ZMod 394357} [Fact (Nat.Prime 394357)]
--   (h : z * x * 9 * y + x * 9 - z * 2 = 3)
--   (h' : z * x * (-9) * y + x * 9 - z * 2 = 3)
--   (h'' : z * x * (-5) * y + x * 9 - z * 2 = 3)
--   (h₁ : x * 4 * y * 4 * x + z^4 = 2)
--   (h₂ : z^3 + x^2 + x^2 = 0)
--   (h₃ : 5 * x * y + y * x + 4 * x^2 + 5 * z^3 * x = 0)
--   (h₄ : x * y + y * x + z^3 * x = 0)
--   (h₆ : 2 * 394356 * x = 0)
--   : x - 42 = 0 := by
--   -- obtainInfo
--   -- normalise_system
--   obtainInfo

  sorry

end EzPz
