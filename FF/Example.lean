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

def obtainInfo : MTacM Unit := do
  -- let x ← IO.FS.readFile "FF/Sample.txt"
  match Parser.runParserCategory (←getEnv) `term s!"[CoCoA|{test}]" with
  | .ok stx => let `([CoCoA|$cocoa]) := stx | throwError "Malformed CoCoA."
              --  logInfo m!"cocoa: {repr cocoa}"
               let xyz ← unsafe Elab.Term.evalTerm (Std.HashMap String (ZMod 41) → Ast.Cocoa) q( Std.HashMap String (ZMod 41) → Ast.Cocoa) stx
               let verbibols : Std.HashMap String (ZMod 41) :=
                 Std.HashMap.ofList [
                   ("c1", (4 : ZMod 41)), ("y", (4 : ZMod 41)), ("z", (4 : ZMod 41))
                 ]
               logInfo m!"xyz: {repr (xyz verbibols)}"
              --  let xyz ← Elab.Term.elabTerm stx .none
              --  logInfo m!"xyz: {xyz}"
              --  liftMTac ∘ runTactic' <| ←`(tactic|have h₇ : )
  | .error e => Lean.logInfo m!"oops: {e}"

elab "obtainInfo" : tactic => obtainInfo

example {x y z : ZMod 394357} [Fact (Nat.Prime 394357)]
  (h : z * x * 9 * y + x * 9 - z * 2 = 3)
  (h' : z * x * (-9) * y + x * 9 - z * 2 = 3)
  (h'' : z * x * (-5) * y + x * 9 - z * 2 = 3)
  (h₁ : x * 4 * y * 4 * x + z^4 = 2)
  (h₂ : z^3 + x^2 + x^2 = 0)
  (h₃ : 5 * x * y + y * x + 4 * x^2 + 5 * z^3 * x = 0)
  (h₄ : x * y + y * x + z^3 * x = 0)
  (h₆ : 2 * 394356 * x = 0)
  : x - 42 = 0 := by
  obtainInfo
  -- normalise_system

  sorry

end EzPz
