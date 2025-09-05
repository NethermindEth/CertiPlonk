import Lean

open Lean

namespace EzPz

structure NormaliseST where
  goal : MVarId
  goals : Array MVarId

/--
Similar to `TacticM`.
-/
abbrev MTacM := StateT NormaliseST Elab.Tactic.TacticM

end EzPz
