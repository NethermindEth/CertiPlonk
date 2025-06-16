import CMvPolynomial
import Certificate

open Lean in
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  IO.println s!"Hello, {hello}!"
