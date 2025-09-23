import Mathlib

import LeanZKCircuit.Plonky3.Circuit
import LeanZKCircuit.Plonky3.Command.Air.define_air

open Plonky3

set_option linter.unusedVariables false

#define_air "Add8Air" using "plonky3_encapsulation" where
  Column["a"]
  Column["b"]
  Column["c"]
  Column["r"]
  Column["c₀"]
  Column["c₁"]
  Column["c₂"]
  Column["c₃"]
  Column["c₄"]
  Column["c₅"]
  Column["c₆"]
  Column["c₇"]
