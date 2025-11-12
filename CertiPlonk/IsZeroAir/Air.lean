import Mathlib
import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

open Plonky3

set_option linter.unusedVariables false

#define_air "IsZeroAir" using "plonky3_encapsulation" where
   Column["x"]
   Column["y"]
   Column["z"]
