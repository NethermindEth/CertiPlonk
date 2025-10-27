import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit

open Plonky3

set_option linter.all false

register_simp_attr NAME_air_simplification
register_simp_attr NAME_constraint_and_interaction_simplification

namespace NAME.extraction
  --extracted constraints here
end NAME.extraction
