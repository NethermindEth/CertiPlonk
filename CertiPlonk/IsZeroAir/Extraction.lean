import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit

open Plonky3

set_option linter.all false

register_simp_attr IsZeroAir_air_simplification
register_simp_attr IsZeroAir_constraint_and_interaction_simplification

namespace IsZeroAir.extraction

--Base constraints---
@[simp]
def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 2) (row := row) (rotation := 0)) * (Circuit.main c (column := 0) (row := row) (rotation := 0))) - 0) = 0

@[simp]
def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 2) (row := row) (rotation := 0)) - 1) * (((Circuit.main c (column := 0) (row := row) (rotation := 0)) * (Circuit.main c (column := 1) (row := row) (rotation := 0))) - 1)) - 0) = 0

@[simp]
def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 2) (row := row) (rotation := 0)) * (Circuit.main c (column := 2) (row := row) (rotation := 0))) - (Circuit.main c (column := 2) (row := row) (rotation := 0))) - 0) = 0

@[simp]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [])

end IsZeroAir.extraction
