import Mathlib

import LeanZKCircuit.Plonky3.Circuit

open Plonky3

set_option linter.all false

register_simp_attr Add8Air_air_simplification
register_simp_attr Add8Air_constraint_and_interaction_simplification

namespace Add8Air.extraction
  --extracted constraints here

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - (((Circuit.main c (column := 3) (row := row) (rotation := 0)) * 256) + (Circuit.main c (column := 2) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 3) (row := row) (rotation := 0)) * (Circuit.main c (column := 3) (row := row) (rotation := 0))) - (Circuit.main c (column := 3) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    ((Circuit.main c (column := 2) (row := row) (rotation := 0)) - ((((((((Circuit.main c (column := 4) (row := row) (rotation := 0)) + ((Circuit.main c (column := 5) (row := row) (rotation := 0)) * 2)) + ((Circuit.main c (column := 6) (row := row) (rotation := 0)) * 4)) + ((Circuit.main c (column := 7) (row := row) (rotation := 0)) * 8)) + ((Circuit.main c (column := 8) (row := row) (rotation := 0)) * 16)) + ((Circuit.main c (column := 9) (row := row) (rotation := 0)) * 32)) + ((Circuit.main c (column := 10) (row := row) (rotation := 0)) * 64)) + ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * 128))) = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 4) (row := row) (rotation := 0)) * (Circuit.main c (column := 4) (row := row) (rotation := 0))) - (Circuit.main c (column := 4) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 5) (row := row) (rotation := 0)) * (Circuit.main c (column := 5) (row := row) (rotation := 0))) - (Circuit.main c (column := 5) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 6) (row := row) (rotation := 0)) * (Circuit.main c (column := 6) (row := row) (rotation := 0))) - (Circuit.main c (column := 6) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 7) (row := row) (rotation := 0)) * (Circuit.main c (column := 7) (row := row) (rotation := 0))) - (Circuit.main c (column := 7) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 8) (row := row) (rotation := 0)) * (Circuit.main c (column := 8) (row := row) (rotation := 0))) - (Circuit.main c (column := 8) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 9) (row := row) (rotation := 0)) * (Circuit.main c (column := 9) (row := row) (rotation := 0))) - (Circuit.main c (column := 9) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 10) (row := row) (rotation := 0)) * (Circuit.main c (column := 10) (row := row) (rotation := 0))) - (Circuit.main c (column := 10) (row := row) (rotation := 0))) = 0

  @[simp]
  def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    (((Circuit.main c (column := 11) (row := row) (rotation := 0)) * (Circuit.main c (column := 11) (row := row) (rotation := 0))) - (Circuit.main c (column := 11) (row := row) (rotation := 0))) = 0

  @[simp]
  def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
    Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [])

end Add8Air.extraction
