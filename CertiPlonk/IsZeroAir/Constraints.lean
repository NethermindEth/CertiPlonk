import CertiPlonk.IsZeroAir.Air
import CertiPlonk.IsZeroAir.Extraction
import CertiPlonk.Fundamentals.BabyBear
import CertiPlonk.Util

import LeanZKCircuit_Plonky3.Interactions

namespace IsZeroAir.constraints

  section constraint_simplification

    -- Note: `air` and `row` are not included as section variables
    --       so that the file can still be used with `sorry`
    --       during the extraction process
    --       Additionally, the proofs are split into more stages
    --       than required so that it can be easily checked that all
    --       intending folding is occuring

    variable [Field F] [Field ExtF]

    section row_constraints

      -- constraints and constraints_of_extraction
      -----Constraint simplification------
      -- z * x = 0
      @[IsZeroAir_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_IsZeroAir F ExtF) (row : ℕ) : Prop :=
        air.z row 0 * air.x row 0 = 0

      @[IsZeroAir_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_IsZeroAir F ExtF) (row : ℕ)
      : IsZeroAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification] at h
        simp only [IsZeroAir_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification]
        simp only [IsZeroAir_constraint_and_interaction_simplification] at h
        exact h

      -- (z - 1) * (x * y - 1) = 0
      @[IsZeroAir_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_IsZeroAir F ExtF) (row : ℕ) : Prop :=
        (air.z row 0 - 1) * (air.x row 0 * air.y row 0 - 1) = 0
      
      @[IsZeroAir_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_IsZeroAir F ExtF) (row : ℕ)
      : IsZeroAir.extraction.constraint_1 air row ↔ constraint_1 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification] at h
        simp only [IsZeroAir_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification]
        simp only [IsZeroAir_constraint_and_interaction_simplification] at h
        exact h

      -- z^2 - z = 0
      @[IsZeroAir_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_IsZeroAir F ExtF) (row : ℕ) : Prop :=
        (air.z row 0 * air.z row 0) - (air.z row 0) = 0

      @[IsZeroAir_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_IsZeroAir F ExtF) (row : ℕ)
      : IsZeroAir.extraction.constraint_2 air row ↔ constraint_2 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification] at h
        simp only [IsZeroAir_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification]
        simp only [IsZeroAir_constraint_and_interaction_simplification] at h
        exact h


    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction
      
      -----Interaction simplification-----
      @[IsZeroAir_constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_IsZeroAir F ExtF) : Prop :=
        air.bus = List.flatMap (fun row ↦ []) (List.range (air.last_row + 1))

      @[IsZeroAir_air_simplification]
      lemma constrain_interactions_of_extraction
          (air : Valid_IsZeroAir F ExtF)
      : IsZeroAir.extraction.constrain_interactions air ↔ constrain_interactions air := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification] at h
        simp only [IsZeroAir_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification]
        simp only [IsZeroAir_constraint_and_interaction_simplification] at h
        exact h


    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold
    
    -----All hold definitions-----------
    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_IsZeroAir FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        IsZeroAir.extraction.constraint_0 air row,
        IsZeroAir.extraction.constraint_1 air row,
        IsZeroAir.extraction.constraint_2 air row,
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_IsZeroAir FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      IsZeroAir.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_IsZeroAir FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        constraint_0 air row,
        constraint_1 air row,
        constraint_2 air row,
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_IsZeroAir FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_IsZeroAir FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold IsZeroAir.extraction.constrain_interactions
        simp [plonky3_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  IsZeroAir_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

  end properties

end IsZeroAir.constraints
