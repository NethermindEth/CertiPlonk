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
        simp_all only [mul_eq_zero] -- From aesop?
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification]
        simp only [IsZeroAir_constraint_and_interaction_simplification] at h
        simp_all only [mul_eq_zero]

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
        simp_all only [mul_eq_zero]
      . intro h
        simp [plonky3_encapsulation, IsZeroAir_constraint_and_interaction_simplification]
        simp only [IsZeroAir_constraint_and_interaction_simplification] at h
        simp_all only [mul_eq_zero]

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
    
    @[simp]
    lemma is_bool {a : FBB} : a * a - a = 0 ↔ a = 0 ∨ a = 1 := by grind

    theorem spec_soundness_FBB
      {air : Valid_IsZeroAir FBB ExtF}
      {row}
      (r_le : row ≤ air.last_row)
    :
      allHold_simplified air row r_le →
        if air.x row 0 = 0
        then air.z row 0 = 1
        else air.z row 0 = 0
    := by
      intro constraints
      simp [IsZeroAir_constraint_and_interaction_simplification] at constraints
      grind

    theorem spec_soundness_ℕ
      {air : Valid_IsZeroAir FBB ExtF}
      {row}
      (r_le : row ≤ air.last_row)
    :
      allHold_simplified air row r_le → 
        if (air.x row 0).val = 0
        then ((air.z row 0).val = 1)
        else (air.z row 0).val = 0
    := by
      intro constraints
      have := spec_soundness_FBB r_le constraints
      grind
      
    theorem determinism
      {air₁ : Valid_IsZeroAir FBB ExtF}
      {air₂ : Valid_IsZeroAir FBB ExtF}
      {row₁ row₂}
      (r_le₁ : row₁ ≤ air₁.last_row)
      (r_le₂ : row₂ ≤ air₂.last_row)
      (h_cstrs₁ : allHold_simplified air₁ row₁ r_le₁)
      (h_cstrs₂ : allHold_simplified air₂ row₂ r_le₂)
      (h_eq_a : air₁.x row₁ 0 = air₂.x row₂ 0)
    :
      air₁.z row₁ 0 = air₂.z row₂ 0
    := by
      have h_eq_z : air₁.z row₁ 0 = air₂.z row₂ 0 := by
        have := spec_soundness_FBB r_le₁ h_cstrs₁
        have := spec_soundness_FBB r_le₂ h_cstrs₂
        grind
      simp [IsZeroAir_constraint_and_interaction_simplification] at h_cstrs₁ h_cstrs₂
      obtain ⟨ h_bus₁, h0₁, h1₁, h2₁ ⟩ := h_cstrs₁
      obtain ⟨ h_bus₂, h0₂, h1₂, h2₂ ⟩ := h_cstrs₂
      
      simp_all

    theorem spec_completeness
      {x : FBB}
    :
      ∃ (air : Valid_IsZeroAir FBB ExtF) (row : ℕ) (r_le : row ≤ air.last_row),
        air.x row 0 = x ∧
        allHold_simplified air row r_le
    := by
      let y : FBB := x⁻¹
      let z : FBB :=
        if x = 0
        then 1
        else 0
      let isZeroAir := 
        Raw_IsZeroAir.mk
          (F := FBB)
          (ExtF := ExtF)
          (bus := List.flatMap (fun _ ↦ []) (List.range 1))
          (challenge := fun _ ↦ 0)
          (permutation := fun _ ↦ 0)
          (preprocessed := fun _ ↦ 0)
          (public_values := fun _ ↦ 0)
          (last_row := 0)
          (x := fun _ _ ↦ x)
          (y := fun _ _ ↦ y)
          (z := fun _ _ ↦ z)
          (main := fun col row rotation =>
            match col with
            | 0 => x
            | 1 => y
            | 2 => z
            | _ => 0 )
      have isZeroAir_valid : isZeroAir.isValid := by
        unfold Raw_IsZeroAir.isValid
        unfold Raw_IsZeroAir.col_0 Raw_IsZeroAir.col_1 Raw_IsZeroAir.col_2
        subst isZeroAir; simp_all
      have : isZeroAir.last_row = 0 := by simp [isZeroAir]
      exists ⟨ isZeroAir, isZeroAir_valid ⟩, isZeroAir.last_row, by simp
      simp_all [IsZeroAir_constraint_and_interaction_simplification]
      simp_all [Valid_IsZeroAir.bus,
                Valid_IsZeroAir.x,
                Valid_IsZeroAir.y,
                Valid_IsZeroAir.z,
                isZeroAir]
      split_ands
      · unfold z
        simp
        tauto
      · unfold z
        unfold y
        by_cases h : x = 0
        · simp [h]
        · simp [h]
      · unfold z
        simp
        tauto

  end properties

end IsZeroAir.constraints
