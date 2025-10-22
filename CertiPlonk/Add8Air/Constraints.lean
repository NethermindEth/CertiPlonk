import CertiPlonk.Add8Air.Air
import CertiPlonk.Add8Air.Extraction
import CertiPlonk.Fundamentals.BabyBear
import CertiPlonk.Util

import LeanZKCircuit.Interactions

namespace Add8Air.constraints

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

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.a row 0 + air.b row 0 - (air.r row 0 * 256 + air.c row 0) = 0

      @[Add8Air_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_0 air row ↔ constraint_0 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.r row 0 * air.r row 0 - air.r row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_1 air row ↔ constraint_1 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c row 0 -
      (air.c₀ row 0 + air.c₁ row 0 * 2 + air.c₂ row 0 * 4 + air.c₃ row 0 * 8 + air.c₄ row 0 * 16 + air.c₅ row 0 * 32 +
          air.c₆ row 0 * 64 +
        air.c₇ row 0 * 128) =
    0

      @[Add8Air_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_2 air row ↔ constraint_2 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c₀ row 0 * air.c₀ row 0 - air.c₀ row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_3 air row ↔ constraint_3 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c₁ row 0 * air.c₁ row 0 - air.c₁ row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_4 air row ↔ constraint_4 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c₂ row 0 * air.c₂ row 0 - air.c₂ row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_5 air row ↔ constraint_5 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c₃ row 0 * air.c₃ row 0 - air.c₃ row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_6 air row ↔ constraint_6 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c₄ row 0 * air.c₄ row 0 - air.c₄ row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_7 air row ↔ constraint_7 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c₅ row 0 * air.c₅ row 0 - air.c₅ row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_8 air row ↔ constraint_8 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c₆ row 0 * air.c₆ row 0 - air.c₆ row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_9 air row ↔ constraint_9 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

      @[Add8Air_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_Add8Air F ExtF) (row : ℕ) : Prop :=
        air.c₇ row 0 * air.c₇ row 0 - air.c₇ row 0 = 0

      @[Add8Air_air_simplification]
      lemma constraint_10_of_extraction
          (air : Valid_Add8Air F ExtF) (row : ℕ)
      : Add8Air.extraction.constraint_10 air row ↔ constraint_10 air row := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction

      @[Add8Air_constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_Add8Air F ExtF) : Prop :=
        air.bus = List.flatMap (fun row ↦ []) (List.range (air.last_row + 1))

      @[Add8Air_air_simplification]
      lemma constrain_interactions_of_extraction
          (air : Valid_Add8Air F ExtF)
      : Add8Air.extraction.constrain_interactions air ↔ constrain_interactions air := by
      apply Iff.intro
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification] at h
        simp only [Add8Air_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [plonky3_encapsulation, Add8Air_constraint_and_interaction_simplification]
        simp only [Add8Air_constraint_and_interaction_simplification] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold

    @[simp]
def extracted_row_constraint_list
  [Field ExtF]
  (air : Valid_Add8Air FBB ExtF)
  (row : ℕ)
: List Prop :=
  [
    Add8Air.extraction.constraint_0 air row,
    Add8Air.extraction.constraint_1 air row,
    Add8Air.extraction.constraint_2 air row,
    Add8Air.extraction.constraint_3 air row,
    Add8Air.extraction.constraint_4 air row,
    Add8Air.extraction.constraint_5 air row,
    Add8Air.extraction.constraint_6 air row,
    Add8Air.extraction.constraint_7 air row,
    Add8Air.extraction.constraint_8 air row,
    Add8Air.extraction.constraint_9 air row,
    Add8Air.extraction.constraint_10 air row,
  ]

@[simp]
def allHold
  [Field ExtF]
  (air : Valid_Add8Air FBB ExtF)
  (row : ℕ)
  (_ : row ≤ air.last_row)
: Prop :=
  Add8Air.extraction.constrain_interactions air ∧
  List.Forall (·) (extracted_row_constraint_list air row)

@[simp]
def row_constraint_list
  [Field ExtF]
  (air : Valid_Add8Air FBB ExtF)
  (row : ℕ)
: List Prop :=
  [
    constraint_0 air row,
    constraint_1 air row,
    constraint_2 air row,
    constraint_3 air row,
    constraint_4 air row,
    constraint_5 air row,
    constraint_6 air row,
    constraint_7 air row,
    constraint_8 air row,
    constraint_9 air row,
    constraint_10 air row,
  ]

@[simp]
def allHold_simplified
  [Field ExtF]
  (air : Valid_Add8Air FBB ExtF)
  (row : ℕ)
  (_ : row ≤ air.last_row)
: Prop :=
  constrain_interactions air ∧
  List.Forall (·) (row_constraint_list air row)

lemma allHold_simplified_of_allHold
  [Field ExtF]
  (air : Valid_Add8Air FBB ExtF)
  (row : ℕ)
  (h_row : row ≤ air.last_row)
: allHold air row h_row ↔ allHold_simplified air row h_row := by
  unfold allHold allHold_simplified
  apply Iff.and
  . unfold Add8Air.extraction.constrain_interactions
    simp [plonky3_encapsulation]
    rfl
  . simp only [extracted_row_constraint_list,
              row_constraint_list,
              Add8Air_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

    @[simp]
    lemma is_bool {a : FBB} : a * a - a = 0 ↔ a = 0 ∨ a = 1 := by grind

    theorem spec_soundness_FBB
      {air : Valid_Add8Air FBB ExtF}
      {row}
      (r_le : row ≤ air.last_row)
      (h_a : air.a row 0 < 256)
      (h_b : air.b row 0 < 256)
    :
      allHold_simplified air row r_le → air.c row 0 = (air.a row 0 + air.b row 0) % 256
    := by
      intro constraints
      simp [Add8Air_constraint_and_interaction_simplification] at constraints
      grind

    theorem spec_soundness_ℕ
      {air : Valid_Add8Air FBB ExtF}
      {row}
      (r_le : row ≤ air.last_row)
      (h_a : air.a row 0 < 256)
      (h_b : air.b row 0 < 256)
    :
      allHold_simplified air row r_le → (air.c row 0).val = ((air.a row 0).val + (air.b row 0).val) % 256
    := by
      intro constraints
      have := spec_soundness_FBB r_le h_a h_b constraints
      grind

    attribute [local grind] Bool.toNat_le

    set_option maxHeartbeats 1_000_000_000 in
    lemma bit_decomposition
      {x x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : FBB}
      (h_x : x < 256)
      (h0 : x₀ = 0 ∨ x₀ = 1)
      (h1 : x₁ = 0 ∨ x₁ = 1)
      (h2 : x₂ = 0 ∨ x₂ = 1)
      (h3 : x₃ = 0 ∨ x₃ = 1)
      (h4 : x₄ = 0 ∨ x₄ = 1)
      (h5 : x₅ = 0 ∨ x₅ = 1)
      (h6 : x₆ = 0 ∨ x₆ = 1)
      (h7 : x₇ = 0 ∨ x₇ = 1)
      (h_dcmp : x = x₀ + x₁ * 2 + x₂ * 4 + x₃ * 8 + x₄ * 16 + x₅ * 32 + x₆ * 64 + x₇ * 128)
    :
      x₀ = x % 2 ∧
      x₁ = (x / 2) % 2 ∧
      x₂ = (x / 4) % 2 ∧
      x₃ = (x / 8) % 2 ∧
      x₄ = (x / 16) % 2 ∧
      x₅ = (x / 32) % 2 ∧
      x₆ = (x / 64) % 2 ∧
      x₇ = (x / 128) % 2
    := by
      split_ands
      all_goals
        simp [Fin.ext_iff]
        grind

    set_option maxHeartbeats 1_000_000_000 in
    theorem determinism
      {air₁ : Valid_Add8Air FBB ExtF}
      {air₂ : Valid_Add8Air FBB ExtF}
      {row₁ row₂}
      (r_le₁ : row₁ ≤ air₁.last_row)
      (r_le₂ : row₂ ≤ air₂.last_row)
      (h_a : air₁.a row₁ 0 < 256)
      (h_b : air₁.b row₁ 0 < 256)
      (h_cstrs₁ : allHold_simplified air₁ row₁ r_le₁)
      (h_cstrs₂ : allHold_simplified air₂ row₂ r_le₂)
      (h_eq_a : air₁.a row₁ 0 = air₂.a row₂ 0)
      (h_eq_b : air₁.b row₁ 0 = air₂.b row₂ 0)
    :
      air₁.a row₁ 0 = air₂.a row₁ 0 ∧
      air₂.b row₂ 0 = air₂.b row₂ 0
        →
      air₁.c row₁ 0 = air₂.c row₂ 0 ∧
      air₁.r row₁ 0 = air₂.r row₂ 0 ∧
      air₁.c₀ row₁ 0 = air₂.c₀ row₂ 0 ∧
      air₁.c₁ row₁ 0 = air₂.c₁ row₂ 0 ∧
      air₁.c₂ row₁ 0 = air₂.c₂ row₂ 0 ∧
      air₁.c₃ row₁ 0 = air₂.c₃ row₂ 0 ∧
      air₁.c₄ row₁ 0 = air₂.c₄ row₂ 0 ∧
      air₁.c₅ row₁ 0 = air₂.c₅ row₂ 0 ∧
      air₁.c₆ row₁ 0 = air₂.c₆ row₂ 0 ∧
      air₁.c₇ row₁ 0 = air₂.c₇ row₂ 0
    := by
      intro ⟨ eq_a, eq_b ⟩
      obtain ⟨ h_c, h_eq_c ⟩ : air₁.c row₁ 0 < 256 ∧ air₁.c row₁ 0 = air₂.c row₂ 0
      := by
        have := spec_soundness_FBB r_le₁ h_a h_b h_cstrs₁
        have := spec_soundness_FBB r_le₂ (by grind) (by grind) h_cstrs₂
        grind
      simp [Add8Air_constraint_and_interaction_simplification] at h_cstrs₁ h_cstrs₂
      obtain ⟨ h_bus₁, h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, h6₁, h7₁, h8₁, h9₁, h10₁ ⟩ := h_cstrs₁
      obtain ⟨ h_bus₂, h0₂, h1₂, h2₂, h3₂, h4₂, h5₂, h6₂, h7₂, h8₂, h9₂, h10₂ ⟩ := h_cstrs₂
      simp [sub_eq_zero] at *
      simp [*]

      apply bit_decomposition h_c h3₁ h4₁ h5₁ h6₁ h7₁ h8₁ h9₁ h10₁ at h2₁
      apply bit_decomposition (by omega) h3₂ h4₂ h5₂ h6₂ h7₂ h8₂ h9₂ h10₂ at h2₂
      simp_all

    @[simp] lemma mod_2_is_bit (x : FBB) : x % 2 = 0 ∨ x % 2 = 1 := by grind

    lemma bit_recomposition
      {x : FBB}
      (ub_x : x < 256)
    :
      x = x % 2 + x / 2 % 2 * 2 + x / 4 % 2 * 4 + x / 8 % 2 * 8 +
          x / 16 % 2 * 16 + x / 32 % 2 * 32 + x / 64 % 2 * 64 + x / 128 % 2 * 128
    := by
      simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
      grind

    set_option maxHeartbeats 1_000_000_000 in
    theorem spec_completeness
      {a b : FBB}
      (h_a : a < 256)
      (h_b : b < 256)
    :
      ∃ (air : Valid_Add8Air FBB ExtF) (row : ℕ) (r_le : row ≤ air.last_row),
        air.a row 0 = a ∧ air.b row 0 = b ∧
        allHold_simplified air row r_le
    := by
      let c : FBB := (a + b) % 256
      let add8air :=
        Raw_Add8Air.mk
          (F := FBB)
          (ExtF := ExtF)
          (bus := List.flatMap (fun _ ↦ []) (List.range 1))
          (challenge := fun _ ↦ 0)
          (permutation := fun _ ↦ 0)
          (preprocessed := fun _ ↦ 0)
          (public_values := fun _ ↦ 0)
          (last_row := 0)
          (a := fun _ _ ↦ a)
          (b := fun _ _ ↦ b)
          (c := fun _ _ ↦ c)
          (r := fun _ _ ↦ if a + b < 256 then 0 else 1)
          (c₀ := fun _ _ ↦ c % 2)
          (c₁ := fun _ _ ↦ (c / 2) % 2)
          (c₂ := fun _ _ ↦ (c / 4) % 2)
          (c₃ := fun _ _ ↦ (c / 8) % 2)
          (c₄ := fun _ _ ↦ (c / 16) % 2)
          (c₅ := fun _ _ ↦ (c / 32) % 2)
          (c₆ := fun _ _ ↦ (c / 64) % 2)
          (c₇ := fun _ _ ↦ (c / 128) % 2)
          (main := fun col row rotation =>
            match col with
            | 0 => a
            | 1 => b
            | 2 => c
            | 3 => if a + b < 256 then 0 else 1
            | 4 => c % 2
            | 5 => (c / 2) % 2
            | 6 => (c / 4) % 2
            | 7 => (c / 8) % 2
            | 8 => (c / 16) % 2
            | 9 => (c / 32) % 2
            | 10 => (c / 64) % 2
            | 11 => (c / 128) % 2
            | _ => 0 )
      have add8air_valid : add8air.isValid := by
        unfold Raw_Add8Air.isValid
        unfold Raw_Add8Air.col_0 Raw_Add8Air.col_1 Raw_Add8Air.col_2 Raw_Add8Air.col_3 Raw_Add8Air.col_4
               Raw_Add8Air.col_5 Raw_Add8Air.col_6 Raw_Add8Air.col_7 Raw_Add8Air.col_8 Raw_Add8Air.col_9
               Raw_Add8Air.col_10 Raw_Add8Air.col_11
        subst add8air; simp_all
      have : add8air.last_row = 0 := by simp [add8air]
      exists ⟨ add8air, add8air_valid ⟩, add8air.last_row, by simp
      simp_all [Add8Air_constraint_and_interaction_simplification]
      simp_all [Valid_Add8Air.bus,
                Valid_Add8Air.a,
                Valid_Add8Air.b,
                Valid_Add8Air.c,
                Valid_Add8Air.r,
                Valid_Add8Air.c₀,
                Valid_Add8Air.c₁,
                Valid_Add8Air.c₂,
                Valid_Add8Air.c₃,
                Valid_Add8Air.c₄,
                Valid_Add8Air.c₅,
                Valid_Add8Air.c₆,
                Valid_Add8Air.c₇,
                add8air]
      simp [sub_eq_zero]
      constructor
      . simp [ c]
        simp [Fin.ext_iff, Fin.val_add]
        repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
        split_ifs with sum_byte <;> omega
      . split_ands
        . omega
        . apply bit_recomposition
          simp [c, Fin.lt_def]
          omega

  end properties

end Add8Air.constraints
