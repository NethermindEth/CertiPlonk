import Mathlib.Data.Nat.Basic

instance : Std.Irrefl λ x1 x2 : ℕ ↦ x1 < x2 := ⟨Nat.lt_irrefl⟩

instance : Std.Total λ x1 x2 : ℕ ↦ ¬x1 < x2 := by
  constructor
  simp [Nat.le_total]

instance : Std.Asymm λ x1 x2 : ℕ ↦ x1 < x2 := ⟨λ _ _ h ↦ Nat.lt_asymm h⟩

instance :
  Trans
    (λ x1 x2 : ℕ ↦ ¬x1 < x2)
    (λ x1 x2 ↦ ¬x1 < x2)
    λ x1 x2 : ℕ ↦ ¬x1 < x2
:= by
  constructor
  intros a b c h₁ h₂
  rw [not_lt] at *
  simp [Nat.le_trans h₂ h₁]

-- instance isStrictCut {x : CMvMonomial n} [CommSemiring R] :
--   RBNode.IsStrictCut
--     (Ordering.byKey Prod.fst simpleCmp)
--     (λ x₁ : CMvMonomial n × R ↦ simpleCmp x x₁.1)
-- where
--   le_lt_trans := by
--     unfold simpleCmp compareOfLessAndEq
--     simp
--     intro m₁ c₁ m₂ c₂ _ h₁ h₂
--     simp [Ordering.byKey] at h₁
--     by_cases h_lt : (m₁ < m₂)
--     · trans m₁ <;> assumption
--     · rw [←h₁ h_lt]
--       assumption
--   le_gt_trans := by
--     unfold simpleCmp compareOfLessAndEq
--     simp
--     intro m₁ c₁ m₂ c₂ _ h₁ h₂ h₃
--     simp [Ordering.byKey] at h₁
--     constructor
--     · by_cases h_lt : (m₁ < m₂)
--       · trans m₂
--         · apply Vector.le_of_lt h_lt
--         · assumption
--       · rw [h₁ h_lt]
--         assumption
--     · intro contra
--       subst contra
--       apply h₃
--       apply h₁
--       assumption
--   exact := by
--     intro ⟨m₁, c₁⟩ ⟨m₂, c₂⟩ _
--     simp [Ordering.byKey, simpleCmp, compareOfLessAndEq]
--     intro h h_eq
--     subst h_eq
--     rfl
