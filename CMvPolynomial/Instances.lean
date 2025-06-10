import Mathlib

instance : Std.Irrefl λ x1 x2 : ℕ => x1 < x2 := ⟨Nat.lt_irrefl⟩

instance : Std.Total λ x1 x2 : ℕ => ¬x1 < x2 := by
  constructor
  simp [Nat.le_total]

instance : Std.Asymm λ x1 x2 : ℕ => x1 < x2 := ⟨λ _ _ h => Nat.lt_asymm h⟩

instance :
  Trans
    (λ x1 x2 : ℕ => ¬x1 < x2)
    (λ x1 x2 => ¬x1 < x2)
    λ x1 x2 : ℕ => ¬x1 < x2
:= by
  constructor
  intros a b c h₁ h₂
  rw [not_lt] at *
  simp [Nat.le_trans h₂ h₁]
