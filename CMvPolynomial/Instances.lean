import Mathlib

instance : Std.Irrefl fun (x1 x2 : ℕ) => x1 < x2 := ⟨Nat.lt_irrefl⟩

instance : Std.Total fun (x1 x2 : ℕ) => ¬x1 < x2 := by
  constructor
  simp [Nat.le_total]

instance : Std.Asymm fun (x1 x2 : ℕ) => x1 < x2 := ⟨λ _ _ h => Nat.lt_asymm h⟩

instance :
  Trans
    (fun (x1 x2 : ℕ) => ¬x1 < x2)
    (fun x1 x2 => ¬x1 < x2)
    fun (x1 x2 : ℕ) => ¬x1 < x2
:= by
  constructor
  intros a b c h₁ h₂
  rw [not_lt] at *
  simp [Nat.le_trans h₂ h₁]
