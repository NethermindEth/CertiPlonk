import Mathlib

instance : Std.Irrefl fun (x1 x2 : ℕ) => x1 < x2 := by
  constructor
  apply Nat.lt_irrefl

instance : Std.Total fun (x1 x2 : ℕ) => ¬x1 < x2 := by
  constructor
  intros a b
  rw [Nat.not_lt, Nat.not_lt]
  apply Nat.le_or_le b a

instance : Std.Asymm fun (x1 x2 : ℕ) => x1 < x2 := by
  constructor
  intros a b h_lt
  simp only [not_lt]
  rw [Nat.le_iff_lt_or_eq]
  simp [h_lt]

instance :
  Trans
    (fun (x1 x2 : ℕ) => ¬x1 < x2)
    (fun x1 x2 => ¬x1 < x2)
    fun (x1 x2 : ℕ) => ¬x1 < x2
:= by
  constructor
  intros a b c h₁ h₂
  simp only [not_lt] at *
  apply Nat.le_trans (m := b) <;> simp [*]
