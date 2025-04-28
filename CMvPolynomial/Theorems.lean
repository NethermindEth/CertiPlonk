import CMvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic

def finRangeNoDup (top n : Nat) (le_top_n : top ≤ n) :
  Σ' (l : List (Fin n)), (∀ x, x ∈ l ↔ x.val < top) ∧ List.Nodup l := by
  cases top with
    | zero => exists []; simp
    | succ top' =>
      have top_le_n : top' ≤ n := by
        apply le_trans _ le_top_n
        simp only [Nat.le_step, Nat.le_refl]
      let ⟨l', in_l_iff_lt, nodup⟩ := finRangeNoDup top' n top_le_n
      exists ⟨top', le_top_n⟩ :: l'
      constructor
      · intro x
        constructor
        · intro x_belongs
          cases x_belongs with
          | head l' => simp
          | tail n' belongs =>
            have x_le_top := (in_l_iff_lt x).1 belongs
            simp only [Nat.lt_succ_of_lt, x_le_top]
        · intro a_le_succ_top
          rw [Nat.lt_succ_iff_lt_or_eq] at a_le_succ_top
          simp only [List.mem_cons]
          rcases a_le_succ_top with h₁ | h₂
          · simp only [in_l_iff_lt x, h₁, or_true]
          · left; cases h₂; simp only [Fin.eta]
      · apply List.Pairwise.cons
        · intros a a_in_l'
          simp only [Fin.ne_iff_vne, Nat.ne_iff_lt_or_gt]
          right
          simp_all only
        · exact nodup

def fromCMvMonomial (m : CMvMonomial n) : (Fin n →₀ ℕ) :=
  let ⟨l, in_l_iff_lt, nodup⟩ := finRangeNoDup n n (Nat.le_refl n)
  let ms : Multiset (Fin n) := Multiset.ofList l
  let support0 : Finset (Fin n) :=
    { val := Multiset.ofList l
      nodup := by simp only [Multiset.coe_nodup, nodup]
    }
  let support := { i ∈ support0 | m.get i ≠ 0 }
  let toFun : Fin n → ℕ := m.get
  let mem_support_fun : ∀ (a : Fin n), a ∈ support ↔ toFun a ≠ 0 := by
    intro a; constructor
    · intro a_belongs
      simp [support] at a_belongs
      simp [a_belongs, toFun]
    · intro toFunNeZero
      simp only [toFun] at toFunNeZero
      simp [support]
      constructor <;> simp [support0, in_l_iff_lt a, *]
  Finsupp.mk support toFun mem_support_fun

def toMvPolynomial [CommRing R] (p : CMvPolynomial n R) :
  MvPolynomial (Fin n) R
:=
  let support : Finset ((Fin n) →₀ ℕ) := sorry
  let toFun : (Fin n →₀ ℕ) → R := sorry
  let mem_support_fun : ∀ (a : Fin n →₀ ℕ), a ∈ support ↔ toFun a ≠ 0 := sorry
  Finsupp.mk support toFun mem_support_fun
