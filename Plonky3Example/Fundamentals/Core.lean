import Mathlib

/-- A prime finite field has no zero divisors -/
instance Fin.noZeroDivisors_of_prime (p : ℕ)
    [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
  refine IsDomain.to_noZeroDivisors (ZMod (p + 1))

namespace BitVec

/-- `BitVec` extensionality as an iff -/
lemma ext_iff {n : ℕ} {x y : BitVec n} : x = y ↔ ∀ i : Fin n, x[i] = y[i] := by
  constructor <;> [ simp_all; intro heq ]
  . ext j lt_j
    exact heq ⟨ j, lt_j ⟩

/-- `BitVec` extension, signed and unsigned -/
def extend {m : ℕ} (bv : BitVec m) (n : ℕ) (sgn : Prop) [Decidable sgn] :=
  (if sgn then signExtend else setWidth) n bv

/-- Equality of `BitVec` concatenation, equal lengths -/
@[simp, grind =]
lemma append_eq_append_eql {m n : ℕ} {x1 y1 : BitVec m} {x2 y2 : BitVec n} :
  (x1 ++ x2) = (y1 ++ y2) ↔ x1 = y1 ∧ x2 = y2 := by
  constructor <;> [ intro h_eq_bv; simp_all ]
  split_ands <;> rw [ext_iff] at h_eq_bv ⊢ <;> intro i
  . specialize h_eq_bv ⟨i + n, by omega⟩; simp_all
    iterate 2 rw [BitVec.getElem_append (by omega)] at h_eq_bv
    simp_all
  . specialize h_eq_bv ⟨i, by omega⟩; simp_all
    iterate 2 rw [BitVec.getElem_append (by omega)] at h_eq_bv
    simp_all

/-- Reformulation of `sshiftRight` -/
lemma sshiftright_eq {n : ℕ} {bv : BitVec n} {shift : ℕ} :
  bv.sshiftRight shift =
    BitVec.setWidth n
      (BitVec.extractLsb ((n - 1) + shift) shift (BitVec.signExtend (n + shift) bv))
    := by grind

end BitVec

namespace Int

/-- Case analysis on `abs` -/
lemma abs_cases {a : ℤ} : abs a = if 0 ≤ a then a else -a := by
  unfold abs; rw [Int.max_def]; omega

/-- Case analysis of `Int.sign` -/
lemma sign_cases (a : ℤ) : a.sign = if a < 0 then -1 else if a = 0 then 0 else 1 := by
  by_cases a = 0
  . simp_all
  . by_cases 0 < a
    . rw [Int.sign_eq_one_of_pos (by omega)]; omega
    . rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega

/-- Case analysis on negative-zero-positive -/
lemma split_nzp (a : ℤ) (P : Prop) :
  (a < 0 → P) → (a = 0 → P) → (0 < a → P) → P := by
  intro an az ap
  by_cases a = 0
  . apply az (by assumption)
  . by_cases 0 < a
    . apply ap (by omega)
    . apply an (by omega)

end Int

section auxiliaries

lemma List.forall_in_range
  {n : ℕ}
  {P : ℕ → Prop}
  (m : ℕ)
  (in_range : m < n)
:
  List.Forall (fun n => P n) (List.range n) → P m
:= by
  induction n generalizing m
  case zero => simp_all
  case succ n ih => simp [List.range_add]; grind

@[simp low] lemma to_the_right_nat_0 : 0 = a ↔ a = 0 := by omega
@[simp low] lemma to_the_right_nat_1 : 1 = a ↔ a = 1 := by omega
@[simp low] lemma to_the_right_nat_255 : 255 = a ↔ a = 255 := by omega

end auxiliaries
