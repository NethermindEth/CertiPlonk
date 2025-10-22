import CertiPlonk.Fundamentals.Core
-- import CertiPlonk.Fundamentals.U32

notation "BB_prime" => 2013265921
@[simp] lemma BB_eq : BB_prime = 2013265921 := rfl

namespace BabyBear

-- notation "F" => Fin BB_prime
notation "FBB" => Fin BB_prime
@[simp] lemma F_eq : FBB = Fin BB_prime := rfl

lemma prime_BabyBearPrime : Nat.Prime BB_prime := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime BB_prime) := ⟨prime_BabyBearPrime⟩
instance : NeZero BB_prime := by constructor; decide

instance : Field FBB := ZMod.instField BB_prime
instance : NoZeroDivisors FBB := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

section inverses

lemma inv_255 : (465814468 : FBB) = 255⁻¹ := by native_decide
lemma inv_256 : (2005401601 : FBB) = 256⁻¹ := by native_decide

lemma inv_256_eq_one_lr : (2005401601 : FBB) * 256 = 1 := by rfl
lemma inv_256_eq_one_rl : 256 * (2005401601 : FBB) = 1 := by rfl

@[simp] lemma inv_256_eq_256_lr : (2005401601 : FBB) * x = 1 ↔ x = 256 := by rw [inv_256, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_256_eq_256_rl : x * (2005401601 : FBB) = 1 ↔ x = 256 := by rw [mul_comm, inv_256_eq_256_lr]

end inverses

section coercions

instance : Coe (BitVec 8) FBB where
  coe b := ⟨ b.toNat, by omega ⟩

instance : Coe FBB (BitVec 8) where
  coe bb := { toFin := ⟨ bb.val % 256, by omega ⟩ }

end coercions

section U32

@[simp, grind]
def isU32 (bb0 bb1 bb2 bb3 : FBB) :=
  bb0.val < 256 ∧ bb1.val < 256 ∧ bb2.val < 256 ∧ bb3.val < 256

-- @[simp, grind]
-- def toU32 {bb0 bb1 bb2 bb3 : FBB}
--   (isU32_b : isU32 bb0 bb1 bb2 bb3) : U32
-- :=
--   #v[ { toFin := ⟨ bb0.val, (by grind)⟩ },
--       { toFin := ⟨ bb1.val, (by grind)⟩ },
--       { toFin := ⟨ bb2.val, (by grind)⟩ },
--       { toFin := ⟨ bb3.val, (by grind)⟩ } ]

end U32

section auxiliaries

lemma lt_via_diff_and_range_check
  (a b c d : FBB)
  (h_c : c.val < 2^17)
  (h_d : d.val < 2^12)
  (h_diff : (a - b - 1).val < c + d * 131072)
: b.val < BB_prime - 2^29 + 1 → b.val < a.val := by
  grind

@[simp low] lemma to_the_right_FBB_0 : (0 : FBB) = a ↔ a = 0 := by omega
@[simp low] lemma to_the_right_FBB_1 : (1 : FBB) = a ↔ a = 1 := by omega
@[simp low] lemma to_the_right_FBB_255 : (255 : FBB) = a ↔ a = 255 := by omega

@[simp low] lemma one_plus_eq_zero : (1 : FBB) + a = 0 ↔ a = 2013265920 := by omega
@[simp low] lemma neg_one_plus_eq_zero : (2013265920 : FBB) + a = 0 ↔ a = 1 := by omega

end auxiliaries

end BabyBear
