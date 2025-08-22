import CMvPolynomial.CMvPolynomial
import CMvPolynomial.Wheels
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib

section

open Std

namespace CPoly
open CMvPolynomial

section

variable {n : ℕ} {R : Type} [CommSemiring R]

def fromCMvPolynomial [BEq R] [LawfulBEq R] (p : CMvPolynomial n R) : MvPolynomial (Fin n) R :=
  let support : List (Fin n →₀ ℕ) := p.monomials.map CMvMonomial.toFinsupp
  let toFun (f : Fin n →₀ ℕ) : R := p[CMvMonomial.ofFinsupp f]?.getD 0
  let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by
    dsimp [toFun, support]
    refine ⟨fun _ _ ↦ ?p₁, fun _ ↦ ?p₂⟩
    · grind
    · suffices ∃ m ∈ p, CMvMonomial.toFinsupp m = a by grind
      grind
  Finsupp.mk support.toFinset toFun (by simp [mem_support_fun])

@[aesop simp]
lemma eq_iff_fromCMvPolynomial [BEq R] [LawfulBEq R] {u v: CMvPolynomial n R} :
  u = v ↔ fromCMvPolynomial u = fromCMvPolynomial v := by sorry

@[simp]
lemma map_mul [BEq R] [LawfulBEq R] (a b : CMvPolynomial n R) :
  fromCMvPolynomial (a * b) = (fromCMvPolynomial a) * (fromCMvPolynomial b)
:= by
  sorry

@[simp]
lemma map_add [BEq R] [LawfulBEq R]  (a b : CMvPolynomial n R) :
  fromCMvPolynomial (a + b) = fromCMvPolynomial a + fromCMvPolynomial b
:= by
  sorry

@[simp]
lemma map_zero [BEq R] [LawfulBEq R] : fromCMvPolynomial (0 : CMvPolynomial n R) = 0 := by
  sorry

@[simp]
lemma map_one [BEq R] [LawfulBEq R] : fromCMvPolynomial (1 : CMvPolynomial n R) = 1 := by
  sorry

noncomputable def toCMvPolynomial (p : MvPolynomial (Fin n) R) : CMvPolynomial n R :=
  let ⟨s, f, _⟩ := p
  let unlawful := Std.ExtTreeMap.ofList <| s.toList.map fun m ↦ (CMvMonomial.ofFinsupp m, f m)
  ⟨
    unlawful,
    by
      intros m contra
      obtain ⟨elem, h₁⟩ : ∃ (h : m ∈ unlawful), unlawful[m] = 0 :=
        ExtTreeMap.getElem?_eq_some_iff.1 contra
      obtain ⟨a, ha₁, ⟨rfl⟩⟩ : ∃ a ∈ s, .ofFinsupp a = m := by simpa [unlawful] using elem
      have : f a = 0 := by
        dsimp [unlawful] at h₁
        rwa [ExtTreeMap.getElem_ofList_of_mem (k := CMvMonomial.ofFinsupp a)
                                              (v := f a)
                                              (k_eq := by simp)
                                              (mem := by simp; use a)
                                              (distinct := ?distinct)] at h₁
        case distinct =>
          simp only [Std.compare_eq_iff_eq, List.pairwise_map]
          exact distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)
      grind
  ⟩

variable [BEq R] [LawfulBEq R]

@[grind=, simp]
theorem toCMvPolynomial_fromCMvPolynomial {p : CMvPolynomial n R} :
  toCMvPolynomial (fromCMvPolynomial p) = p := by
  dsimp [fromCMvPolynomial, toCMvPolynomial, toCMvPolynomial, fromCMvPolynomial]
  ext m; simp only [CMvPolynomial.coeff]; congr 1
  by_cases eq : m ∈ p <;> simp [eq]
  rw [ExtTreeMap.getElem_ofList_of_mem (k := m) (k_eq := by simp)
                                       (mem := ?mem) (distinct := ?distinct)]
  case mem => simp; grind
  case distinct =>
    simp only [Std.compare_eq_iff_eq, List.pairwise_map]
    exact distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)

@[grind=, simp]
theorem fromCMvPolynomial_toCMvPolynomial {p : MvPolynomial (Fin n) R} :
  fromCMvPolynomial (toCMvPolynomial p) = p := by
  dsimp [fromCMvPolynomial, toCMvPolynomial, toCMvPolynomial, fromCMvPolynomial]
  ext m; simp [MvPolynomial.coeff]
  rcases p with ⟨s, f, hf⟩
  simp only [Finsupp.coe_mk]
  generalize eq : (ExtTreeMap.ofList _ _) = p
  by_cases eq₁ : CMvMonomial.ofFinsupp m ∈ p
  · obtain ⟨m', hm'₁, hm'₂⟩ : ∃ a ∈ s, CMvMonomial.ofFinsupp a = CMvMonomial.ofFinsupp m := by aesop
    have : f m' ≠ 0 := by grind
    obtain ⟨rfl⟩ : m' = m := CMvMonomial.injective_ofFinsupp hm'₂
    suffices p[CMvMonomial.ofFinsupp m] = f m by simpa [eq₁]
    simp_rw [←eq]
    rw [ExtTreeMap.getElem_ofList_of_mem (k := CMvMonomial.ofFinsupp m) (k_eq := by simp)
                                         (mem := by simp; use m) (distinct := ?distinct)]
    case distinct =>
      simp only [Std.compare_eq_iff_eq, List.pairwise_map]
      exact distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)
  · have : ∀ x ∈ s, CMvMonomial.ofFinsupp x ≠ CMvMonomial.ofFinsupp m := by aesop
    grind

noncomputable def polyEquiv:
  Equiv (CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toFun := fromCMvPolynomial
  invFun := toCMvPolynomial
  left_inv := fun _ ↦ toCMvPolynomial_fromCMvPolynomial
  right_inv := fun _ ↦ fromCMvPolynomial_toCMvPolynomial

lemma add_zero {p : CMvPolynomial n R} : p + 0 = p := by aesop

lemma zero_add {p : CMvPolynomial n R} : 0 + p = p := by aesop

attribute [local grind=] Unlawful.add Lawful.add Unlawful.mul Lawful.mul

lemma mul_one {p : CMvPolynomial n R} : p * 1 = p := by aesop

lemma left_distrib : ∀ {p q r : CMvPolynomial n R}, (p + q) * r = p * r + q * r := by aesop

instance {n : ℕ} : AddCommSemigroup (CPoly.CMvPolynomial n R) where
  add_assoc := by aesop (add safe apply add_assoc)
  add_comm := by grind

instance {n : ℕ} : AddMonoid (CPoly.CMvPolynomial n R) where
  zero_add _ := zero_add -- this is just `by grind` but in a different scope
  add_zero _ := add_zero -- this is just `by grind` but in a different scope
  nsmul n p := (List.replicate n p).sum
  nsmul_succ {m x} := by grind -- `nsmul` def changed + `add_comm` is now available; `grind`!

lemma mul_assoc : ∀ (a b c : CMvPolynomial n R), a * b * c = a * (b * c) := by
  aesop (add safe apply _root_.mul_assoc)

instance {n : ℕ} : MonoidWithZero (CPoly.CMvPolynomial n R) where
  zero_mul := by grind
  mul_zero := by aesop
  mul_assoc := mul_assoc
  one_mul := by aesop
  mul_one := fun _ ↦ mul_one

instance {n : ℕ} : Semiring (CPoly.CMvPolynomial n R) where
  left_distrib {p q r} := by aesop
  right_distrib {p q r} := by aesop

instance {n : ℕ} : CommSemiring (CPoly.CMvPolynomial n R) where
  natCast_zero := by grind
  natCast_succ := by intro n; simp
  npow_zero := by intro x; simp [npowRecAuto, npowRec]
  npow_succ := by intro n x; simp [npowRecAuto, npowRec]
  mul_comm := by aesop (add safe apply _root_.mul_comm)

noncomputable def polyRingEquiv :
  RingEquiv (CPoly.CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toEquiv := CPoly.polyEquiv
  map_mul' := map_mul
  map_add' := map_add

end

end CPoly
