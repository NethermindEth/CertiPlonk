import CMvPolynomial.CMvPolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Equiv.TransferInstance

open Std

namespace CPoly

variable {n : ℕ} {R : Type}

def fromCMvMonomial (m : CMvMonomial n) : Fin n →₀ ℕ :=
  ⟨{i : Fin n | m[i] ≠ 0}, m.get, by aesop⟩

def toCMvMonomial (m : Fin n →₀ ℕ) : CMvMonomial n := Vector.ofFn m

@[grind=, simp]
theorem monomial_id₁ {m : CMvMonomial n} : toCMvMonomial (fromCMvMonomial m) = m := by
  ext i hi; aesop (add simp [toCMvMonomial, fromCMvMonomial]) (add safe (by omega))

@[grind=, simp]
theorem monomial_id₂ {m : Fin n →₀ ℕ} : fromCMvMonomial (toCMvMonomial m) = m := by
  ext i; aesop (add simp [toCMvMonomial, Vector.get, fromCMvMonomial]) (add safe (by omega))

lemma injective_toCMvMonomial : Function.Injective (toCMvMonomial (n := n)) := 
  Function.HasLeftInverse.injective ⟨fromCMvMonomial, fun _ ↦ monomial_id₂⟩   

def monomial_equiv : CMvMonomial n ≃ (Fin n →₀ ℕ) where
  toFun := fromCMvMonomial
  invFun := toCMvMonomial
  left_inv := fun _ ↦ monomial_id₁
  right_inv := fun _ ↦ monomial_id₂

def fromLawfulCMvPolynomial [CommSemiring R] (p : LawfulCMvPolynomial n R) : MvPolynomial (Fin n) R :=  
  let support : List (Fin n →₀ ℕ) := p.monomials.map fromCMvMonomial
  let toFun (f : Fin n →₀ ℕ) : R := p[toCMvMonomial f]?.getD 0
  let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by
    dsimp [toFun, support]
    refine ⟨fun h contra ↦ ?p₁, fun h ↦ ?p₂⟩
    · obtain ⟨m, ⟨h₁, rfl⟩⟩ : ∃ m : CMvMonomial n, m ∈ p ∧ fromCMvMonomial m = a := by aesop
      obtain ⟨m', ⟨h₂, h₃⟩⟩ : ∃ a ∈ p, fromCMvMonomial a = fromCMvMonomial m := by aesop
      obtain ⟨rfl⟩ : m = m' := by injection h₃ with _ h₄
                                  ext x hx
                                  apply congr_fun (a := ⟨x, hx⟩) at h₄
                                  aesop (add simp Vector.get)
      simp [monomial_id₁, show m ∈ p.1 from h₂] at contra
      exact absurd (show (p.1)[m]? = .some 0 by grind)
                   LawfulCMvPolynomial.getElem?_ne_some_zero
    · suffices ∃ m ∈ p.1, fromCMvMonomial m = a by aesop
      use toCMvMonomial a
      grind
  Finsupp.mk support.toFinset toFun (by simp [mem_support_fun])

noncomputable def toLawfulCMvPolynomial [CommSemiring R]
  (p : MvPolynomial (Fin n) R) : LawfulCMvPolynomial n R := 
  let ⟨s, f, _⟩ := p
  let unlawful := Std.ExtTreeMap.ofList <| s.toList.map fun m ↦ (toCMvMonomial m, f m)
  ⟨
    unlawful,
    by
      intros m contra
      obtain ⟨elem, h₁⟩ : ∃ (h : m ∈ unlawful), unlawful[m] = 0 :=
        ExtTreeMap.getElem?_eq_some_iff.1 contra
      obtain ⟨a, ha₁, ⟨rfl⟩⟩ : ∃ a ∈ s, toCMvMonomial a = m := by simpa [unlawful] using elem
      have : f a = 0 := by
        dsimp [unlawful] at h₁
        rwa [ExtTreeMap.getElem_ofList_of_mem (k := toCMvMonomial a)
                                              (v := f a)
                                              (k_eq := by simp)
                                              (mem := by simp; use a)
                                              (distinct := ?distinct)] at h₁
        case distinct =>
          simp only [Std.compare_eq_iff_eq, List.pairwise_map]
          exact distinct_of_inj_nodup injective_toCMvMonomial (Finset.nodup_toList _)
      grind
  ⟩

def fromCMvPolynomial [CommSemiring R]
  (p : CMvPolynomial n R) : MvPolynomial (Fin n) R := fromLawfulCMvPolynomial p

noncomputable def toCMvPolynomial [CommSemiring R]
  (p : MvPolynomial (Fin n) R) : CMvPolynomial n R := toLawfulCMvPolynomial p

theorem polynomial_id₁ [CommSemiring R] {p : CMvPolynomial n R} :
  toCMvPolynomial (fromCMvPolynomial p) = p := by
  dsimp [fromCMvPolynomial, toCMvPolynomial, toLawfulCMvPolynomial, fromLawfulCMvPolynomial]
  ext m; simp only [CMvPolynomial.coeff]; congr 1
  by_cases eq : m ∈ p.1 <;> simp [eq]
  rw [ExtTreeMap.getElem_ofList_of_mem (k := m) (k_eq := by simp)
                                       (mem := ?mem) (distinct := ?distinct)]
  case mem => simp; grind
  case distinct =>
    simp only [Std.compare_eq_iff_eq, List.pairwise_map]
    exact distinct_of_inj_nodup injective_toCMvMonomial (Finset.nodup_toList _)  

theorem polynomial_id₂ [CommSemiring R] {p : MvPolynomial (Fin n) R} :
  fromCMvPolynomial (toCMvPolynomial p) = p := by
  dsimp [fromCMvPolynomial, toCMvPolynomial, toLawfulCMvPolynomial, fromLawfulCMvPolynomial]
  ext m; simp [MvPolynomial.coeff]
  rcases p with ⟨s, f, hf⟩
  simp only [Finsupp.coe_mk]
  generalize eq : (ExtTreeMap.ofList _ _) = p
  by_cases eq₁ : toCMvMonomial m ∈ p
  · obtain ⟨m', hm'₁, hm'₂⟩ : ∃ a ∈ s, toCMvMonomial a = toCMvMonomial m := by aesop
    have : f m' ≠ 0 := by grind
    obtain ⟨rfl⟩ : m' = m := injective_toCMvMonomial hm'₂
    suffices p[toCMvMonomial m] = f m by simpa [eq₁]
    simp_rw [←eq]
    rw [ExtTreeMap.getElem_ofList_of_mem (k := toCMvMonomial m) (k_eq := by simp)
                                         (mem := ?mem) (distinct := ?distinct)]
    case mem => simp; grind
    case distinct =>
      simp only [Std.compare_eq_iff_eq, List.pairwise_map]
      exact distinct_of_inj_nodup injective_toCMvMonomial (Finset.nodup_toList _)
  · have : ∀ x ∈ s, toCMvMonomial x ≠ toCMvMonomial m := by aesop
    grind  

noncomputable def polyEquiv [CommSemiring R] :
  Equiv (CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toFun := fromCMvPolynomial
  invFun := toCMvPolynomial
  left_inv := fun _ ↦ polynomial_id₁
  right_inv := fun _ ↦ polynomial_id₂

variable [CommSemiring R]

noncomputable instance : CommSemiring (CMvPolynomial n R) := Equiv.commSemiring polyEquiv

noncomputable def homomorphism₁ :
  RingHom (CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toFun := fromCMvPolynomial
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

-- noncomputable def homomorphism₂ [BEq R] [CommSemiring R] [LawfulBEq R] :
--   RingHom (MvPolynomial (Fin n) R) (CMvPolynomial n R)
-- where
--   toFun := toCMvPolynomial
--   map_one' := sorry
--   map_mul' := sorry
--   map_zero' := sorry
--   map_add' := sorry

end CPoly
