import CMvPolynomial.CMvPolynomial
import CMvPolynomial.Wheels
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.MvPolynomial.Basic
-- import Mathlib

-- import Std.Data.DTreeMap
section

open Std

namespace CPoly

section

variable {n : ℕ} {R : Type} [csR : CommSemiring R]

def fromCMvPolynomial [BEq R] [LawfulBEq R] (p : CMvPolynomial n R) : MvPolynomial (Fin n) R :=
  let support : List (Fin n →₀ ℕ) := p.monomials.map CMvMonomial.toFinsupp
  let toFun (f : Fin n →₀ ℕ) : R := p[CMvMonomial.ofFinsupp f]?.getD 0
  let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by
    dsimp [toFun, support]
    refine ⟨fun h contra ↦ ?p₁, fun h ↦ ?p₂⟩
    · obtain ⟨m, ⟨h₁, rfl⟩⟩ : ∃ m : CMvMonomial n, m ∈ p ∧ CMvMonomial.toFinsupp m = a := by aesop
      obtain ⟨m', ⟨h₂, h₃⟩⟩ : ∃ a ∈ p, CMvMonomial.toFinsupp a = CMvMonomial.toFinsupp m := by aesop
      obtain ⟨rfl⟩ : m = m' := by injection h₃ with _ h₄
                                  ext x hx
                                  apply congr_fun (a := ⟨x, hx⟩) at h₄
                                  aesop (add simp Vector.get)
      simp [CMvMonomial.ofFinsupp_toFinsupp, show m ∈ p.1 from h₂] at contra
      exact absurd (show (p.1)[m]? = .some 0 by grind)
                   Lawful.getElem?_ne_some_zero
    · suffices ∃ m ∈ p.1, CMvMonomial.toFinsupp m = a by aesop
      use CMvMonomial.ofFinsupp a
      grind
  Finsupp.mk support.toFinset toFun (by simp [mem_support_fun])

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

@[grind=, simp]
theorem toCMvPolynomial_fromCMvPolynomial [BEq R] [LawfulBEq R] {p : CMvPolynomial n R} :
  toCMvPolynomial (fromCMvPolynomial p) = p := by
  dsimp [fromCMvPolynomial, toCMvPolynomial, toCMvPolynomial, fromCMvPolynomial]
  ext m; simp only [CMvPolynomial.coeff]; congr 1
  by_cases eq : m ∈ p.1 <;> simp [eq]
  rw [ExtTreeMap.getElem_ofList_of_mem (k := m) (k_eq := by simp)
                                       (mem := ?mem) (distinct := ?distinct)]
  case mem => simp; grind
  case distinct =>
    simp only [Std.compare_eq_iff_eq, List.pairwise_map]
    exact distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)

@[grind=, simp]
theorem fromCMvPolynomial_toCMvPolynomial [BEq R] [LawfulBEq R] {p : MvPolynomial (Fin n) R} :
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

noncomputable def polyEquiv [BEq R] [LawfulBEq R]:
  Equiv (CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toFun := fromCMvPolynomial
  invFun := toCMvPolynomial
  left_inv := fun _ ↦ toCMvPolynomial_fromCMvPolynomial
  right_inv := fun _ ↦ fromCMvPolynomial_toCMvPolynomial

#check ExtTreeMap.mergeWith
#check ExtDTreeMap.Const.mergeWith
#check DTreeMap.Const.mergeWith
#check Std.DTreeMap.Internal.Impl.Const.mergeWith
#check Std.DTreeMap.Internal.Impl.Const.mergeWith!
#check Std.DTreeMap.Internal.Impl.foldl
#check Std.DTreeMap.Internal.Impl.insertMany
-- #check ExtTreeMap.getElem
-- variable (cmp : α → α → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (m : Std.ExtTreeMap α β cmp)
-- variable (k : α)

#check Unlawful.mergeWith₀
#check Lawful.from_to_Unlawful
#check ExtTreeMap.getElem?_filter

def zero_add [BEq R] [LawfulBEq R] :
  ∀ (a : CMvPolynomial n R), Lawful.add 0 a = a
:= by
  intro a
  ext m
  unfold CMvPolynomial.coeff Lawful.add -- HAdd.hAdd
  unfold_projs
  unfold Unlawful.add Lawful.fromUnlawful
  simp only
  have bla :=
    @ExtTreeMap.getElem?_filter
      (CMvMonomial n)
      R
      _
      _
      compare
      _
      _
      (fun x c => c != 0)
      m
      (ExtTreeMap.mergeWith
        (fun x c₁ c₂ => c₁ + c₂)
        (Lawful.C (@Nat.cast R csR.toNatCast 0 : R)).1 a.1
      )
  unfold_projs at bla ⊢
  rw [bla]
  have zero_map_empty : ∀ m₀ : CMvMonomial n, m₀ ∉ (Lawful.C (0 : R)).1 := by
    intro m₀
    unfold Lawful.C Unlawful.C
    unfold_projs
    simp
  specialize zero_map_empty m
  have bal : (@Nat.cast R csR.toNatCast 0 : R) = Zero.zero := by
    simp only [Nat.cast_zero]
    unfold_projs
    rfl
  by_cases m_in_a : m ∈ (a.1 : Unlawful n R)
  · have :=
      @Unlawful.mergeWith₂
        n
        R
        m
        (fun x c₁ c₂ => Add.add c₁ c₂)
        (@Subtype.val (Unlawful n R) (fun p => p.isNoZeroCoef) (Lawful.C ↑0) : Unlawful n R)
        a.1
        zero_map_empty
        m_in_a
    unfold_projs at this ⊢
    rw [bal, this]
    have no_0 := a.2
    match blue : ExtTreeMap.get? a.1 m with
    | .none => simp
    | .some v =>
      by_cases v_is_0 : v = Zero.zero
      · rw [v_is_0] at blue
        unfold Unlawful.isNoZeroCoef at no_0
        exfalso
        apply no_0 m
        exact blue
      · rw [Option.filter_some]
        simp [v_is_0]
  · have :=
      @Unlawful.mergeWith₃
        n
        R
        m
        (fun x c₁ c₂ => Add.add c₁ c₂)
        (@Subtype.val (Unlawful n R) (fun p => p.isNoZeroCoef) (Lawful.C ↑0) : Unlawful n R)
        a.1
        zero_map_empty
        m_in_a
    unfold_projs at this ⊢
    rw [bal, this]
    simp only [Option.filter_none, Option.getD_none, ExtTreeMap.get?_eq_getElem?]
    have blue := Std.ExtTreeMap.getElem?_eq_none m_in_a
    unfold_projs at blue ⊢
    rw [blue]
    simp

def add_zero [BEq R] [LawfulBEq R] : ∀ (a : CMvPolynomial n R), Lawful.add a 0 = a := by
  intro a
  simp
    [ OfNat.ofNat
    , Lawful.add
    ]
  unfold_projs
  simp
    [ Unlawful.add
    , ExtTreeMap.mergeWith
    , ExtDTreeMap.Const.mergeWith
    , DTreeMap.Const.mergeWith
    , DTreeMap.Internal.Impl.Const.mergeWith
    ]
  unfold_projs
  dsimp
  -- aesop
  sorry

instance {n : ℕ} [BEq R] [LawfulBEq R] :
  CommSemiring (CPoly.CMvPolynomial n R)
where
  add := Lawful.add
  add_assoc := sorry
  zero := 0
  zero_add := zero_add
  add_zero := sorry
  nsmul n p := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := sorry
  mul := Lawful.mul
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := 1
  one_mul := sorry
  mul_one := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  npow := sorry
  npow_zero := sorry
  npow_succ := sorry
  mul_comm := sorry


/-
We needed a `Zero` instance for the coefficients' type in `CommSemiring` because
`Lawful.add` requires it.
-/

-- def polyRingHom [BEq R] [LawfulBEq R] :
--   RingHom (CPoly.CMvPolynomial n R) (MvPolynomial (Fin n) R) where
--     toFun := fromCMvPolynomial
--     map_one' := sorry
--     map_mul' := sorry
--     map_zero' := sorry
--     map_add' := sorry

noncomputable def polyRingEquiv [BEq R] [LawfulBEq R] :
  RingEquiv (CPoly.CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toEquiv := CPoly.polyEquiv
  map_mul' := sorry
  map_add' := sorry

end

end CPoly
