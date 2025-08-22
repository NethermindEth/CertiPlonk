import CMvPolynomial.CMvPolynomial
import CMvPolynomial.Wheels
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib

-- import Std.Data.DTreeMap
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

def Unlawful.toMvPoly [BEq R] [LawfulBEq R] (p : Unlawful n R) : (Fin n →₀ ℕ) →₀ R :=
  let support : List (Fin n →₀ ℕ) :=
    (p.monomials.filter (fun x ↦ p[x]? != some 0)).map CMvMonomial.toFinsupp
  let toFun (f : Fin n →₀ ℕ) : R := p[CMvMonomial.ofFinsupp f]?.getD 0
  let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by
    dsimp [toFun, support]
    refine ⟨fun _ _ ↦ ?p₁, fun _ ↦ ?p₂⟩
    · grind
    · suffices ∃ m ∈ p, CMvMonomial.toFinsupp m = a by grind
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
  by_cases eq : m ∈ p <;> simp [eq]
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

#check ExtTreeMap.getElem?_filter

lemma Unlawful.mem_add {m : CMvMonomial n} {p₁ p₂ : Unlawful n R} :
  m ∈ p₁ + p₂ ↔ m ∈ p₁ ∨ m ∈ p₂ := by
  simp [(·+·), Add.add, Unlawful.add]
  grind

attribute [grind =] Option.filter_eq_some_iff

section

attribute [local grind=] Lawful.fromUnlawful

lemma eq_iff_unlawful_eq [BEq R] [LawfulBEq R] {u v: Lawful n R} :
  u = v ↔ u.1 = v.1
:= by
  rcases u; rcases v; grind

@[aesop simp]
lemma eq_iff_fromCmvPoly [BEq R] [LawfulBEq R] {u v: CMvPolynomial n R} :
  u = v ↔ fromCMvPolynomial u = fromCMvPolynomial v := by sorry

@[simp]
lemma mul_lem [BEq R] [LawfulBEq R] (a b : CMvPolynomial n R) : fromCMvPolynomial (a * b) = (fromCMvPolynomial a) * (fromCMvPolynomial b) := by

  sorry

@[simp]
lemma add_lem [BEq R] [LawfulBEq R]  (a b : CMvPolynomial n R) : fromCMvPolynomial (a + b) = fromCMvPolynomial a + fromCMvPolynomial b := by
  sorry

@[simp]
lemma zero_lem [BEq R] [LawfulBEq R] : fromCMvPolynomial (0 : Lawful n R) = 0 := by
  sorry

@[simp]
lemma one_lem [BEq R] [LawfulBEq R] : fromCMvPolynomial (1 : Lawful n R) = 1 := by
  sorry

lemma bla [BEq R] [LawfulBEq R] {u : Unlawful n R} :
  (Lawful.fromUnlawful u).1.toMvPoly = u.toMvPoly
:= by sorry
  -- unfold Lawful.fromUnlawful Unlawful.toMvPoly
  -- simp
  -- constructor
  -- · ext x
  --   simp
  --   sorry
  -- · ext x
  --   grind

#check Finsupp.zipWith

lemma merge_lemma [BEq R] [LawfulBEq R] {p q : Unlawful n R} :
  Unlawful.toMvPoly (ExtTreeMap.mergeWith (fun _ ↦ f) p q) =
    Finsupp.zipWith f h (Unlawful.toMvPoly p) (Unlawful.toMvPoly q)
:= by sorry

lemma from_empty_zero [BEq R] [LawfulBEq R] :
  Unlawful.toMvPoly (ExtTreeMap.empty : Unlawful n R) = 0
:= by
  sorry

lemma add_zero [BEq R] [LawfulBEq R] {p : CMvPolynomial n R} : p + 0 = p := by
  aesop


lemma zero_add [BEq R] [LawfulBEq R] {p : CMvPolynomial n R} : 0 + p = p := by
  aesop

end

attribute [grind=] Option.some_inj


lemma ring_trivial_of_zero_eq_one (h : 1 = (0 : R)) {a : R} : a = 0 := by
  have h' := one_mul a
  aesop

lemma all_polys_eq_zero_of_1_eq_0 {n : ℕ} [BEq R] [LawfulBEq R]
  (h : 1 = (0 : R)) {p : CMvPolynomial n R} : p = 0 := by
  have h := @ring_trivial_of_zero_eq_one (h := h)
  suffices p.1 = ∅ by grind
  ext m a
  specialize @h a
  grind

instance : LawfulEqCmp fun (x : ℕ) y => compareOfLessAndEq x y where
  eq_of_compare {a b} := by unfold compareOfLessAndEq; grind
  compare_self {a} := by unfold compareOfLessAndEq; grind

attribute [local grind=] Unlawful.add Lawful.add Unlawful.mul Lawful.mul

omit [CommSemiring R] in
lemma ofList_toList_MonoR {t : MonoR n R} :
  ExtTreeMap.toList (ExtTreeMap.ofList [t] compare) = [t]
:= by rfl

lemma mul_one [BEq R] [i : LawfulBEq R] {p : CMvPolynomial n R} : p * 1 = p := by
  aesop

lemma add_getD? [BEq R] [LawfulBEq R] {m : CMvMonomial n} {p q : CMvPolynomial n R} :
  (p + q).val[m]?.getD 0 = p.val[m]?.getD 0 + q.val[m]?.getD 0
:= by
  rw [HAdd.hAdd, instHAdd, Add.add, Lawful.instAdd]; dsimp
  simp only [Lawful.add, Lawful.fromUnlawful];
  rw [HAdd.hAdd, instHAdd, Add.add, Unlawful.instAdd]; dsimp
  rw [Unlawful.add];
  rw [ExtTreeMap.getElem?_filter]
  by_cases in_p : m ∈ p <;> by_cases in_q : m ∈ q
  · simp [ExtTreeMap.mergeWith₀ in_p in_q, Option.filter]
    by_cases sum_0 : p.val[m] + q.val[m] != 0
      <;> simp [sum_0]
      <;> by_cases pm_0 : p.val[m] = 0 <;> by_cases qm_0 : q.val[m] = 0
      <;> grind [add_comm]
  · simp [ExtTreeMap.mergeWith₁ in_p in_q]
    by_cases p.val[m] = 0
    · grind
    · unfold_projs at in_p; simp at in_p
      rw [ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at in_p
      rcases in_p with ⟨c₁, in_p⟩
      simp [Option.filter, in_p]
      by_cases c₁_eq_0 : c₁ = 0 <;> simp [c₁_eq_0, in_q]
  · simp [ExtTreeMap.mergeWith₂ in_p in_q]
    by_cases q.val[m] = 0
    · grind
    · unfold_projs at in_q; simp at in_q
      rw [ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at in_q
      rcases in_q with ⟨c₁, in_q⟩
      simp [Option.filter, in_q]
      by_cases c₁_eq_0 : c₁ = 0 <;> simp [c₁_eq_0, in_p]
  · simp [ExtTreeMap.mergeWith₃ in_p in_q]
    unfold_projs at in_p; simp at in_p
    unfold_projs at in_q; simp at in_q
    aesop


lemma left_distrib [BEq R] [LawfulBEq R] : ∀ {p q r : CMvPolynomial n R},
  (p + q) * r = p * r + q * r
:= by aesop
  -- ext m
  -- rw [add_getD?']
  -- simp [mul_sum]
  -- trans
  --   ∑ mᵢ ∈ filter_monomials m (p + q) r,
  --     (coeff mᵢ p * coeff (m / mᵢ) r + coeff mᵢ q * coeff (m / mᵢ) r)
  -- · congr
  --   ext a
  --   simp [add_getD?', right_distrib]
  -- · rw [Finset.sum_add_distrib]
  --   -- congr 1
  --   sorry

variable [BEq R] [LawfulBEq R]

instance {n : ℕ} [BEq R] [LawfulBEq R] :
  AddCommSemigroup (CPoly.CMvPolynomial n R) where
    add_assoc := by
      intro a b c
      ext m
      unfold CMvPolynomial.coeff
      simp [add_getD?]
      rw [add_assoc]
    add_comm {p q} := by grind

instance {n : ℕ} [BEq R] [LawfulBEq R] : AddMonoid (CPoly.CMvPolynomial n R) where
  zero_add _ := zero_add -- this is just `by grind` but in a different scope
  add_zero _ := add_zero -- this is just `by grind` but in a different scope
  nsmul n p := (List.replicate n p).sum
  nsmul_succ {m x} := by grind -- `nsmul` def changed + `add_comm` is now available; `grind`!

instance {n : ℕ} [BEq R] [LawfulBEq R] : AddCommMonoid (CPoly.CMvPolynomial n R) where
  toAddMonoid := inferInstance
  add_comm := by grind

-- instance [BEq R] [LawfulBEq R] : AddCommMonoid (Lawful n R) where
--   add := Lawful.add
--   add_assoc := by
--     intro a b c
--     ext m
--     unfold CMvPolynomial.coeff
--     simp [add_getD?]
--     rw [add_assoc]
--   zero := 0
--   zero_add := zero_add
--   add_zero := _
--   nsmul := _
--   nsmul_zero := _
--   nsmul_succ := _
--   add_comm := _

lemma foldl_eq_sum [BEq R] [LawfulBEq R] [AddCommMonoid δ] {t : Unlawful n R} (f : CMvMonomial n → R → δ) :
    ExtTreeMap.foldl (fun x a b => (f a b) + x) 0 t =
      Finsupp.sum (Unlawful.toMvPoly t) (f ∘ CMvMonomial.ofFinsupp) := by
  sorry

lemma bad_lemma_name [BEq R] [LawfulBEq R] {t : Unlawful n R} (f : CMvMonomial n → R → Unlawful n R) :
    Lawful.fromUnlawful (ExtTreeMap.foldl (fun x a b => (f a b) + x) 0 t) =
      ExtTreeMap.foldl (fun x a b => (Lawful.fromUnlawful (f a b)) + x) 0 (Lawful.fromUnlawful t).1 := by
  sorry

#check Unlawful.toMvPoly

lemma mul_assoc :
  ∀ (a b c : CMvPolynomial n R), a * b * c = a * (b * c)
:= by
  aesop (add safe apply _root_.mul_assoc)

instance {n : ℕ} [BEq R] [LawfulBEq R] : MonoidWithZero (CPoly.CMvPolynomial n R) where
  zero_mul := by grind
  mul_zero := by aesop
  mul_assoc := mul_assoc
  one_mul := by aesop
  mul_one := fun _ ↦ mul_one

instance {n : ℕ} [BEq R] [LawfulBEq R] : Semiring (CPoly.CMvPolynomial n R) where
  left_distrib {p q r} := by aesop
  right_distrib {p q r} := by aesop

instance {n : ℕ} [BEq R] [LawfulBEq R] :
  CommSemiring (CPoly.CMvPolynomial n R) where
    natCast_zero := by grind
    natCast_succ := by intro n; simp
    npow_zero := by intro x; simp [npowRecAuto, npowRec]
    npow_succ := by intro n x; simp [npowRecAuto, npowRec]
    mul_comm := by aesop (add safe apply _root_.mul_comm)


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
