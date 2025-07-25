import CMvPolynomial.CMvPolynomial
import CMvPolynomial.Wheels
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib

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

#check Lawful.from_to_Unlawful
#check ExtTreeMap.getElem?_filter

lemma Unlawful.mem_add {m : CMvMonomial n} {p₁ p₂ : Unlawful n R} :
  m ∈ p₁ + p₂ ↔ m ∈ p₁ ∨ m ∈ p₂ := by
  simp [(·+·), Add.add, Unlawful.add]
  grind

attribute [grind =] Option.filter_eq_some_iff

lemma zero_add [BEq R] [LawfulBEq R] {p : CMvPolynomial n R} : 0 + p = p := by
  dsimp only [(·+·), Add.add, Lawful.add, Lawful.fromUnlawful, Unlawful.add]
  grind

lemma add_zero [BEq R] [LawfulBEq R] {p : CMvPolynomial n R} : p + 0 = p := by
  dsimp only [(·+·), Add.add, Lawful.add, Lawful.fromUnlawful, Unlawful.add]
  grind

attribute [grind=] Option.some_inj

lemma ring_trivial_of_zero_eq_one : 1 = (0 : R) → ∀ a : R, a = 0 := by
  intros h a
  have h' := one_mul a
  rw [h, zero_mul] at h'
  exact h'.symm

lemma all_polys_eq_zero_of_1_eq_0 {n : ℕ} [BEq R] [LawfulBEq R] : 1 = (0 : R) → ∀ p : CMvPolynomial n R,  p = 0 := by
  intros h p
  have h := ring_trivial_of_zero_eq_one h
  unfold_projs
  unfold Lawful.C Unlawful.C
  unfold_projs
  simp only [Unlawful.zero_eq_zero, ↓reduceIte]
  rcases p with ⟨p, ph⟩
  congr
  ext m a
  have h' := @Std.ExtTreeMap.getElem?_empty (CMvMonomial n) R compare _ m
  unfold Unlawful.isNoZeroCoef at ph
  unfold_projs at h' ph ⊢
  rw [h']
  simp only [reduceCtorEq, iff_false, ne_eq]
  intros h''
  specialize ph m
  rw [h''] at ph
  apply ph
  simp only [Unlawful.zero_eq_zero, Option.some.injEq]
  exact h a

instance : LawfulEqCmp fun (x : ℕ) y => compareOfLessAndEq x y where
  eq_of_compare := by
    intros a b
    unfold compareOfLessAndEq
    aesop
  compare_self := by
    intros a
    unfold compareOfLessAndEq
    aesop

instance {n : ℕ} [BEq R] [LawfulBEq R] :
  CommSemiring (CPoly.CMvPolynomial n R)
where
  add := Lawful.add
  add_assoc := by
    intros p q r
    unfold_projs
    unfold Lawful.add
    unfold_projs
    unfold Unlawful.add
    congr 1
    ext m a
    by_cases h : m ∈ p.1 <;> by_cases h' : m ∈ q.1 <;> by_cases h'' : m ∈ r.1 <;> sorry
  zero := 0
  zero_add := fun _ ↦ zero_add
  add_zero := fun _ ↦ add_zero
  nsmul n p := List.foldl (.+.) 0 (List.replicate n p) -- `(List.replicate n p).sum` might be better
                                                       -- there's things like `List.sum_replciate`
                                                       -- admittedly this wants a monoid which we're
                                                       -- in the process of defining, eh...
  nsmul_zero := by simp
  nsmul_succ {m x} := by
    generalize (0 : CMvPolynomial n R) = y
    induction m generalizing y with
    | zero => simp
    | succ n ih => specialize ih (y + x); grind
  add_comm := by
    intros p q
    unfold_projs
    unfold Lawful.add
    unfold_projs
    unfold Unlawful.add
    congr 1
    ext1 m -- dont extensionality-ise too much, no lemmas for = some, but lemmas for [x]?
    grind -- attribute [grind=] Option.some_inj
  mul := Lawful.mul
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := by
    intros p
    unfold_projs
    unfold Lawful.mul
    unfold_projs
    unfold Unlawful.mul
    grind -- `fromUnlawful_zero`, `grind_pattern zero_eq_empty`
  mul_zero := by
    intro p
    unfold_projs
    unfold Lawful.mul
    unfold_projs
    unfold Unlawful.mul Lawful.C
    simp
    have sum_zeros {size : ℕ} :
      List.sum (α := Unlawful n R) (List.replicate size 0) = 0
    := by
      induction' size with s' ih
      · grind
      · simp [List.replicate, ih]
        unfold_projs
        simp [Unlawful.add]
        ext m k
        grind
    rw [sum_zeros]
    grind
  mul_assoc := sorry
  one := 1
  one_mul := by
    intros a
    by_cases h : (1 : R) = 0
    · rw [all_polys_eq_zero_of_1_eq_0 h (1 * a), all_polys_eq_zero_of_1_eq_0 h a]
    · dsimp only [(·*·), Mul.mul, Lawful.mul, Lawful.fromUnlawful, Unlawful.mul₀, Unlawful.mul]
      unfold_projs
      unfold Lawful.C Unlawful.C MonoR.C
      have : @ExtTreeMap.toList (CMvMonomial n) R (Vector.compareLex fun x y => compareOfLessAndEq x y) Vector.instTransOrd (ExtTreeMap.ofList [(CMvMonomial.one, 1)] compare) = [(CMvMonomial.one, 1)] := by rfl
      simp only [Unlawful.zero_eq_zero, Nat.cast_one, Nat.cast_one, h, ↓reduceIte, this, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      unfold CMvMonomial.mul
      have : List.map (fun (x : CMvMonomial n × R) => (Vector.zipWith Nat.add CMvMonomial.one x.1, Mul.mul 1 x.2)) = id := by
        rw [←List.map_id_fun]
        apply congrArg List.map
        funext ⟨m, a⟩
        have : Mul.mul 1 a = 1 * a := by rfl
        unfold CMvMonomial.one
        aesop
      simp only [this, id_eq]
      rcases a with ⟨a, h⟩
      simp only
      congr
      have : @ExtTreeMap.ofList (CMvMonomial n) R (@ExtTreeMap.toList (CMvMonomial n) R (Vector.compareLex fun x y => compareOfLessAndEq x y) Vector.instTransOrd a) (Vector.compareLex fun x y => compareOfLessAndEq x y) = a := by
        haveI : TransCmp fun (x : ℕ) y => compareOfLessAndEq x y := by
          apply Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff <;> grind
        exact @ExtTreeMap.toList_ofList (CMvMonomial n) R _ _ (Vector.compareLex fun x y => compareOfLessAndEq x y) inferInstance inferInstance a
      rw [this]
      unfold_projs
      unfold Unlawful.add Unlawful.C
      simp only [Unlawful.zero_eq_zero, ↓reduceIte, ExtTreeMap.empty_eq_emptyc, ExtTreeMap.mergeWith_empty]
      apply Std.ExtTreeMap.ext_getElem? (cmp := compare)
      intro k
      by_cases h' : k ∈ a
      · specialize h k
        rw [ExtTreeMap.filter_mem (f := (fun x c => c != 0)) h'] <;> grind
      · have := @ExtTreeMap.filter_not_mem (CMvMonomial n) R _ _ compare _ _ k (fun x c => c != 0) a h'
        rw [this]
        simp [h']
  mul_one := by
    -- intros a
    -- unfold_projs
    -- unfold Lawful.C Unlawful.C Lawful.mul
    -- split_ifs with h
    -- · simp at h
    --   have h := @all_polys_eq_zero_of_1_eq_0 R _ n _ _ h
    --   rw (occs := .pos [2]) [h a]
    --   simp only [ExtTreeMap.empty_eq_emptyc]
    --   rw [h (Lawful.fromUnlawful (a.1 * ∅))]
    -- · simp only [Nat.cast_one]
    --   unfold_projs
    --   unfold Unlawful.mul


      sorry
  natCast := fun n => Lawful.C n
  natCast_zero := by
    unfold Lawful.C Unlawful.C
    unfold_projs
    simp only [Nat.cast_zero, Unlawful.zero_eq_zero, ↓reduceIte, Lawful.C_zero]
    unfold_projs
    unfold Lawful.C Unlawful.C
    unfold_projs
    simp
  natCast_succ := sorry
  npow := Lawful.npow
  npow_zero := by intros x; rfl
  npow_succ := by intros e p; rfl
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
