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

lemma eq_iff_fromCMvPolynomial [BEq R] [LawfulBEq R] {u₁ u₂: Unlawful n R} :
  u₁ = u₂ ↔ u₁.toMvPoly = u₂.toMvPoly
:= by
  sorry

#check Finsupp.zipWith

lemma merge_lemma [BEq R] [LawfulBEq R] {p q : Unlawful n R} :
  Unlawful.toMvPoly (ExtTreeMap.mergeWith (fun _ ↦ f) p q) =
    Finsupp.zipWith f h (Unlawful.toMvPoly p) (Unlawful.toMvPoly q)
:= by sorry

lemma abc [BEq R] [LawfulBEq R] {u v: Lawful n R} :
  u = v ↔ u.1 = v.1
:= by
  rcases u; rcases v; grind

lemma from_empty_zero [BEq R] [LawfulBEq R] :
  Unlawful.toMvPoly (ExtTreeMap.empty : Unlawful n R) = 0
:= by
  sorry

lemma add_zero [BEq R] [LawfulBEq R] {p : CMvPolynomial n R} : p + 0 = p := by
  unfold_projs
  unfold Lawful.add Lawful.C Unlawful.C MonoR.C
  dsimp
  simp_rw [if_pos]
  unfold_projs
  unfold Unlawful.add

  rw [abc]
  -- rcases p with ⟨p', _⟩
  rw [eq_iff_fromCMvPolynomial]
  rw [bla]
  rw [merge_lemma]
  rw [from_empty_zero]
  apply _root_.add_zero
  rw [_root_.add_zero]

#synth Add (MvPolynomial (Fin 2) R)
#synth Distrib (MvPolynomial (Fin 2) R)
#synth NonUnitalNonAssocSemiring (MvPolynomial (Fin 2) R)


lemma zero_add [BEq R] [LawfulBEq R] {p : CMvPolynomial n R} : 0 + p = p := by
  grind

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
  by_cases eq_1_0 : (1 : R) = 0
  · rw
      [ all_polys_eq_zero_of_1_eq_0 eq_1_0 (p := p * 1),
        all_polys_eq_zero_of_1_eq_0 eq_1_0 (p := p)
      ]
  · rw [Lawful.grind_mul_skip]
    unfold_projs
    simp only [Lawful.C, Nat.cast_one]
    have list_MonoR_map_Unlawful [BEq R] [LawfulBEq R] {terms : List (MonoR n R)}:
      List.map (fun t ↦ Unlawful.mul₀ t (Unlawful.C 1)) terms
        = terms.map (fun t ↦ ({t} : Unlawful n R))
    := by
      simp only [ExtTreeMap.singleton_eq_insert]
      induction' terms with t ts ih
      · simp
      · simp at ih ⊢
        constructor
        · simp [Unlawful.mul₀, Unlawful.C, eq_1_0, ofList_toList_MonoR]
          simp [MonoR.C, CMvMonomial.mul_one]
        · intros; grind
    rw [list_MonoR_map_Unlawful]
    generalize terms_def : ExtTreeMap.toList p.val = terms
    have terms_distinct := ExtTreeMap.distinct_keys_toList (t := p.val)
    rw [terms_def] at terms_distinct
    have sum_id [BEq R] [LawfulBEq R] {terms : List (MonoR n R)} :
      List.Pairwise (fun a b ↦ ¬compare a.1 b.1 = Ordering.eq) terms →
      (List.map (fun t ↦ {t}) terms).sum = ExtTreeMap.ofList terms
    := by
      intro terms_distinct
      induction' terms with t ts ih
      · grind
      · have ts_distinct := (List.pairwise_cons.1 terms_distinct).2
        specialize ih ts_distinct
        simp only [List.sum, List.map_cons, List.foldr_cons] at ih ⊢
        rw [ih]
        rcases t with ⟨m, c⟩
        have distinct₀ := terms_distinct
        simp at terms_distinct
        ext m' c'
        simp only [HAdd.hAdd, Add.add, Unlawful.add]
        dsimp
        by_cases m_eq : m = m'
        · subst m_eq
          have in₁ : m ∈ (∅ : Unlawful n R).insert m c := by simp
          have in₂ : m ∉ ExtTreeMap.ofList ts compare := by grind
          rw
            [ ExtTreeMap.mergeWith₁ in₁ in₂,
              ExtTreeMap.getElem?_ofList_of_mem (k := m) (v := c) (by simp) distinct₀ (by simp)
            ]
          simp
        · by_cases ex_coeff : ∃ coeff, (m', coeff) ∈ ts
          · rcases ex_coeff with ⟨coeff, m'coeff_in⟩
            have in₁ : m' ∉ (∅ : Unlawful n R).insert m c := by grind
            have in₂ : m' ∈ ExtTreeMap.ofList ts compare := by grind
            rw
              [ ExtTreeMap.mergeWith₂ in₁ in₂,
                ExtTreeMap.getElem?_ofList_of_mem (by simp) ts_distinct m'coeff_in,
                ExtTreeMap.getElem?_ofList_of_mem (k := m') (v := coeff) (by simp) distinct₀ (by grind)
              ]
          · have in₁ : m' ∉ (∅ : Unlawful n R).insert m c := by grind
            have in₂ : m' ∉ ExtTreeMap.ofList ts compare := by grind
            rw [ExtTreeMap.mergeWith₃ in₁ in₂]
            grind
    rw [sum_id terms_distinct]
    grind

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
:= by
  intro p q r
  rw [Lawful.grind_mul_skip, Lawful.grind_mul_skip, Lawful.grind_mul_skip]
  sorry
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

lemma foldl_eq_sum [BEq R] [LawfulBEq R] [AddCommMonoid δ] {t : Unlawful n R} (f : CMvMonomial n → R → δ) :
    ExtTreeMap.foldl (fun x a b => (f a b) + x) 0 t =
      Finsupp.sum (Unlawful.toMvPoly t) (f ∘ CMvMonomial.ofFinsupp) := by
  sorry

lemma bad_lemma_name [BEq R] [LawfulBEq R] {t : Unlawful n R} (f : CMvMonomial n → R → Unlawful n R) :
    Lawful.fromUnlawful (ExtTreeMap.foldl (fun x a b => (f a b) + x) 0 t) =
      ExtTreeMap.foldl (fun x a b => (Lawful.fromUnlawful (f a b)) + x) 0 (Lawful.fromUnlawful t).1 := by
  sorry

lemma mul_assoc [BEq R] [LawfulBEq R] [AddCommMonoid (Lawful n R)]:
  ∀ (a b c : CMvPolynomial n R), a * b * c = a * (b * c)
:= by
  intro a b c
  unfold_projs
  simp [Lawful.mul]
  unfold_projs
  dsimp [Unlawful.mul]
  simp only [bad_lemma_name, Lawful.fromUnlawful_cast]

  -- generalize eq' : (_ : Lawful n R → CMvMonomial n → R → Lawful n R) = f

  have bla := @foldl_eq_sum n R _ (Lawful n R) _ _ _
  simp [bla]
  conv =>
    lhs
    arg 1
    ext a b c
    arg 1
    simp [foldl_eq_sum]




    -- (fun b c_1 => ExtTreeMap.foldl (fun x a b_1 => Lawful.fromUnlawful ((∅ : ExtTreeMap (CMvMonomial n) R compare).insert (b * a) (c_1 * b_1)) + x) 0 c.1)


  -- convert bla


  -- conv =>
  --   lhs
  --   arg 1
  --   ext a b c
  --   arg 1
  --   rw [@foldl_eq_sum n R _ (Lawful n R) _ _ sorry _ (fun f b c)]

  -- have bla := @foldl_eq_sum n R _ (Lawful n R) _ _ sorry _ (f b c)

  -- rw [bla]

  -- set abc' := Lawful.fromUnlawful (R := R) (ExtTreeMap.foldl (cmp := Ord.compare (α := CMvMonomial n)) _ _ c.1) with eq'



  -- have bla := @foldl_eq_sum n R _ (Unlawful n R) _ _ _
  -- unfold Unlawful.mul₀
  -- dsimp
  sorry

#exit

instance {n : ℕ} [BEq R] [LawfulBEq R] : MonoidWithZero (CPoly.CMvPolynomial n R) where
  zero_mul := by grind
  mul_zero := by
    intro p
    -- have := List.sum_replicate (ExtTreeMap.size p.1) (0 : Lawful n R) -- Mmmmm. Will grind.
    have sum_zeros : List.sum (List.replicate (ExtTreeMap.size p.1) (0 : Unlawful n R)) = 0 := by
      generalize ExtTreeMap.size p.1 = n
      induction n <;> grind
    rw [Lawful.grind_mul_skip]
    unfold_projs
    unfold Lawful.C
    simp; grind
  mul_assoc := sorry
  one_mul := by
    intros a
    by_cases h : (1 : R) = 0
    · rw [all_polys_eq_zero_of_1_eq_0 h (p := (1 * a)), all_polys_eq_zero_of_1_eq_0 h (p := a)]
    · rw [Lawful.grind_mul_skip]
      dsimp only [Unlawful.mul₀, Unlawful.mul]
      unfold_projs
      unfold Lawful.C Unlawful.C MonoR.C
      simp only [Unlawful.zero_eq_zero, Nat.cast_one, Nat.cast_one, h, ↓reduceIte]
      simp only [ofList_toList_MonoR, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      unfold CMvMonomial.mul
      have :
        List.map (fun (x : CMvMonomial n × R) => (Vector.zipWith Nat.add CMvMonomial.one x.1, Mul.mul 1 x.2)) = id
      := by
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
      have :
        @ExtTreeMap.ofList (CMvMonomial n) R
          (@ExtTreeMap.toList (CMvMonomial n) R (Vector.compareLex fun x y => compareOfLessAndEq x y) Vector.instTransOrd a)
          (Vector.compareLex fun x y => compareOfLessAndEq x y) = a
      := by
        haveI : TransCmp fun (x : ℕ) y => compareOfLessAndEq x y := by
          apply Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff <;> grind
        exact
          @ExtTreeMap.toList_ofList (CMvMonomial n) R _ _
            (Vector.compareLex fun x y => compareOfLessAndEq x y)
            inferInstance
            inferInstance
            a
      rw [this]
      unfold_projs
      unfold Unlawful.add Unlawful.C
      simp only
        [Unlawful.zero_eq_zero, ↓reduceIte, ExtTreeMap.empty_eq_emptyc, ExtTreeMap.mergeWith_empty]
      unfold Lawful.fromUnlawful
      grind
  mul_one := fun _ ↦ mul_one

instance {n : ℕ} [BEq R] [LawfulBEq R] : Semiring (CPoly.CMvPolynomial n R) where
  left_distrib {p q r} := sorry
  right_distrib {p q r} := sorry

instance {n : ℕ} [BEq R] [LawfulBEq R] :
  CommSemiring (CPoly.CMvPolynomial n R) where
    natCast_zero := by grind
    natCast_succ := by intro n; simp
    npow_zero := by intro x; simp [npowRecAuto, npowRec]
    npow_succ := by intro n x; simp [npowRecAuto, npowRec]
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
