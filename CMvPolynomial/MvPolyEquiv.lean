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

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

def fromCMvPolynomial  (p : CMvPolynomial n R) : MvPolynomial (Fin n) R :=
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

lemma fromCMvPolynomial_injective : Function.Injective (@fromCMvPolynomial n R _ _ _) := by
  rw [Function.injective_iff_hasLeftInverse]
  exists toCMvPolynomial
  apply toCMvPolynomial_fromCMvPolynomial

lemma coeff_eq {m} (a : CMvPolynomial n R) : MvPolynomial.coeff m (fromCMvPolynomial a) = a.coeff (CMvMonomial.ofFinsupp m) := by
  aesop

lemma filter_get {R : Type} [BEq R] [LawfulBEq R] {v : R} {m : CMvMonomial n} (a : Unlawful n R) :
    (ExtTreeMap.filter (fun _ c => c != v) a)[m]?.getD v = a[m]?.getD v := by
  by_cases h : m ∈ a
  · by_cases h' : a[m] = v
    · erw [ExtTreeMap.filter_not_pred h (by simp [h'])]
      have : a[m]? = .some v := by
        aesop
      rw [this]
      simp
    · erw [ExtTreeMap.filter_mem h (by simp [h'])]
      have : a[m]?.getD v = a[m] := by
        have : a[m]? = some a[m] := by
          simp [h]
        rw [this]
        simp
      rw [this]
      simp
  · simp [h, ExtTreeMap.filter_not_mem h]

@[aesop simp]
lemma eq_iff_fromCMvPolynomial {u v: CMvPolynomial n R} :
    u = v ↔ fromCMvPolynomial u = fromCMvPolynomial v := by
  apply Iff.intro
  · intros h; rw [h]
  · apply fromCMvPolynomial_injective

@[simp]
lemma map_add (a b : CMvPolynomial n R) :
  fromCMvPolynomial (a + b) = fromCMvPolynomial a + fromCMvPolynomial b
:= by
  ext m
  rw [MvPolynomial.coeff_add, coeff_eq, coeff_eq, coeff_eq]
  unfold CMvPolynomial.coeff
  unfold_projs
  unfold CPoly.Lawful.add
  simp only [ExtTreeMap.get?_eq_getElem?, Unlawful.zero_eq_zero]
  unfold_projs
  unfold Unlawful.add Lawful.fromUnlawful
  simp only [ExtTreeMap.get?_eq_getElem?, Unlawful.zero_eq_zero]
  erw [filter_get]
  by_cases h : (CMvMonomial.ofFinsupp m) ∈ a.1 <;> by_cases h' : (CMvMonomial.ofFinsupp m) ∈ b.1
  · rw [ExtTreeMap.mergeWith₀ h h', Option.getD_some]
    have h₁ : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) = (a.1)[CMvMonomial.ofFinsupp m] := by simp [h]
    have h₂ : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) = (b.1)[CMvMonomial.ofFinsupp m] := by simp [h']
    erw [h₁, h₂]
    rfl
  · rw [ExtTreeMap.mergeWith₁ h h']
    have : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h']
    erw [this]
    have {x : R} : x + 0 = x := by simp
    specialize @this ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0)
    unfold_projs at this
    erw [this]
    rfl
  · rw [ExtTreeMap.mergeWith₂ h h']
    have : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h]
    erw [this]
    have {x : R} : 0 + x = x := by simp
    specialize @this ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0)
    unfold_projs at this
    erw [this]
    rfl
  · rw [ExtTreeMap.mergeWith₃ h h']
    have h₁ : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h]
    have h₂ : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h']
    erw [h₁, h₂, Option.getD_none]
    have : 0 + 0 = (0 : R) := by simp
    unfold_projs at this
    erw [this]
    rfl

-- def Unlawful.toMvPoly (p : Unlawful n R) : (Fin n →₀ ℕ) →₀ R :=
--   let support : List (Fin n →₀ ℕ) :=
--     (p.monomials.filter (fun x ↦ p[x]? != some 0)).map CMvMonomial.toFinsupp
--   let toFun (f : Fin n →₀ ℕ) : R := p[CMvMonomial.ofFinsupp f]?.getD 0
--   let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by
--     dsimp [toFun, support]
--     refine ⟨fun _ _ ↦ ?p₁, fun _ ↦ ?p₂⟩
--     · grind
--     · suffices ∃ m ∈ p, CMvMonomial.toFinsupp m = a by grind
--       grind
--   Finsupp.mk support.toFinset toFun (by simp [mem_support_fun])

@[simp]
lemma map_zero : fromCMvPolynomial (0 : CMvPolynomial n R) = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  unfold fromCMvPolynomial
  simp only [Lawful.getElem?_eq_val_getElem?, Lawful.mem_iff_cast, Lawful.not_mem_zero,
    not_false_eq_true, getElem?_neg, Option.getD_none]
  rfl

@[simp]
lemma map_one : fromCMvPolynomial (1 : CMvPolynomial n R) = 1 := by
  ext m
  have : MvPolynomial.coeff m 1 = if m = 0 then 1 else (0 : R) := by
    unfold MvPolynomial.coeff
    unfold_projs
    simp only [Nat.zero_eq, Unlawful.zero_eq_zero]
    split_ifs with h
    · rw [h]
      unfold AddMonoidAlgebra.single Finsupp.toFun Finsupp.single Pi.single Function.update
      dsimp
      simp
    · unfold AddMonoidAlgebra.single Finsupp.toFun Finsupp.single Pi.single Function.update
      dsimp
      simp [h]
  rw [this]
  unfold fromCMvPolynomial
  unfold MvPolynomial.coeff
  simp only [Lawful.getElem?_eq_val_getElem?, Finsupp.coe_mk]
  unfold_projs
  unfold Lawful.C Unlawful.C MonoR.C
  simp only [Nat.cast_one, ExtTreeMap.empty_eq_emptyc, ExtTreeMap.ofList_singleton,
    ExtTreeMap.get?_eq_getElem?, Unlawful.zero_eq_zero, Nat.zero_eq]
  have triv_lem : (1 : R) = 0 → ∀ x y : R, x = y := by
    intros h
    have (x : R) : x = 0 := by
      have : x * 1 = x * 0 := by
        rw [h]
      simp only [mul_one, mul_zero] at this
      exact this
    intros x y; rw [this x, this y]
  split_ifs with g g' g'
  · rw [Nat.cast_one] at g; apply triv_lem g
  · rw [Nat.cast_one] at g; apply triv_lem g
  · have : CMvMonomial.ofFinsupp m = CMvMonomial.one := by
      rw [g']
      unfold CMvMonomial.ofFinsupp CMvMonomial.one
      ext i h
      simp
    rw [this]
    have h := @Std.ExtTreeMap.getElem?_insert (CMvMonomial n) R compare ∅ _ CMvMonomial.one CMvMonomial.one 1
    simp only [compare_self, ↓reduceIte] at h
    have : ((∅ : ExtTreeMap (CMvMonomial n) R compare).insert CMvMonomial.one 1)[(CMvMonomial.one : CMvMonomial n)]?.getD 0 = One.one := by
      rw [h]
      simp
      rfl
    convert this
  · have : CMvMonomial.ofFinsupp m ≠ CMvMonomial.one := by
      unfold CMvMonomial.ofFinsupp CMvMonomial.one
      intros h
      have {i} : (Vector.ofFn m).get i = (Vector.replicate n 0).get i := by
        rw [h]
      apply g'
      ext i
      simp only [Finsupp.coe_mk]
      specialize @this i
      simp only [Vector.get_ofFn, Vector.get_replicate] at this
      exact this
    have h := @Std.ExtTreeMap.getElem?_insert (CMvMonomial n) R compare ∅ _ (CMvMonomial.ofFinsupp m) CMvMonomial.one 1
    simp only [Std.compare_eq_iff_eq, this.symm, ExtTreeMap.not_mem_empty, not_false_eq_true, getElem?_neg, ↓reduceIte] at h
    have h : ((∅ : ExtTreeMap (CMvMonomial n) R compare).insert CMvMonomial.one 1)[CMvMonomial.ofFinsupp m]?.getD 0 = 0 := by
      rw [h]
      simp
    convert h

noncomputable def polyEquiv:
  Equiv (CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toFun := fromCMvPolynomial
  invFun := toCMvPolynomial
  left_inv := fun _ ↦ toCMvPolynomial_fromCMvPolynomial
  right_inv := fun _ ↦ fromCMvPolynomial_toCMvPolynomial

attribute [local grind=] Unlawful.add Lawful.add Unlawful.mul Lawful.mul

instance {n : ℕ} : AddCommSemigroup (CPoly.CMvPolynomial n R) where
  add_assoc := by aesop (add safe apply add_assoc)
  add_comm := by grind

instance {n : ℕ} : AddMonoid (CPoly.CMvPolynomial n R) where
  zero_add _ := by aesop
  add_zero _ := by aesop
  nsmul n p := (List.replicate n p).sum
  nsmul_succ {m x} := by grind -- `nsmul` def changed + `add_comm` is now available; `grind`!

instance {n : ℕ} : AddCommMonoid (CPoly.CMvPolynomial n R) where
  toAddMonoid := inferInstance
  add_comm := by grind

omit [CommSemiring R] in
lemma ofList_toList {terms : List (MonoR n R)} :
  List.Pairwise (fun a b ↦ ¬compare a.1 b.1 = Ordering.eq) terms →
  ExtTreeMap.toList (ExtTreeMap.ofList terms compare) = terms
:= by
  intro distinct
  induction' terms with t ts ih
  · simp
  · simp only [List.pairwise_cons, Prod.forall] at distinct
    -- rw [ExtTreeMap.ofList_cons]
    specialize ih distinct.2
    nth_rw 2 [←ih]
    -- revert ts
    -- induction' ts with t' ts' ih'
    -- · rw [ofList_toList_empty, ofList_toList_MonoR]
    -- · simp
    sorry

lemma mul_getD?₀ {m : Fin n →₀ ℕ} {p q : MvPolynomial (Fin n) R} :
  (p * q).coeff m = c ↔
  ∃ lms : List ((Fin n →₀ ℕ) × (Fin n →₀ ℕ)),
    lms.foldr (fun (m₁, m₂) acc ↦ p.coeff m₁ * q.coeff m₂ + acc) 0 = c ∧
    ∀ m₁ m₂ c₁ c₂,
      p.coeff m₁ = c₁ ∧ q.coeff m₂ = c₂ ∧ m₁ * m₂ = m ∧ c₁ * c₂ ≠ 0 ↔ (m₁, m₂) ∈ lms
:= by
  sorry

lemma mul_getD? {m : CMvMonomial n} {p q : CMvPolynomial n R} :
  coeff m (p * q) = c ↔
  ∃ lms : List (CMvMonomial n × CMvMonomial n),
    lms.foldr (fun (m₁, m₂) acc ↦ coeff m₁ p * coeff m₂ q + acc) 0 = c ∧
    ∀ m₁ m₂ c₁ c₂,
      coeff m₁ p = c₁ ∧ coeff m₂ q = c₂ ∧ m₁ * m₂ = m ∧ c₁ * c₂ ≠ 0 ↔
      (m₁, m₂) ∈ lms
:= by
  rw [HMul.hMul, instHMul, Mul.mul, Lawful.instMulOfAdd]; dsimp
  simp only [Lawful.mul, Lawful.fromUnlawful];
  rw [HMul.hMul, instHMul, Mul.mul, Unlawful.instMulOfLawfulBEqOfAddOfZero]; dsimp
  -- rw [Unlawful.mul]
  -- rw [ExtTreeMap.getElem?_filter]


  -- have sum_list_getD? :
  --   p.val[m]?.getD 0 =
  --     List.sum (p.val.toList.map (fun t ↦ ({t} : Unlawful n R)[m]?.getD 0))
  -- := by
  --   generalize terms_def : ExtTreeMap.toList p.val = terms
  --   revert p
  --   induction' terms with t ts ih
  --   · intro p terms_def
  --     rw [ExtTreeMap.toList_eq_nil_iff] at terms_def
  --     simp [*]
  --   · intro p to_list_p
  --     simp
  --     have :
  --       (List.map (fun t => ((∅ : Unlawful n R).insert t.1 t.2)[m]?.getD 0) ts).sum =
  --     sorry
  sorry

lemma Option.filter_getD_0_id [BEq R] [LawfulBEq R] {o : Option R} :
  (o.filter (fun c ↦ c != 0)).getD 0 = o.getD 0
:= by
  rcases o
  case none => rfl
  case some val =>
    by_cases val_eq_0 : val = 0 <;> simp [Option.filter, val_eq_0]

lemma filter_zero_coeff {u : Unlawful n R} :
  coeff m (Lawful.fromUnlawful u) = coeff m u
:= by
  rcases o
  case none => rfl
  case some val =>
    by_cases val_eq_0 : val = 0 <;> simp [Option.filter, val_eq_0]


-- lemma Option.filter_getD_0_id [BEq R] [LawfulBEq R] {o : Option R} :
--   (o.filter (fun c ↦ c != 0)).getD 0 = o.getD 0
-- := by
--   rcases o
--   case none => rfl
--   case some val =>
--     by_cases val_eq_0 : val = 0 <;> simp [Option.filter, val_eq_0]

lemma bad_lemma_name {t : Unlawful n R}
  (f : CMvMonomial n → R → Unlawful n R) :
  Lawful.fromUnlawful (ExtTreeMap.foldl (fun x p q => (f p q) + x) 0 t) =
    ExtTreeMap.foldl (fun x p q => (Lawful.fromUnlawful (f p q)) + x) 0 (Lawful.fromUnlawful t).1
:= by
  sorry

-- lemma foldl_eq_sum [AddCommMonoid δ] {t : Unlawful n R}
--   (f : CMvMonomial n → R → δ) :
--   ExtTreeMap.foldl (fun x p q => (f p q) + x) 0 t =
--     Finsupp.sum (toMvPoly t) (f ∘ CMvMonomial.ofFinsupp)
-- := by
--   sorry

lemma foldl_eq_sum' [AddCommMonoid δ] {t : CMvPolynomial n R}
  (f : CMvMonomial n → R → δ) :
  ExtTreeMap.foldl (fun x p q => (f p q) + x) 0 t.1 =
    Finsupp.sum (fromCMvPolynomial t) (f ∘ CMvMonomial.ofFinsupp)
:= by
  sorry

-- fromCMvPolynomial (Finsupp.sum (fromCMvPolynomial a) f) = Finsupp.sum (fromCMvPolynomial a) g
lemma abc {f : (Fin n →₀ ℕ) → R → Lawful n R } {a : MvPolynomial (Fin n) R}:
  fromCMvPolynomial (Finsupp.sum a f) =
    Finsupp.sum a g
:= by sorry

set_option pp.fieldNotation false
@[simp]
lemma map_mul (a b : CMvPolynomial n R) :
  fromCMvPolynomial (a * b) = fromCMvPolynomial a * fromCMvPolynomial b
:= by
  unfold_projs
  ext m
  congr
  -- simp only [coeff_eq]
  unfold Lawful.mul
  unfold_projs
  unfold Unlawful.mul
  simp only [bad_lemma_name]
  simp only [Lawful.fromUnlawful_cast]
  -- simp [foldl_eq_sum']
  conv =>
    lhs
    arg 1; arg 1
    -- arg 2; arg 1
    ext x p q
    rw [foldl_eq_sum' (fun p₁ q₁ ↦ Lawful.fromUnlawful {(p * p₁, q * q₁)})]
  rw [foldl_eq_sum']
  unfold MonoidAlgebra.mul'
  generalize eq₁ : (fun p q =>
          Finsupp.sum (fromCMvPolynomial b)
            ((fun p₁ q₁ => Lawful.fromUnlawful {(p * p₁, q * q₁)}) ∘ CMvMonomial.ofFinsupp)) ∘
        CMvMonomial.ofFinsupp = f
  generalize eq₂ : (fun (a₁ : Multiplicative (Fin n →₀ ℕ)) b₁ =>
    Finsupp.sum (fromCMvPolynomial b) fun (a₂ : Multiplicative (Fin n →₀ ℕ)) b₂ => MonoidAlgebra.single (a₁ * a₂) (b₁ * b₂))
      = g
  rw [eq₁.symm, eq₂.symm]

  rewrite [abc (f := f)]
  -- ext m
  -- simp only [coeff_eq]
  sorry

instance {n : ℕ} : MonoidWithZero (CPoly.CMvPolynomial n R) where
  zero_mul := by grind
  mul_zero := by aesop
  mul_assoc := by aesop (add safe apply _root_.mul_assoc)
  one_mul := by aesop
  mul_one := by aesop

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
