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
  rfl

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

-- lemma filter_zero_coeff {u : Unlawful n R} :
--   coeff m (Lawful.fromUnlawful u) = coeff m u
-- := by
--   rcases o
--   case none => rfl
--   case some val =>
--     by_cases val_eq_0 : val = 0 <;> simp [Option.filter, val_eq_0]


-- lemma Option.filter_getD_0_id [BEq R] [LawfulBEq R] {o : Option R} :
--   (o.filter (fun c ↦ c != 0)).getD 0 = o.getD 0
-- := by
--   rcases o
--   case none => rfl
--   case some val =>
--     by_cases val_eq_0 : val = 0 <;> simp [Option.filter, val_eq_0]
-- #check List.fold_fil

lemma Unlawful.add_getD? {m : CMvMonomial n} {p q : Unlawful n R} :
  (p.add q)[m]?.getD 0 = p[m]?.getD 0 + q[m]?.getD 0
:= by
  rw [Unlawful.add]
  by_cases in_p : m ∈ p <;> by_cases in_q : m ∈ q
  · simp [ExtTreeMap.mergeWith₀ in_p in_q]
    by_cases sum_0 : p[m] + q[m] != 0
      <;> by_cases pm_0 : p[m] = 0 <;> by_cases qm_0 : q[m] = 0
      <;> grind [add_comm]
  · simp [ExtTreeMap.mergeWith₁ in_p in_q]
    by_cases p[m] = 0
    · aesop
    · rw [ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at in_p
      rcases in_p with ⟨c₁, in_p⟩
      simp [in_p]
      by_cases c₁_eq_0 : c₁ = 0 <;> simp [c₁_eq_0, in_q]
  · simp [ExtTreeMap.mergeWith₂ in_p in_q]
    by_cases q[m] = 0
    · aesop
    · rw [ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at in_q
      rcases in_q with ⟨c₁, in_q⟩
      simp [in_q]
      by_cases c₁_eq_0 : c₁ = 0 <;> simp [c₁_eq_0, in_p]
  · simp [ExtTreeMap.mergeWith₃ in_p in_q]
    aesop

lemma CMvPolynomial.add_getD? {m : CMvMonomial n} {p q : CMvPolynomial n R} :
  (p + q).val[m]?.getD 0 = p.val[m]?.getD 0 + q.val[m]?.getD 0
:= by
  rw [HAdd.hAdd, instHAdd, Add.add, Lawful.instAdd]; dsimp
  simp only [Lawful.add, Lawful.fromUnlawful];
  rw [HAdd.hAdd, instHAdd, Add.add, Unlawful.instAdd]; dsimp
  rw [filter_get]
  apply Unlawful.add_getD?

lemma coeff_add {m : CMvMonomial n} {p q : CMvPolynomial n R} :
  coeff m (p + q) = coeff m p + coeff m q
:= by
  simp only [coeff, add_getD?]

lemma fromUnlawful_fold_eq_fold_fromUnlawful₀
  {t : List (CMvMonomial n × R)}
  {f : CMvMonomial n → R → Unlawful n R} :
  ∀ init : Unlawful n R,
  Lawful.fromUnlawful (List.foldl (fun u term => (f term.1 term.2) + u) init t) =
    List.foldl (fun l term => (Lawful.fromUnlawful (f term.1 term.2)) + l) (Lawful.fromUnlawful init) t
:= by
  induction' t with head tail ih
  · simp
  · intro init
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    generalize f head.1 head.2 = x
    ext m
    simp [coeff_add]
    unfold coeff Lawful.fromUnlawful
    simp [filter_get]
    apply Unlawful.add_getD?

lemma fromUnlawful_fold_eq_fold_fromUnlawful
  {t : Unlawful n R}
  {f : CMvMonomial n → R → Unlawful n R} :
  Lawful.fromUnlawful (ExtTreeMap.foldl (fun u m c => (f m c) + u) 0 t) =
    ExtTreeMap.foldl (fun l m c => (Lawful.fromUnlawful (f m c)) + l) 0 t
:= by
  simp [ExtTreeMap.foldl_eq_foldl_toList]
  generalize list_def : ExtTreeMap.toList t = list
  rw [fromUnlawful_fold_eq_fold_fromUnlawful₀ 0]
  simp

#check Multiset.fold_eq_foldl
#check Multiset.fold_eq_foldr
#check List.foldl_map
#check Multiset.sum_eq_foldl
#check Multiset.sum_coe
#check Multiset.map

-- example : Finsupp.sum (fromCMvPolynomial t) (f ∘ g) = sorry
-- example [AddCommMonoid β]
--   {supp : Finset m}
--   {f₁ : m ↪ m'}
--   {f : m' → c → β}
--   {g₁ : m → c} :
--   ∑ x ∈ supp, f (f₁ x) (g₁ x) = ∑ x ∈ supp.map f₁, f x (g₁ x)
-- := by
--   sorry

-- example
--   {p : MvPolynomial (Fin n) R}
--   {f : CMvMonomial n → R → Lawful n R} :
--   Multiset.map (fun x => f (CMvMonomial.ofFinsupp x) ((fromCMvPolynomial t).coeff x)) (fromCMvPolynomial t).support.val =
--     Multiset.map (fun x => f x (t.coeff x)) ((fromCMvPolynomial t).support.val.map CMvMonomial.ofFinsupp)
--   := sorry

lemma foldl_eq_sum' -- [AddCommMonoid δ]
  {t : CMvPolynomial n R}
  {f : CMvMonomial n → R → Lawful n R} :
  ExtTreeMap.foldl (fun x m c => (f m c) + x) 0 t.1 =
    Finsupp.sum (fromCMvPolynomial t) (f ∘ CMvMonomial.ofFinsupp)
:= by
  unfold Finsupp.sum
  simp
  unfold Finset.sum
  -- unfold Multiset.sum
  -- rw [←Multiset.fold_eq_foldr, Multiset.fold_eq_foldl]
  rw [ExtTreeMap.foldl_eq_foldl_toList]
  rw [←List.foldl_map (g := fun x y ↦ y + x)]
  simp_rw [add_comm]
  -- rw [←Multiset.sum_eq_foldl]
  rw [←List.sum_eq_foldl]
  -- simp only [Function.comp_apply]
  ext m
  sorry

lemma coeff_sum [AddCommMonoid X]
  (s : Finset X)
  (f : X → CMvPolynomial n R)
  (m : CMvMonomial n) :
  coeff m (∑ x ∈ s, f x) = ∑ x ∈ s, coeff m (f x)
:= by
  rw [←Finset.sum_map_toList s, ←Finset.sum_map_toList s]
  induction' s.toList with h t ih
  · grind
  · simp [coeff_add]
    congr

lemma fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial
  {f : (Fin n →₀ ℕ) → R → Lawful n R }
  {a : CMvPolynomial n R} :
  fromCMvPolynomial (Finsupp.sum (fromCMvPolynomial a) f) =
    Finsupp.sum (fromCMvPolynomial a) (fun m c ↦ fromCMvPolynomial (f m c))
:= by
  ext m
  simp [coeff_eq]
  unfold Finsupp.sum
  dsimp
  rw [MvPolynomial.coeff_sum, coeff_sum]
  -- TODO (Andrei): I don't understand why `coeff_eq` is just `rfl`, neither why the current goal is closed with a `rfl`.
  rfl

set_option pp.fieldNotation false
@[simp]
lemma map_mul (a b : CMvPolynomial n R) :
  fromCMvPolynomial (a * b) = fromCMvPolynomial a * fromCMvPolynomial b
:= by
  dsimp only [HMul.hMul, Mul.mul, Lawful.mul, Unlawful.mul]
  simp only [fromUnlawful_fold_eq_fold_fromUnlawful]
  unfold MonoidAlgebra.mul'
  rw [foldl_eq_sum']
  simp_rw [foldl_eq_sum']
  let F₀ (p q) : CMvMonomial n → R → Lawful n R :=
    fun p_1 q_1 ↦ Lawful.fromUnlawful {(CMvMonomial.mul p p_1 , Mul.mul q q_1)}
  set F₁ : (Fin n →₀ ℕ) → R → Lawful n R :=
    (fun p q ↦ Finsupp.sum (fromCMvPolynomial b) (F₀ p q ∘ CMvMonomial.ofFinsupp))
      ∘ CMvMonomial.ofFinsupp
    with eqF₁
  let F₂ a₁ b₁ :
    Multiplicative (Fin n →₀ ℕ) → R → MonoidAlgebra R (Multiplicative (Fin n →₀ ℕ))
  := fun a₂ b₂ ↦
    MonoidAlgebra.single (a₁ * a₂) (b₁ * b₂)
  set F₃ : Multiplicative (Fin n →₀ ℕ) → R → MvPolynomial (Fin n) R :=
    fun a₁ b₁ ↦ Finsupp.sum (fromCMvPolynomial b) (F₂ a₁ b₁) with eqF₃
  have {m₁ : Multiplicative (Fin n →₀ ℕ)} {c₁ : R} :
    fromCMvPolynomial (F₁ m₁ c₁) = F₃ m₁ c₁
  := by
    dsimp only [Function.comp_apply, F₁, F₀, F₃, F₂]
    rw [fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial]
    simp only [Function.comp_apply]
    congr
    ext (m₂ : Multiplicative (Fin n →₀ ℕ)) c₂ m
    rw [coeff_eq]
    unfold coeff Lawful.fromUnlawful
    rw [filter_get]
    rw [←CMvMonomial.map_mul]
    simp only [ExtTreeMap.singleton_eq_insert]
    by_cases m_in :
      m = m₁ * m₂
    · rw [←m_in, ExtTreeMap.getElem?_insert]
      simp only [compare_self, ↓reduceIte, Option.getD_some]
      unfold MvPolynomial.coeff
      unfold MonoidAlgebra.single
      simp only [m_in, Finsupp.single_eq_same]
      unfold_projs
      rfl
    · simp only [ExtTreeMap.getElem?_insert]
      simp only [Std.compare_eq_iff_eq, ExtTreeMap.not_mem_empty, not_false_eq_true, getElem?_neg]
      unfold MvPolynomial.coeff
      unfold MonoidAlgebra.single
      rw [Finsupp.single_eq_of_ne (by symm; exact m_in)]
      split
      next h contra =>
        exfalso; apply m_in; symm
        apply CMvMonomial.injective_ofFinsupp contra
      next h => simp_all only [Option.getD_none]
  have : F₃ = fun σ x ↦ fromCMvPolynomial (F₁ σ x) := by ext x y z; rw [this]
  rw [this]
  rw [fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial]

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
