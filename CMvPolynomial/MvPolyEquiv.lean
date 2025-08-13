import CMvPolynomial.CMvPolynomial
import CMvPolynomial.Wheels
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib

example : Polynomial.natDegree (Polynomial.C (1 : ℝ)) = 0 := by
  compute_degree
  simp

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

#check ExtTreeMap.getElem?_filter

lemma Unlawful.mem_add {m : CMvMonomial n} {p₁ p₂ : Unlawful n R} :
  m ∈ p₁ + p₂ ↔ m ∈ p₁ ∨ m ∈ p₂ := by
  simp [(·+·), Add.add, Unlawful.add]
  grind

attribute [grind =] Option.filter_eq_some_iff

section

attribute [local grind=] Lawful.fromUnlawful

lemma add_zero [BEq R] [LawfulBEq R] {p : CMvPolynomial n R} : p + 0 = p := by
  grind

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

-- lemma mul_one_sum [BEq R] [LawfulBEq R] {terms : List (MonoR n R)}:
--   (List.map (fun t => {t}) terms).sum
--     = ExtTreeMap.ofList terms
-- -- := by
--   induction' terms with t ts ih
--   · grind
--   · simp only
--       [ --ExtTreeMap.singleton_eq_insert,
--         List.sum,
--         List.map_cons,
--         List.foldr_cons,
--       ] at ih ⊢
--     rw [ih]
--     rcases t with ⟨m, c⟩

--     unfold_projs
--     unfold Unlawful.add
--     simp
--     -- rw [ExtTreeMap.ofList_eq_insertMany_empty]
--     -- rw [ExtTreeMap.ofList_cons]
--     sorry

#check ExtTreeMap.ordered_keys
#check ExtTreeMap.keys

lemma mul_one [BEq R] [i : LawfulBEq R] {p : CMvPolynomial n R} : p * 1 = p := by
  by_cases h : (1 : R) = 0
  · rw [all_polys_eq_zero_of_1_eq_0 h (p := p * 1), all_polys_eq_zero_of_1_eq_0 h (p := p)]
  · dsimp only [(·*·), Mul.mul, Lawful.mul]
    dsimp only [Unlawful.mul]
    unfold_projs
    unfold Lawful.C
    simp only [Nat.cast_one]
    have map_mul_one' [BEq R] [LawfulBEq R] {terms : List (MonoR n R)}:
      List.map (fun t => Unlawful.mul₀ t (Unlawful.C 1)) terms
        = terms.map (fun t ↦ ({t} : Unlawful n R))
    := by
      simp only [ExtTreeMap.singleton_eq_insert]
      induction' terms with t ts ih
      · simp
      · simp at ih ⊢
        constructor
        · rcases t with ⟨m, r⟩
          unfold Unlawful.mul₀
          simp
          unfold Unlawful.C
          have : ((1 : R) = 0) = False := by simp [*]
          simp [this]
          have : (ExtTreeMap.ofList [@MonoR.C n R 1] compare).toList = [@MonoR.C n R 1] := by
            simp [ExtTreeMap.ofList_eq_insertMany_empty]
            rw [ExtTreeMap.insertMany_cons]
            simp [MonoR.C]
            rw [←ExtTreeMap.ofList_singleton]
            have stolen_from_one_mul :
              @ExtTreeMap.toList (CMvMonomial n) R
                (Vector.compareLex fun x y => compareOfLessAndEq x y)
                Vector.instTransOrd
                (ExtTreeMap.ofList [(CMvMonomial.one, 1)] compare)
                  = [(CMvMonomial.one, 1)]
            := by rfl
            rw [stolen_from_one_mul]
          simp [this]
          congr <;> simp [MonoR.C, CMvMonomial.mul_one]
        · intro m r mr_in
          apply ih
          exact mr_in
    rw [map_mul_one']
    generalize terms_def : ExtTreeMap.toList p.val = terms
    have mul_one_sum [BEq R] [LawfulBEq R] {terms : List (MonoR n R)} :
      (List.map (fun t => {t}) terms).sum = ExtTreeMap.ofList terms
    := by
      induction' terms with t ts ih
      · grind
      · simp only
          [ --ExtTreeMap.singleton_eq_insert,
            List.sum,
            List.map_cons,
            List.foldr_cons,
          ] at ih ⊢
        rw [ih]
        rcases t with ⟨m, c⟩
        rw [ExtTreeMap.ofList_cons]
        -- induction' ts with t' ts' ih'
        -- · simp
        --   grind
        -- ·
        --   simp_all only
        --     [ExtTreeMap.singleton_eq_insert, List.map_inj_left, Prod.forall,
        --       List.map_cons, List.foldr_cons]

        sorry
    rw [mul_one_sum]
    rcases p with ⟨p, _⟩
    simp [Lawful.fromUnlawful]
    congr
    grind

instance {n : ℕ} [BEq R] [LawfulBEq R] :
  AddCommSemigroup (CPoly.CMvPolynomial n R) where
    add_assoc := by
      intros p q r
      unfold_projs
      unfold Lawful.add Lawful.fromUnlawful
      simp only
      unfold_projs
      unfold Unlawful.add
      congr 1
      apply Unlawful.ext' (Lawful.isNoZeroCoef_of_filter _) (Lawful.isNoZeroCoef_of_filter _)
      intros m
      unfold Unlawful.coeff
      rw [ExtTreeMap.getElem?_filter, ExtTreeMap.getElem?_filter]
      by_cases h : m ∈ p <;> by_cases h' : m ∈ q <;> by_cases h'' : m ∈ r
      -- · by_cases g : p[m] + q[m] = 0
      --   · rw [ExtTreeMap.mergeWith₂ _ h'']
      --     by_cases g' : q[m] + r[m] = 0
      --     · rw [ExtTreeMap.mergeWith₁ h]
      repeat sorry
    add_comm {p q} := by grind

instance bla {n : ℕ} [BEq R] [LawfulBEq R] : AddMonoid (CPoly.CMvPolynomial n R) where
  zero_add _ := zero_add -- this is just `by grind` but in a different scope
  add_zero _ := add_zero -- this is just `by grind` but in a different scope
  nsmul n p := (List.replicate n p).sum
  nsmul_succ {m x} := by grind -- `nsmul` def changed + `add_comm` is now available; `grind`!

#synth Mul (MvPolynomial (Fin 42) R)

instance {n : ℕ} [BEq R] [LawfulBEq R] : MonoidWithZero (CPoly.CMvPolynomial n R) where
  zero_mul := by grind
  mul_zero := by
    intro p
    have := List.sum_replicate (ExtTreeMap.size p.1) (0 : Lawful n R) -- Mmmmm. Will grind.

    have sum_zeros : List.sum (List.replicate (ExtTreeMap.size p.1) (0 : Unlawful n R)) = 0 := by
      generalize ExtTreeMap.size p.1 = n
      induction n <;> grind
    unfold_projs
    unfold Lawful.mul
    unfold_projs
    unfold Unlawful.mul Lawful.C
    simp; grind
  mul_assoc := by
    intros a b c
    unfold_projs
    unfold Lawful.mul Lawful.fromUnlawful
    unfold_projs
    unfold Unlawful.mul Unlawful.mul₀
    simp
    congr

    sorry
  one_mul := by
    intros a
    by_cases h : (1 : R) = 0
    · rw [all_polys_eq_zero_of_1_eq_0 h (p := (1 * a)), all_polys_eq_zero_of_1_eq_0 h (p := a)]
    · dsimp only [(·*·), Mul.mul, Lawful.mul, Lawful.fromUnlawful, Unlawful.mul₀, Unlawful.mul]
      unfold_projs
      unfold Lawful.C Unlawful.C MonoR.C
      have :
        @ExtTreeMap.toList (CMvMonomial n) R
          (Vector.compareLex fun x y => compareOfLessAndEq x y)
          Vector.instTransOrd
          (ExtTreeMap.ofList [(CMvMonomial.one, 1)] compare)
            = [(CMvMonomial.one, 1)]
      := by rfl
      simp only [Unlawful.zero_eq_zero, Nat.cast_one, Nat.cast_one, h, ↓reduceIte]
      simp only [this, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
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
      apply Std.ExtTreeMap.ext_getElem? (cmp := compare)
      intro k
      by_cases h' : k ∈ a
      · specialize h k
        rw [ExtTreeMap.filter_mem (f := (fun x c => c != 0)) h'] <;> grind
      · have := @ExtTreeMap.filter_not_mem (CMvMonomial n) R _ _ compare _ _ k (fun x c => c != 0) a h'
        rw [this]
        simp [h']
  mul_one := fun _ ↦ mul_one

instance {n : ℕ} [BEq R] [LawfulBEq R] : Semiring (CPoly.CMvPolynomial n R) where
  left_distrib := sorry
  right_distrib := sorry

#check @List.Perm.sum_eq
#check @List.sum
#check AddCommMonoid

#check Zero.ofOfNat0

example [OfNat (Unlawful n R) 0] {l₁ l₂ : List (Unlawful n R)} : List.Perm l₁ l₂ → l₁.sum = l₂.sum := by
  intros h


  sorry

@[grind =]
def Option.add {α : Type*} [Add α] (a b : Option α) : Option α :=
  match a, b with
  | none  , none   => none
  | none  , some a => a
  | some a, none   => a
  | some a, some b => a + b

variable {α : Type*} {a b c d : Option α} {x y z w : α}

@[simp, grind =]
def Option.zero : Option α := .none

instance : Zero (Option α) := ⟨Option.zero⟩

@[simp, grind =]
lemma Option.zero_eq_none : (Zero.zero : Option α) = none := rfl

@[simp, grind =]
lemma Option.natCast_zero_eq_none [Zero α] : (0 : Option α) = none := rfl

variable [Add α]

@[grind =]
instance {α : Type*} [Add α] : Add (Option α) := ⟨Option.add⟩

@[simp, grind =]
lemma Option.none_add : a + none = a := by aesop (add simp [(·+·), Add.add, Option.add])

@[simp, grind =]
lemma Option.add_none : none + a = a := by aesop (add simp [(·+·), Add.add, Option.add])

@[simp, grind =]
lemma Option.none_add_none : (none : Option α) + none = none := by aesop (add simp [(·+·), Add.add, Option.add])

@[simp, grind =]
lemma Option.some_add_some : some x + some z = some (x + z) := by aesop (add simp [(·+·), Add.add, Option.add])

@[grind =]
def Option.nsmul {α : Type*} [SMul ℕ α] (n : ℕ) (a : Option α) : Option α :=
  match n with
  | 0 => .none
  | k@(_ + 1) => a.map (k•·)

instance [SMul ℕ α] : SMul ℕ (Option α) := ⟨Option.nsmul⟩

attribute [local grind cases] Option
attribute [local grind =] Option.map Option.some_inj

instance abc [AddCommMonoid R] : AddCommMonoid (Option R) where
  add_assoc := by grind
  add_zero := by grind
  zero_add := by grind
  nsmul := Option.nsmul
  nsmul_zero := by grind
  nsmul_succ {n x} := by rcases x <;> rcases n <;> simp [Option.nsmul, Option.map]; grind -- can be 'fixed' to `grind`
  add_comm := by grind

lemma lookup_sum_eq_sum_lookup [BEq R] [LawfulBEq R] {l : List (Unlawful n R)} (m : CMvMonomial n) :
  l.sum[m]? = (l.map (·[m]?)).sum := by
  induction l with
  | nil => simp
  | cons l ls ih =>
    simp [←ih, Unlawful.grind_add_skip]
    dsimp [(·+·), Add.add, Option.add]
    grind

@[simp]
lemma sum_filter_eq_sum {α : Type} [AddZeroClass α] [DecidableEq α] {ls : List α} : (List.filter (fun l => l ≠ 0) ls).sum  = ls.sum := by
  induction ls <;> aesop (add simp List.filter_cons)

lemma sum_eq_ind_sum {α : Type} [AddCommMonoid α] [DecidableEq α] {ls : List α} : ls.sum = ∑ i, ls.get i := by
  simp_all only [List.get_eq_getElem, Fin.sum_univ_getElem]

-- m

--  p * q = q * p
--          (q₀, m'₀)            (q₁, m'₁) ... (qₘ, m'ₘ)
-- (p₀, m₀) (p₀ * q₀, m₀ * m'₀)
-- (p₁, m₁)
-- ...
-- (pₙ, mₙ)

-- p.toList = [(m₀, p₀), (m₁, p₁), ..., (mₙ, pₙ)]
-- q.toList = [(m'₀, q₀), (m'₁, q₁), ..., (m'ₘ, qₘ)]

-- | swap (x y : α) (l m m' : List α) : Perm l (m ++ (x :: y :: m')) → Perm l (m ++ (y :: x :: m'))

lemma exists_list_bij_of_multiset_eq {α : Type} {l₁ l₂ : List α} :
    (Multiset.ofList l₁) = (Multiset.ofList l₂) →
      ∃ f : Fin l₁.length → Fin l₂.length, Function.Bijective f ∧ ∀ i, l₁[i] = l₂[f i] := by
  revert l₂
  induction l₁ with
  | nil =>
    intros l₂ h
    exists Fin.elim0
    have : l₂ = [] := by
      exact (Multiset.coe_eq_zero l₂).mp (id (Eq.symm h))
    rw [this]
    simp
  | cons l l₁' ih =>
    intros l₂ h
    rw [←Multiset.cons_coe] at h
    have : l ∈ (Multiset.ofList l₂) := by
      rw [←h]; simp
    rcases Multiset.exists_cons_of_mem this with ⟨t, h'⟩
    have : Multiset.ofList l₁' = t := by sorry
    specialize @ih (Multiset.toList t)
    rw [Multiset.coe_toList] at ih
    rcases ih this with ⟨f, ih⟩
    have : l ∈ l₂ := by
      have : l ∈ (Multiset.ofList l₂) := by
        rw [h', Multiset.mem_cons]; left; rfl
      rw [Multiset.mem_coe] at this
      exact this
    have : ∃ j : Fin l₂.length, l₂[j] = l := by
      (expose_names; exact List.mem_iff_get.mp this_1)
    rcases this with ⟨j, h''⟩
    have : ∃ l₂' l₂'', l₂ = l₂' ++ (l :: l₂'') ∧ t = Multiset.ofList (l₂' ++ l₂'') := by sorry
    rcases this with ⟨l₂', l₂'', l₂_split, t_eq⟩
    let f (i : Fin (l :: l₁').length) : Fin l₂.length :=
      match i with
      | ⟨0, h⟩ => j
      | ⟨.succ i, h⟩ =>
        let i' : Fin l₁'.length := ⟨i, by simp at h; exact h⟩
        let j' := f i';
        have : t.toList.length + 1 = l₂.length := by
          have : t.card + 1 = (Multiset.ofList l₂).card := by
            rw [h']
            simp
          rw [Multiset.length_toList, this]
          exact Multiset.coe_card _
        if j'.1 < j
        then this ▸ j'.castSucc
        else this ▸ j'.succ
    exists f; dsimp [f]
    apply And.intro
    · sorry
    · rintro ⟨i, i_h⟩
      match i with
      | 0 => simp [h''.symm]
      | .succ i =>
        simp only [Nat.succ_eq_add_one, List.getElem_cons_succ]
        split_ifs with cond
        · sorry
        · sorry

lemma count_le_of_inj {α : Type} [DecidableEq α] {l₁ l₂ : List α} {x : α} : (∃ f : {i | l₁.get i = x} ↪ {j | l₂.get j = x}, True) → List.count x l₁ ≤ List.count x l₂ := by
  rintro ⟨f, h⟩
  sorry

example {a b : Std.ExtTreeMap (CMvMonomial n) R compare} [inst : TransCmp compare] :
  ∀ t ∈ (ExtTreeMap.toList a),
    (m, k) ∈ List.map (fun x => (t.1 * x.1, t.2 * x.2)) (@ExtTreeMap.toList _ _ compare inst b) →
      ∃ t' ∈ (ExtTreeMap.toList b), (m, k) ∈  List.map (fun x => (t'.1 * x.1, t'.2 * x.2)) (@ExtTreeMap.toList _ _ compare inst a) := by
  intros t t_in_a h
  rw [List.mem_map] at h
  rcases h with ⟨t', t'_in_b, h⟩
  exists t'
  apply And.intro t'_in_b
  rw [List.mem_map, ←h]
  exists t
  apply And.intro t_in_a
  rw [mul_comm t'.2, CMvMonomial.mul_com]

#check Classical.choose_spec

lemma List_map_mem_of_eq {α β : Type} {ls : List α} {f : α → β} (l : β) : (∃ i : Fin ls.length, l = f (ls[i])) → l ∈ List.map f ls := by
  intro a_1
  simp_all only [Fin.getElem_fin, List.mem_map]
  obtain ⟨w_1, h⟩ := a_1
  subst h
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl
    }
    · simp_all only [List.getElem_mem]


lemma ofList_lemma {ls : List (CMvMonomial n × R)} {c : R} : (ExtTreeMap.ofList ls compare)[m]? = some c → (m, c) ∈ ls := by
              -- intros h
              -- rw [ExtTreeMap.getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList] at h
              -- rcases h with ⟨m', oh, h⟩
              -- rw[Std.compare_eq_iff_eq] at oh
              -- rw [oh]
              -- convert h


              -- apply?

                sorry

open Classical
instance {n : ℕ} [BEq R] [LawfulBEq R] :
  CommSemiring (CPoly.CMvPolynomial n R) where
    natCast_zero := by grind
    natCast_succ := by intro n; simp
    npow_zero := by intro x; simp [npowRecAuto, npowRec]
    npow_succ := by intro n x; simp [npowRecAuto, npowRec]
    mul_comm := by
      intros a b
      unfold_projs
      unfold Lawful.mul Lawful.fromUnlawful
      unfold_projs
      unfold Unlawful.mul Unlawful.mul₀
      simp only [Unlawful.zero_eq_zero]
      congr 2
      ext1 m
      rw [lookup_sum_eq_sum_lookup, List.map_map, lookup_sum_eq_sum_lookup, List.map_map]
      have {f : MonoR n R → ExtTreeMap (CMvMonomial n) R compare} : (fun (l : Unlawful n R) => l[m]?) ∘ f = (fun x => (f x)[m]?) := by aesop
      rw [this, this]
      generalize eq₁ : List.map _ (ExtTreeMap.toList a.1) = l₁
      generalize eq₂ : List.map _ (ExtTreeMap.toList b.1) = l₂
      rw [←sum_filter_eq_sum, ←sum_filter_eq_sum (ls := l₂)]

      generalize eq'₁ : (List.filter (fun l => decide (l ≠ 0)) l₁) = l'₁
      generalize eq'₂ : (List.filter (fun l => decide (l ≠ 0)) l₂) = l'₂

      have : Multiset.ofList l'₁ = Multiset.ofList l'₂ := by
        ext c
        match mceq_some_c' : c with
        | .none =>
          rw [←eq'₁, ←eq'₂]
          simp
        | .some c' =>
          rw [←eq'₁, ←eq'₂, ←eq₁, ←eq₂, Multiset.coe_count, Multiset.coe_count]
          simp only [Option.natCast_zero_eq_none, ne_eq, decide_not, reduceCtorEq, decide_false,
            Bool.not_false, List.count_filter]
          rw [Nat.eq_iff_le_and_ge]
          apply And.intro
          · apply count_le_of_inj
            refine Exists.intro ?_ (by trivial)
            have {i} : i ∈
              {i |
                (List.map
                  (fun x =>
                    (ExtTreeMap.ofList (List.map (fun x_1 => (x.1 * x_1.1, x.2 * x_1.2)) (ExtTreeMap.toList b.1)) compare)[m]?)
                    (ExtTreeMap.toList a.1)).get i = some c'} → ∃ j : Fin (ExtTreeMap.toList b.1).length, ((ExtTreeMap.toList a.1)[i].1 * (ExtTreeMap.toList b.1)[j].1, (ExtTreeMap.toList a.1)[i].2 * (ExtTreeMap.toList b.1)[j].2) = (m, c') := by
                      intros h
                      simp only [List.get_eq_getElem, List.getElem_map, Set.mem_setOf_eq] at h
                      have := ofList_lemma h
                      rw [List.mem_map] at this
                      rcases this with ⟨mb, cb, h⟩
                      rcases List.mem_iff_get.mp cb with ⟨j, h'⟩
                      exists j
                      unfold_projs at h ⊢
                      rw [h']
                      exact h
            constructor; swap
            · rintro ⟨i, h⟩
              constructor; swap
              · simpa [List.length_map, ExtTreeMap.length_toList, ExtTreeMap.length_toList] using Classical.choose (this h)
              · simp only [List.get_eq_getElem, List.getElem_map, Fin.getElem_fin, Prod.mk.injEq,
                  eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, Set.mem_setOf_eq]
                apply ExtTreeMap.getElem?_ofList_of_mem (k := m) (by simp) sorry
                apply List_map_mem_of_eq
                exists (by simpa using i)
                rw [mul_comm, CMvMonomial.mul_com]
                rcases this h with ⟨j, this⟩
                simp only [←this]
                let N₁ : ℕ :=
                  (ExtTreeMap.toList a.1).map 
                    (fun x =>
                      (ExtTreeMap.ofList (List.map (fun x_1 => (x.1 * x_1.1, x.2 * x_1.2)) (ExtTreeMap.toList b.1)) compare)[m]?)
                    |>.length
                let N₂ : ℕ := (ExtTreeMap.toList a.1).length
                let N₃ : ℕ := (List.map
                      (fun x =>
                        (ExtTreeMap.ofList (List.map (fun x_1 => (x.1 * x_1.1, x.2 * x_1.2)) (ExtTreeMap.toList a.1)) compare)[m]?)
                      (ExtTreeMap.toList b.1)).length
                have eq₁₂ : N₁ = N₂ := by grind
                clear * - N₁ N₂ N₃ eq₁₂
                congr 3
                · rcases i with ⟨i, hi⟩
                  simp only [Fin.getElem_fin, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast]
                  congr 1
                  conv_lhs => rw [show i = (⟨i, show i < N₂ by grind⟩ : Fin _).1 from rfl]
                  apply Fin.val_eq_of_eq
                  rw [←Fin.cast_eq_cast eq₁₂]
                  rfl
                · rcases j with ⟨j, hj⟩
                  simp only [Fin.getElem_fin]
                  congr 1
                  generalize_proofs _ h₁ h₂ _ h₃
                  have eq₃ := choose_spec h₃
                  generalize eq₂ : choose h₃ = E
                  let N₄ : ℕ := (ExtTreeMap.toList b.1).length
                  have eq₃₄ : N₃ = N₄ := by grind
                  conv_lhs => rw [show j = (⟨j, show j < N₃ by grind⟩ : Fin _).1 from rfl]
                  apply Fin.val_eq_of_eq
                  rw [←Fin.cast_eq_cast eq₃₄.symm]
                  rcases E with ⟨E, hE⟩
                  rw [Fin.cast_mk]
                  congr
                  simp [eq₂] at this eq₃
                  -- unique?
                  sorry
                · rcases i with ⟨i, hi⟩
                  simp only [Fin.getElem_fin, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast]
                  congr 1
                  conv_lhs => rw [show i = (⟨i, show i < N₂ by grind⟩ : Fin _).1 from rfl]
                  apply Fin.val_eq_of_eq
                  rw [←Fin.cast_eq_cast eq₁₂]
                  rfl
                · rcases j with ⟨j, hj⟩
                  simp only [Fin.getElem_fin]
                  congr 1
                  generalize_proofs _ h₁ h₂ _ h₃
                  have eq₃ := choose_spec h₃
                  generalize eq₂ : choose h₃ = E
                  let N₄ : ℕ := (ExtTreeMap.toList b.1).length
                  have eq₃₄ : N₃ = N₄ := by grind
                  conv_lhs => rw [show j = (⟨j, show j < N₃ by grind⟩ : Fin _).1 from rfl]
                  apply Fin.val_eq_of_eq
                  rw [←Fin.cast_eq_cast eq₃₄.symm]
                  rcases E with ⟨E, hE⟩
                  rw [Fin.cast_mk]
                  congr
                  simp [eq₂] at this eq₃
                  -- unique?
                  sorry
                  done

            · simp only [List.get_eq_getElem, Set.coe_setOf, Set.mem_setOf_eq, Fin.getElem_fin,
              Prod.mk.injEq, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast]
              intros a b h
              simp at h
              generalize_proofs _ _ _ _ p₁ _ p₂ at h
              -- unique?
              sorry
          · sorry
      rcases exists_list_bij_of_multiset_eq this with ⟨f, f_prop⟩
      rw [sum_eq_ind_sum, sum_eq_ind_sum]
      refine Fintype.sum_bijective (α := Option R) f f_prop.1 l'₁.get l'₂.get f_prop.2


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
