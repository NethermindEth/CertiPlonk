import CMvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Batteries.Data.RBMap.Alter

open Batteries

def finRangeNoDup (top n : Nat) (le_top_n : top ≤ n) :
  Σ' (l : List (Fin n)), (∀ x, x ∈ l ↔ x.val < top) ∧ List.Nodup l := by
  cases top with
    | zero => exists []; simp
    | succ top' =>
      have top_le_n : top' ≤ n := by
        apply le_trans _ le_top_n
        simp only [Nat.le_step, Nat.le_refl]
      let ⟨l', in_l_iff_lt, nodup⟩ := finRangeNoDup top' n top_le_n
      exists ⟨top', le_top_n⟩ :: l'
      constructor
      · intro x
        constructor
        · intro x_belongs
          cases x_belongs with
          | head l' => simp
          | tail n' belongs =>
            have x_le_top := (in_l_iff_lt x).1 belongs
            simp only [Nat.lt_succ_of_lt, x_le_top]
        · intro a_le_succ_top
          rw [Nat.lt_succ_iff_lt_or_eq] at a_le_succ_top
          simp only [List.mem_cons]
          rcases a_le_succ_top with h₁ | h₂
          · simp only [in_l_iff_lt x, h₁, or_true]
          · left; cases h₂; simp only [Fin.eta]
      · apply List.Pairwise.cons
        · intros a a_in_l'
          simp only [Fin.ne_iff_vne, Nat.ne_iff_lt_or_gt]
          right
          simp_all only
        · exact nodup

def fromCMvMonomial (m : CMvMonomial n) : (Fin n →₀ ℕ) :=
  let ⟨l, in_l_iff_lt, nodup⟩ := finRangeNoDup n n (Nat.le_refl n)
  let ms : Multiset (Fin n) := Multiset.ofList l
  let support0 : Finset (Fin n) :=
    { val := Multiset.ofList l
      nodup := by simp only [Multiset.coe_nodup, nodup]
    }
  let support := { i ∈ support0 | m.get i ≠ 0 }
  let toFun : Fin n → ℕ := m.get
  let mem_support_fun : ∀ (a : Fin n), a ∈ support ↔ toFun a ≠ 0 := by
    intro a; constructor
    · intro a_belongs
      simp [support] at a_belongs
      simp [a_belongs, toFun]
    · intro toFunNeZero
      simp only [toFun] at toFunNeZero
      simp [support]
      constructor <;> simp [support0, in_l_iff_lt a, *]
  Finsupp.mk support toFun mem_support_fun

lemma size_zero : ∀ (a : Array α), a.size = 0 → a = #[] := by
  intros a h
  rcases a with ⟨l⟩
  cases l
  · rfl
  · contradiction

lemma Finsupp.toFun_eq :
  ∀ (f₁ f₂ : Fin n →₀ ℕ), f₁ = f₂ → f₁.toFun = f₂.toFun
:= by
  intro f₁ f₂ h_eq
  rcases f₁ with ⟨_, toFun₁, _⟩
  rcases f₂ with ⟨_, toFun₂, _⟩
  simp
  cases h_eq
  rfl

lemma vector_get_eq :
  ∀ (v₁ v₂ : Vector ℕ n), Vector.get v₁ = Vector.get v₂ → v₁ = v₂
:= by
  induction n with
  | zero =>
    intros v₁ v₂ h
    cases v₁; cases v₂
    simp [size_zero, *]
  | succ n' ih =>
    intros v₁ v₂ h
    rw [funext_iff] at h
    aesop

-- TODO: Use `σ` instead of `Fin n`
def toCMvMonomial {n} (m : Fin n →₀ ℕ) : (CMvMonomial n) := by
  cases h : n with
  | zero => exact #m[]
  | succ n' =>
    have n_gt_0 : 0 < n := by
      simp only [h, add_pos_iff, Nat.lt_one_iff, or_true]
    rw [←h]
    let init : Vector ℕ n := default
    exact
      init.mapFinIdx
        λ i _ le_n => if ⟨i, le_n⟩ ∈ m.support then m.toFun ⟨i, le_n⟩ else 0

lemma if_zero_then_zero : ∀ n : ℕ, (if n = 0 then 0 else n) = n := by
  simp only [ite_eq_right_iff, forall_eq]

theorem monomial_id₁ :
  ∀ (m : CMvMonomial n), toCMvMonomial (fromCMvMonomial m) = m
:= by
  intro m
  cases n with
  | zero =>
    have is_zero : m = #m[] := by
      simp only [Vector.eq_mk, Vector.toArray_eq_empty_iff]
    simp [is_zero]
  | succ n' =>
    unfold toCMvMonomial
    simp only
      [Fin.zero_eta, Finsupp.mem_support_iff, ite_not, eq_mpr_eq_cast, cast_eq]
    unfold fromCMvMonomial
    simp
    split
    rename_i x l in_l_iff_lt nodup heq
    simp_all only [Finsupp.coe_mk]
    obtain ⟨fst, snd⟩ := x
    obtain ⟨left, right⟩ := snd
    simp_all only [Fin.is_lt, iff_true]
    simp only [if_zero_then_zero]
    rw [Vector.mapFinIdx_eq_iff]
    intro i h
    rfl

theorem Vector.get_at :
  ∀ (v : Vector ℕ n) (f : Fin n → ℕ) (ix : Fin n),
    (v.mapFinIdx λ i _ le_n => f ⟨i, le_n⟩)[ix] = f ix
:= by
  intros v f ix
  apply Vector.getElem_mapFinIdx ix.2

theorem monomial_id₂ :
  ∀ (m : Fin n →₀ ℕ), fromCMvMonomial (toCMvMonomial m) = m
:= by
  intro m
  cases n with
  | zero => ext a; cases a; contradiction
  | succ n' =>
    unfold fromCMvMonomial
    unfold toCMvMonomial
    split
    simp only [Fin.zero_eta, Finsupp.mem_support_iff, eq_mpr_eq_cast, cast_eq]
    rcases m with ⟨sₘ, fₘ, memₘ⟩
    simp only [Finsupp.coe_mk, ite_not, Finsupp.mk.injEq]
    rename_i x l in_l_iff_lt nodup heq
    simp only [if_zero_then_zero]
    constructor
    · ext a
      rw [memₘ]
      rw [←@Vector.get_at (n'+1) default fₘ a]
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_mk, Multiset.mem_coe] at h
        let ⟨h₁, h₂⟩ := h
        apply h₂
      · intro h
        simp only [Finset.mem_filter, Finset.mem_mk, Multiset.mem_coe]
        constructor
        · apply (in_l_iff_lt a).2
          simp only [Fin.is_lt]
        · apply h
    · ext a
      apply Vector.get_at

def monomial_equiv : (CMvMonomial n ≃ (Fin n →₀ ℕ)) where
  toFun := fromCMvMonomial
  invFun := toCMvMonomial
  left_inv := by
    unfold Function.LeftInverse
    apply monomial_id₁
  right_inv := by
    unfold Function.RightInverse
    apply monomial_id₂

def fromCMvMonomialEmbedding : CMvMonomial n ↪ (Fin n →₀ ℕ) :=
  monomial_equiv.toEmbedding

theorem monomial_list_nodup (l : List (CMvMonomial n)) :
  l.Pairwise (RBNode.cmpLT simpleCmp) → l.Pairwise (· ≠ ·)
:= by
  induction l with
  | nil => simp
  | cons head tail ih =>
    intro h
    rcases h with _ | ⟨h₁, h₂⟩
    apply List.Pairwise.cons
    · intro a a_in
      replace h₁ := h₁ a a_in
      have instanceTransMonomial :
        TransCmp (simpleCmp : CMvMonomial n → CMvMonomial n → Ordering) := by
          infer_instance
      simp [RBNode.cmpLT] at h₁
      specialize @ h₁ instanceTransMonomial
      intro contra
      rw [contra] at h₁
      simp [simpleCmp] at h₁
    · apply ih
      apply h₂

lemma findFst (a : α) (l : List (α × β)) (a_in : a ∈ l.unzip.1) :
  ∃ (b : β), (a, b) ∈ l
:= by
  simp at a_in
  rcases a_in with ⟨x, pair_in⟩
  exists x

lemma pair_list_pairwise_lt (l : List (CMvMonomial n × R)) :
  l.Pairwise (RBNode.cmpLT (simpleCmp ·.1 ·.1)) →
    l.unzip.1.Pairwise (RBNode.cmpLT simpleCmp)
:= by
  intro h
  induction h with
  | nil => simp only [List.unzip_nil, List.Pairwise.nil]
  | @cons a l head tail ih =>
    apply List.Pairwise.cons
    · intros a' a'_in
      let ⟨r, r_in⟩ := findFst a' l a'_in
      replace head := head (a', r) r_in
      simp [RBNode.cmpLT] at head
      have instanceTransMonomial :
        TransCmp (λ x1 x2 : (CMvMonomial n × R) => simpleCmp x1.1 x2.1) := by
          infer_instance
      simp [RBNode.cmpLT, *]
    · apply ih

lemma list_pairwise_lt_nodup (l : List (CMvMonomial n)) :
  l.Pairwise (RBNode.cmpLT simpleCmp) → l.Nodup
:= by
  intro h
  induction h with
  | nil => simp
  | @cons a l head tail ih =>
    apply List.Pairwise.cons
    · intros a' a'_in contra
      rw [contra] at head
      specialize head a' a'_in
      simp [RBNode.cmpLT] at head
      specialize head
      simp [simpleCmp] at head
    · apply ih

theorem monomials_nodup [CommRing R] (p : CMvPolynomial n R) :
  p.monomialsList.Nodup
:= by
  apply list_pairwise_lt_nodup
  apply pair_list_pairwise_lt
  apply RBMap.toList_sorted

theorem find_no_zero [CommRing R]
  : ∀ (p : CMvPolynomial n R) (m : CMvMonomial n), p.find? m ≠ some 0
:= by
  intro p m
  simp only [ne_eq]
  intro contra
  unfold CMvPolynomial UnlawfulCMvPolynomial.isNoZeroCoef at p
  rcases p with ⟨p', ne_zero⟩
  specialize ne_zero m
  contradiction

theorem find_no_zero_key [CommRing R]
  : ∀ (p : CMvPolynomial n R) (m : CMvMonomial n),
    m ∈ p.monomialsList → p.findD m 0 ≠ 0
:= by
  intros p m h_in
  unfold CMvPolynomial.findD Option.getD
  split
  case h_1 v₀ v h_find =>
    intro contra
    unfold CMvPolynomial UnlawfulCMvPolynomial.isNoZeroCoef at p
    rcases p with ⟨p', ne_zero⟩
    apply ne_zero m
    rw [←contra]
    simp [CMvPolynomial.find?] at h_find
    exact h_find
  case h_2 v h_find =>
    unfold CMvPolynomial.monomialsList at h_in
    have ⟨val, find_val⟩ : ∃ r, p.find? m = some r := by
      let pre@⟨b, h_b⟩ := findFst m (RBMap.toList p.val) h_in
      have eq_m : simpleCmp m m = .eq := by simp [simpleCmp]
      exists b
      apply RBMap.find?_some.2
      exists m
    rw [h_find] at find_val
    contradiction

theorem find_no_zero_key' [CommRing R]
  : ∀ (p : CMvPolynomial n R) (m : CMvMonomial n),
    p.findD m 0 ≠ 0 → m ∈ p.monomialsList
:= by
  unfold CMvPolynomial.findD CMvPolynomial.find? Option.getD
  intro p m h
  split at h
  case h_1 v₀ v h_find =>
    apply RBMap.find?_some.1 at h_find
    rcases h_find with ⟨y, hy⟩
    unfold CMvPolynomial.monomialsList
    simp_all only
      [simpleCmp, List.unzip_fst, List.mem_map, Prod.exists]
    simp only [exists_and_right, exists_eq_right]
    obtain ⟨left, right⟩ := hy
    aesop
  case h_2 v₀ v h_find =>
    simp_all only [ne_eq, not_true_eq_false]

def fromCMvPolynomial [CommRing R]
  (p : CMvPolynomial n R) :
  MvPolynomial (Fin n) R
:=
  let monomials := p.monomialsList
  let monomials_nodup : monomials.Nodup := by apply monomials_nodup p
  let monomials' := Multiset.ofList monomials
  let monomials'_nodup : monomials'.Nodup := by
    unfold monomials'
    simp [monomials_nodup]
  let support0 : Finset (CMvMonomial n) :=
    { val := monomials'
      nodup := monomials'_nodup
    }
  let support : Finset (Fin n →₀ ℕ) :=
    support0.map fromCMvMonomialEmbedding
  let toFun (f : Fin n →₀ ℕ) : R :=
    let m := toCMvMonomial f
    p.findD m 0
  let mem_support_fun : ∀ (a : Fin n →₀ ℕ), a ∈ support ↔ toFun a ≠ 0 := by
    intro a
    constructor
    · intro a_in
      simp [support] at a_in
      simp_all only [Finset.mem_mk, Multiset.mem_coe, ne_eq]
      simp_all only [support0, monomials', monomials, support, toFun]
      obtain ⟨w, h⟩ := a_in
      obtain ⟨left, right⟩ := h
      subst right
      simp [fromCMvMonomialEmbedding, monomial_id₁, monomial_equiv]
      apply find_no_zero_key
      exact left
    · intro a_ne_0
      simp [support]
      simp [fromCMvMonomialEmbedding]
      simp only [toFun, monomials, monomials'] at a_ne_0
      exists (toCMvMonomial a)
      constructor
      · apply find_no_zero_key'
        exact a_ne_0
      · apply monomial_id₂
  Finsupp.mk support toFun mem_support_fun

-- TODO: Use `σ` instead of `Fin n`
noncomputable def toCMvPolynomial [CommRing R]
  (p : MvPolynomial (Fin n) R) :
  CMvPolynomial n R
:=
  let {support, toFun, mem_support_toFun} := p
  let monomials := support.toList
  let unlawful :=
    monomials.foldr
    (fun m p => p.insert (toCMvMonomial m) (toFun m) )
    (mkRBMap (CMvMonomial n) R simpleCmp)
  { val := unlawful
  , property := by
      unfold UnlawfulCMvPolynomial.isNoZeroCoef
      intro m
      let m' := fromCMvMonomial m
      have h : m' ∈ support ∨ ¬ m' ∈ support := by
        apply Classical.em (m' ∈ support)
      cases h with
      | inl h_in =>
        unfold unlawful
        induction monomials with
        | nil =>
          simp
          rw [RBMap.find?_some]
          intro ⟨_, _, _⟩; contradiction
        | cons head tail ih =>
          simp only [RBMap.mkRBSet_eq, List.foldr_cons, RBMap.find?_insert] at *
          split
          case inl.cons.isTrue h_cmp =>
            apply monomial_eq at h_cmp
            subst h_cmp
            simp_all only [ne_eq, Option.some.injEq, m']
            intro a
            apply h_in
            simp only [monomial_id₂, a]
          case inl.cons.isFalse => apply ih
      | inr h_out =>
        unfold unlawful
        have h_out' : m' ∉ monomials := by simp [monomials, h_out]
        revert h_out'
        induction monomials with
        | nil =>
          simp
          rw [RBMap.find?_some]
          intro ⟨_, _, _⟩; contradiction
        | cons head tail ih =>
          simp only [RBMap.mkRBSet_eq, List.foldr_cons, RBMap.find?_insert] at *
          intro h_out
          simp only [List.mem_cons, not_or] at h_out
          rcases h_out with ⟨h_out₁, h_out₂⟩
          split
          case inr.cons.intro.isTrue h_cmp =>
            apply monomial_eq at h_cmp
            subst h_cmp
            have head_eq : m' = head := by
              simp only [monomial_id₂, m']
            contradiction
          case inr.cons.intro.isFalse =>
            apply ih
            exact h_out₂
  }
