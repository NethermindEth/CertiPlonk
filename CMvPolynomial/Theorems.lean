import CMvPolynomial.CMvPolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Batteries.Data.RBMap.Alter
import CMvPolynomial.Instances

open Batteries

def fromCMvMonomial (m : CMvMonomial n) : (Fin n →₀ ℕ) :=
  ⟨{i : Fin n | m.get i ≠ 0}, m.get, by aesop⟩

lemma size_zero (a : Array α) : a.size = 0 → a = #[] := Array.eq_empty_of_size_eq_zero

lemma Finsupp.toFun_eq :
  ∀ (f₁ f₂ : Fin n →₀ ℕ), f₁ = f₂ → f₁.toFun = f₂.toFun
:= by
  aesop

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

-- TODO: Use `Fintype` instead of `Fin n`
#check Fintype
def toCMvMonomial {n} (m : Fin n →₀ ℕ) : CMvMonomial n := by
  cases h : n with
  | zero => exact #m[]
  | succ n' =>
    have n_gt_0 : 0 < n := by
      simp only [h, add_pos_iff, Nat.lt_one_iff, or_true]
    rw [←h]
    let init : Vector ℕ n := default
    exact
      init.mapFinIdx
        λ i _ le_n ↦ if ⟨i, le_n⟩ ∈ m.support then m.toFun ⟨i, le_n⟩ else 0

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
    simp [if_zero_then_zero, Vector.mapFinIdx_eq_iff]
    intro i h
    rfl

theorem Vector.get_at :
  ∀ (v : Vector ℕ n) (f : Fin n → ℕ) (ix : Fin n),
    (v.mapFinIdx λ i _ le_n ↦ f ⟨i, le_n⟩)[ix] = f ix
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
    simp only [Finsupp.mem_support_iff]
    rcases m with ⟨sₘ, fₘ, memₘ⟩
    simp only [Finsupp.coe_mk, ite_not, Finsupp.mk.injEq, if_zero_then_zero]
    constructor
    · ext a
      rw [memₘ]
      rw [←@Vector.get_at (n'+1) default fₘ a]
      constructor
      · intro h
        simp only [Finset.mem_filter] at h
        apply h.2
      · intro h
        simp only [Finset.mem_filter]
        constructor
        · simp only [Finset.mem_univ]
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

-- theorem monomial_list_nodup (l : List (CMvMonomial n)) :
--   l.Pairwise (RBNode.cmpLT simpleCmp) → l.Pairwise (· ≠ ·)
-- := by
--   induction l with
--   | nil => simp
--   | cons head tail ih =>
--     intro h
--     rcases h with _ | ⟨h₁, h₂⟩
--     apply List.Pairwise.cons
--     · intro a a_in
--       replace h₁ := h₁ a a_in
--       have instanceTransMonomial :
--         TransCmp (simpleCmp : CMvMonomial n → CMvMonomial n → Ordering) := by
--           infer_instance
--       simp [RBNode.cmpLT] at h₁
--       specialize @ h₁ instanceTransMonomial
--       intro contra
--       rw [contra] at h₁
--       simp [simpleCmp] at h₁
--     · apply ih
--       apply h₂

lemma findFst (a : α) (l : List (α × β)) (a_in : a ∈ l.unzip.1) :
  ∃ (b : β), (a, b) ∈ l
:= by
  simp at a_in
  rcases a_in with ⟨x, pair_in⟩
  exists x

-- lemma pair_list_pairwise_lt (l : List (CMvMonomial n × R)) :
--   l.Pairwise (RBNode.cmpLT (simpleCmp ·.1 ·.1)) →
--     l.unzip.1.Pairwise (RBNode.cmpLT simpleCmp)
-- := by
--   intro h
--   induction h with
--   | nil => simp only [List.unzip_nil, List.Pairwise.nil]
--   | @cons a l head tail ih =>
--     apply List.Pairwise.cons
--     · intros a' a'_in
--       let ⟨r, r_in⟩ := findFst a' l a'_in
--       replace head := head (a', r) r_in
--       simp [RBNode.cmpLT] at head
--       have instanceTransMonomial :
--         TransCmp (λ x1 x2 : (CMvMonomial n × R) ↦ simpleCmp x1.1 x2.1) := by
--           infer_instance
--       simp [RBNode.cmpLT, *]
--     · apply ih



-- theorem find_no_zero [CommSemiring R]
--   : ∀ (p : CMvPolynomial n R) (m : CMvMonomial n), p.find? m ≠ some 0
-- := by
--   intro p m
--   simp only [ne_eq]
--   intro contra
--   unfold CMvPolynomial UnlawfulCMvPolynomial.isNoZeroCoef at p
--   rcases p with ⟨p', ne_zero⟩
--   specialize ne_zero m
--   contradiction

def fromLawfulCMvPolynomial [CommSemiring R]
  (p : LawfulCMvPolynomial n R) :
  MvPolynomial (Fin n) R
:=
  let support0 : Finset (CMvMonomial n) := p.monomials
  let support : Finset (Fin n →₀ ℕ) := support0.map fromCMvMonomialEmbedding
  let toFun (f : Fin n →₀ ℕ) : R :=
    let m := toCMvMonomial f
    p.findD m 0
  let mem_support_fun : ∀ (a : Fin n →₀ ℕ), a ∈ support ↔ toFun a ≠ 0 := by
    intro a
    constructor
    · intro a_in
      simp [support] at a_in
      simp_all only [Finset.mem_mk, Multiset.mem_coe, ne_eq]
      simp_all only [support0, support, toFun]
      obtain ⟨w, h⟩ := a_in
      obtain ⟨left, right⟩ := h
      subst right
      simp
        [ fromCMvMonomialEmbedding, monomial_id₁, monomial_equiv
        , LawfulCMvPolynomial.findD]
      intro contra
      cases w_in : p.find? w
      case mp.intro.intro.none =>
        unfold LawfulCMvPolynomial.monomials UnlawfulCMvPolynomial.monomials at left
        apply RBNode.mem_of_mem_foldr_insert at left
        rcases left with (⟨b₀, left⟩ | in_empty)
        · rw [←LawfulCMvPolynomial.mem_node] at left
          rw [w_in] at left
          contradiction
        · contradiction
      case mp.intro.intro.some val =>
        rw [w_in] at contra
        unfold Option.getD at contra
        split at contra
        case h_1 x h_eq =>
          subst contra; rcases h_eq with ⟨h_eq⟩
          apply LawfulCMvPolynomial.find_no_zero p w
          assumption
        case h_2 x h_eq => contradiction
    · intro a_ne_0
      simp [support]
      simp [fromCMvMonomialEmbedding]
      simp only [toFun] at a_ne_0
      exists (toCMvMonomial a)
      constructor
      · unfold LawfulCMvPolynomial.findD at a_ne_0
        unfold Option.getD at a_ne_0
        split at a_ne_0
        case h_1 x h_eq =>
          apply LawfulCMvPolynomial.mem_node.1 at h_eq
          apply LawfulCMvPolynomial.mem_monomials_of_mem
          assumption
        case h_2 x h_eq => contradiction
      · apply monomial_id₂
  Finsupp.mk support toFun mem_support_fun

#check Finset
-- TODO: Use `σ` instead of `Fin n`
noncomputable def toLawfulCMvPolynomial [CommSemiring R]
  (p : MvPolynomial (Fin n) R) :
  LawfulCMvPolynomial n R
:=
  let {support, toFun, mem_support_toFun} := p
  let monomials := support.toList
  let unlawful :=
    monomials.foldr (λ m p ↦ p.insert (toCMvMonomial m) (toFun m)) ∅
  { val := unlawful
  , property := by
      unfold UnlawfulCMvPolynomial.isNoZeroCoef
      intro m
      let m' := fromCMvMonomial m
      by_cases m' ∈ support
      case pos h_in =>
        unfold unlawful
        induction monomials with
        | nil =>
          simp
          rw [RBMap.find?_some]
          intro ⟨_, _, _⟩; contradiction
        | cons head tail ih =>
          simp only [RBMap.mkRBSet_eq, List.foldr_cons, RBMap.find?_insert] at *
          split
          case cons.isTrue h_cmp =>
            apply CMvMonomial.simpleCmp_eq at h_cmp
            simp_all only [ne_eq, Option.some.injEq, m']
            intro a
            apply h_in
            simp only [monomial_id₂, a]
          case cons.isFalse => apply ih
      case neg h_out =>
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
          case cons.intro.isTrue h_cmp =>
            apply CMvMonomial.simpleCmp_eq at h_cmp
            subst h_cmp
            have head_eq : m' = head := by
              simp only [monomial_id₂, m']
            contradiction
          case cons.intro.isFalse =>
            apply ih
            exact h_out₂
  }

noncomputable def fromCMvPolynomial [CommSemiring R]
  (p : CMvPolynomial n R) :
  MvPolynomial (Fin n) R
:=
  fromLawfulCMvPolynomial p.out

-- TODO: Use `σ` instead of `Fin n`
noncomputable def toCMvPolynomial [CommSemiring R]
  (p : MvPolynomial (Fin n) R) :
  CMvPolynomial n R
:=
  ⟦toLawfulCMvPolynomial p⟧

-- theorem polynomial_id₁ {n R} [CommSemiring R] :
--   ∀ (p : CMvPolynomial n R), toCMvPolynomial (fromCMvPolynomial p) = p
-- := by
--   intro p
--   unfold fromCMvPolynomial toCMvPolynomial
--   -- simp
--   simp [Finset.map]
--   simp only [Finset.toList]
--   simp only [Multiset.ofList, Multiset.toList]
--   aesop
--   let ms := p.monomialsList
--   -- revert p
--   -- induction p.monomialsList with
--   -- | nil => sorry
--   -- | cons mHead mTail => sorry
--   sorry

-- theorem polynomial_id₂ {n R} [CommSemiring R] :
--   ∀ (p : MvPolynomial (Fin n) R), fromCMvPolynomial (toCMvPolynomial p) = p
-- := by
--   intro p
--   unfold toCMvPolynomial
--   split
--   rename_i p support toFun mem_support_fun
--   unfold fromCMvPolynomial
--   simp only
--   simp only [RBMap.mkRBSet_eq]
--   congr
--   sorry

noncomputable def polyEquiv [CommSemiring R] :
  Equiv (CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toFun := sorry -- fromCMvPolynomial
  invFun := sorry -- toCMvPolynomial
  left_inv := by sorry
    -- unfold Function.LeftInverse
    -- intro x
    -- rcases x with ⟨x⟩
    -- apply Quotient.sound
    -- simp only [HasEquiv.Equiv]
    -- intros m
    -- let q := Quot.mk (⇑extEquiv) x
    -- have hq : Quot.mk (⇑extEquiv) x = q := by rfl
    -- -- rw [hq]
    -- unfold fromCMvPolynomial fromLawfulCMvPolynomial toLawfulCMvPolynomial
    -- simp
    -- simp [Finset.toList]
  right_inv := sorry

noncomputable def homomorphism₁ [BEq R] [CommSemiring R] [LawfulBEq R] :
  RingHom (CMvPolynomial n R) (MvPolynomial (Fin n) R)
where
  toFun := fromCMvPolynomial
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

noncomputable def homomorphism₂ [BEq R] [CommSemiring R] [LawfulBEq R] :
  RingHom (MvPolynomial (Fin n) R) (CMvPolynomial n R)
where
  toFun := toCMvPolynomial
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
