import CMvPolynomial.UnlawfulCMvPolynomial

open Batteries

def LawfulCMvPolynomial n R [CommSemiring R] :=
  { p : UnlawfulCMvPolynomial n R // p.isNoZeroCoef}

namespace LawfulCMvPolynomial
section R_CommSemiring
variable {n R} [CommSemiring R]

def fromUnlawful [BEq R]
  (p : UnlawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  { val := p.filter (λ _ c ↦ !c == 0)
    property := sorry
  }

def constant [BEq R] [LawfulBEq R]
  (c : R) :
  LawfulCMvPolynomial n R
:=
  -- LawfulCMvPolynomial.fromUnlawful <| .constant c
  if h : c == 0 then
    ⟨ .empty
    , by
        unfold UnlawfulCMvPolynomial.isNoZeroCoef UnlawfulCMvPolynomial.empty
        intro m
        cases h : RBMap.empty.find? m
        · simp
        · rw [RBMap.find?_some] at h
          aesop
    ⟩
  else
    ⟨ UnlawfulCMvPolynomial.constant c
    , by
        simp at h
        unfold
          UnlawfulCMvPolynomial.isNoZeroCoef
          UnlawfulCMvPolynomial.constant
          Function.uncurry
        dsimp
        intro m
        by_contra contra
        have ⟨y, contra, _⟩ := RBMap.find?_some_mem_toList contra
        simp at contra
        unfold Term.constant at contra
        aesop
    ⟩

instance [BEq R] [LawfulBEq R]:
  OfNat (LawfulCMvPolynomial n R) natural
where
  ofNat := LawfulCMvPolynomial.constant natural

def extend [BEq R]
  (n' : ℕ)
  (p : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial (max n n') R
:=
  fromUnlawful <| p.val.extend n'

def add [BEq R] (p₁ p₂ : LawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  fromUnlawful <| UnlawfulCMvPolynomial.add p₁.val p₂.val

def mul [BEq R] (p₁ p₂ : LawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  fromUnlawful <| UnlawfulCMvPolynomial.mul p₁.val p₂.val

def find? (p : LawfulCMvPolynomial n R) (m : CMvMonomial n) : Option R :=
  p.val.find? m

def monomials (p : LawfulCMvPolynomial n R) :
  Finset (CMvMonomial n)
:=
  p.val.monomials

lemma mem_monomials_of_mem
  {p : LawfulCMvPolynomial n R} :
  (a₀, b₀) ∈ p.val.val → a₀ ∈ p.monomials
:= by
  unfold LawfulCMvPolynomial.monomials
  intro h
  apply UnlawfulCMvPolynomial.mem_monomials_of_mem
  assumption

lemma mem_of_mem_monomials
  {p : LawfulCMvPolynomial n R} :
  a₀ ∈ p.monomials → (∃ b₀, (a₀, b₀) ∈ p.val.val)
:= by
  unfold LawfulCMvPolynomial.monomials
  intro h
  apply UnlawfulCMvPolynomial.mem_of_mem_monomials
  assumption

def findD (p : LawfulCMvPolynomial n R) (m : CMvMonomial n) (v₀ : R) : R :=
  (p.find? m).getD v₀

lemma mem_node
  {a : LawfulCMvPolynomial n R} :
  a.find? x = some c ↔ (x, c) ∈ a.val.val
:= by
  unfold find?
  exact UnlawfulCMvPolynomial.mem_node

def extEquiv : Setoid (LawfulCMvPolynomial n R) where
  r a b := ∀ x, a.find? x = b.find? x
  iseqv := by constructor <;> (intros; simp only [*])

instance : HasEquiv (LawfulCMvPolynomial n R) where
  Equiv := extEquiv

lemma from_to_Lawful₀ [BEq R] [LawfulBEq R] :
  ∀ (node : RBNode (CMvMonomial n × R)) (init : UnlawfulCMvPolynomial n R),
    (∀ k v, (k, v) ∈ node → v ≠ 0) →
    node.foldl (fun acc a => bif !a.2 == 0 then RBSet.insert acc a else acc) init
      = node.foldl (fun acc a => RBSet.insert acc a) init
:= by
  intro node
  let node' := node
  induction node
  case nil => intros; rfl
  case node _ l v r ih₁ ih₂ =>
    intro init h
    simp only [RBNode.foldl]
    rw [ih₁, ih₂]
    have coeff_nonzero : !v.2 == 0 = true := by
      simp
      intro h_eq
      specialize h v.1 v.2 (by simp)
      contradiction
    simp [coeff_nonzero]
    · intro k v h_in
      apply h k v
      simp
      right
      right
      assumption
    · intro k v h_in
      apply h k v
      simp
      right
      left
      assumption

#printaxioms from_to_Lawful₀

lemma from_to_Unlawful [BEq R] [LawfulBEq R] (p : LawfulCMvPolynomial n R) :
  fromUnlawful p.val ≈ p
:= by
  intro x
  unfold fromUnlawful
  cases x_in_p : p.find? x
  case none =>
    rcases p with ⟨⟨node, wf⟩, node_nozero⟩
    have nonzero_coeff : ∀ (m : CMvMonomial n) (c : R), (m, c) ∈ node → c ≠ 0 := by
      intro m c mc_in c_zero
      specialize node_nozero m
      apply node_nozero
      rw [UnlawfulCMvPolynomial.mem_node]
      simp
      subst c_zero
      assumption
    unfold RBMap.filter RBSet.filter RBSet.foldl
    dsimp at x_in_p ⊢
    unfold find?
    dsimp
    rw [from_to_Lawful₀] <;> try apply nonzero_coeff
    unfold LawfulCMvPolynomial.find? at x_in_p
    simp at x_in_p
    by_contra find_some
    rw [←ne_eq, Option.ne_none_iff_exists] at find_some
    rcases find_some with ⟨val, find_some⟩
    let find_some := find_some.symm
    apply UnlawfulCMvPolynomial.mem_of_filter_insert at find_some
    · rcases find_some with (f₁ | f₂)
      · have find_x : RBMap.find? ⟨node, wf⟩ x = val := by
          rw [UnlawfulCMvPolynomial.mem_node]
          simp [*]
        rw [find_x] at x_in_p
        contradiction
      · contradiction
    · rw [RBNode.WF_iff] at wf
      exact wf.1
  case some val =>
    rcases p with ⟨⟨node, wf⟩, node_nozero⟩
    rw [mem_node] at x_in_p
    unfold RBMap.filter RBSet.filter RBSet.foldl
    dsimp at x_in_p ⊢
    unfold find?
    dsimp
    have nonzero_coeff : ∀ (m : CMvMonomial n) (c : R), (m, c) ∈ node → c ≠ 0 := by
      intro m c mc_in c_zero
      specialize node_nozero m
      apply node_nozero
      rw [UnlawfulCMvPolynomial.mem_node]
      simp
      subst c_zero
      assumption
    rw [from_to_Lawful₀ _ _ nonzero_coeff]
    rw [RBNode.WF_iff] at wf
    rcases wf with ⟨ordered, _⟩
    unfold Ordering.byKey at ordered
    apply UnlawfulCMvPolynomial.mem_filter_insert_of_mem node <;> assumption

theorem find_no_zero
  : ∀ (p : LawfulCMvPolynomial n R) (m : CMvMonomial n), p.find? m ≠ some 0
:= by
  intro p m
  simp only [ne_eq]
  intro contra
  unfold LawfulCMvPolynomial UnlawfulCMvPolynomial.isNoZeroCoef at p
  rcases p with ⟨p', ne_zero⟩
  specialize ne_zero m
  contradiction

lemma fromUnlawful_find_no_zero_iff [BEq R] :
  ∀ (p : UnlawfulCMvPolynomial n R) (m : CMvMonomial n) (c : R),
    (fromUnlawful p).find? m = some c ↔ p.find? m = some c ∧ c ≠ 0
:= by
  intro p m c
  constructor
  · intro h
    constructor
    · unfold fromUnlawful at h
      rw [UnlawfulCMvPolynomial.mem_node]
      simp
        [ mem_node
        , RBMap.filter
        , RBSet.filter
        , RBSet.foldl
        ] at h
      sorry
    · intro hc
      rw [hc] at h
      apply find_no_zero (fromUnlawful p) m h
  · sorry

end R_CommSemiring

section R_CommRing
variable {n R} [CommRing R]

def neg [BEq R] (p : LawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  fromUnlawful p.val.neg

def sub [BEq R] (p₁ p₂ : LawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  add p₁ p₂.neg

def reduce [BEq R] (p d : LawfulCMvPolynomial n R) :
  Option (LawfulCMvPolynomial n R)
:= do
  let up ← UnlawfulCMvPolynomial.reduce p.val d.val
  pure (fromUnlawful up)

end R_CommRing
end LawfulCMvPolynomial

-- private def p : LawfulCMvPolynomial 2 ℤ where -- 2 * X0^2 * X1^3
--   val := [⟨#m[2, 3], 2⟩].toRBMap CMvMonomial.simpleCmp
--   property := by sorry

-- private def d : LawfulCMvPolynomial 2 ℤ where -- X0^2 * X1^0 + X0^2 * X1^2
--   val := [⟨#m[2, 2], 1⟩, ⟨#m[2, 0], 1⟩].toRBMap CMvMonomial.simpleCmp
--   property := sorry

-- #eval! p
-- #eval! d
-- #eval! p.reduce d -- some -2 * X0^2 * X1^1

-- -- private def p₁_1 := [⟨#m[2], 1⟩, ⟨#m[0], -1⟩].toRBMap CMvMonomial.simpleCmp
-- -- private def p₁_2 := [⟨#m[1], 2⟩, ⟨#m[0], -1⟩].toRBMap CMvMonomial.simpleCmp
-- private def i : UnlawfulCMvPolynomial 1 ℤ := [⟨#m[2], 1⟩, ⟨#m[0], -1⟩].toRBMap CMvMonomial.simpleCmp
-- #eval i
-- private def p₁ : UnlawfulCMvPolynomial 1 ℤ := [⟨#m[1], -2⟩, ⟨#m[0], -1⟩].toRBMap CMvMonomial.simpleCmp
-- #eval p₁
-- private def p₂ : UnlawfulCMvPolynomial 1 ℤ := [⟨#m[1], 2⟩, ⟨#m[0], 2⟩].toRBMap CMvMonomial.simpleCmp
-- #eval p₂
-- private def t₁ : UnlawfulCMvPolynomial 1 ℤ := [⟨#m[1], 1⟩, ⟨#m[0], 2⟩].toRBMap CMvMonomial.simpleCmp
-- #eval t₁
-- private def x : UnlawfulCMvPolynomial 1 ℤ := [⟨#m[1], 1⟩].toRBMap CMvMonomial.simpleCmp
-- #eval! x
-- #eval! i.reduce t₁
-- #eval! i.sub (x.mul t₁)
