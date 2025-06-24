import Mathlib.Algebra.Lie.OfAssociative
import CMvPolynomial.UnlawfulCMvPolynomial
import Batteries.Data.RBMap.Lemmas

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
  { val := p.filter (λ _ c ↦ ¬ c == 0)
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
        unfold UnlawfulCMvPolynomial.isNoZeroCoef
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
  LawfulCMvPolynomial.fromUnlawful <| p.val.extend n'

def add [BEq R]
  (p₁ : LawfulCMvPolynomial n R)
  (p₂ : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  LawfulCMvPolynomial.fromUnlawful <| UnlawfulCMvPolynomial.add p₁.val p₂.val

def mul [BEq R]
  (p₁ : LawfulCMvPolynomial n R)
  (p₂ : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  LawfulCMvPolynomial.fromUnlawful <| UnlawfulCMvPolynomial.mul p₁.val p₂.val

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
  unfold LawfulCMvPolynomial.find? RBMap.find? RBMap.findEntry? RBSet.findP?
  constructor
  · intro h
    apply RBNode.find?_some_mem (cut := (λ x_1 ↦ CMvMonomial.simpleCmp x x_1.1))
    simp
    simp only [Option.map_eq_some', Prod.exists, exists_eq_right] at h
    obtain ⟨w, h⟩ := h
    simp_all only [Option.some.injEq, Prod.mk.injEq, and_true]
    rw [←Option.mem_def] at h
    apply RBNode.find?_some_eq_eq at h
    unfold CMvMonomial.simpleCmp compareOfLessAndEq at h
    simp at h
    rcases h with ⟨_, h⟩
    symm; assumption
  · unfold Membership.mem RBNode.instMembership
    intro h
    simp [RBNode.EMem] at h
    simp
    use x
    let p := a.val.2.out.1
    apply (RBNode.Ordered.find?_some p).2
    constructor
    · aesop
    · unfold CMvMonomial.simpleCmp compareOfLessAndEq
      simp
      apply Vector.le_refl

-- #eval myPolynomial
-- #check RBNode.find
def extEquiv : Setoid (LawfulCMvPolynomial n R) where
  r a b := ∀ x, a.find? x = b.find? x
  iseqv := by constructor <;> (intros; simp only [*])

instance : HasEquiv (LawfulCMvPolynomial n R) where
  Equiv := extEquiv

lemma to_list_equiv [DecidableEq R]
  (a b : LawfulCMvPolynomial n R) :
  a ≈ b →
  a.val.toList.toFinset = b.val.toList.toFinset
:= by
  unfold HasEquiv.Equiv instHasEquiv Setoid.r extEquiv
  dsimp
  intro h
  ext x
  rw [List.mem_toFinset, List.mem_toFinset]
  rw [RBMap.mem_toList, RBMap.mem_toList]
  unfold LawfulCMvPolynomial.find? at h
  unfold Membership.mem RBNode.instMembership RBNode.EMem
  dsimp
  unfold RBMap.find? RBMap.findEntry? RBSet.findP? at h
  -- let nodeA : RBNode (CMvMonomial n × R) := a.val.val
  -- let nodeB : RBNode (CMvMonomial n × R) := b.val.val
  -- have h_nodeA : nodeA = a.val.val := by rfl
  -- have h_nodeB : nodeB = b.val.val := by rfl
  -- rw [←h_nodeA] at ⊢ h
  -- rw [←h_nodeB] at ⊢ h
  constructor
  · induction' a.val.val
    case h.mp.nil => simp
    case h.mp.node l v r ih₁ ih₂ =>
      simp
      rcases b.val.val with (_| ⟨_, l₂, v, r₂⟩)
      · sorry
      · sorry
  · sorry

end R_CommSemiring

section R_CommRing
variable {n R} [CommRing R]

def neg [BEq R]
  (p : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  LawfulCMvPolynomial.fromUnlawful p.val.neg

def sub [BEq R]
  (p₁ : LawfulCMvPolynomial n R)
  (p₂ : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  LawfulCMvPolynomial.add p₁ p₂.neg

def reduce [BEq R]
  (p : LawfulCMvPolynomial n R)
  (d : LawfulCMvPolynomial n R) :
  Option (LawfulCMvPolynomial n R)
:= do
  let up ← UnlawfulCMvPolynomial.reduce p.val d.val
  pure (LawfulCMvPolynomial.fromUnlawful up)

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
