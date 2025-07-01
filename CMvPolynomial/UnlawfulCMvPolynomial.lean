import CMvPolynomial.CMvMonomial
import CMvPolynomial.Wheels
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Ordering.Lemmas

open Batteries

/-- Polynomial in `n` variables with coefficients in `R`. -/
abbrev UnlawfulCMvPolynomial n R [CommSemiring R] :=
  Batteries.RBMap (CMvMonomial n) R CMvMonomial.simpleCmp

-- instance [LT α] [DecidableEq α] [∀ (a₁ a₂ : α), Decidable (a₁ < a₂)] :
--   Membership (α × β) (RBMap α β (λ a₁ a₂ ↦ compareOfLessAndEq a₁ a₂))
-- where
--   mem map pair := by
--     unfold RBMap at map
--     exact pair ∈ map

instance [LT α] [DecidableEq α] [∀ (a₁ a₂ : α), Decidable (a₁ < a₂)] :
  Membership α (RBMap α β (λ a₁ a₂ ↦ compareOfLessAndEq a₁ a₂)) where
  mem map a := a ∈ RBMap.keysArray map

namespace UnlawfulCMvPolynomial

section R_CommSemiring
variable {n R} [CommSemiring R]

def extend
  (n' : ℕ) (p : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial (max n n') R
:=
  p.map λ (m, c) ↦ (m.extend n', c)

def isNoZeroCoef (p : UnlawfulCMvPolynomial n R) : Prop :=
  ∀ m, p.find? m ≠ some 0

def toFinset [DecidableEq R]
  (p : UnlawfulCMvPolynomial n R) :
  Finset (CMvMonomial n × R)
:=
  p.val.foldr (init := .empty) insert

lemma mem_node
  {a : UnlawfulCMvPolynomial n R} :
  a.find? x = some c ↔ (x, c) ∈ a.val
:= by
  unfold RBMap.find? RBMap.findEntry? RBSet.findP?
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
    let p := a.2.out.1
    apply (RBNode.Ordered.find?_some p).2
    constructor
    · aesop
    · unfold CMvMonomial.simpleCmp compareOfLessAndEq
      simp
      apply Vector.le_refl

def monomials (p : UnlawfulCMvPolynomial n R) : Finset (CMvMonomial n) :=
  p.foldr (init := .empty) λ a _ s ↦ insert a s

lemma mem_monomials_of_mem
  {p : UnlawfulCMvPolynomial n R} :
  (a₀, b₀) ∈ p.val → a₀ ∈ p.monomials
:= RBNode.mem_foldr_insert_of_mem (b₀ := b₀) _ _

lemma mem_of_mem_monomials
  {p : UnlawfulCMvPolynomial n R} :
  a₀ ∈ p.monomials → (∃ b₀, (a₀, b₀) ∈ p.val)
:= fun h ↦ (RBNode.mem_of_mem_foldr_insert _ _ h).elim id fun c ↦ by contradiction

lemma mem_filter_insert_of_mem₀ [BEq R]
  (t : RBNode (MonoR n R)):
  ∀ init : UnlawfulCMvPolynomial n R,
    init.find? a = some b →
    RBMap.find?
      (t.foldl (λ acc (a, b) ↦ bif ! b == 0 then acc.insert a b else acc) init)
      a
      = some b
:= by
  induction t
  case nil h =>
    intro init h
    simp; assumption
  case node l v r ih₁ ih₂ =>
    intro init h
    simp_all
    apply ih₂
    cases v.2 == 0
    · 
      -- rw [RBMap.insert]
      sorry
    · 
      sorry

lemma mem_filter_insert_of_mem [BEq R]
  (t : RBNode (MonoR n R)):
  ∀ init : UnlawfulCMvPolynomial n R,
    (a₀, b₀) ∈ t →
    RBMap.find?
      (t.foldl (λ acc (a, b) ↦ bif ! b == 0 then acc.insert a b else acc) init)
      a₀
      = some b₀
:= by
  intro init h
  revert init
  induction t
  case nil h => contradiction
  case node l v r ih₁ ih₂ =>
    simp
    intro init
    rw [RBNode.mem_node] at h
    rcases h with (h₁ | h₂ | h₃)
    · sorry
    · sorry
    · sorry

instance [Repr R] : Repr (UnlawfulCMvPolynomial n R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial n × R) :=
      ⟨λ (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

-- def myPolynomial : UnlawfulCMvPolynomial 3 ℤ :=
--   [⟨#m[1, 2, 1], 5⟩, ⟨#m[3, 2, 0], 5⟩].toRBMap CMvMonomial.simpleCmp

-- def myPolynomial₂ : UnlawfulCMvPolynomial 3 ℤ :=
--   [⟨#m[1, 2, 1], -5⟩, ⟨#m[3, 2, 0], -5⟩].toRBMap CMvMonomial.simpleCmp

/--
  Ref: @Frantisek - Why `BEq`?
-/
def constant (c : R) : UnlawfulCMvPolynomial n R :=
  Function.uncurry RBMap.single (MonoR.constant c)
  -- Function.uncurry RBMap.empty.insert (MonoR.constant c)

def zero : UnlawfulCMvPolynomial n R := constant 0

instance : Zero (UnlawfulCMvPolynomial n R) := ⟨zero⟩

def add (p₁ p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  RBMap.mergeWith (λ _ c₁ c₂ ↦ c₁ + c₂) p₁ p₂

instance : Add (UnlawfulCMvPolynomial n R) := ⟨add⟩

-- lemma add_comm [BEq R] :
--   ∀ (p₁ p₂ : UnlawfulCMvPolynomial n R), add p₁ p₂ = add p₂ p₁
-- := by
--   intro p₁ p₂
--   unfold add
    -- RBMap.mergeWith RBSet.mergeWith RBSet.foldl RBSet.insert
  -- sorry

/--
  Ref: @Frantisek - Why `BEq`?
-/
def mul₀
  (t : MonoR n R)
  (p : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  p.map λ (m, c) ↦ (t.1 * m, t.2 * c)

theorem list_nodup {p : UnlawfulCMvPolynomial n R} :
  p.toList.Nodup := CMvMonomial.list_pairwise_lt_nodup RBMap.toList_sorted

/--
  Ref: @Frantisek - Why `CommSemiring` and `BEq`?
-/
def mul (p₁ p₂ : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R
:=
  -- let Pairs : Type := {x : CMvMonomial n × R // x ∈ p₁.toList}
  -- have : Fintype Pairs :=
  --   { elems :=
  --     ⟨ Multiset.ofList p₁.toList.attach
  --     , by
  --         simp
  --         rw [List.nodup_attach]
  --         apply UnlawfulCMvPolynomial.list_nodup
  --     ⟩
  --   , complete := by
  --       rintro ⟨x, hs⟩
  --       simp
  --       apply List.mem_attach
  --   }
  let terms : List (UnlawfulCMvPolynomial n R) :=
    p₁.foldl (λ acc m c ↦ UnlawfulCMvPolynomial.mul₀ (m, c) p₂ :: acc) []
  terms.foldl UnlawfulCMvPolynomial.add .empty
  -- Not sure the `AddCommMonoid` instance works
  -- ∑ t : Pairs, UnlawfulCMvPolynomial.mul₀ t p₂

instance : Mul (UnlawfulCMvPolynomial n R) := ⟨mul⟩

theorem nonemptySome
  {p : UnlawfulCMvPolynomial n R}
  (nonempty : 0 < p.size) :
  ∃ m r, p.find? m = some r
:= by  
  unfold UnlawfulCMvPolynomial at *
  rcases p with ⟨_ | ⟨_, l, ⟨m, r⟩, _⟩⟩ <;> [contradiction; skip]
  use m, r
  simp [RBMap.find?_some, RBMap.mem_toList]
  
end R_CommSemiring

section R_CommRing
variable {n R} [CommRing R]

/--
  Ref: @Frantisek - Why `BEq`?
-/
def neg (p : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R :=
  p.map λ (m, c) ↦ (m, -c)

instance : Neg (UnlawfulCMvPolynomial n R) := ⟨neg⟩

/--
  Ref: @Frantisek - Why `BEq`?
-/
def sub (p₁ p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  UnlawfulCMvPolynomial.add p₁ p₂.neg

instance : Sub (UnlawfulCMvPolynomial n R) := ⟨sub⟩

/-- lt(p) according to the `simpleCmp` order -/
def leadingTerm? [BEq R] : UnlawfulCMvPolynomial n R → Option (MonoR n R) :=
  RBMap.max?

/-- lm(p) according to the `simpleCmp` order -/
def leadingMonomial? [BEq R] :
  UnlawfulCMvPolynomial n R → Option (CMvMonomial n)
:=
  .map Prod.fst ∘ UnlawfulCMvPolynomial.leadingTerm?

def findDivisibleTerm?
  (p : UnlawfulCMvPolynomial n R)
  (divisor : CMvMonomial n) :
  Option (MonoR n R)
:=
  p.foldl (λ acc m c ↦ if m.divides divisor then .some (m, c) else acc) none

def div₀
  (f : UnlawfulCMvPolynomial n R)
  (m : UnlawfulCMvPolynomial n R)
  (q : UnlawfulCMvPolynomial n R)
  (r : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R × UnlawfulCMvPolynomial n R
:= sorry

-- instance [CommRing R] [BEq R] :
--   AddCommMonoid (UnlawfulCMvPolynomial n R)
-- where
--   add := UnlawfulCMvPolynomial.add
--   add_assoc := sorry
--   zero := .empty
--   zero_add := sorry
--   add_zero := by aesop
--   nsmul n p := if n == 0 then .empty else p.map λ (m, c) ↦ (m, n * c)
--   nsmul_zero := by aesop
--   nsmul_succ := by
--     simp
--     intro n ⟨x₁, x₂⟩
--     induction' n with n' ih
--     · simp
--       sorry
--     · sorry
--   add_comm := sorry

def reduce [BEq R] (p d : UnlawfulCMvPolynomial n R) :
  Option (UnlawfulCMvPolynomial n R)
:= do
  let lm_d ← d.leadingMonomial?
  let t ← p.findDivisibleTerm? lm_d
  let m ← t.1.div lm_d
  let termQuotient : UnlawfulCMvPolynomial n R := RBMap.single m t.2
  pure <| p.sub (UnlawfulCMvPolynomial.mul termQuotient d)

end R_CommRing


end UnlawfulCMvPolynomial

def myPolynomial₃ : UnlawfulCMvPolynomial 2 ℤ :=
  [⟨#m[1, 0], 2⟩, ⟨#m[0, 1], 3⟩].toRBMap CMvMonomial.simpleCmp

def myPolynomial₄ : UnlawfulCMvPolynomial 2 ℤ :=
  [⟨#m[1, 1], 1⟩, ⟨#m[2, 0], -1⟩].toRBMap CMvMonomial.simpleCmp

-- #eval myPolynomial₃
-- #eval myPolynomial₄
-- #eval! myPolynomial₃.mul myPolynomial₄
