import CMvPolynomial.CMvMonomial
import CMvPolynomial.Wheels
import Std.Data.ExtTreeMap
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Ordering.Lemmas
import Mathlib.Data.Finmap

open Std

universe u

/-- Polynomial in `n` variables with coefficients in `R`. -/
abbrev UnlawfulCMvPolynomial (n : ℕ) (R : Type) : Type :=
  Std.ExtTreeMap (CMvMonomial n) R

namespace UnlawfulCMvPolynomial

section R_CommSemiring
variable {n : ℕ} {R : Type}

def empty : UnlawfulCMvPolynomial n R := ExtTreeMap.empty

/--
  TODO: There is no `map` that would allow modifying keys.
-/
def extend
  (n' : ℕ) (p : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial (max n n') R
:=
  p.foldl (init := ∅) fun acc k v ↦ acc.insert (k.extend n') v

/--
  TODO: This dodges `fold` for `insertMany`. Order is preserved in both cases.
-/
def extend_not_fold {n : ℕ} (n' : ℕ) (p : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial (max n n') R :=
  UnlawfulCMvPolynomial.empty.insertMany (p.keys.map (CMvMonomial.extend n') |>.zip p.values)

@[grind →]
def isNoZeroCoef [Zero R] (p : UnlawfulCMvPolynomial n R) : Prop :=
  ∀ (m : CMvMonomial n), p[m]? ≠ some 0

def toFinset [DecidableEq R]
  (p : UnlawfulCMvPolynomial n R) :
  Finset (CMvMonomial n × R)
:=
  p.toList.toFinset

abbrev monomials (p : UnlawfulCMvPolynomial n R) : List (CMvMonomial n) :=
  p.keys

@[simp]
lemma mem_monomials {m : CMvMonomial n} {up : UnlawfulCMvPolynomial n R} : 
  m ∈ up.monomials ↔ m ∈ up := ExtTreeMap.mem_keys

instance [Repr R] : Repr (UnlawfulCMvPolynomial n R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial n × R) :=
      ⟨λ (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

def constant [BEq R] [Zero R] (c : R) : UnlawfulCMvPolynomial n R :=
  if c == 0 then .empty else ExtTreeMap.ofList [MonoR.constant c]

def zero [BEq R] [Zero R] : UnlawfulCMvPolynomial n R := constant 0

instance : Zero (UnlawfulCMvPolynomial n R) := ⟨empty⟩

def add [HAdd R R R] (p₁ p₂ : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R :=
  ExtTreeMap.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₁ p₂

instance [CommSemiring R] : Add (UnlawfulCMvPolynomial n R) := ⟨add⟩

def addMonoR (p : UnlawfulCMvPolynomial n R) (term : MonoR n R) : UnlawfulCMvPolynomial n R :=
  ExtTreeMap.insert _ _ _
  -- RBSet.insert p
  --   (match RBSet.find? p term with
  --     | some term₁ => (term.1, term₁.2 + term.2)
  --     | none => term
  --   )

/--
  This avoids a fold, so yey?

  `RBMap.map` is a little curious because it treats the collection as a list of pairs in a 'raw'
  fashion and thus allows mapping the keys as well.
lemma add_find_of_find_add_helper [BEq R]
  (t : RBNode (MonoR n R))
  (p : UnlawfulCMvPolynomial n R) :
  (m, cₜ) ∈ t →
  p.find? m = cₚ? →
  c = RBMap.findD (t.foldl addTerm p) m 0 →
  cₜ + cₚ?.getD 0 = c
:= by
  intro m_in_t m_in_p find_in_foldl
  induction t
  case nil => simp_all
  case node _ l v r ih₁ ih₂ =>
    simp [RBMap.findD] at find_in_foldl
    sorry

lemma add_find_of_find_add [BEq R]
  (p₁ p₂ : UnlawfulCMvPolynomial n R) :
  (p₁.add p₂).findD m 0 = c →
  p₁.findD m 0 + p₂.findD m 0 = c
:= by
  unfold add RBMap.mergeWith RBSet.mergeWith RBSet.foldl
  simp
  intro h
  unfold RBMap.findD Option.getD
  -- intro h
  sorry
  -- rcases h_find : RBMap.find? (p₁.add p₂) m with ⟨c⟩
  -- ·

-- lemma add_comm [BEq R] :
--   ∀ (p₁ p₂ : UnlawfulCMvPolynomial n R), add p₁ p₂ = add p₂ p₁
-- := by
--   intro p₁ p₂
--   unfold add
    -- RBMap.mergeWith RBSet.mergeWith RBSet.foldl RBSet.insert
  -- sorry

  `ExtTreeMap` has a more 'standard' interface and its `.map` only allows changing the values.
-/
def mul₀
  [CommSemiring R]
  (t : MonoR n R)
  (p : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  -- p.map λ (m, c) ↦ (t.1 * m, t.2 * c)
  .ofList (p.keys.map (t.1*·) |>.zip <| p.values.map (t.2*·))

theorem list_nodup {p : UnlawfulCMvPolynomial n R} :
  p.toList.Nodup := sorry -- TODO: Look at this.

def mul [CommSemiring R] (p₁ p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  let Pairs : Type := {x : CMvMonomial n × R // x ∈ p₁.toList}
  have : Fintype Pairs :=
    { elems :=
      ⟨ Multiset.ofList p₁.toList.attach
      , by
          simp
          rw [List.nodup_attach]
          apply UnlawfulCMvPolynomial.list_nodup
      ⟩
    , complete := by
        rintro ⟨x, hs⟩
        simp
        apply List.mem_attach
    }
  let terms : List (UnlawfulCMvPolynomial n R) :=
    p₁.foldl (λ acc m c ↦ UnlawfulCMvPolynomial.mul₀ (m, c) p₂ :: acc) []
  terms.foldl UnlawfulCMvPolynomial.add .empty

instance [CommSemiring R] : Mul (UnlawfulCMvPolynomial n R) := ⟨mul⟩
  
end R_CommSemiring

section R_CommRing

variable {n : ℕ} {R : Type} [CommRing R]

def neg (p : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R :=
  p.map fun _ v ↦ -v

instance : Neg (UnlawfulCMvPolynomial n R) := ⟨neg⟩

def sub (p₁ p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  UnlawfulCMvPolynomial.add p₁ (-p₂)

instance : Sub (UnlawfulCMvPolynomial n R) := ⟨sub⟩

/-- lt(p) according to the `simpleCmp` order -/
def leadingTerm? [BEq R] : UnlawfulCMvPolynomial n R → Option (MonoR n R) :=
  ExtTreeMap.maxEntry?
  RBMap.max?

/-- lm(p) according to the `simpleCmp` order -/
def leadingMonomial? [BEq R] :
  UnlawfulCMvPolynomial n R → Option (CMvMonomial n)
:=
  .map Prod.fst ∘ UnlawfulCMvPolynomial.leadingTerm?

def findDivisibleTerm?'
  (p : UnlawfulCMvPolynomial n R)
  (divisor : CMvMonomial n) :
  Option (MonoR n R)
:=
  p.foldl (λ acc m c ↦ if m ∣ divisor then .some (m, c) else acc) none

/--
  Double check, but better than fold. Do we want max or min?
-/
def findDivisibleTerm?
  (p : UnlawfulCMvPolynomial n R)
  (divisor : CMvMonomial n) :
  Option (MonoR n R) := p.filter (fun k _ ↦ k ∣ divisor) |>.maxEntry?
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

-- def reduce [BEq R] (p d : UnlawfulCMvPolynomial n R) :
--   Option (UnlawfulCMvPolynomial n R)
-- := do
--   let lm_d ← d.leadingMonomial?
--   let t ← p.findDivisibleTerm? lm_d
--   let m ← t.1.div lm_d
--   let termQuotient : UnlawfulCMvPolynomial n R := RBMap.single m t.2
--   pure <| p.sub (UnlawfulCMvPolynomial.mul termQuotient d)

def reduce [BEq R]
  (p : UnlawfulCMvPolynomial n R)
  (l : List (R × UnlawfulCMvPolynomial n R)) :
  UnlawfulCMvPolynomial n R
:=
  l.foldl
    (init := p)
    (λ acc (cᵢ, pᵢ) ↦ acc.sub <| (UnlawfulCMvPolynomial.constant cᵢ).mul pᵢ)

def Reduces [BEq R]
  (p : UnlawfulCMvPolynomial n R)
  (l : List (R × UnlawfulCMvPolynomial n R))
  (q : UnlawfulCMvPolynomial n R) :
  Prop
:=
  -- (p.reduce l).toList = q.toList
  (p.reduce l).toList.length = 1
  -- [] = ([] : List (R × UnlawfulCMvPolynomial n R))

instance [BEq R]
  {p : UnlawfulCMvPolynomial n R}
  {l : List (R × UnlawfulCMvPolynomial n R)}
  {q : UnlawfulCMvPolynomial n R} :
  Decidable (Reduces p l q)
:= by
  dsimp [Reduces, reduce]
  infer_instance
  -- sorry

end R_CommRing


end UnlawfulCMvPolynomial
