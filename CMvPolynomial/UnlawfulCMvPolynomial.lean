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

-- instance [LT α] [DecidableEq α] [∀ (a₁ a₂ : α), Decidable (a₁ < a₂)] :
--   Membership α (RBMap α β (λ a₁ a₂ ↦ compareOfLessAndEq a₁ a₂)) where
--   mem map a := a ∈ RBMap.keysArray map

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

def add [CommSemiring R] (p₁ p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  ExtTreeMap.mergeWith (λ _ c₁ c₂ ↦ c₁ + c₂) p₁ p₂

instance [CommSemiring R] : Add (UnlawfulCMvPolynomial n R) := ⟨add⟩

/--
  This avoids a fold, so yey?

  `RBMap.map` is a little curious because it treats the collection as a list of pairs in a 'raw'
  fashion and thus allows mapping the keys as well.

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

def mul [CommSemiring R] (p₁ p₂ : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R
:=  
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

def div₀
  (f : UnlawfulCMvPolynomial n R)
  (m : UnlawfulCMvPolynomial n R)
  (q : UnlawfulCMvPolynomial n R)
  (r : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R × UnlawfulCMvPolynomial n R
:= sorry

def reduce [BEq R] (p d : UnlawfulCMvPolynomial n R) :
  Option (UnlawfulCMvPolynomial n R)
:= do
  let lm_d : CMvMonomial n ← d.leadingMonomial?
  let t ← p.findDivisibleTerm? lm_d
  let m : CMvMonomial n := t.1.div lm_d
  let termQuotient : UnlawfulCMvPolynomial n R := ExtTreeMap.ofList [(m, t.2)]
  p - termQuotient * d

end R_CommRing


end UnlawfulCMvPolynomial
