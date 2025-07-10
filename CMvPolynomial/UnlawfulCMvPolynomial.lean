import CMvPolynomial.CMvMonomial
import CMvPolynomial.Wheels
import Std.Data.ExtTreeMap
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Ordering.Lemmas
import Mathlib.Data.Finmap

open Std

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

def add [Add R] (p₁ p₂ : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R :=
  p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂

instance [Add R] : Add (UnlawfulCMvPolynomial n R) := ⟨add⟩

def addMonoR [Add R] (p : UnlawfulCMvPolynomial n R) (term : MonoR n R) : UnlawfulCMvPolynomial n R :=
  p + (ExtTreeMap.ofList [term] : UnlawfulCMvPolynomial n R)

/--
  This avoids a fold, so yey?

  `ExtTreeMap` has a more 'standard' interface and its `.map` only allows changing the values.
-/
def mul₀ [Mul R] (t : MonoR n R) (p : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R :=
  ExtTreeMap.ofList (p.toList.map fun (k, v) ↦ (t.1*k, t.2*v))

def mul [CommSemiring R] (p₁ p₂ : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R :=
  let terms : List (UnlawfulCMvPolynomial n R) := p₁.toList.map p₂.mul₀
  terms.sum

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

/--
  @ANDREI: Double check, but better than fold. Do we want max or min?
-/
def findDivisibleTerm? (p : UnlawfulCMvPolynomial n R) (divisor : CMvMonomial n) :
  Option (MonoR n R) := p.filter (fun k _ ↦ k ∣ divisor) |>.maxEntry?

def reduce [BEq R] (p : UnlawfulCMvPolynomial n R) (l : List (R × UnlawfulCMvPolynomial n R)) :
  UnlawfulCMvPolynomial n R :=
  p - (l.map (fun (cᵢ, pᵢ) ↦ .constant cᵢ * pᵢ) |>.sum)

def Reduces [BEq R]
  (p : UnlawfulCMvPolynomial n R)
  (l : List (R × UnlawfulCMvPolynomial n R))
  (q : UnlawfulCMvPolynomial n R) :
  Prop := p.reduce l = q

instance instDecidableEq [DecidableEq R] : DecidableEq (UnlawfulCMvPolynomial n R) := fun x y ↦
  if h : x.toList = y.toList
  then Decidable.isTrue (ExtTreeMap.ext_toList (h ▸ List.perm_rfl))
  else Decidable.isFalse (by grind)

instance [BEq R] [DecidableEq R]
  {p : UnlawfulCMvPolynomial n R}
  {l : List (R × UnlawfulCMvPolynomial n R)}
  {q : UnlawfulCMvPolynomial n R} :
  Decidable (Reduces p l q) := by dsimp [Reduces]; infer_instance

end R_CommRing


end UnlawfulCMvPolynomial
