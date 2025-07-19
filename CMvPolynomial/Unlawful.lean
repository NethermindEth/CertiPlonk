import CMvPolynomial.CMvMonomial
import Mathlib.Algebra.Lie.OfAssociative
import Std.Data.ExtTreeMap.Lemmas

attribute [local instance 5] instDecidableEqOfLawfulBEq

namespace CPoly

open Std

/--
  Polynomial in `n` variables with coefficients in `R`.
-/
abbrev Unlawful (n : ℕ) (R : Type) : Type :=
  Std.ExtTreeMap (CMvMonomial n) R

namespace Unlawful

variable {n : ℕ} {R : Type}

def extend (n' : ℕ) (p : Unlawful n R) : Unlawful (n ⊔ n') R :=
  .ofList (p.keys.map (CMvMonomial.extend n') |>.zip p.values)

abbrev isNoZeroCoef [Zero R] (p : Unlawful n R) : Prop := ∀ (m : CMvMonomial n), p[m]? ≠ some 0

def toFinset [DecidableEq R] (p : Unlawful n R) : Finset (CMvMonomial n × R) :=
  p.toList.toFinset

abbrev monomials (p : Unlawful n R) : List (CMvMonomial n) :=
  p.keys

@[simp]
lemma mem_monomials {m : CMvMonomial n} {up : Unlawful n R} :
  m ∈ up.monomials ↔ m ∈ up := ExtTreeMap.mem_keys

instance [Repr R] : Repr (Unlawful n R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial n × R) :=
      ⟨λ (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

instance : Zero (Unlawful n R) := ⟨.empty⟩

@[simp]
lemma not_mem_zero {x : CMvMonomial n} : x ∉ (0 : Unlawful n R) := by unfold_projs; grind

@[simp, grind←]
lemma isNoZeroCoef_zero [Zero R] : isNoZeroCoef (n := n) (R := R) 0 := fun _ ↦ by simp

def C [BEq R] [Zero R] (c : R) : Unlawful n R :=
  if c == 0 then 0 else .ofList [MonoR.C c]

def add [Add R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂

instance [Add R] : Add (Unlawful n R) := ⟨add⟩

def addMonoR [Add R] (p : Unlawful n R) (term : MonoR n R) : Unlawful n R :=
  p + (ExtTreeMap.ofList [term] : Unlawful n R)

def mul₀ [Mul R] (t : MonoR n R) (p : Unlawful n R) : Unlawful n R :=
  ExtTreeMap.ofList (p.toList.map fun (k, v) ↦ (t.1*k, t.2*v))

def mul [CommSemiring R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.toList.map p₂.mul₀ |>.sum

instance [CommSemiring R] : Mul (Unlawful n R) := ⟨mul⟩

def neg [Neg R] (p : Unlawful n R) : Unlawful n R :=
  p.map fun _ v ↦ -v

instance [Neg R] : Neg (Unlawful n R) := ⟨neg⟩

def sub [Neg R] [Add R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  Unlawful.add p₁ (-p₂)

instance [Neg R] [Add R] : Sub (Unlawful n R) := ⟨sub⟩

def leadingTerm? : Unlawful n R → Option (MonoR n R) :=
  ExtTreeMap.maxEntry?

def leadingMonomial? : Unlawful n R → Option (CMvMonomial n) :=
  .map Prod.fst ∘ Unlawful.leadingTerm?

def findDivisibleTerm? (p : Unlawful n R) (divisor : CMvMonomial n) : Option (MonoR n R) :=
  p.filter (fun k _ ↦ k ∣ divisor) |>.maxEntry?

def reduce [CommRing R] [BEq R] (p : Unlawful n R) (l : List (R × Unlawful n R)) : Unlawful n R :=
  p - (l.map (fun (cᵢ, pᵢ) ↦ C cᵢ * pᵢ) |>.sum)

def Reduces [BEq R] [CommRing R] (p q : Unlawful n R) (l : List (R × Unlawful n R)) : Prop :=
  p.reduce l = q

instance instDecidableEq [DecidableEq R] : DecidableEq (Unlawful n R) := fun x y ↦
  if h : x.toList = y.toList
  then Decidable.isTrue (ExtTreeMap.ext_toList (h ▸ List.perm_rfl))
  else Decidable.isFalse (by grind)

instance [BEq R] [LawfulBEq R] [CommRing R]
  {p q : Unlawful n R} {l : List (R × Unlawful n R)} :
  Decidable (Reduces p q l) := by dsimp [Reduces]; infer_instance

lemma mergeWith₀ (m₁ m₂ : Unlawful n R) (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = .some (f k m₁[k] m₂[k])
:= sorry

lemma mergeWith₁ (m₁ m₂ : Unlawful n R) (h₁ : k ∈ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₁[k]?
:= sorry

lemma mergeWith₂ (m₁ m₂ : Unlawful n R) (h₁ : k ∉ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₂[k]?
:= sorry

lemma mergeWith₃ (m₁ m₂ : Unlawful n R) (h₁ : k ∉ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = .none
:= sorry

end Unlawful

end CPoly
