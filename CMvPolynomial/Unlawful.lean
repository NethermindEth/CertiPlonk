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

@[grind=]
def C [BEq R] [LawfulBEq R] [Zero R] (c : R) : Unlawful n R :=
  if c = 0 then ⟨.empty⟩ else .ofList [MonoR.C c]

section

variable {m : ℕ} [Zero R] {x : CMvMonomial n}

section

variable [BEq R] [LawfulBEq R]

instance : OfNat (Unlawful n R) 0 := ⟨C 0⟩

instance [NatCast R] [NeZero m] : OfNat (Unlawful n R) m := ⟨C m⟩

@[simp, grind]
lemma C_zero : C (n := n) (0 : R) = 0 := rfl

end

@[simp, grind]
lemma C_zero' : C (n := n) (0 : ℕ) = 0 := rfl

@[simp, grind]
lemma zero_eq_zero : (Zero.zero : R) = 0 := rfl

@[grind←]
lemma zero_eq_empty [BEq R] [LawfulBEq R] : (0 : Unlawful n R) = ∅ := by unfold_projs; simp [C]; rfl

@[simp, grind]
lemma not_mem_C_zero : x ∉ C 0 := by grind

section

variable [BEq R] [LawfulBEq R]

@[simp, grind]
lemma not_mem_zero : x ∉ (0 : Unlawful n R) := by grind

@[simp, grind]
lemma isNoZeroCoef_zero : isNoZeroCoef (n := n) (R := R) 0 := fun _ ↦ by simp

end

end

def add [Add R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂

instance [Add R] : Add (Unlawful n R) := ⟨add⟩

def addMonoR [Add R] (p : Unlawful n R) (term : MonoR n R) : Unlawful n R :=
  p + (ExtTreeMap.ofList [term] : Unlawful n R)

def mul₀ [Mul R] (t : MonoR n R) (p : Unlawful n R) : Unlawful n R :=
  ExtTreeMap.ofList (p.toList.map fun (k, v) ↦ (t.1*k, t.2*v))

attribute [grind=] ExtTreeMap.ofList_eq_empty_iff List.map_eq_nil_iff ExtTreeMap.toList_eq_nil_iff

@[simp, grind=]
lemma mul₀_zero [Zero R] [BEq R] [LawfulBEq R] [Mul R] {t : MonoR n R} : mul₀ t 0 = 0 := by
  unfold mul₀
  grind

def mul [CommSemiring R] [BEq R] [LawfulBEq R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.toList.map p₂.mul₀ |>.sum

instance [CommSemiring R] [BEq R] [LawfulBEq R] : Mul (Unlawful n R) := ⟨mul⟩

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

def reduce [CommRing R] [BEq R] [LawfulBEq R]
  (p : Unlawful n R) (l : List (R × Unlawful n R)) : Unlawful n R :=
  p - (l.map (fun (cᵢ, pᵢ) ↦ C cᵢ * pᵢ) |>.sum)

def Reduces[CommRing R] [BEq R] [LawfulBEq R] (p q : Unlawful n R) (l : List (R × Unlawful n R)) : Prop :=
  p.reduce l = q

instance instDecidableEq [DecidableEq R] : DecidableEq (Unlawful n R) := fun x y ↦
  if h : x.toList = y.toList
  then Decidable.isTrue (ExtTreeMap.ext_toList (h ▸ List.perm_rfl))
  else Decidable.isFalse (by grind)

instance [BEq R] [LawfulBEq R] [CommRing R]
  {p q : Unlawful n R} {l : List (R × Unlawful n R)} :
  Decidable (Reduces p q l) := by dsimp [Reduces]; infer_instance

def coeff {R : Type} {n : ℕ} [Zero R] (m : CMvMonomial n) (p : Unlawful n R) : R :=
  p[m]?.getD 0

/--
  Conditional extensionality.
-/
theorem ext' {n : ℕ} [Zero R] {p q : Unlawful n R}
  (h₀ : isNoZeroCoef p) (h₁ : isNoZeroCoef q)
  (h : ∀ m, coeff m p = coeff m q) : p = q := by
  unfold coeff at h
  apply ExtTreeMap.ext_getElem?
  grind

end Unlawful

end CPoly
