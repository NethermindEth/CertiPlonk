import CMvPolynomial.Unlawful
import CMvPolynomial.Wheels

attribute [local instance 5] instDecidableEqOfLawfulBEq

namespace CPoly

open Std

def Lawful (n : ℕ) (R : Type) [Zero R] :=
  {p : Unlawful n R // p.isNoZeroCoef}

variable {n : ℕ} {R : Type} [Zero R]

@[grind=]
instance instEmptyCol : EmptyCollection (Lawful n R) := ⟨∅, by grind⟩

instance : GetElem (Lawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp.1) :=
  ⟨fun lp m h ↦ lp.1[m]'h⟩

instance : GetElem? (Lawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp.1) :=
  ⟨fun lp m ↦ lp.1[m]?, fun lp m ↦ lp.1[m]!⟩

instance : Membership (CMvMonomial n) (Lawful n R) :=
  ⟨fun lp m ↦ m ∈ lp.1⟩

namespace Lawful

variable {p : Lawful n R} {m x : CMvMonomial n}

@[simp, grind _=_]
lemma getElem?_eq_val_getElem? : p[m]? = p.1[m]? := rfl

@[simp, grind _=_]
lemma mem_iff_cast : x ∈ p.1 ↔ x ∈ p := by rfl

@[grind =]
lemma mem_iff : x ∈ p ↔ ∃ v, v ≠ 0 ∧ p[x]? = .some v := by
  rw [←mem_iff_cast, ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  rcases p; grind

@[simp]
theorem getElem?_ne_some_zero : p[m]? ≠ some 0 := by
  rcases p; grind

variable [BEq R] [LawfulBEq R]

def fromUnlawful (p : Unlawful n R) : Lawful n R :=
  {
    val := p.filter fun _ c ↦ c != 0
    property _ := by aesop (add simp ExtTreeMap.getElem?_filter)
  }

@[grind←]
protected lemma grind_fromUnlawful_congr {p₁ p₂ : Unlawful n R}
  (h : p₁ = p₂) : Lawful.fromUnlawful p₁ = Lawful.fromUnlawful p₂ := by grind

def C (c : R) : Lawful n R :=
  ⟨Unlawful.C c, by grind⟩

instance instOfNat_zero : OfNat (Lawful n R) 0 := ⟨C 0⟩

lemma zero_def : Zero.zero (α := Lawful n R) = C 0 := rfl

instance instOfNat {m : ℕ} [NeZero m] [NatCast R] : OfNat (Lawful n R) m := ⟨C m⟩

@[simp, grind]
lemma C_zero : C (n := n) (0 : R) = 0 := rfl

@[simp, grind]
lemma C_zero' : C (n := n) (0 : ℕ) = 0 := rfl

lemma zero_eq_zero : (0 : Lawful n R) = ⟨0, by grind⟩ := rfl

lemma zero_eq_empty : (0 : Lawful n R) = ∅ := by unfold_projs; simp [C, Unlawful.zero_eq_empty]

-- Not sure why `zero_eq_empty` dislikes `grind` annotation of the form `(∅ : Unlawful n R)`.
grind_pattern zero_eq_empty => (∅ : Unlawful n R), (0 : Lawful n R) 

@[simp, grind]
lemma not_mem_C_zero : x ∉ C 0 := by simp [zero_eq_empty]; unfold_projs; grind

@[simp, grind]
lemma not_mem_zero : x ∉ (0 : Lawful n R) := by rw [zero_eq_zero]; exact Unlawful.not_mem_zero

@[simp]
lemma cast_fromUnlawful : (fromUnlawful p.1).1 = p.1 := by
  unfold fromUnlawful
  rcases p with ⟨p, hp⟩
  simp; ext1 x
  rw [ExtTreeMap.getElem?_filter, Option.filter_irrel (by aesop)]  
    
section

def extend (n' : ℕ) (p : Lawful n R) : Lawful (max n n') R :=
  fromUnlawful <| p.val.extend n'

def add [Add R] (p₁ p₂ : Lawful n R) : Lawful n R :=
  fromUnlawful <| p₁.val + p₂.val

instance [Add R] : Add (Lawful n R) := ⟨add⟩

@[grind=]
protected lemma grind_add_skip [Add R] {p₁ p₂ : Lawful n R} :
  p₁ + p₂ = Lawful.fromUnlawful (p₁.1.add p₂.1) := rfl

/--
  Note to self: This goes too far.
-/
@[grind=]
protected lemma grind_add_skip_aggressive [Add R] {p₁ p₂ : Lawful n R} :
  p₁ + p₂ = fromUnlawful (ExtTreeMap.mergeWith (fun x c₁ c₂ => c₁ + c₂) p₁.1 p₂.1) := rfl

def mul [Mul R] [Add R] (p₁ p₂ : Lawful n R) : Lawful n R :=
  fromUnlawful <| p₁.val * p₂.val

instance [Mul R] [Add R] [Zero R] : Mul (Lawful n R) := ⟨mul⟩

/--
  Note to self: This goes too far, we could stop at `Unlawful.mul` and formualte lemmas thereabout.
-/
@[grind=]
protected lemma grind_mul_skip [Mul R] [Add R] {p₁ p₂ : Lawful n R} :
  p₁ * p₂ =
  fromUnlawful (List.map (fun t => Unlawful.mul₀ t p₂.1) (ExtTreeMap.toList p₁.1)).sum := by
  rfl

def npow [NatCast R] [Add R] [Mul R] : ℕ → Lawful n R → Lawful n R
| .zero  , _ => 1
| .succ n, p => (npow n p) * p

-- instance [NatCast R] [Add R] [Mul R] : HPow (Lawful n R) ℕ (Lawful n R) := ⟨fun p n => npow n p⟩

instance [NatCast R] [Add R] [Mul R] : NatPow (Lawful n R) := ⟨fun e b ↦ npow b e⟩

abbrev monomials (p : Lawful n R) : List (CMvMonomial n) :=
  p.1.monomials

def NZConst {n : ℕ} {R : Type} [Zero R] (p : Lawful n R) : Prop :=
  p.val.size = 1 ∧ p.val.contains CMvMonomial.one

instance {p : Lawful n R} : Decidable (NZConst p) := by
  dsimp [NZConst]
  infer_instance

end

@[simp, grind=]
lemma fromUnlawful_cast {p : Lawful n R} : fromUnlawful p.1 = p := by
  unfold fromUnlawful
  rcases p with ⟨up, h⟩
  congr
  grind

section

variable [BEq R] [LawfulBEq R] [CommRing R]

def neg (p : Lawful n R) : Lawful n R :=
  fromUnlawful p.1.neg

instance : Neg (Lawful n R) := ⟨neg⟩

def sub (p₁ p₂ : Lawful n R) : Lawful n R :=
  p₁ + (-p₂)

instance : Sub (Lawful n R) := ⟨sub⟩

def reduce [BEq R] [LawfulBEq R] (p : Lawful n R) (l : List (R × Lawful n R)) : Lawful n R :=
  fromUnlawful <| Unlawful.reduce p.val <| l.map fun (c, p) ↦ (c, p.val)

def Reduces [BEq R] [LawfulBEq R] (p q : Lawful n R) (l : List (R × Lawful n R)) : Prop :=
  p.reduce l = q

instance instDecidableEq [DecidableEq R] : DecidableEq (Lawful n R) := fun x y ↦
  if h : x.1.toList = y.1.toList
  then Decidable.isTrue (by have := ExtTreeMap.ext_toList (t₁ := x.1) (t₂ := y.1)
                            simp_rw [Subtype.val_inj] at this
                            grind)
  else Decidable.isFalse (by grind)

instance [BEq R] [LawfulBEq R] {p q : Lawful n R} {l : List (R × Lawful n R)} :
  Decidable (Reduces p q l) := by dsimp [Reduces]; infer_instance

def X (i : ℕ) : Lawful (i + 1) ℤ :=
  let monomial := Vector.replicate i 0 |>.push 1
  Lawful.fromUnlawful <| ExtTreeMap.ofList [(monomial, (1 : ℤ))]

section

variable {n₁ n₂ : ℕ}

def align
  (p₁ : Lawful n₁ R) (p₂ : Lawful n₂ R) :
  Lawful (n₁ ⊔ n₂) R × Lawful (n₁ ⊔ n₂) R :=
  letI sup := n₁ ⊔ n₂
  (
    cast (by congr 1; grind) (p₁.extend sup),
    cast (by congr 1; grind) (p₂.extend sup)
  )

def liftPoly
  (f : Lawful (n₁ ⊔ n₂) R →
       Lawful (n₁ ⊔ n₂) R →
       Lawful (n₁ ⊔ n₂) R)
  (p₁ : Lawful n₁ R) (p₂ : Lawful n₂ R) : Lawful (n₁ ⊔ n₂) R :=
  Function.uncurry f (align p₁ p₂)

section

variable [CommRing R]

instance : HAdd (Lawful n₁ R) (Lawful n₂ R) (Lawful (n₁ ⊔ n₂) R) :=
  ⟨fun p₁ p₂ ↦ liftPoly (·+·) p₁ p₂⟩

instance : HSub (Lawful n₁ R) (Lawful n₂ R) (Lawful (n₁ ⊔ n₂) R) :=
  ⟨fun p₁ p₂ ↦ liftPoly (·-·) p₁ p₂⟩

instance : HMul (Lawful n₁ R) (Lawful n₂ R) (Lawful (n₁ ⊔ n₂) R) :=
  ⟨fun p₁ p₂ ↦ liftPoly (·*·) p₁ p₂⟩

instance : HPow (Lawful n R) ℕ (Lawful n R) :=
  ⟨fun p₁ exp ↦ exp.iterate p₁.mul 1⟩

def polyCoe (p : Lawful n R) : Lawful (n + 1) R := cast (by simp) (p.extend n.succ)

instance : Coe (Lawful n R) (Lawful (n + 1) R) := ⟨polyCoe⟩

end

end

end

end Lawful

end CPoly
