import CMvPolynomial.Unlawful

attribute [local instance 5] instDecidableEqOfLawfulBEq

namespace CPoly

open Std

def Lawful (n : ℕ) (R : Type) [Zero R] :=
  {p : Unlawful n R // p.isNoZeroCoef}

variable {n : ℕ} {R : Type} [Zero R]

instance : GetElem (Lawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp.1) :=
  ⟨fun lp m h ↦ lp.1[m]'h⟩

instance : GetElem? (Lawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp.1) :=
  ⟨fun lp m ↦ lp.1[m]?, fun lp m ↦ lp.1[m]!⟩

@[simp]
lemma getElem?_eq_val_getElem? {p : Lawful n R} {m : CMvMonomial n} :
  p[m]? = p.1[m]? := rfl

instance : Membership (CMvMonomial n) (Lawful n R) :=
  ⟨fun lp m ↦ m ∈ lp.1⟩

/-
  Something like this might be needed for `.getElem?_filter`.
-/
-- lemma ExtTreeMap.mem_filter {α β : Type} {cmp} [TransCmp cmp]
--                             {f : α → β → Bool} {m : ExtTreeMap α β cmp} {k : α} :
--   k ∈ m.filter f ↔ ∃ (h' : k ∈ m), f (m.getKey k h') m[k] = true := sorry

lemma ExtTreeMap.getElem?_filter {α β : Type} [BEq α] [LawfulBEq α]
                                 {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
  {f : α → β → Bool} {k : α} {m : ExtTreeMap α β cmp} :
  (m.filter f)[k]? = m[k]?.filter (f k) := sorry

omit [Zero R] in
lemma Unlawful.mem_of_mem_lawful {p : Unlawful n R} {m : CMvMonomial n}
  (h : m ∈ p) : m ∈ p.1 := h

namespace Lawful  

@[simp]
theorem getElem?_ne_some_zero {p : Lawful n R} {m : CMvMonomial n} :
  p[m]? ≠ some 0 := by simp only [getElem?_eq_val_getElem?, ne_eq]; rcases p; grind

variable [BEq R] [LawfulBEq R]

def fromUnlawful (p : Unlawful n R) : Lawful n R :=
  { 
    val := p.filter fun _ c ↦ c != 0
    property _ := by aesop (add simp ExtTreeMap.getElem?_filter)
  }

instance : Zero (Lawful n R) := ⟨.empty, by grind⟩

def C (c : R) : Lawful n R :=
  ⟨
    Unlawful.C c,
    by unfold Unlawful.C
       by_cases eq : c = 0
       · grind
       · simp [eq, MonoR.C]
         grind
  ⟩

section

variable [CommSemiring R]

instance {m : ℕ} : OfNat (Lawful n R) m := ⟨C n⟩

def extend (n' : ℕ) (p : Lawful n R) : Lawful (max n n') R :=
  fromUnlawful <| p.val.extend n'

def add (p₁ p₂ : Lawful n R) : Lawful n R :=
  fromUnlawful <| p₁.val + p₂.val

instance : Add (Lawful n R) := ⟨add⟩

def mul (p₁ p₂ : Lawful n R) : Lawful n R :=
  fromUnlawful <| p₁.val * p₂.val

instance : Mul (Lawful n R) := ⟨mul⟩

abbrev monomials (p : Lawful n R) : List (CMvMonomial n) :=
  p.1.monomials

def NZConst {n : ℕ} {R : Type} [Zero R] (p : Lawful n R) : Prop :=
  p.val.size = 1 ∧ p.val.contains CMvMonomial.one

instance {p : Lawful n R} : Decidable (NZConst p) := by
  dsimp [NZConst]
  infer_instance

end

@[simp]
lemma from_to_Unlawful {p : Lawful n R} : fromUnlawful p.1 = p := by
  unfold fromUnlawful
  rcases p with ⟨up, h⟩
  dsimp; congr
  refine ExtTreeMap.ext_getElem? fun k ↦ ?p₁
  rw [ExtTreeMap.getElem?_filter]
  rcases eq : up[k]? <;> simp; grind

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

def align [Zero R]
  (p₁ : Lawful n₁ R) (p₂ : Lawful n₂ R) :
  Lawful (n₁ ⊔ n₂) R × Lawful (n₁ ⊔ n₂) R :=
  letI sup := n₁ ⊔ n₂
  (
    cast (by congr 1; grind) (p₁.extend sup),
    cast (by congr 1; grind) (p₂.extend sup)
  )

def liftPoly [Zero R]
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
