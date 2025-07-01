import CMvPolynomial.CMvMonomial
import CMvPolynomial.UnlawfulCMvPolynomial

open Std

def LawfulCMvPolynomial (n : ℕ) (R : Type) [Zero R] :=
  { p : UnlawfulCMvPolynomial n R // p.isNoZeroCoef }

variable {n : ℕ} {R : Type} [Zero R]

instance [Zero R] : GetElem (LawfulCMvPolynomial n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp.1) :=
  ⟨fun lp m h ↦ lp.1[m]'h⟩

instance [Zero R] : GetElem? (LawfulCMvPolynomial n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp.1) :=
  ⟨fun lp m ↦ lp.1[m]?, fun lp m ↦ lp.1[m]!⟩

@[simp]
lemma getElem?_eq_val_getElem? {p : LawfulCMvPolynomial n R} {m : CMvMonomial n} :
  p[m]? = p.1[m]? := rfl

instance [Zero R] : Membership (CMvMonomial n) (LawfulCMvPolynomial n R) :=
  ⟨fun lp m ↦ m ∈ lp.1⟩

lemma ExtTreeMap.mem_filter {α β : Type} {cmp} [TransCmp cmp]
                            {f : α → β → Bool} {m : ExtTreeMap α β cmp} {k : α} :
  k ∈ m.filter f ↔ ∃ (h' : k ∈ m), f (m.getKey k h') m[k] = true := sorry

lemma ExtTreeMap.getElem?_filter {α β : Type} [BEq α] [LawfulBEq α]
                                 {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
  {f : α → β → Bool} {k : α} {m : ExtTreeMap α β cmp} :
  (m.filter f)[k]? = m[k]?.filter (f k) := sorry

omit [Zero R] in
lemma UnlawfulCMvPolynomial.mem_of_mem_lawful {p : UnlawfulCMvPolynomial n R} {m : CMvMonomial n}
  (h : m ∈ p) : m ∈ p.1 := h

namespace LawfulCMvPolynomial  

@[simp]
theorem getElem?_ne_some_zero {p : LawfulCMvPolynomial n R} {m : CMvMonomial n} :
  p[m]? ≠ some 0 := by simp only [getElem?_eq_val_getElem?, ne_eq]; rcases p; grind

variable [BEq R] [LawfulBEq R]

section R_CommSemiring

def fromUnlawful (p : UnlawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  { 
    val := p.filter fun _ c ↦ c != 0
    property _ := by aesop (add simp ExtTreeMap.getElem?_filter)
  }

def constant
  (c : R) :
  LawfulCMvPolynomial n R
:=
  if h : c == 0 then
    ⟨ .empty
    , by unfold UnlawfulCMvPolynomial.isNoZeroCoef UnlawfulCMvPolynomial.empty
         grind
    ⟩
  else
    ⟨ UnlawfulCMvPolynomial.constant c
    , by
        unfold UnlawfulCMvPolynomial.isNoZeroCoef UnlawfulCMvPolynomial.constant
        intros m
        simp [
          h, MonoR.constant, ExtTreeMap.ofList_cons, CMvMonomial.one,
          ExtTreeMap.getElem?_eq_some_iff
        ]
        grind
    ⟩

variable [CommSemiring R]

instance {m : ℕ} : OfNat (LawfulCMvPolynomial n R) m
where
  ofNat := LawfulCMvPolynomial.constant n

def extend (n' : ℕ) (p : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial (max n n') R :=
  fromUnlawful <| p.val.extend n'

def add (p₁ p₂ : LawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  fromUnlawful <| p₁.val + p₂.val

instance : Add (LawfulCMvPolynomial n R) := ⟨add⟩

def mul (p₁ p₂ : LawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  fromUnlawful <| p₁.val * p₂.val

instance : Mul (LawfulCMvPolynomial n R) := ⟨mul⟩

abbrev monomials (p : LawfulCMvPolynomial n R) :
  List (CMvMonomial n)
:=
  p.1.monomials

end R_CommSemiring

@[simp]
lemma from_to_Unlawful {p : LawfulCMvPolynomial n R} :
  fromUnlawful p.1 = p := by
  unfold fromUnlawful
  rcases p with ⟨up, h⟩
  dsimp; congr
  refine ExtTreeMap.ext_getElem? fun k ↦ ?p₁
  rw [ExtTreeMap.getElem?_filter]
  rcases eq : up[k]? <;> simp; grind

section R_CommRing

variable [BEq R] [LawfulBEq R] [CommRing R] 

def neg (p : LawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  fromUnlawful p.1.neg

instance : Neg (LawfulCMvPolynomial n R) := ⟨neg⟩

def sub (p₁ p₂ : LawfulCMvPolynomial n R) : LawfulCMvPolynomial n R :=
  p₁ + (-p₂)

instance : Sub (LawfulCMvPolynomial n R) := ⟨sub⟩

def reduce (p d : LawfulCMvPolynomial n R) :
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
