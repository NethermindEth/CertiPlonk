import Batteries.Data.RBMap

import Mathlib.Algebra.Ring.Nat
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.List.Lex

import Aesop

open Batteries

def hello := "world"

/-- Monomial in `n` variables. `#v[e₀, e₁, e₂]` denotes X₀^e₀ * X₁^e₁ * X₂^e₂ -/
abbrev CMvMonomial n := Vector ℕ n

-- instance : LawfulOrd (CMvMonomial n) where
--   symm := sorry
--   le_trans := sorry
--   cmp_iff_beq := sorry
--   cmp_iff_lt := sorry
--   cmp_iff_le := sorry

-- #check List.compare_le

theorem List.symm :
  ∀ (x y : List ℕ), (compare x y).swap = compare y x
:= by
  intro x
  induction x with
  | nil =>
    intro y
    cases y <;> simp
  | cons h₁ t₁ ih =>
    intro y
    cases y with
    | nil => simp
    | cons h₂ t₂ =>
      simp
      simp [Ordering.swap_then]
      rw [←ih t₂]
      rw [Nat.compare_swap]


theorem CMvMonomial.symm :
  ∀ (x y : CMvMonomial n), (compare x y).swap = compare y x
:= by
  intros x y
  rcases x with ⟨⟨x⟩, _⟩
  rcases y with ⟨⟨y⟩, _⟩
  rw [Vector.compare_eq_compare_toList, Vector.compare_eq_compare_toList]
  dsimp
  apply List.symm

theorem CMvMonomial.le_trans :
  ∀ {x y z : CMvMonomial n},
    compare x y ≠ Ordering.gt →
    compare y z ≠ Ordering.gt →
    compare x z ≠ Ordering.gt
:= by
  intros x y z
  rcases x with ⟨⟨x⟩, _⟩
  rcases y with ⟨⟨y⟩, _⟩
  rcases z with ⟨⟨z⟩, _⟩
  rw [Vector.compare_eq_compare_toList, Vector.compare_eq_compare_toList]
  dsimp only []
  intros h_le₁ h_le₂
  -- rw [compare_le_iff_le (a := x) (b := y)] at h_le₁
  sorry

instance : TransCmp (λ x1 x2 : CMvMonomial n => compare x1 x2) where
  symm := CMvMonomial.symm
  le_trans := sorry


-- instance : LE (CMvMonomial n × R) where
--   le a b := a.1 ≤ b.1
-- instance : LT (CMvMonomial n × R) where
--   lt a b := a.1 < b.1
-- instance : BEq (CMvMonomial n × R) where
--   beq a b := a.1 = b.1
-- instance : Ord (CMvMonomial n × R) where
--   compare a b := compare a.1 b.1

-- instance : LawfulOrd (CMvMonomial n × R) where
--   symm := sorry
--   le_trans := sorry
--   cmp_iff_beq := sorry
--   cmp_iff_lt := sorry
--   cmp_iff_le := sorry

-- instance : TransCmp (λ x1 x2 : (CMvMonomial n × Unit) => compare x1.1 x2.1) where
--   symm := sorry
--   le_trans := sorry

instance : TransCmp (λ x1 x2 : (CMvMonomial n × R) => compare x1.1 x2.1) where
  symm := by intros; apply CMvMonomial.symm
  le_trans := sorry

syntax "#m[" withoutPosition(term,*,?) "]" : term

open Lean in
macro_rules
  | `(#m[ $elems,* ]) => `(#v[ $elems,* ])

instance : Repr (CMvMonomial n) where
  reprPrec m _ :=
    let indexed := (Array.range m.size).zip m.1
    let toFormat : Std.ToFormat (ℕ × ℕ) :=
      ⟨λ (i, p) => "X" ++ repr i ++ "^" ++ repr p⟩
    @Std.Format.joinSep _ toFormat indexed.toList " * "

def myMonomial : CMvMonomial 3 := #m[4, 2, 5]

-- #eval myMonomial

example : CMvMonomial 2 := #m[1, 2]

def totalDegree (m : CMvMonomial n) : ℕ := m.foldl Nat.add 0

abbrev GrevlexOrderingVector n := Vector ℤ (n + 1)

def orderingVector (m : CMvMonomial n) : GrevlexOrderingVector n :=
  ⟨ #[.ofNat (totalDegree m)] ++ m.toArray.reverse.map .negOfNat
  , by simp [Nat.add_comm]
  ⟩

-- #eval orderingVector #m[]
-- #eval orderingVector #m[1, 2, 3]

def grevlex (m1 m2 : CMvMonomial n) : Ordering :=
  compare (totalDegree m1) (totalDegree m2) |>.then
    (compareOfLessAndEq m2 m1)

/-- Polynomial in `n` variables with coefficients in `R`. -/
abbrev UnlawfulCMvPolynomial n R [CommSemiring R] :=
  Batteries.RBMap (CMvMonomial n) R compare

def UnlawfulCMvPolynomial.isNoZeroCoef [CommSemiring R]
  (p : UnlawfulCMvPolynomial n R) : Prop
:=
  ∀ m, p.find? m ≠ some 0

def CMvPolynomial n R [CommSemiring R] :=
  { p : UnlawfulCMvPolynomial n R // p.isNoZeroCoef}

def CMvPolynomial.monomialsList [CommSemiring R] (p : CMvPolynomial n R) :=
  p.val.toList.unzip.1

def CMvPolynomial.find? [CommSemiring R]
  (p : CMvPolynomial n R)
  (m : CMvMonomial n) :
  Option R
:=
  p.val.find? m

def CMvPolynomial.findD [CommSemiring R]
  (p : CMvPolynomial n R) (m : CMvMonomial n) (v₀ : R) : R
:=
  (p.find? m).getD v₀

-- #check (compare : (CMvMonomial 1) → (CMvMonomial 1) → Ordering)
-- #check Vector.compare

instance [Repr R] [CommSemiring R] : Repr (UnlawfulCMvPolynomial n R) where
  reprPrec p _ :=
    let toFormat : Std.ToFormat (CMvMonomial n × R) :=
      ⟨λ (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

def myPolynomial : UnlawfulCMvPolynomial 3 ℕ :=
  [⟨#m[1, 2, 1], 5⟩, ⟨#m[3, 2, 0], 5⟩].toRBMap compare

-- #eval myPolynomial
