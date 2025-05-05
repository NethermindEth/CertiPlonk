import Batteries.Data.RBMap

import Mathlib.Algebra.Ring.Nat
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.List.Lex

import Aesop

open Batteries

def hello := "world"

#check List.le

/-- Monomial in `n` variables. `#v[e₀, e₁, e₂]` denotes X₀^e₀ * X₁^e₁ * X₂^e₂ -/
abbrev CMvMonomial n := Vector ℕ n

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

def grevlex (m₁ m₂ : CMvMonomial n) : Ordering :=
  compare (totalDegree m₁) (totalDegree m₂) |>.then
    (compareOfLessAndEq m₂ m₁)

def simpleCmp [LT α] [DecidableLT α] [BEq α] (a₁ a₂ : α) : Ordering :=
  if a₁ == a₂ then .eq else
    if a₁ < a₂ then .lt else
      .gt

instance : Std.Irrefl fun (x1 x2 : ℕ) => x1 < x2 := by
  constructor
  apply Nat.lt_irrefl

instance : Std.Total fun (x1 x2 : ℕ) => ¬x1 < x2 := by
  constructor
  intros a b
  rw [Nat.not_lt, Nat.not_lt]
  apply Nat.le_or_le b a

instance : Std.Asymm fun (x1 x2 : ℕ) => x1 < x2 := by
  constructor
  intros a b h_lt
  simp only [not_lt]
  rw [Nat.le_iff_lt_or_eq]
  simp [h_lt]

instance :
  Trans
    (fun (x1 x2 : ℕ) => ¬x1 < x2)
    (fun x1 x2 => ¬x1 < x2)
    fun (x1 x2 : ℕ) => ¬x1 < x2
:= by
  constructor
  intros a b c h₁ h₂
  simp only [not_lt] at *
  apply Nat.le_trans (m := b) <;> simp [*]

def monomial_symm : ∀ (x y : CMvMonomial n),
  (simpleCmp x y).swap = simpleCmp y x
:= by
  intros x y
  unfold simpleCmp
  split
  case isTrue h =>
    simp
    simp only [beq_iff_eq] at h
    subst h
    simp only [↓reduceIte]
  case isFalse h =>
    simp [neq_of_not_iff] at h
    simp_all only [beq_iff_eq]
    have h' : y ≠ x := by
      intro contra
      subst contra
      contradiction
    simp [h']
    split
    case isTrue h_lt =>
      have h' : ¬ y < x := by
        apply Vector.lt_asymm (i := _)
        · exact h_lt
        · constructor; intros; simp [Nat.lt_asymm, *]
      simp [Ordering.swap_lt]
      split <;> trivial
    case isFalse h_lt =>
      simp_all only [ne_eq, Vector.not_lt, Ordering.swap_gt]
      split
      next h_1 => simp_all only
      next h_1 =>
        simp_all only [Vector.not_lt, reduceCtorEq]
        rw [Vector.le_iff_lt_or_eq (xs := x)] at h_1
        rw [Vector.le_iff_lt_or_eq (xs := y)] at h_lt
        cases h_lt <;> cases h_1 <;> try contradiction
        · apply Vector.lt_irrefl x
          apply Vector.lt_trans (ys := y) <;> simp [*]

lemma monomial_eq : ∀ m₁ m₂ : CMvMonomial n,
  simpleCmp m₁ m₂ = .eq → m₁ = m₂
:= by
  unfold simpleCmp
  intros m₁ m₂ h
  split at h
  case isTrue h_eq => simp_all only [beq_iff_eq]
  case isFalse h_neq =>
    simp_all only [beq_iff_eq]
    split at h
    next h_1 => simp_all only [reduceCtorEq]
    next h_1 => simp_all only [Vector.not_lt, reduceCtorEq]


lemma monomial_not_gt : ∀ m₁ m₂ : CMvMonomial n,
  simpleCmp m₁ m₂ ≠ .gt ↔ m₁ ≤ m₂
:= by
  unfold simpleCmp; simp only [beq_iff_eq]
  intro m₁ m₂
  constructor
  · intro h_cmp
    split at h_cmp
    case isTrue h_eq => subst h_eq; apply Vector.le_refl
    case isFalse h_neq =>
      split at h_cmp
      case isTrue h_lt => simp only [Vector.le_iff_lt_or_eq, h_lt, true_or]
      case isFalse => contradiction
  · intro h_le
    split
    case mpr.isTrue => simp
    case mpr.isFalse h_neq =>
      have h_lt : m₁ < m₂ := by
        rw [Vector.le_iff_lt_or_eq] at h_le
        cases h_le
        · simp only [*]
        · contradiction
      simp [*]

def monomial_le_trans : ∀ {x y z : CMvMonomial n},
  simpleCmp x y ≠ Ordering.gt →
  simpleCmp y z ≠ Ordering.gt →
  simpleCmp x z ≠ Ordering.gt
:= by
  intros x y z h_lt₁ h_lt₂
  have h_lt₁' := (monomial_not_gt x y).1 h_lt₁
  have h_lt₂' := (monomial_not_gt y z).1 h_lt₂
  have h_lt₃ : x ≤ z := by
    apply Vector.le_trans (ys := y) <;> simp [*]
  rw [monomial_not_gt x z]
  apply Vector.le_trans (ys := y) <;> simp only [*]


instance : TransCmp (λ x1 x2 : CMvMonomial n => simpleCmp x1 x2) where
  symm := monomial_symm
  le_trans := monomial_le_trans

instance : TransCmp (λ x1 x2 : (CMvMonomial n × R) => simpleCmp x1.1 x2.1) where
  symm := by
    intros
    apply monomial_symm
  le_trans := by
    intros x y z
    apply monomial_le_trans

/-- Polynomial in `n` variables with coefficients in `R`. -/
abbrev UnlawfulCMvPolynomial n R [CommSemiring R] :=
  Batteries.RBMap (CMvMonomial n) R simpleCmp

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
  [⟨#m[1, 2, 1], 5⟩, ⟨#m[3, 2, 0], 5⟩].toRBMap simpleCmp

-- #eval myPolynomial
