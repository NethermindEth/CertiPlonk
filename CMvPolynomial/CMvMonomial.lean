import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Batteries.Classes.Order
import Batteries.Data.RBMap
import CMvPolynomial.Instances

open Batteries

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
      ⟨λ (i, p) ↦ "X" ++ repr i ++ "^" ++ repr p⟩
    @Std.Format.joinSep _ toFormat indexed.toList " * "

def CMvMonomial.extend (n' : ℕ) (m : CMvMonomial n) : CMvMonomial (max n n') :=
  if h_le : n' ≤ n then by
    have : max n n' = n := by
      rw [sup_eq_left]
      exact h_le
    rw [this]
    exact m
  else by
    let diff := n' - n
    have : max n n' = n + diff := by
      unfold diff
      simp only [not_le] at h_le
      have h_le : n ≤ n' := by
        rw [le_iff_lt_or_eq]
        left; exact h_le
      rw [sup_comm, sup_eq_left.2 h_le]
      rw [←Nat.add_sub_assoc h_le]
      simp
    rw [this]
    exact m ++ (Vector.replicate diff 0)

abbrev Term n R [CommSemiring R] := CMvMonomial n × R

instance [DecidableEq R] : DecidableEq (CMvMonomial n × R) :=
  instDecidableEqProd

instance [CommSemiring R] [Repr R] : Repr (Term n R) where
  reprPrec
    | (m, c), _ => repr c ++ " * " ++ repr m

def myMonomial : CMvMonomial 3 := #m[4, 2, 5]

-- #eval myMonomial

example : CMvMonomial 2 := #m[1, 2]

def totalDegree (m : CMvMonomial n) : ℕ := m.foldl Nat.add 0

def CMvMonomial.one : CMvMonomial n := Vector.replicate n 0

def Term.constant [CommSemiring R] (c : R) : Term n R :=
  (CMvMonomial.one, c)

def CMvMonomial.mul : CMvMonomial n → CMvMonomial n → CMvMonomial n :=
  Vector.zipWith .add

def CMvMonomial.divides (m₁ : CMvMonomial n) (m₂ : CMvMonomial n) : Bool :=
  Vector.all (Vector.zipWith (flip Nat.ble) m₁ m₂) (· == true)

def CMvMonomial.div (m₁ : CMvMonomial n) (m₂ : CMvMonomial n) :
  Option (CMvMonomial n)
:=
  if m₁.divides m₂ then Vector.zipWith Nat.sub m₁ m₂ else none

def Term.divides [CommSemiring R] [HMod R R R] [BEq R]
  (t₁ : Term n R)
  (t₂ : Term n R) :
  Bool
:=
  t₁.1.divides t₂.1 ∧ t₁.2 % t₂.2 == 0

#eval CMvMonomial.mul #m[2, 2, 0] #m[0, 1, 5]

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

abbrev simpleCmp (a₁ a₂ : CMvMonomial n) : Ordering :=
  compareOfLessAndEq a₁ a₂

lemma simpleCmp_eq : simpleCmp a₁ a₂ = .eq → a₁ = a₂ := by
  unfold simpleCmp
  intro h
  rw [←compareOfLessAndEq_eq_eq]
  · assumption
  · apply Vector.le_refl
  · intro x y; apply Vector.not_le

theorem CMvMonomial.lt_iff_not_gt_and_ne : ∀ (x y : CMvMonomial n),
  x < y ↔ ¬y < x ∧ x ≠ y
:= by
  intro x y
  constructor
  · intro h
    constructor
    · simp [Vector.le_iff_lt_or_eq, h]
    · simp
      intro contra
      subst contra
      apply Vector.lt_irrefl x
      exact h
  · intro ⟨h₁, h₂⟩
    rw [Vector.not_lt] at h₁
    rw [Vector.le_iff_lt_or_eq] at h₁
    rcases h₁ with hl | hr
    · exact hl
    · contradiction

lemma CMvMonomial.symm : ∀ (x y : CMvMonomial n),
  (simpleCmp x y).swap = simpleCmp y x
:= by
  intros x y
  unfold simpleCmp
  rw [←compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne CMvMonomial.lt_iff_not_gt_and_ne]

lemma CMvMonomial.not_gt : ∀ m₁ m₂ : CMvMonomial n,
  simpleCmp m₁ m₂ ≠ .gt ↔ m₁ ≤ m₂
:= by
  intro m₁ m₂
  unfold simpleCmp
  simp
  rw [compareOfLessAndEq_eq_gt_of_lt_iff_not_gt_and_ne CMvMonomial.lt_iff_not_gt_and_ne]
  rw [Vector.not_lt]

lemma CMvMonomial.le_trans : ∀ {x y z : CMvMonomial n},
  simpleCmp x y ≠ Ordering.gt →
  simpleCmp y z ≠ Ordering.gt →
  simpleCmp x z ≠ Ordering.gt
:= by
  intros x y z h_lt₁ h_lt₂
  have h_lt₁' := (CMvMonomial.not_gt x y).1 h_lt₁
  have h_lt₂' := (CMvMonomial.not_gt y z).1 h_lt₂
  have h_lt₃ : x ≤ z := by
    apply Vector.le_trans (ys := y) <;> simp [*]
  rw [CMvMonomial.not_gt x z]
  apply Vector.le_trans (ys := y) <;> simp only [*]

instance : TransCmp (λ x1 x2 : CMvMonomial n ↦ simpleCmp x1 x2) where
  symm := CMvMonomial.symm
  le_trans := CMvMonomial.le_trans
