import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Nat.Defs

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

abbrev Term n R [CommSemiring R] := CMvMonomial n × R

def myMonomial : CMvMonomial 3 := #m[4, 2, 5]

-- #eval myMonomial

example : CMvMonomial 2 := #m[1, 2]

def totalDegree (m : CMvMonomial n) : ℕ := m.foldl Nat.add 0

def CMvMonomial.mul : CMvMonomial n → CMvMonomial n → CMvMonomial n :=
  Vector.zipWith .add

def CMvMonomial.divides (m₁ : CMvMonomial n) (m₂ : CMvMonomial n) : Bool :=
  Vector.all (Vector.zipWith (flip Nat.blt) m₁ m₂) (· == true)

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
