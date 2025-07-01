import Batteries.Data.RBMap.Basic
import CMvPolynomial.Instances
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Lattice

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

namespace CMvMonomial

variable {n : ℕ}

def extend (n' : ℕ) (m : CMvMonomial n) : CMvMonomial (max n n') :=
  cast (have : n + (n' - n) = n ⊔ n' :=
          if h : n' ≤ n
          then by simp [h]
          else by have := le_of_lt (not_le.1 h)
                  rw [sup_of_le_right this, Nat.add_sub_cancel' this]
        this ▸ rfl)
       (m ++ Vector.replicate (n' - n) 0)

def totalDegree (m : CMvMonomial n) : ℕ := m.sum

/-
  Ref: @Andrei @Julian

  What notion of `zero` makes sense; here `0^n` is `Πᵢ X<i>^0 = 1`, as below.
-/

def one : CMvMonomial n := Vector.replicate n 0

instance : One (CMvMonomial n) := ⟨one⟩

def mul : CMvMonomial n → CMvMonomial n → CMvMonomial n :=
  Vector.zipWith .add

instance : Mul (CMvMonomial n) := ⟨mul⟩

/-
  Ref: @Andrei @Julian

  Which `HMul`s do we want? Needs thought.
-/

def divides (m₁ : CMvMonomial n) (m₂ : CMvMonomial n) : Bool :=
  Vector.all (Vector.zipWith (flip Nat.ble) m₁ m₂) (· == true)

instance : Dvd (CMvMonomial n) := ⟨fun m₁ m₂ ↦ divides m₁ m₂⟩ -- Do not eta.

instance {m₁ m₂ : CMvMonomial n} : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance

/--
  Ref: @Andrei @Julian

  I would probably suggest *not* spooning this into `Option`.
  Two alternatives:
  - a) return `Vector.zipWith Nat.sub`, and sature silly subterms to zero.
  - b) return `Vector.zipWith Nat.sub` if m₁ | m₂, _zero_ otherwise.
  
  Then we have statements assuming `m₁ | m₂ → P` for most `P` regarding `div`.
-/
def div (m₁ : CMvMonomial n) (m₂ : CMvMonomial n) :
  Option (CMvMonomial n)
:=
  if m₁.divides m₂ then Vector.zipWith Nat.sub m₁ m₂ else none

/--
  Ref: @Andrei @Julian

  - Depending on the answer to the question wrt. `div` above, we might want `Div` as well.
  - Furthermore, which other `HDiv`s do we want?
-/
instance : HDiv (CMvMonomial n) (CMvMonomial n) (Option (CMvMonomial n)) := ⟨div⟩

abbrev simpleCmp (a₁ a₂ : CMvMonomial n) : Ordering :=
  compareOfLessAndEq a₁ a₂

@[simp]
lemma simpleCmp_iff : simpleCmp a₁ a₂ = .eq ↔ a₁ = a₂ :=
  compareOfLessAndEq_eq_eq Vector.le_refl Vector.not_le

lemma lt_iff_not_gt_and_ne {x y : CMvMonomial n} :
  x < y ↔ ¬y < x ∧ x ≠ y := by
  rw [Vector.not_lt_iff_ge, Vector.le_iff_lt_or_eq]
  aesop (add simp Vector.lt_irrefl)

lemma symm {x y : CMvMonomial n} : (simpleCmp x y).swap = simpleCmp y x :=
  (compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne (fun _ _ ↦ lt_iff_not_gt_and_ne)).symm

@[simp]
lemma simpleCmp_eq_gt : simpleCmp m₁ m₂ = .gt ↔ m₁ > m₂ :=
  compareOfLessAndEq_eq_gt_of_lt_iff_not_gt_and_ne fun _ _ ↦ lt_iff_not_gt_and_ne

@[simp]
lemma not_gt {m₁ m₂ : CMvMonomial n} : simpleCmp m₁ m₂ ≠ .gt ↔ m₁ ≤ m₂ := by simp

lemma le_trans {x y z : CMvMonomial n} :
  simpleCmp x y ≠ Ordering.gt →
  simpleCmp y z ≠ Ordering.gt →
  simpleCmp x z ≠ Ordering.gt := by simp; exact Vector.le_trans

end CMvMonomial

instance :
  TransCmp fun x1 x2 : CMvMonomial n ↦ CMvMonomial.simpleCmp x1 x2
where
  symm := fun _ _ ↦ CMvMonomial.symm
  le_trans := CMvMonomial.le_trans

instance :
  TransCmp fun x1 x2 : (CMvMonomial n × R) ↦ CMvMonomial.simpleCmp x1.1 x2.1
where
  symm := fun _ _ ↦ CMvMonomial.symm
  le_trans := CMvMonomial.le_trans

lemma CMvMonomial.list_pairwise_lt_nodup {l : List (CMvMonomial n × R)} :
  l.Pairwise (RBNode.cmpLT (CMvMonomial.simpleCmp ·.1 ·.1)) → l.Nodup := by
  induction' l with hd tl ih
  · simp
  · aesop (add simp RBNode.cmpLT) (config := {warnOnNonterminal := false})
    exact absurd (left _ _ a) (Vector.lt_irrefl _)

def MonoR n R [CommSemiring R] := CMvMonomial n × R

namespace MonoR

instance [DecidableEq R] : DecidableEq (CMvMonomial n × R) :=
  instDecidableEqProd

section

variable [CommSemiring R]

instance [Repr R] : Repr (MonoR n R) where
  reprPrec
    | (m, c), _ => repr c ++ " * " ++ repr m

def constant (c : R) : MonoR n R :=
  (CMvMonomial.one, c)

def divides [HMod R R R] [BEq R]
  (t₁ : MonoR n R)
  (t₂ : MonoR n R) :
  Bool
:=
  t₁.1 ∣ t₂.1 ∧ t₁.2 % t₂.2 == 0

instance [HMod R R R] [BEq R] : Dvd (MonoR n R) := ⟨fun t₁ t₂ ↦ divides t₁ t₂⟩ -- Do not eta.

instance [HMod R R R] [BEq R] {t₁ t₂ : MonoR n R} : Decidable (t₁ ∣ t₂) := by
  dsimp [(·∣·)]
  infer_instance

end

end MonoR

abbrev GrevlexOrderingVector n := Vector ℤ (n + 1)

def orderingVector (m : CMvMonomial n) : GrevlexOrderingVector n :=
  ⟨ #[.ofNat m.totalDegree] ++ m.toArray.reverse.map .negOfNat
  , by simp +arith
  ⟩

def grevlex (m₁ m₂ : CMvMonomial n) : Ordering :=
  compare m₁.totalDegree m₂.totalDegree |>.then
    (compareOfLessAndEq m₂ m₁)
