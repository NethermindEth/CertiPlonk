import Batteries.Data.RBMap.Basic
import CMvPolynomial.Instances
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Lattice

open Batteries

/-- Monomial in `n` variables. `#v[e₀, e₁, e₂]` denotes X₀^e₀ * X₁^e₁ * X₂^e₂ -/
abbrev CMvMonomial (n : ℕ) : Type := Vector ℕ n

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

def one : CMvMonomial n := Vector.replicate n 0

instance : One (CMvMonomial n) := ⟨one⟩

def mul : CMvMonomial n → CMvMonomial n → CMvMonomial n :=
  Vector.zipWith .add

instance : Mul (CMvMonomial n) := ⟨mul⟩

def divides (m₁ : CMvMonomial n) (m₂ : CMvMonomial n) : Bool :=
  Vector.all (Vector.zipWith (flip Nat.ble) m₁ m₂) (· == true)

instance : Dvd (CMvMonomial n) := ⟨fun m₁ m₂ ↦ divides m₁ m₂⟩ -- Do not eta.

instance {m₁ m₂ : CMvMonomial n} : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance

/--
  The polynomial `m₁ / m₂`.

  The result makes sense assuming  `m₁ | m₂`.
-/
def div (m₁ m₂ : CMvMonomial n) : CMvMonomial n :=
  Vector.zipWith Nat.sub m₁ m₂

instance : Div (CMvMonomial n) := ⟨div⟩

instance : Ord (CMvMonomial n) := ⟨fun a b ↦ compareOfLessAndEq a b⟩

section

variable {n : ℕ} {a₁ a₂ : CMvMonomial n}

@[simp]
lemma simpleCmp_iff : compare a₁ a₂ = .eq ↔ a₁ = a₂ :=
  compareOfLessAndEq_eq_eq Vector.le_refl Vector.not_le

@[simp]
lemma simpleCmp_lt : compare a₁ a₂ = .lt ↔ a₁ < a₂ :=
  Batteries.compareOfLessAndEq_eq_lt

lemma lt_iff_not_gt_and_ne {x y : CMvMonomial n} :
  x < y ↔ ¬y < x ∧ x ≠ y := by
  rw [Vector.not_lt_iff_ge, Vector.le_iff_lt_or_eq]
  aesop (add simp Vector.lt_irrefl)

lemma symm {x y : CMvMonomial n} : compare y x = (compare x y).swap :=
  compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne (fun _ _ ↦ lt_iff_not_gt_and_ne)

@[simp]
lemma simpleCmp_eq_gt : compare a₁ a₂ = .gt ↔ a₁ > a₂ :=
  compareOfLessAndEq_eq_gt_of_lt_iff_not_gt_and_ne fun _ _ ↦ lt_iff_not_gt_and_ne

@[simp]
lemma not_gt : compare a₁ a₂ ≠ .gt ↔ a₁ ≤ a₂ := by simp

@[simp]
lemma isLE_simple_cmp : (compare a₁ a₂).isLE = true ↔ a₁ ≤ a₂ := by
  aesop (add simp Ordering.isLE)

lemma le_trans {c : CMvMonomial n} :
  compare a b ≠ Ordering.gt →
  compare b c ≠ Ordering.gt →
  compare a c ≠ Ordering.gt := by simp; exact Vector.le_trans

end

end CMvMonomial

variable {n : ℕ}

instance : Std.TransOrd (CMvMonomial n) where
  eq_swap := CMvMonomial.symm
  isLE_trans := by aesop (add safe forward Vector.le_trans)

instance : Std.LawfulEqOrd (CMvMonomial n) where
  eq_of_compare h := by simpa using h

def MonoR n R := CMvMonomial n × R

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
