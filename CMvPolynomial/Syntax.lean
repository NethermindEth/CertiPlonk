import CMvPolynomial.CMvPolynomial
import Batteries.Data.RBMap.Lemmas

import Lean
open Lean Batteries

-- declare_syntax_cat polynomial

-- syntax num : polynomial

-- partial def denotePolynomial : TSyntax `polynomial → UnlawfulCMvPolynomial n ℕ
--   | `(polynomial| $x:num) => UnlawfulCMvPolynomial.constant x.getNat
--   | _ => .empty

-- def test : Elab.TermElabM (UnlawfulCMvPolynomial n ℕ) := do
--   let stx ← `(polynomial| 17)
--   pure (denotePolynomial stx)

-- #eval @test 3 -- 11

instance : Neg (LawfulCMvPolynomial n ℤ) where
  neg p := (LawfulCMvPolynomial.constant 0).sub p

def X /- [CommSemiring R] [BEq R] [LawfulBEq R] -/ (i : ℕ) :
  LawfulCMvPolynomial (i + 1) ℤ
:=
  let monomial := Vector.replicate i 0 |>.push 1
  LawfulCMvPolynomial.fromUnlawful <| RBMap.single monomial 1

instance [CommRing R] [BEq R] [LawfulBEq R] :
  HAdd
    (LawfulCMvPolynomial n₁ R)
    (LawfulCMvPolynomial n₂ R)
    (LawfulCMvPolynomial (max n₁ n₂) R)
where
  hAdd p₁ p₂ := by
    have : ∀ a b : ℕ, a ⊔ (a ⊔ b) = a ⊔ b := by
      intro a b
      rw [←sup_assoc]
      rw [sup_eq_right.2 (le_refl a)]
    have p₁ := p₁.extend (max n₁ n₂)
    have p₂ := p₂.extend (max n₁ n₂)
    rw [this] at p₁
    rw [sup_comm n₁ n₂, this, sup_comm] at p₂
    exact p₁.add p₂

instance [CommRing R] [BEq R] [LawfulBEq R] :
  HSub
    (LawfulCMvPolynomial n₁ R)
    (LawfulCMvPolynomial n₂ R)
    (LawfulCMvPolynomial (max n₁ n₂) R)
where
  hSub p₁ p₂ := by
    have : ∀ a b : ℕ, a ⊔ (a ⊔ b) = a ⊔ b := by
      intro a b
      rw [←sup_assoc]
      rw [sup_eq_right.2 (le_refl a)]
    have p₁ := p₁.extend (max n₁ n₂)
    have p₂ := p₂.extend (max n₁ n₂)
    rw [this] at p₁
    rw [sup_comm n₁ n₂, this, sup_comm] at p₂
    exact p₁.sub p₂

instance [CommRing R] [BEq R] [LawfulBEq R] :
  HMul
    (LawfulCMvPolynomial n₁ R)
    (LawfulCMvPolynomial n₂ R)
    (LawfulCMvPolynomial (max n₁ n₂) R)
where
  hMul p₁ p₂ := by
    have : ∀ a b : ℕ, a ⊔ (a ⊔ b) = a ⊔ b := by
      intro a b
      rw [←sup_assoc]
      rw [sup_eq_right.2 (le_refl a)]
    have p₁ := p₁.extend (max n₁ n₂)
    have p₂ := p₂.extend (max n₁ n₂)
    rw [this] at p₁
    rw [sup_comm n₁ n₂, this, sup_comm] at p₂
    exact p₁.mul p₂

instance [CommRing R] [BEq R] [LawfulBEq R] :
  HPow
    (LawfulCMvPolynomial n R)
    ℕ
    (LawfulCMvPolynomial n R)
where
  hPow p₁ exp := exp.iterate p₁.mul 1

def polyCoe [CommRing R] [BEq R] (p : LawfulCMvPolynomial n R) :
  (LawfulCMvPolynomial n.succ R)
:= by
  let p' := p.extend n.succ
  rw [sup_eq_right.2 (Nat.le_succ n)] at p'
  exact p'

instance [CommRing R] [BEq R] :
  Coe (LawfulCMvPolynomial n R) (LawfulCMvPolynomial n.succ R)
where
  coe := polyCoe

#eval (0 : LawfulCMvPolynomial 0 ℤ)
#eval (0 : LawfulCMvPolynomial 5 ℤ)
#eval! (2 : LawfulCMvPolynomial 0 ℤ)
#eval! (-2 : LawfulCMvPolynomial 1 ℤ)
#eval! (-2 : LawfulCMvPolynomial 3 ℤ)
#eval! (2 * -2 : LawfulCMvPolynomial 3 ℤ)
#eval! (X 1 ^ 1 : LawfulCMvPolynomial _ ℤ)
-- #eval! (X 1 : LawfulCMvPolynomial 1 ℤ)
#eval! (X 1 : LawfulCMvPolynomial 3 ℤ)
#eval! (X 1 - X 1 : LawfulCMvPolynomial 3 ℤ)
#eval! (2 * X 3 : LawfulCMvPolynomial 4 ℤ)
#eval! (X 1 * 2 * X 1 : LawfulCMvPolynomial 2 ℤ)
#eval! (2 * X 0 + 2 * X 0 ^ 2 + X 1 ^ 2 : LawfulCMvPolynomial 2 ℤ)
-- #eval! (2 * X 0 + 2 * X 0 ^ 2 + X 1 ^ 2 : LawfulCMvPolynomial 1 ℤ)
#eval! (2 * X 0 + 2 * X 0 ^ 2 + X 1 ^ 2 : LawfulCMvPolynomial 5 ℤ)

def i' : LawfulCMvPolynomial 1 ℤ :=
  -1 * X 0 ^ 0 + 1 * X 0 ^ 2
def p₁' : LawfulCMvPolynomial 1 ℤ :=
  -1 * X 0 ^ 0 + -2 * X 0 ^1
def p₂' : LawfulCMvPolynomial 1 ℤ :=
  2 * X 0 ^ 0 + 2 * X 0 ^ 1
def t' : LawfulCMvPolynomial 1 ℤ :=
  2 * X 0 ^ 0 + 1 * X 0 ^ 1
def x' : LawfulCMvPolynomial 1 ℤ :=
  1 * X 0 ^ 1

#eval! i'.reduce t'
#eval! i'.sub (x'.mul t')
