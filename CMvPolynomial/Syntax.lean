import CMvPolynomial.LawfulCMvPolynomial
import CMvPolynomial.UnlawfulCMvPolynomial
import Lean
open Lean Std

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
  LawfulCMvPolynomial.fromUnlawful <| ExtTreeMap.ofList [(monomial, (1 : ℤ))]

def align [Zero R] [BEq R] [LawfulBEq R]
  (p₁ : LawfulCMvPolynomial n₁ R) (p₂ : LawfulCMvPolynomial n₂ R) :
  LawfulCMvPolynomial (n₁ ⊔ n₂) R × LawfulCMvPolynomial (n₁ ⊔ n₂) R :=
  letI sup := n₁ ⊔ n₂
  (
    cast (by congr 1; grind) (p₁.extend sup),
    cast (by congr 1; grind) (p₂.extend sup)
  )

def liftPoly [Zero R] [BEq R] [LawfulBEq R]
  (f : LawfulCMvPolynomial (n₁ ⊔ n₂) R →
       LawfulCMvPolynomial (n₁ ⊔ n₂) R →
       LawfulCMvPolynomial (n₁ ⊔ n₂) R)
  (p₁ : LawfulCMvPolynomial n₁ R) (p₂ : LawfulCMvPolynomial n₂ R) : LawfulCMvPolynomial (n₁ ⊔ n₂) R :=
  Function.uncurry f (align p₁ p₂)

instance [CommRing R] [BEq R] [LawfulBEq R] :
  HAdd
    (LawfulCMvPolynomial n₁ R)
    (LawfulCMvPolynomial n₂ R)
    (LawfulCMvPolynomial (n₁ ⊔ n₂) R)
where
  hAdd p₁ p₂ := liftPoly (·+·) p₁ p₂

instance [CommRing R] [BEq R] [LawfulBEq R] :
  HSub
    (LawfulCMvPolynomial n₁ R)
    (LawfulCMvPolynomial n₂ R)
    (LawfulCMvPolynomial (n₁ ⊔ n₂) R)
where
  hSub p₁ p₂ := liftPoly (·-·) p₁ p₂

instance [CommRing R] [BEq R] [LawfulBEq R] :
  HMul
    (LawfulCMvPolynomial n₁ R)
    (LawfulCMvPolynomial n₂ R)
    (LawfulCMvPolynomial (max n₁ n₂) R)
where
  hMul p₁ p₂ := liftPoly (·*·) p₁ p₂

instance [CommRing R] [BEq R] [LawfulBEq R] :
  HPow
    (LawfulCMvPolynomial n R)
    ℕ
    (LawfulCMvPolynomial n R)
where
  hPow p₁ exp := exp.iterate p₁.mul 1

def polyCoe [CommRing R] [BEq R] [LawfulBEq R] (p : LawfulCMvPolynomial n R) :
  (LawfulCMvPolynomial n.succ R) := cast (by simp) (p.extend n.succ)

instance [CommRing R] [BEq R] [LawfulBEq R]:
  Coe (LawfulCMvPolynomial n R) (LawfulCMvPolynomial n.succ R)
where
  coe := polyCoe

/-
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
-/

#min_imports
