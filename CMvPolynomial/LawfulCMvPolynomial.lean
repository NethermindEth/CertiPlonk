import Mathlib.Algebra.Lie.OfAssociative
import CMvPolynomial.UnlawfulCMvPolynomial

def LawfulCMvPolynomial n R [CommSemiring R] :=
  { p : UnlawfulCMvPolynomial n R // p.isNoZeroCoef}

def LawfulCMvPolynomial.neg [CommRing R] [BEq R]
  (p : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  { val := p.val.neg
    property := sorry
  }

def LawfulCMvPolynomial.add [CommSemiring R] [BEq R]
  (p₁ : LawfulCMvPolynomial n R)
  (p₂ : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  { val := UnlawfulCMvPolynomial.add p₁.val p₂.val |>.filter (λ _ c => ¬ c == 0)
    property := sorry
  }

def LawfulCMvPolynomial.sub [CommRing R] [BEq R]
  (p₁ : LawfulCMvPolynomial n R)
  (p₂ : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  LawfulCMvPolynomial.add p₁ p₂.neg

def LawfulCMvPolynomial.mul [CommRing R] [BEq R]
  (p₁ : LawfulCMvPolynomial n R)
  (p₂ : LawfulCMvPolynomial n R) :
  LawfulCMvPolynomial n R
:=
  { val := UnlawfulCMvPolynomial.mul p₁.val p₂.val |>.filter (λ _ c => ¬ c == 0)
    property := sorry
  }

def LawfulCMvPolynomial.reduce [CommRing R] [BEq R]
  (p : LawfulCMvPolynomial n R)
  (d : LawfulCMvPolynomial n R) :
  Option (LawfulCMvPolynomial n R)
:= do
  let up ← UnlawfulCMvPolynomial.reduce p.val d.val
  pure
    { val := up.filter (λ _ c => ¬ c == 0)
      property := sorry
    }

def LawfulCMvPolynomial.find? [CommSemiring R]
  (p : LawfulCMvPolynomial n R)
  (m : CMvMonomial n) :
  Option R
:=
  p.val.find? m

def LawfulCMvPolynomial.monomialsList [CommSemiring R]
  (p : LawfulCMvPolynomial n R)
:=
  p.val.toList.unzip.1

def LawfulCMvPolynomial.findD [CommSemiring R]
  (p : LawfulCMvPolynomial n R) (m : CMvMonomial n) (v₀ : R) : R
:=
  (p.find? m).getD v₀

-- #eval myPolynomial

def extEquiv {n R} [CommSemiring R] : Setoid (LawfulCMvPolynomial n R) where
  r a b := ∀ x, a.find? x = b.find? x
  iseqv := by constructor <;> (intros; simp only [*])

def p : LawfulCMvPolynomial 2 ℤ where -- 2 * X0^2 * X1^3
  val := [⟨#m[2, 3], 2⟩].toRBMap simpleCmp
  property := by sorry

def d : LawfulCMvPolynomial 2 ℤ where -- X0^2 * X1^0 + X0^2 * X1^2
  val := [⟨#m[2, 2], 1⟩, ⟨#m[2, 0], 1⟩].toRBMap simpleCmp
  property := sorry

#eval! p
#eval! d
#eval! p.reduce d -- some -2 * X0^2 * X1^1
