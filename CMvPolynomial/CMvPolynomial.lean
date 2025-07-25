import CMvPolynomial.Lawful

namespace CPoly

open Std

abbrev CMvPolynomial (n : ℕ) R [Zero R] : Type := Lawful n R

variable {R : Type}

namespace CMvPolynomial

def coeff {R : Type} {n : ℕ} [Zero R] (m : CMvMonomial n) (p : CMvPolynomial n R) : R :=
  p.1[m]?.getD 0

attribute [grind=] coeff.eq_def

@[ext, grind ext]
theorem ext {n : ℕ} [Zero R] (p q : CMvPolynomial n R)
  (h : ∀ m, coeff m p = coeff m q) : p = q := by
  unfold coeff at h
  rcases p with ⟨p, hp⟩; rcases q with ⟨q, hq⟩
  congr
  apply ExtTreeMap.ext_getElem?
  grind

attribute [grind=] Option.some_inj

@[simp, grind=]
lemma fromUnlawful_zero {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] :
  Lawful.fromUnlawful 0 = (0 : Lawful n R) := by
  unfold Lawful.fromUnlawful
  grind

end CMvPolynomial

end CPoly
