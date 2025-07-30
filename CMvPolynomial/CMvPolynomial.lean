import CMvPolynomial.Lawful

namespace CPoly

open Std

abbrev CMvPolynomial (n : ℕ) R [Zero R] : Type := Lawful n R

variable {R : Type} {n : ℕ}

namespace CMvPolynomial

def coeff {R : Type} [Zero R] (m : CMvMonomial n) (p : CMvPolynomial n R) : R :=
  p.1[m]?.getD 0

@[ext]
theorem ext [Zero R] (p q : CMvPolynomial n R)
  (h : ∀ m, coeff m p = coeff m q) : p = q := by
  unfold coeff at h
  rcases p with ⟨p, hp⟩; rcases q with ⟨q, hq⟩
  congr
  apply ExtTreeMap.ext_getElem?
  grind

end CMvPolynomial

end CPoly
