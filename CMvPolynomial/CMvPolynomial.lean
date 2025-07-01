import CMvPolynomial.LawfulCMvPolynomial

open Std

abbrev CMvPolynomial (n : ℕ) R [Zero R] : Type := LawfulCMvPolynomial n R

variable {R : Type}

namespace CMvPolynomial

def coeff {R : Type} {n : ℕ} [Zero R] (m : CMvMonomial n) (p : CMvPolynomial n R) : R :=
  p.1[m]?.getD 0

@[ext]
theorem ext {n : ℕ} [Zero R] (p q : CMvPolynomial n R)
  (h : ∀ m, coeff m p = coeff m q) : p = q := by
  unfold coeff at h
  rcases p with ⟨p, hp⟩; rcases q with ⟨q, hq⟩
  congr
  apply ExtTreeMap.ext_getElem?
  grind

end CMvPolynomial

namespace CMvPolynomial

end CMvPolynomial
