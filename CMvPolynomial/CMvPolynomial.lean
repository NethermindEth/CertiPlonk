import CMvPolynomial.LawfulCMvPolynomial

open Batteries

@[reducible]
def CMvPolynomial (n : ℕ) R [CommSemiring R] : Type :=
  Quotient (@LawfulCMvPolynomial.extEquiv n R _)

namespace CMvPolynomial

section R_CommSemiring
variable {n R} [CommSemiring R]

def add [BEq R] (p₁ : CMvPolynomial n R) (p₂ : CMvPolynomial n R) :
  CMvPolynomial n R
:=
  Quotient.map₂ LawfulCMvPolynomial.add sorry p₁ p₂

def mul [BEq R] (p₁ : CMvPolynomial n R) (p₂ : CMvPolynomial n R) :
  CMvPolynomial n R
:=
  Quotient.map₂ LawfulCMvPolynomial.mul sorry p₁ p₂

def find? (p : CMvPolynomial n R) (m : CMvMonomial n) : Option R :=
  Quotient.lift LawfulCMvPolynomial.find? valid p m
where
  valid := by
    intros p₁ p₂
    simp [instHasEquivOfSetoid, LawfulCMvPolynomial.extEquiv]
    intro h
    funext x
    simp [*]

def monomials [DecidableEq R] (p : CMvPolynomial n R) :
  Finset (CMvMonomial n)
:=
  Quotient.lift LawfulCMvPolynomial.monomials valid p
where
  valid : ∀ (a b : LawfulCMvPolynomial n R), a ≈ b → a.monomials = b.monomials := by
    intro a b h_eq
    unfold LawfulCMvPolynomial.instHasEquiv at h_eq
    dsimp at h_eq
    ext x
    specialize h_eq x
    constructor
    · intro h
      cases x_in_a : a.find? x
      case h.mp.none =>
        apply LawfulCMvPolynomial.mem_of_mem_monomials at h
        rcases h with ⟨b₀, h_in⟩
        rw [←LawfulCMvPolynomial.mem_node] at h_in
        rw [x_in_a] at h_in
        contradiction
      case h.mp.some val =>
        apply LawfulCMvPolynomial.mem_monomials_of_mem
        rw [x_in_a] at h_eq
        rw [←LawfulCMvPolynomial.mem_node]
        exact symm h_eq
    · intro h
      cases x_in_b : b.find? x
      case h.mpr.none =>
        apply LawfulCMvPolynomial.mem_of_mem_monomials at h
        rcases h with ⟨b₀, h_in⟩
        rw [←LawfulCMvPolynomial.mem_node] at h_in
        rw [x_in_b] at h_in
        contradiction
      case h.mpr.some val =>
        rw [x_in_b] at h_eq
        apply LawfulCMvPolynomial.mem_monomials_of_mem
        rw [←LawfulCMvPolynomial.mem_node]
        exact h_eq

def findD (p : CMvPolynomial n R) (m : CMvMonomial n) (v₀ : R) : R :=
  (p.find? m).getD v₀

instance [BEq R] [LawfulBEq R] : NonAssocSemiring (CMvPolynomial n R) where
  add := add
  add_assoc := sorry
  zero := ⟦0⟧
  zero_add := sorry
  add_zero := by
    unfold_projs
    intro a
    simp [add, Quotient.map₂, Quotient.lift₂]
    let a' : LawfulCMvPolynomial n R := Quotient.out a
    have mka : a = ⟦a'⟧ := by rw [Quotient.eq_mk_iff_out]; aesop
    simp [mka]
    unfold LawfulCMvPolynomial.extEquiv; dsimp
    intro x
    unfold
      LawfulCMvPolynomial.add
      LawfulCMvPolynomial.constant
    simp
    unfold UnlawfulCMvPolynomial.add RBMap.mergeWith RBSet.mergeWith
    simp [RBSet.foldl_eq_foldl_toList, UnlawfulCMvPolynomial.empty]
    rw [RBSet.empty_toList]
    dsimp
    apply LawfulCMvPolynomial.from_to_Unlawful
  nsmul c p := mul (⟦.constant c⟧) p
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := by
    intro a b
    unfold HAdd.hAdd instHAdd
    dsimp [add]
    let a' : LawfulCMvPolynomial n R := Quotient.out a
    let b' : LawfulCMvPolynomial n R := Quotient.out b
    have mka : a = ⟦a'⟧ := by rw [Quotient.eq_mk_iff_out]; aesop
    have mkb : b = ⟦b'⟧ := by rw [Quotient.eq_mk_iff_out]; aesop
    rw [mka, mkb]
    rw [Quotient.map₂, Quotient.lift₂, Quotient.lift₂]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    rw [Quotient.eq]
    unfold LawfulCMvPolynomial.extEquiv; dsimp
    intro x
    unfold LawfulCMvPolynomial.add
    sorry
  mul := mul
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  one := ⟦.constant 1⟧
  one_mul := sorry
  mul_one := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry

end R_CommSemiring

section R_CommRing
variable {n R} [CommRing R]

def sub [BEq R] (p₁ p₂ : CMvPolynomial n R) : CMvPolynomial n R :=
  Quotient.map₂ LawfulCMvPolynomial.sub sorry p₁ p₂

def reduce [BEq R] (p₁ : CMvPolynomial n R) (p₂ : CMvPolynomial n R) :
  Option (CMvPolynomial n R)
:= do
  let p ← Quotient.lift₂ LawfulCMvPolynomial.reduce sorry p₁ p₂
  return ⟦p⟧

end R_CommRing

end CMvPolynomial
