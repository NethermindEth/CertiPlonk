import Batteries.Data.RBMap.Lemmas
import Aesop

import CMvPolynomial.LawfulCMvPolynomial
import CMvPolynomial.Wheels

open Batteries

def hello := "world"

@[reducible]
def CMvPolynomial (n : ℕ) R [CommSemiring R] : Type :=
  Quotient (@extEquiv n R _)

def CMvPolynomial.add [CommSemiring R] [BEq R]
  (p₁ : CMvPolynomial n R)
  (p₂ : CMvPolynomial n R) :
  CMvPolynomial n R
:=
  Quotient.mk extEquiv <| Quotient.lift₂ LawfulCMvPolynomial.add sorry p₁ p₂

def CMvPolynomial.sub [CommRing R] [BEq R]
  (p₁ : CMvPolynomial n R)
  (p₂ : CMvPolynomial n R) :
  CMvPolynomial n R
:=
  Quotient.mk extEquiv <| Quotient.lift₂ LawfulCMvPolynomial.sub sorry p₁ p₂

def CMvPolynomial.mul [CommRing R] [BEq R]
  (p₁ : CMvPolynomial n R)
  (p₂ : CMvPolynomial n R) :
  CMvPolynomial n R
:=
  Quotient.mk extEquiv <| Quotient.lift₂ LawfulCMvPolynomial.mul sorry p₁ p₂

def CMvPolynomial.reduce [CommRing R] [BEq R]
  (p₁ : CMvPolynomial n R)
  (p₂ : CMvPolynomial n R) :
  Option (CMvPolynomial n R)
:= do
  let p ← Quotient.lift₂ LawfulCMvPolynomial.reduce sorry p₁ p₂
  return Quotient.mk extEquiv p

def CMvPolynomial.find? [CommSemiring R]
  (p : CMvPolynomial n R)
  (m : CMvMonomial n) :
  Option R
:=
  Quotient.lift LawfulCMvPolynomial.find? valid p m
where
  valid := by
    intros p₁ p₂
    unfold HasEquiv.Equiv instHasEquivOfSetoid Setoid.r extEquiv
    simp
    intro h
    funext x
    simp [*]

def P [CommSemiring R]
  (f : CMvMonomial n → R → Multiset (CMvMonomial n) → Multiset (CMvMonomial n)) :
  Prop
:=
  f = λ m _ acc => m ::ₘ acc

def incl' [CommSemiring R] (a b : UnlawfulCMvPolynomial n R) : Prop :=
  ∀ (m : CMvMonomial n) (c : R), (m, c) ∈ a → (m, c) ∈ b
  --  a.find? m = some c → b.find? m = some c

def incl [CommSemiring R] (a b : UnlawfulCMvPolynomial n R) : Prop :=
  ∀ (m : CMvMonomial n) (c : R), a.find? m = some c → b.find? m = some c

def P' [CommSemiring R]
  (f : CMvMonomial n → R → Finset (CMvMonomial n) → Finset (CMvMonomial n)) :
  Prop
:=
  f = λ m _ acc => insert m acc

lemma RBMap.size_zero [CommSemiring R] :
  ∀ (p : UnlawfulCMvPolynomial n R), p.size = 0 → p = ∅
:= by
  intros a h
  rcases a with ⟨n⟩
  cases n <;> trivial

-- theorem UnlawfulCMvPolynomial.removeOne [CommSemiring R]
--   (p : UnlawfulCMvPolynomial n R)
--   (sizePred : ℕ)
--   (h_size : p.size = sizePred + 1) :
--   ∃ (p' : UnlawfulCMvPolynomial n R),
--     p'.size = sizePred ∧
--       ∀ (m : CMvMonomial n) c, p'.find? m = some c → p.find? m = some c
-- := by
--   unfold UnlawfulCMvPolynomial at *
--   let pList := p.toList
--   rcases p with ⟨p⟩
--   cases p with
--     | nil => contradiction
--     | node _ l v r =>
--       let p' : UnlawfulCMvPolynomial n R :=
--         RBMap.ofList (l.toList ++ r.toList) simpleCmp
--       exists p'
--       constructor
--       · simp [RBMap.size, RBSet.size] at h_size
--         unfold p'
--         sorry
--       · sorry

lemma find?_some_iff_contains {comparison : α → α → Ordering} [TransCmp comparison]
  (m : RBMap α β comparison)
  (a : α) :
  m.contains a ↔ ∃ b, m.find? a = some b
:= by
  unfold RBMap.contains
  rw [Option.isSome_iff_exists]
  constructor
  · intro h
    rcases h with ⟨⟨a₁, b₁⟩, h_a₁⟩
    rw [RBMap.findEntry?_some] at h_a₁
    use b₁
    rw [RBMap.find?_some]
    use a₁
  · rintro ⟨b₁, h⟩
    rw [RBMap.find?_some] at h
    rcases h with ⟨a₁, h⟩
    use ⟨a₁, b₁⟩
    rw [RBMap.findEntry?_some]
    aesop

axiom erase_pred_size
  {size' : ℕ}
  (m : RBMap α β comparison)
  (h_size : m.size = size' + 1)
  (a : α) :
  m.contains a → (m.erase a).size = size'

axiom erase_incl
  (m : RBMap α β comparison)
  (a : α) :
  (m.erase a).find? a' = b' → m.find? a' = b'

lemma match_insert
  {size' : ℕ}
  (M : RBMap α β comparison)
  (h_size : M.size = size' + 1) :
  ∃ (k : α) (v : β) (M' : RBMap α β comparison),
    M'.size = size' ∧ M'.insert k v = M ∧ M'.find? k = none
:= sorry

/-- Inspired by `Finset.mem_insert` -/
theorem RBSet.mem_insert [CommSemiring R]
  {p : RBSet (CMvMonomial n × R) (Ordering.byKey Prod.fst simpleCmp)}
  {m m' : CMvMonomial n} {c c' : R} :
    (m, c) ∈ p.insert (m', c') ↔ (m, c) = (m', c') ∨ (m, c) ∈ p
:= by
  sorry

theorem RBMap.mem_insert [CommSemiring R]
  {p : UnlawfulCMvPolynomial n R} {m m' : CMvMonomial n} {c c' : R} :
    (m, c) ∈ p.insert m' c' ↔ (m, c) = (m', c') ∨ (m, c) ∈ p
:= by
  unfold RBMap.insert
  unfold UnlawfulCMvPolynomial RBMap at p
  apply RBSet.mem_insert

example [CommSemiring R]
  (a b : LawfulCMvPolynomial n R)
  (h : ∀ (x : CMvMonomial n), RBMap.find? a.val x = RBMap.find? b.val x) :
  ∀ (x : CMvMonomial n) (c : R), a.find? x = some c → b.find? x = some c
:= by
  unfold LawfulCMvPolynomial.find?
  intro x c ha
  simp [←h, ha]

def CMvPolynomial.monomials [DecidableEq R] [CommSemiring R]
  (p : CMvPolynomial n R) :
  Finset (CMvMonomial n)
:=
  let monomials (lp : LawfulCMvPolynomial n R) : Finset (CMvMonomial n) :=
    lp.monomials
  Quotient.lift monomials valid p
where
  valid := by
    intro a b h_eq
    dsimp
    unfold HasEquiv.Equiv instHasEquivOfSetoid Setoid.r extEquiv at h_eq
    dsimp at h_eq
    unfold LawfulCMvPolynomial.monomials UnlawfulCMvPolynomial.monomials
    ext x
    specialize h_eq x
    constructor
    · intro h
      cases x_in_a : a.find? x
      case h.mp.none =>
        apply RBNode.mem_of_mem_foldr_insert at h
        rcases h with (⟨b₀, h_in⟩ | contra)
        · rw [←LawfulCMvPolynomial.mem_node] at h_in
          rw [x_in_a] at h_in
          contradiction
        . contradiction
      case h.mp.some val =>
        rw [x_in_a] at h_eq
        apply RBNode.mem_foldr_insert_of_mem (b₀ := val)
        rw [←LawfulCMvPolynomial.mem_node]
        exact symm h_eq
    · intro h
      cases x_in_b : b.find? x
      case h.mpr.none =>
        apply RBNode.mem_of_mem_foldr_insert at h
        rcases h with (⟨b₀, h_in⟩ | contra)
        · rw [←LawfulCMvPolynomial.mem_node] at h_in
          rw [x_in_b] at h_in
          contradiction
        . contradiction
      case h.mpr.some val =>
        rw [x_in_b] at h_eq
        apply RBNode.mem_foldr_insert_of_mem (b₀ := val)
        rw [←LawfulCMvPolynomial.mem_node]
        exact h_eq

def CMvPolynomial.findD [CommSemiring R]
  (p : CMvPolynomial n R) (m : CMvMonomial n) (v₀ : R) : R
:=
  (p.find? m).getD v₀
