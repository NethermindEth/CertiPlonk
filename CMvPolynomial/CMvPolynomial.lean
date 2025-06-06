import Batteries.Data.RBMap.Lemmas
import Mathlib.Algebra.Lie.OfAssociative
import Aesop

import CMvPolynomial.LawfulCMvPolynomial

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

instance [LT α] [DecidableEq α] [∀ (a b : α), Decidable (a < b)] :
  Membership (α × β) (RBMap α β (λ a b => compareOfLessAndEq a b))
where
  mem map pair := by
    unfold RBMap at map
    exact pair ∈ map

#synth Membership (Nat × Nat) (RBMap Nat Nat (λ a b => compareOfLessAndEq a b))

def incl [CommSemiring R] (a b : UnlawfulCMvPolynomial n R) : Prop :=
  ∀ (m : CMvMonomial n) (c : R), (m, c) ∈ a → (m, c) ∈ b
  --  a.find? m = some c → b.find? m = some c

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

theorem UnlawfulCMvPolynomial.removeOne [CommSemiring R]
  (p : UnlawfulCMvPolynomial n R)
  (sizePred : ℕ)
  (h_size : p.size = sizePred + 1) :
  ∃ (p' : UnlawfulCMvPolynomial n R),
    p'.size = sizePred ∧
      ∀ (m : CMvMonomial n) c, p'.find? m = some c → p.find? m = some c
:= by
  unfold UnlawfulCMvPolynomial at *
  let pList := p.toList
  rcases p with ⟨p⟩
  cases p with
    | nil => contradiction
    | node _ l v r =>
      let p' : UnlawfulCMvPolynomial n R :=
        RBMap.ofList (l.toList ++ r.toList) simpleCmp
      exists p'
      constructor
      · simp [RBMap.size, RBSet.size] at h_size
        unfold p'
        sorry
      · sorry

lemma erase_pred_size
  {size' : ℕ}
  (m : RBMap α β comparison)
  (h_size : m.size = size' + 1)
  (a : α) :
  m.contains a → (m.erase a).size = size'
:= sorry

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

#check Finset.fold_insert
#check Std.Commutative

theorem RBMap.in_foldr_insert [CommSemiring R]
  (f : CMvMonomial n → R → Finset (CMvMonomial n) → Finset (CMvMonomial n))
  (p : UnlawfulCMvPolynomial n R)
  (s : ℕ)
  (h_size : s = p.size)
  (h_f : P' f)
  (h_ext : (m₀, c₀) ∈ p) :
  m₀ ∈ RBMap.foldr f ∅ p
:= by
  unfold P' at h_f
  subst h_f
  induction' s with s' ih generalizing p
  · have p_empty : p = ∅ := RBMap.size_zero p h_size.symm
    subst p_empty
    contradiction
  · sorry

theorem fake' [CommSemiring R]
  (f : CMvMonomial n → R → Finset (CMvMonomial n) → Finset (CMvMonomial n))
  (a b : UnlawfulCMvPolynomial n R)
  (s_a s_b : ℕ)
  (p₁ : s_a = a.size)
  (p₂ : s_b = b.size)
  (h_ext : incl a b)
  (h_f : P' f) :
  -- (h_m : P' m)
  ∀ x, x ∈ RBMap.foldr f ∅ ↑a → x ∈ RBMap.foldr f ∅ ↑b
:= by
  unfold incl at h_ext
  unfold P' at h_f
  induction' s_a with s_a' ih generalizing a b s_b
  · have a_empty : a = ∅ := RBMap.size_zero a p₁.symm
    subst a_empty
    intro x x_in_a
    simp [RBMap.foldr_eq_foldr_toList] at x_in_a
  · intro x x_in_foldr_a
    let ⟨m₀, c₀, a', h_size, h_insert, h_contains⟩ := match_insert a p₁.symm
    by_cases h_eq : m₀ = x
    · subst h_eq
      have in_a₀ : (m₀, c₀) ∈ a := by
        rw [←h_insert]
        unfold RBMap.insert
        apply RBSet.mem_insert.2
        simp [*]
      specialize h_ext m₀ c₀ in_a₀
      subst h_insert
      -- follows from h_ext
      sorry
    · suffices x ∈ RBMap.foldr f ∅ (b.erase m₀) by -- induction
        sorry

      -- case on b, is it empty?
      specialize ih a' (b.erase m₀) (s_b - 1) h_size.symm sorry -- from p₂
      apply ih
      · intro m c h_find_a'
        specialize h_ext m c sorry -- from h_ext
        -- m ≠ m₀
        sorry
      · -- we know h_eq and x_in_foldr_a
        sorry

theorem fake'' [CommSemiring R]
  (f : CMvMonomial n → R → Finset (CMvMonomial n) → Finset (CMvMonomial n))
  (a b : UnlawfulCMvPolynomial n R)
  (la lb : List (CMvMonomial n × R))
  (s_a s_b : ℕ)
  (p₁ : la = a.toList)
  (p₂ : lb = b.toList)
  (hl₁ : s_a = a.size)
  (hl₂ : s_b = b.size)
  (h_ext : incl a b)
  (h_f : P' f) :
  x ∈ List.foldr (fun p r => f p.1 p.2 r) ∅ la →
  x ∈ List.foldr (fun p r => f p.1 p.2 r) ∅ lb
:= by
  induction' s_a with s_a' ih generalizing a
  · intro h₀
    rw [RBMap.size_eq, ←p₁] at hl₁
    have h₀ : la = [] := by
      apply List.length_eq_zero_iff.1
      exact hl₁.symm
    subst h₀
    contradiction
  · intro h
    sorry

example [CommSemiring R]
  (a b : LawfulCMvPolynomial n R)
  (h : ∀ (x : CMvMonomial n), RBMap.find? a.val x = RBMap.find? b.val x) :
  ∀ (x : CMvMonomial n) (c : R), a.find? x = some c → b.find? x = some c
:= by
  unfold LawfulCMvPolynomial.find?
  intro x c ha
  simp [←h, ha]

def CMvPolynomial.monomials' [CommSemiring R]
  (p : CMvPolynomial n R) :
  Finset (CMvMonomial n)
:=
  let monomials (lp : LawfulCMvPolynomial n R) : Finset (CMvMonomial n) :=
    lp.1.foldr (init := ∅) λ m _ acc => insert m acc
  Quotient.lift monomials valid p
where
  valid := by
    simp only [HasEquiv.Equiv, extEquiv]
    intros a b h
    ext x
    generalize eq :
      (fun m _ acc => insert m acc :
        CMvMonomial n → R → Finset (CMvMonomial n) → Finset (CMvMonomial n)
      ) = f
    simp [RBMap.foldr_eq_foldr_toList]
    unfold LawfulCMvPolynomial.find? at h
    sorry

def CMvPolynomial.findD [CommSemiring R]
  (p : CMvPolynomial n R) (m : CMvMonomial n) (v₀ : R) : R
:=
  (p.find? m).getD v₀
