import Mathlib.Algebra.Lie.OfAssociative
import Batteries.Data.RBMap.Lemmas
import Aesop
import CMvPolynomial.CMvMonomial

open Batteries

/-- Polynomial in `n` variables with coefficients in `R`. -/
abbrev UnlawfulCMvPolynomial n R [CommSemiring R] :=
  Batteries.RBMap (CMvMonomial n) R simpleCmp

def UnlawfulCMvPolynomial.isNoZeroCoef [CommSemiring R]
  (p : UnlawfulCMvPolynomial n R) : Prop
:=
  ∀ m, p.find? m ≠ some 0

instance [Repr R] [CommSemiring R] : Repr (UnlawfulCMvPolynomial n R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial n × R) :=
      ⟨λ (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

def myPolynomial : UnlawfulCMvPolynomial 3 ℤ :=
  [⟨#m[1, 2, 1], 5⟩, ⟨#m[3, 2, 0], 5⟩].toRBMap simpleCmp

def myPolynomial₂ : UnlawfulCMvPolynomial 3 ℤ :=
  [⟨#m[1, 2, 1], -5⟩, ⟨#m[3, 2, 0], -5⟩].toRBMap simpleCmp

def UnlawfulCMvPolynomial.add [CommSemiring R] [BEq R]
  (p₁ : UnlawfulCMvPolynomial n R)
  (p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  RBMap.mergeWith (λ _ c₁ c₂ => c₁ + c₂) p₁ p₂

def UnlawfulCMvPolynomial.neg [CommRing R] [BEq R]
  (p : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  p.map (λ (m, c) => (m, -c))

def UnlawfulCMvPolynomial.sub [CommRing R] [BEq R]
  (p₁ : UnlawfulCMvPolynomial n R)
  (p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  UnlawfulCMvPolynomial.add p₁ p₂.neg

def UnlawfulCMvPolynomial.mul₀ [CommRing R] [BEq R]
  (t : Term n R)
  (p : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  p.map (λ (m, c) => (CMvMonomial.mul t.1 m, t.2 * c))

/-- lt(p) according to the `simpleCmp` order -/
def UnlawfulCMvPolynomial.leadingTerm? [CommRing R] [BEq R] :
  UnlawfulCMvPolynomial n R → Option (Term n R)
:=
  RBMap.max?

/-- lm(p) according to the `simpleCmp` order -/
def UnlawfulCMvPolynomial.leadingMonomial? [CommRing R] [BEq R] :
  UnlawfulCMvPolynomial n R → Option (CMvMonomial n)
:=
  .map Prod.fst ∘ UnlawfulCMvPolynomial.leadingTerm?

def UnlawfulCMvPolynomial.findDivisibleTerm? [CommRing R]
  (p : UnlawfulCMvPolynomial n R)
  (divisor : CMvMonomial n) :
  Option (Term n R)
:=
  p.foldl (λ acc m c => if m.divides divisor then (m, c) else acc) none

def UnlawfulCMvPolynomial.div₀ [CommRing R]
  (f : UnlawfulCMvPolynomial n R)
  (m : UnlawfulCMvPolynomial n R)
  (q : UnlawfulCMvPolynomial n R)
  (r : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R × UnlawfulCMvPolynomial n R
:= sorry

instance [CommRing R] [BEq R] :
  AddCommMonoid (UnlawfulCMvPolynomial n R)
where
  add := UnlawfulCMvPolynomial.add
  add_assoc := sorry
  zero := .empty
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := sorry

instance : TransCmp (λ x1 x2 : (CMvMonomial n × R) => simpleCmp x1.1 x2.1) where
  symm := by
    intros
    apply CMvMonomial.symm
  le_trans := by
    intros x y z
    apply CMvMonomial.le_trans

lemma list_pairwise_lt_nodup (l : List (CMvMonomial n × R)) :
  l.Pairwise (RBNode.cmpLT (simpleCmp ·.1 ·.1)) → l.Nodup
:= by
  intro h
  induction h with
  | nil => simp
  | @cons a l head tail ih =>
    apply List.Pairwise.cons
    · intros a' a'_in contra
      rw [contra] at head
      specialize head a' a'_in
      simp [RBNode.cmpLT] at head
      specialize head
      simp [Vector.lt_irrefl] at head
    · apply ih

theorem UnlawfulCMvPolynomial.list_nodup [CommSemiring R] (p : UnlawfulCMvPolynomial n R) :
  p.toList.Nodup
:= by
  apply list_pairwise_lt_nodup
  apply RBMap.toList_sorted

def UnlawfulCMvPolynomial.mul [CommRing R] [BEq R]
  (p₁ : UnlawfulCMvPolynomial n R)
  (p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  let Pairs : Type := {x : CMvMonomial n × R // x ∈ p₁.toList}
  have : Fintype Pairs :=
    { elems :=
      ⟨ Multiset.ofList p₁.toList.attach
      , by
          simp
          rw [List.nodup_attach]
          apply UnlawfulCMvPolynomial.list_nodup
      ⟩
    , complete := by
        rintro ⟨x, hs⟩
        simp
        apply List.mem_attach
    }
  -- let terms : List (UnlawfulCMvPolynomial n R) :=
  --   p₁.foldl (λ acc m c => UnlawfulCMvPolynomial.mul₀ (m, c) p₂ :: acc) []
  -- terms.foldl UnlawfulCMvPolynomial.add .empty
  ∑ t : Pairs, UnlawfulCMvPolynomial.mul₀ t p₂

def UnlawfulCMvPolynomial.reduce [CommRing R] [BEq R]
  (p : UnlawfulCMvPolynomial n R)
  (d : UnlawfulCMvPolynomial n R) :
  Option (UnlawfulCMvPolynomial n R)
:= do
  let lm_d ← d.leadingMonomial?
  let t ← p.findDivisibleTerm? lm_d
  let m ← t.1.div lm_d
  let termQuotient : UnlawfulCMvPolynomial n R := RBMap.single m t.2
  pure <| p.sub (UnlawfulCMvPolynomial.mul termQuotient d)

def myPolynomial₃ : UnlawfulCMvPolynomial 2 ℤ :=
  [⟨#m[1, 0], 2⟩, ⟨#m[0, 1], 3⟩].toRBMap simpleCmp

def myPolynomial₄ : UnlawfulCMvPolynomial 2 ℤ :=
  [⟨#m[1, 1], 1⟩, ⟨#m[2, 0], -1⟩].toRBMap simpleCmp

#eval myPolynomial₃
#eval myPolynomial₄
#eval! myPolynomial₃.mul myPolynomial₄

instance : Std.Irrefl fun (x1 x2 : ℕ) => x1 < x2 := by
  constructor
  apply Nat.lt_irrefl

theorem UnlawfulCMvPolynomial.nonemptySome [CommSemiring R]
  (p : UnlawfulCMvPolynomial n R)
  (h_size : p.size > 0) :
  ∃ m r, p.find? m = some r
:= by
  unfold UnlawfulCMvPolynomial at *
  rcases p with ⟨p⟩
  cases p with
    | nil => contradiction
    | node _ l v r =>
      rcases v with ⟨m, r⟩
      exists m, r
      simp
        [ RBMap.find?, RBMap.findEntry?, RBSet.findP?, RBNode.find?, simpleCmp
        , compareOfLessAndEq, gt_iff_lt
        ]
      split <;> (try simp [Vector.lt_irrefl] at *)
