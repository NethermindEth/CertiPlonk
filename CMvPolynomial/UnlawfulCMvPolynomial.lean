import CMvPolynomial.CMvMonomial
import CMvPolynomial.Wheels
import Std.Data.HashMap
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Ordering.Lemmas
import Mathlib.Data.Finmap

open Batteries Std

/-- Polynomial in `n` variables with coefficients in `R`. -/
abbrev UnlawfulCMvPolynomial (n : ℕ) (R : Type) :=
  Std.ExtHashMap (CMvMonomial n) R

-- instance [LT α] [DecidableEq α] [∀ (a₁ a₂ : α), Decidable (a₁ < a₂)] :
--   Membership (α × β) (RBMap α β (λ a₁ a₂ ↦ compareOfLessAndEq a₁ a₂))
-- where
--   mem map pair := by
--     unfold RBMap at map
--     exact pair ∈ map

-- instance [LT α] [DecidableEq α] [∀ (a₁ a₂ : α), Decidable (a₁ < a₂)] :
--   Membership α (RBMap α β (λ a₁ a₂ ↦ compareOfLessAndEq a₁ a₂)) where
--   mem map a := a ∈ RBMap.keysArray map

namespace UnlawfulCMvPolynomial

section R_CommSemiring
variable {n : ℕ} {R}

def empty : UnlawfulCMvPolynomial n R := HashMap.emptyWithCapacity

def extend {n : ℕ} (n' : ℕ) (p : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial (max n n') R :=
  p.fold (init := ∅) fun acc k v ↦ acc.insert (k.extend n') v

def isNoZeroCoef [Zero R] (p : UnlawfulCMvPolynomial n R) : Prop :=
  ∀ m, p.get? m ≠ some 0

def toFinset [DecidableEq R] (p : UnlawfulCMvPolynomial n R) : Finset (CMvMonomial n × R) :=
  p.toList.toFinset

def monomials (p : UnlawfulCMvPolynomial n R) : Finset (CMvMonomial n) :=
  p.keys.toFinset

-- lemma mem_monomials_of_mem {p : UnlawfulCMvPolynomial n R} :
--   (a₀, b₀) ∈ p.val → a₀ ∈ p.monomials
-- := RBNode.mem_foldr_insert_of_mem (b₀ := b₀) _ _

-- lemma mem_of_mem_monomials
--   {p : UnlawfulCMvPolynomial n R} :
--   a₀ ∈ p.monomials → (∃ b₀, (a₀, b₀) ∈ p.val)
-- := fun h ↦ (RBNode.mem_of_mem_foldr_insert _ _ h).elim id fun c ↦ by contradiction

-- lemma mem_filter_insert_of_mem₀ [BEq R]
--   (t : RBNode (MonoR n R)):
--   ∀ init : UnlawfulCMvPolynomial n R,
--     init.find? a = some b →
--     (∀ c, (a, c) ∉ t) →
--     RBMap.find? (t.foldl (λ acc (a, b) ↦ acc.insert a b) init) a = some b
-- := by
--   induction t
--   case nil h => intros; assumption
--   case node l v r ih₁ ih₂ =>
--     intro init h_in h
--     simp at h ih₁ ih₂ ⊢
--     apply ih₂ _ _
--     · intro c
--       rcases h c with ⟨_, _, _⟩; assumption
--     rcases v with ⟨v₁, v₂⟩; simp_all
--     have neq : a.simpleCmp v₁ ≠ Ordering.eq := by
--       intro contra
--       rw [CMvMonomial.simpleCmp_iff] at contra
--       apply (h v₂).1 contra
--       rfl
--     rw [RBMap.find?_insert_of_ne _ neq]
--     apply ih₁ _ h_in

-- lemma mem_filter_insert_of_mem₀
--   {t : RBNode (MonoR n R)}
--   {init : UnlawfulCMvPolynomial n R}
--   {h₁ : init.get? a = some b}
--   {h₂ : a ∉ t} :
--   HashS

-- lemma mem_filter_insert_of_mem [BEq R]
--   (t : RBNode (MonoR n R)):
--   RBNode.Ordered (Ordering.byKey Prod.fst CMvMonomial.simpleCmp) t →
--   ∀ init : UnlawfulCMvPolynomial n R,
--     (a₀, b₀) ∈ t →
--     RBMap.find? (t.foldl (λ acc (a, b) ↦ acc.insert a b) init) a₀ = some b₀
-- := by
--   intro ordered init h
--   revert init
--   induction t
--   case nil h => contradiction
--   case node l v r ih₁ ih₂ =>
--     simp at ordered; rcases ordered with ⟨all_lt₁, all_lt₂, ordered₁, ordered₂⟩
--     intro init
--     rw [RBNode.mem_node] at h
--     rw [RBNode.All_def] at all_lt₁ all_lt₂
--     rcases h with (h₁ | h₂ | h₃)
--     · simp only [RBNode.foldl, Bool.cond_not]
--       rw [←h₁]
--       dsimp
--       apply mem_filter_insert_of_mem₀ _ _ _
--       · intro c a₀c_in
--         simp [Membership.mem, RBNode.EMem] at a₀c_in
--         rw [RBNode.Any_def] at a₀c_in
--         rcases a₀c_in with ⟨⟨m', c'⟩, x_in_r, h_eq⟩
--         specialize all_lt₂ (m', c') x_in_r
--         simp [Ordering.byKey, RBNode.cmpLT] at all_lt₂
--         -- simp at h_eq
--         specialize all_lt₂
--         subst h₁
--         simp_all only [forall_const, Prod.forall]
--         apply Vector.lt_irrefl m'
--         injection h_eq with p₁ p₂
--         subst p₁
--         assumption
--       apply RBMap.find?_insert_of_eq
--       simp
--     · have a₀_lt_v1 : a₀ < v.1 := by
--         specialize all_lt₁ (a₀, b₀) h₂
--         simp [Ordering.byKey, RBNode.cmpLT] at all_lt₁
--         apply all_lt₁
--       specialize ih₁ ordered₁ h₂
--       simp
--       apply mem_filter_insert_of_mem₀ _ _ _
--       · intro c a₀c_in
--         simp [Membership.mem, RBNode.EMem] at a₀c_in
--         rw [RBNode.Any_def] at a₀c_in
--         rcases a₀c_in with ⟨⟨m', c'⟩, x_in_r, h_eq⟩
--         specialize all_lt₂ (m', c') x_in_r
--         simp [Ordering.byKey, RBNode.cmpLT] at all_lt₂
--         injection h_eq with p₁ p₂
--         specialize all_lt₂
--         simp_all only [forall_const, Prod.forall]
--         apply Vector.lt_irrefl m'
--         trans v.1 <;> assumption
--       rcases v with ⟨v, hv⟩
--       rw [RBMap.find?_insert_of_ne]
--       apply ih₁
--       rw [CMvMonomial.simpleCmp_lt.2 a₀_lt_v1]
--       simp
--     · apply ih₂ ordered₂ h₃

-- lemma mem_filter_insert_of_mem [BEq R]
--   (t : RBNode (MonoR n R)):
--   RBNode.Ordered (Ordering.byKey Prod.fst CMvMonomial.simpleCmp) t →
--   ∀ init : UnlawfulCMvPolynomial n R,
--     (a₀, b₀) ∈ t →
--     RBMap.find? (t.foldl (λ acc (a, b) ↦ acc.insert a b) init) a₀ = some b₀

-- #printaxioms mem_filter_insert_of_mem

-- lemma mem_of_filter_insert [BEq R]
--   (t : RBNode (MonoR n R)):
--   RBNode.Ordered (Ordering.byKey Prod.fst CMvMonomial.simpleCmp) t →
--   ∀ init : UnlawfulCMvPolynomial n R,
--     RBMap.find? (t.foldl (λ acc (a, b) ↦ acc.insert a b) init) a₀ = some b₀ →
--     (a₀, b₀) ∈ t ∨ init.find? a₀ = some b₀
-- := by
--   intro ordered init h
--   revert init
--   induction t
--   case nil h =>
--     intro init in_fold
--     simp at in_fold
--     right; assumption
--   case node l v r ih₁ ih₂ =>
--     rcases v with ⟨v, hv⟩
--     simp only [RBNode.foldl, RBNode.mem_node]
--     rcases ordered with ⟨o₁, o₂, o₃, o₄⟩
--     intro init find_in_fold
--     specialize
--       ih₂ o₄
--         ((RBNode.foldl (fun acc x => acc.insert x.1 x.2) init l).insert v hv)
--         find_in_fold
--     rcases ih₂ with (in_r | ih₂)
--     · left; right; right; assumption
--     · by_cases is_val : a₀ = v
--       · rw [RBMap.find?_insert_of_eq] at ih₂
--         · simp at ih₂
--           left; left; simp [is_val, ←ih₂]
--         · rw [CMvMonomial.simpleCmp_iff]; assumption
--       · rw [RBMap.find?_insert_of_ne] at ih₂
--         · specialize ih₁ o₃ init ih₂
--           rcases ih₁ with (in_v | ih₁)
--           · left; right; left; assumption
--           · right; assumption
--         · intro contra
--           rw [CMvMonomial.simpleCmp_iff] at contra
--           contradiction

-- #printaxioms mem_of_filter_insert

private lemma mem_of_filter_insert_aux {init : UnlawfulCMvPolynomial n R}
  {l : List (CMvMonomial n × R)}
  (h : (List.foldl (fun a b => a.insert b.1 b.2) init l).get? k = some v) :
  l.find? (·.1 == k) = .some (k, v) ∨ init[k]? = .some v := by
  sorry
  -- induction' l with hd tl ih generalizing init
  -- · tauto
  -- · rcases hd with ⟨k₁, v₁⟩; simp at h ⊢
  --   by_cases eq : k₁ = k
  --   · subst eq
  --     simp at ih ⊢
  --     suffices v ≠ v₁ → init[k₁]? = some v by tauto
  --     intros eq
  --     rw [HashMap.getElem?_eq


  -- sorry
  -- done

lemma mem_of_filter_insert {t init : UnlawfulCMvPolynomial n R}
  (h : HashMap.get? (t.fold (λ acc a b ↦ acc.insert a b) init) k = some v) :
  t[k]? = .some v ∨ init[k]? = .some v := by
  rw [HashMap.fold_eq_foldl_toList] at h
  have := HashMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some
            (m := t) (k := k) (k' := k) (v := v)
  have := mem_of_filter_insert_aux (k := k) (l := t.toList) h
  tauto

lemma mem_of_filter_insert' {t init : UnlawfulCMvPolynomial n R}
  (h : HashMap.get? (t.fold (λ acc a b ↦ acc.insert a b) init) k = some v) :
  t[k]? = .some v ∨ init[k]? = .some v := by
  rw [←HashMap.mem_toList_iff_getElem?_eq_some]
  done

instance [Repr R] : Repr (UnlawfulCMvPolynomial n R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial n × R) :=
      ⟨λ (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

-- def myPolynomial : UnlawfulCMvPolynomial 3 ℤ :=
--   [⟨#m[1, 2, 1], 5⟩, ⟨#m[3, 2, 0], 5⟩].toRBMap CMvMonomial.simpleCmp

-- def myPolynomial₂ : UnlawfulCMvPolynomial 3 ℤ :=
--   [⟨#m[1, 2, 1], -5⟩, ⟨#m[3, 2, 0], -5⟩].toRBMap CMvMonomial.simpleCmp

def constant (c : R) : UnlawfulCMvPolynomial n R :=
  HashMap.ofList [MonoR.constant c]

-- def zero : UnlawfulCMvPolynomial n R := constant 0

instance : Zero (UnlawfulCMvPolynomial n R) := ⟨empty⟩

-- def add (p₁ p₂ : UnlawfulCMvPolynomial n R) :
--   UnlawfulCMvPolynomial n R
-- :=
--   RBMap.mergeWith (λ _ c₁ c₂ ↦ c₁ + c₂) p₁ p₂

def add (p₁ p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  RBMap.merge (λ _ c₁ c₂ ↦ c₁ + c₂) p₁ p₂

instance : Add (UnlawfulCMvPolynomial n R) := ⟨add⟩

/--
  Merging with a commutative `mergeFn` makes the entire operation commutative.

  - We only need it commutativity assuming `k ∈ t₁ ∧ k ∈ t₂`, so this is too strong.
-/
lemma mergeWith_comm_of_comm {α : Type u} {β : Type v}
                             {cmp : α → α → Ordering}
                             {mergeFn : α → β → β → β}
                             {t₁ t₂ : RBMap α β cmp}
                             (h : ∀ k a b, mergeFn k a b = mergeFn k b a) :
  RBMap.mergeWith mergeFn t₁ t₂ = RBMap.mergeWith mergeFn t₂ t₁ := sorry

lemma add_comm {p₁ p₂ : UnlawfulCMvPolynomial n R} : p₁ + p₂ = p₂ + p₁ :=
  mergeWith_comm_of_comm fun _ ↦ AddCommMagma.add_comm

/--
  Merging with an associative `mergeFn` makes the entire operation associative.

  - We only need associativity assuming `k ∈ t₁ ∧ k ∈ t₂ ∧ k ∈ t₃`, so this is too strong.
-/
lemma mergeWith_assoc_of_assoc {α : Type u} {β : Type v}
                               {cmp : α → α → Ordering}
                               {mergeFn : α → β → β → β}
                               {t₁ t₂ t₃ : RBMap α β cmp}
                               (h : ∀ k a b c, mergeFn k (mergeFn k a b) c =
                                               mergeFn k a (mergeFn k b c)) :
  RBMap.mergeWith mergeFn (RBMap.mergeWith mergeFn t₁ t₂) t₃ =
  RBMap.mergeWith mergeFn t₁ (RBMap.mergeWith mergeFn t₂ t₃) := sorry

example {R : Type} [CommSemiring R] {a b c : R} : a + b + c = a + (b + c) := by
  exact add_assoc a b c

lemma add_assoc {p₁ p₂ p₃ : UnlawfulCMvPolynomial n R} : p₁ + p₂ + p₃ = p₁ + (p₂ + p₃) :=
  mergeWith_assoc_of_assoc fun _ ↦ _root_.add_assoc  

lemma zero_add {p : UnlawfulCMvPolynomial n R} : 0 + p = p := sorry

/--
  Ref: @Frantisek - Why `BEq`? -- FIX
-/
def mul₀
  (t : MonoR n R)
  (p : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  p.map λ (m, c) ↦ (t.1 * m, t.2 * c)

theorem list_nodup {p : UnlawfulCMvPolynomial n R} :
  p.toList.Nodup := CMvMonomial.list_pairwise_lt_nodup RBMap.toList_sorted

/--
  Ref: @Andrei @Julian
  
  I think we want this.

  From which `AddCommMonoid` is just `inferInstance`.
-/
-- instance : CommRing (UnlawfulCMvPolynomial n R) := sorry

instance : AddZeroClass (UnlawfulCMvPolynomial n R) where
  add_zero := by aesop
  zero_add := fun _ ↦ zero_add

instance : AddSemigroup (UnlawfulCMvPolynomial n R) where
  add_assoc := fun _ _ _ ↦ add_assoc

instance : AddMonoid (UnlawfulCMvPolynomial n R) where
  nsmul n p := if n == 0 then .empty else p.map λ (m, c) ↦ (m, n * c)
  nsmul_succ := sorry

instance :
  AddCommMonoid (UnlawfulCMvPolynomial n R) where
  add_comm := fun _ _ ↦ add_comm
/--
  Ref: @Frantisek - Why `CommSemiring` and `BEq`?
-/
def mul (p₁ p₂ : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R
:=
  -- letI Pairs : Type := {x : CMvMonomial n × R // x ∈ p₁.toList}
  -- have : Fintype Pairs :=
  --   ⟨⟨Multiset.ofList p₁.toList.attach,
  --     by aesop (add simp UnlawfulCMvPolynomial.list_nodup)⟩,
  --     by aesop
  --   ⟩
    
  let terms : List (UnlawfulCMvPolynomial n R) :=
    p₁.foldl (λ acc m c ↦ UnlawfulCMvPolynomial.mul₀ (m, c) p₂ :: acc) []
  terms.foldl UnlawfulCMvPolynomial.add .empty
  -- Not sure the `AddCommMonoid` instance works
  
  -- -- Ref: @Andrei - What is wrong with this?
  -- ∑ t : Pairs, UnlawfulCMvPolynomial.mul₀ t.1 p₂

variable {p₁ p₂ : UnlawfulCMvPolynomial 3 ℚ}

instance : Mul (UnlawfulCMvPolynomial n R) := ⟨mul⟩

theorem nonemptySome
  {p : UnlawfulCMvPolynomial n R}
  (nonempty : 0 < p.size) :
  ∃ m r, p.find? m = some r
:= by  
  unfold UnlawfulCMvPolynomial at *
  rcases p with ⟨_ | ⟨_, l, ⟨m, r⟩, _⟩⟩ <;> [contradiction; skip]
  use m, r
  simp [RBMap.find?_some, RBMap.mem_toList]
  
end R_CommSemiring

section R_CommRing
variable {n R} [CommRing R]

/--
  Ref: @Frantisek - Why `BEq`?
-/
def neg (p : UnlawfulCMvPolynomial n R) : UnlawfulCMvPolynomial n R :=
  p.map λ (m, c) ↦ (m, -c)

instance : Neg (UnlawfulCMvPolynomial n R) := ⟨neg⟩

/--
  Ref: @Frantisek - Why `BEq`?
-/
def sub (p₁ p₂ : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R
:=
  UnlawfulCMvPolynomial.add p₁ p₂.neg

instance : Sub (UnlawfulCMvPolynomial n R) := ⟨sub⟩

/-- lt(p) according to the `simpleCmp` order -/
def leadingTerm? [BEq R] : UnlawfulCMvPolynomial n R → Option (MonoR n R) :=
  RBMap.max?

/-- lm(p) according to the `simpleCmp` order -/
def leadingMonomial? [BEq R] :
  UnlawfulCMvPolynomial n R → Option (CMvMonomial n)
:=
  .map Prod.fst ∘ UnlawfulCMvPolynomial.leadingTerm?

def findDivisibleTerm?
  (p : UnlawfulCMvPolynomial n R)
  (divisor : CMvMonomial n) :
  Option (MonoR n R)
:=
  p.foldl (λ acc m c ↦ if m.divides divisor then .some (m, c) else acc) none

def div₀
  (f : UnlawfulCMvPolynomial n R)
  (m : UnlawfulCMvPolynomial n R)
  (q : UnlawfulCMvPolynomial n R)
  (r : UnlawfulCMvPolynomial n R) :
  UnlawfulCMvPolynomial n R × UnlawfulCMvPolynomial n R
:= sorry

def reduce [BEq R] (p d : UnlawfulCMvPolynomial n R) :
  Option (UnlawfulCMvPolynomial n R)
:= do
  let lm_d ← d.leadingMonomial?
  let t ← p.findDivisibleTerm? lm_d
  let m ← t.1.div lm_d
  let termQuotient : UnlawfulCMvPolynomial n R := RBMap.single m t.2
  pure <| p.sub (UnlawfulCMvPolynomial.mul termQuotient d)

end R_CommRing


end UnlawfulCMvPolynomial

def myPolynomial₃ : UnlawfulCMvPolynomial 2 ℤ :=
  [⟨#m[1, 0], 2⟩, ⟨#m[0, 1], 3⟩].toRBMap CMvMonomial.simpleCmp

def myPolynomial₄ : UnlawfulCMvPolynomial 2 ℤ :=
  [⟨#m[1, 1], 1⟩, ⟨#m[2, 0], -1⟩].toRBMap CMvMonomial.simpleCmp

-- #eval myPolynomial₃
-- #eval myPolynomial₄
-- #eval! myPolynomial₃.mul myPolynomial₄
