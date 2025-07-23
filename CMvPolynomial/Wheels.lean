import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Cases
import Aesop
import Std.Classes.Ord.Basic
import Std.Data.ExtTreeMap

lemma distinct_of_inj_nodup {α β : Type*} {l : List α} {f : α → β}
  (h₁ : Function.Injective f) (h₂ : l.Nodup) :
  List.Pairwise (fun a b => f a ≠ f b) l := by
  induction' l with hd tl ih
  · simp
  · simp_all only [ne_eq, List.nodup_cons, List.pairwise_cons, and_true, forall_const]
    intros a' ha' contra
    have : hd = a' := by aesop
    aesop

/-
  Something like this might be needed for `.getElem?_filter`.
-/
-- lemma ExtTreeMap.mem_filter {α β : Type} {cmp} [TransCmp cmp]
--                             {f : α → β → Bool} {m : ExtTreeMap α β cmp} {k : α} :
--   k ∈ m.filter f ↔ ∃ (h' : k ∈ m), f (m.getKey k h') m[k] = true := sorry

namespace ExtTreeMap

variable {α β : Type} [BEq α] [LawfulBEq α]
         {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
         {k : α} {m m₁ m₂ : Std.ExtTreeMap α β cmp} {f : α → β → β → β}

lemma mergeWith₀ (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = .some (f k m₁[k] m₂[k]) := sorry

lemma mergeWith₁ (h₁ : k ∈ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₁[k]? := sorry

lemma mergeWith₂ (h₁ : k ∉ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₂[k]? := sorry

lemma mergeWith₃ (h₁ : k ∉ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = .none := sorry

grind_pattern mergeWith₀ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₁ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₂ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₃ => (Std.ExtTreeMap.mergeWith f m₁ m₂)[k]?

lemma mergeWith_of_comm (h : ∀ {x}, Std.Commutative (f x)) :
  m₁.mergeWith f m₂ = m₂.mergeWith f m₁ := by sorry

@[grind =]
lemma getElem?_filter {α β : Type} [BEq α] [LawfulBEq α]
                      {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {f : α → β → Bool} {k : α} {m : Std.ExtTreeMap α β cmp} :
  (m.filter f)[k]? = m[k]?.filter (f k) := sorry

end ExtTreeMap

lemma Option.filter_irrel {α : Type} {o : Option α} {p : α → Bool}
  (h : ∀ x, x ∈ o → p x) : o.filter p = o := by
  aesop (add simp Option.filter)  
