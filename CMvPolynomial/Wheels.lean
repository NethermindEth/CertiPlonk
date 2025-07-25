import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Cases
import Aesop
import Std.Classes.Ord.Basic
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas

namespace Std

/-
  PROOF BY Markus Himmel from:
  ```
    https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ExtTreeMap.20-.20Filter.20.2F.20MergeWith/near/530761978
  ```
-/

attribute [local instance low] beqOfOrd

theorem DTreeMap.Internal.Impl.Const.get?_filter [Ord α] [TransOrd α]
    (m : DTreeMap.Internal.Impl α (fun _ => β)) (h : m.WF) (f : α → β → Bool) (k : α) :
    Const.get? (m.filter f h.balanced).1 k = (Const.get? m k).pfilter (fun v h' => f (m.getKey k ((contains_eq_isSome_get? h).trans (Option.isSome_of_eq_some h'))) v) := by
  -- This manual proof is usually done by the `simp_to_model` tactic
  simp only [Const.get?_eq_getValue? h.filter.ordered, toListModel_filter,
    Const.get?_eq_getValue? h.ordered, getKey_eq_getKey h.ordered]
  apply Std.Internal.List.Const.getValue?_filter
  apply h.ordered.distinctKeys

theorem DTreeMap.get?_filter {cmp : α → α → Ordering} [TransCmp cmp]
    (m : DTreeMap α (fun _ => β) cmp) (f : α → β → Bool) (k : α) :
    Const.get? (m.filter f) k = (Const.get? m k).pfilter (fun v h' => f (m.getKey k (Const.contains_eq_isSome_get?.trans (Option.isSome_of_eq_some h'))) v) :=
  letI : Ord α := ⟨cmp⟩
  DTreeMap.Internal.Impl.Const.get?_filter m.inner m.wf _ _

theorem ExtDTreeMap.get?_filter {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtDTreeMap α (fun _ => β) cmp) (f : α → β → Bool) (k : α) :
    Const.get? (m.filter f) k = (Const.get? m k).pfilter (fun v h' => f (m.getKey k (Const.contains_eq_isSome_get?.trans (Option.isSome_of_eq_some h'))) v) :=
  m.inductionOn fun _ => DTreeMap.get?_filter _ _ _

theorem ExtTreeMap.getElem?_filter {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap α β cmp) (f : α → β → Bool) (k : α) :
    (m.filter f)[k]? = m[k]?.pfilter (fun v h' => f (m.getKey k (contains_eq_isSome_getElem?.trans (Option.isSome_of_eq_some h'))) v) :=
  ExtDTreeMap.get?_filter m.inner f k

end Std


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

@[grind=]
lemma mergeWith₀ (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = .some (f k m₁[k] m₂[k]) := sorry

@[grind=]
lemma mergeWith₁ (h₁ : k ∈ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₁[k]? := sorry

@[grind=]
lemma mergeWith₂ (h₁ : k ∉ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₂[k]? := sorry

@[grind=]
lemma mergeWith₃ (h₁ : k ∉ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = .none := sorry

@[simp, grind=]
lemma filter_empty {α : Type} {f : α → β → Bool} {cmp : α → α → Ordering} : Std.ExtTreeMap.filter f (∅ : Std.ExtTreeMap α β cmp) = ∅ := by
  rfl

@[simp, grind=]
lemma mergeWith_empty {f : α → β → β → β} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {t : Std.ExtTreeMap α β cmp} :
  Std.ExtTreeMap.mergeWith f t ∅ = t := by ext; grind

@[simp, grind=]
lemma toList_ofList {a : Std.ExtTreeMap α β cmp} : @Std.ExtTreeMap.ofList α β (@Std.ExtTreeMap.toList α β cmp _ a) cmp = a := by
  ext k v
  revert v
  by_cases h : ∃ v, (k, v) ∈ a.toList
  · rcases h with ⟨v, h⟩
    rw [@Std.ExtTreeMap.getElem?_ofList_of_mem α β cmp _ a.toList k k (by grind) v Std.ExtTreeMap.distinct_keys_toList h]
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at h
    rw [h]
    simp
  · simp only [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, not_exists] at h
    intros v
    simp only [h v, iff_false]
    rw [Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false]
    · simp
    · simp
      intros h'
      rw [←Std.ExtTreeMap.isSome_getKey?_iff_mem] at h'
      aesop

grind_pattern mergeWith₀ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₁ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₂ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₃ => (Std.ExtTreeMap.mergeWith f m₁ m₂)[k]?

lemma mergeWith_of_comm (h : ∀ {x}, Std.Commutative (f x)) :
    m₁.mergeWith f m₂ = m₂.mergeWith f m₁ := by
  ext k v
  by_cases h' : k ∈ m₁ <;> by_cases h'' : k ∈ m₂
  · rw [mergeWith₀ h' h'', mergeWith₀ h'' h', h.comm]
  · rw [mergeWith₁ h' h'', mergeWith₂ h'' h']
  · rw [mergeWith₂ h' h'', mergeWith₁ h'' h']
  · rw [mergeWith₃ h' h'', mergeWith₃ h'' h']

open Std ExtTreeMap

@[grind =]
lemma getElem?_filter {α β : Type} [BEq α] [LawfulBEq α]
                      {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {f : α → β → Bool} {k : α} {m : Std.ExtTreeMap α β cmp} :
  (m.filter f)[k]? = m[k]?.filter (f k) := by
  rw [Std.ExtTreeMap.getElem?_filter]
  simp

@[grind=]
lemma filter_mem {f : α → β → Bool} {m : Std.ExtTreeMap α β cmp} (h : k ∈ m) : f k m[k] → (Std.ExtTreeMap.filter f m)[k]? = .some m[k] := by
  intro h'
  rw [getElem?_filter]
  simp only [h, getElem?_pos, Option.filter_eq_some_iff, true_and]
  exact h'

@[grind=]
lemma filter_not_mem {f : α → β → Bool} {m : Std.ExtTreeMap α β cmp} (h : k ∉ m) : (Std.ExtTreeMap.filter f m)[k]? = .none := by
  rw [getElem?_filter]
  simp [h]

attribute [grind ext] Std.ExtTreeMap.ext_getElem?

end ExtTreeMap

lemma Option.filter_irrel {α : Type} {o : Option α} {p : α → Bool}
  (h : ∀ x, x ∈ o → p x) : o.filter p = o := by
  aesop (add simp Option.filter)

  variable {α : Type u} {β : Type v}
