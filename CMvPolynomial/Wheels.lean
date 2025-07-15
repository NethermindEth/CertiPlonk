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

lemma ExtTreeMap.getElem?_filter {α β : Type} [BEq α] [LawfulBEq α]
                                 {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {f : α → β → Bool} {k : α} {m : Std.ExtTreeMap α β cmp} :
  (m.filter f)[k]? = m[k]?.filter (f k) := sorry
