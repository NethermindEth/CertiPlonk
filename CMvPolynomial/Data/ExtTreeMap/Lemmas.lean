import Std.Classes.Ord.Basic
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
import Std.Data.DTreeMap.Lemmas
import CMvPolynomial.Data.DTreeMap.Lemmas

namespace ExtTreeMap

variable {α β : Type}
         {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

-- Pointwise characterization of `mergeWith` on optional access at a key.
theorem get?_mergeWith_at
    (m₁ m₂ : Std.ExtTreeMap α β cmp) (f : α → β → β → β) (k : α) :
    (m₁.mergeWith f m₂)[k]? =
      match m₁[k]?, m₂[k]? with
      | .some v₁, .some v₂ => .some (f k v₁ v₂)
      | .some v₁, .none    => .some v₁
      | .none,    .some v₂ => .some v₂
      | .none,    .none    => .none := by
  let merge_values : Option β → Option β → Option β := fun
    | .some v₁, .some v₂ => .some (f k v₁ v₂)
    | .some v₁, .none    => .some v₁
    | .none,    .some v₂ => .some v₂
    | .none,    .none    => .none
  change _ = merge_values _ _
  match m₁ with
  | Std.ExtTreeMap.mk t₁ =>
    match m₂ with
    | Std.ExtTreeMap.mk t₂ =>
      induction t₁, t₂ using Std.ExtDTreeMap.inductionOn₂ with
      | mk t₁ t₂ =>
        change Std.DTreeMap.Const.get? (Std.DTreeMap.Const.mergeWith f t₁ t₂) k =
          merge_values (Std.DTreeMap.Const.get? t₁ k) (Std.DTreeMap.Const.get? t₂ k)
        cases h₁ : Std.DTreeMap.Const.get? t₁ k <;>
          cases h₂ : Std.DTreeMap.Const.get? t₂ k <;>
          simp [merge_values, Std.DTreeMap.Const.get?_mergeWith, h₁, h₂]

end ExtTreeMap
