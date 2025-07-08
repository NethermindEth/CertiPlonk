import Batteries.Data.RBMap.Lemmas
import Mathlib.Data.Finset.Insert

open Batteries

lemma RBNode.mem_Finset₀ [DecidableEq α] (t : RBNode (α × β)) :
  ∀ init : Finset α,
  x ∈ init → x ∈ t.foldr (init := init) (λ (a, _) s ↦ insert a s)
:= by
  induction t
  case nil h =>
    intro init h
    simp; assumption
  case node l v r ih₁ ih₂ =>
    intro init h
    simp
    apply ih₁
    rw [Finset.mem_insert]
    right
    apply ih₂
    assumption

lemma RBNode.mem_foldr_insert_of_mem [DecidableEq α]
  (t : RBNode (α × b)) :
  ∀ init : Finset α,
    (a₀, b₀) ∈ t →
    a₀ ∈ t.foldr (init := init) (λ (a, _) s ↦ insert a s)
:= by
  intro init h
  revert init
  induction t
  case nil h => contradiction
  case node l v r ih₁ ih₂ =>
    simp
    intro init
    rw [RBNode.mem_node] at h
    rcases h with (h₁ | h₂ | h₃)
    · apply RBNode.mem_Finset₀ l
      rw [Finset.mem_insert]
      left
      cases h₁
      rfl
    · apply ih₁
      assumption
    · apply RBNode.mem_Finset₀ l
      rw [Finset.mem_insert]
      right
      apply ih₂
      assumption

lemma RBNode.mem_of_mem_foldr_insert [DecidableEq α]
  (t : RBNode (α × b)) :
  ∀ init : Finset α,
    a₀ ∈ t.foldr (λ (a, _) s ↦ insert a s) init →
    (∃ b₀, (a₀, b₀) ∈ t) ∨ a₀ ∈ init
:= by
  induction t
  case nil h =>
    intro init h
    simp at h
    right
    assumption
  case node l v r ih₁ ih₂ =>
    intro init h
    simp
    simp at h
    specialize ih₁ (insert v.1 (RBNode.foldr (λ x s ↦ insert x.1 s) r init)) h
    rcases ih₁ with (in_l | ih₁)
    · rcases in_l with ⟨b₀, in_l⟩
      left;
      use b₀
      right; left; assumption
    · rw [Finset.mem_insert] at ih₁
      rcases ih₁ with (in_v | ih₁)
      · left;
        use v.2
        left
        simp [in_v]
      · specialize ih₂ init ih₁
        rcases ih₂ with (in_r | ih₁)
        · rcases in_r with ⟨b₀, in_r⟩
          left
          use b₀
          right; right
          assumption
        · right; assumption
