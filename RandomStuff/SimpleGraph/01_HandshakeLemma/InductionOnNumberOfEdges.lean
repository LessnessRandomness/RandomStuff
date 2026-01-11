import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite


import RandomStuff.SimpleGraph.Utils

set_option linter.flexible false
set_option linter.unusedDecidableInType false



theorem degree_sum_formula_aux {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (hg : G.edgeFinset.card = n) :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  revert G; induction n with
  | zero =>
    intros G _ hg
    rw [Finset.card_eq_zero, Set.toFinset_eq_empty, SimpleGraph.edgeSet_eq_empty] at hg
    simp [hg]
    intros v; subst G
    rw [← SimpleGraph.bot_degree v]; congr
    ext x y; exact of_decide_eq_true rfl
  | succ n iH =>
    intros G inst h
    obtain ⟨⟨v₁, v₂⟩, t, h₁, h₂, h₃⟩ := (Finset.card_eq_succ.mp h)
    have h₄ : s(v₁, v₂) ∈ G.edgeFinset := by rw [← h₂]; simp
    have h₅ : G.Adj v₁ v₂ := by simp at h₄; exact h₄
    have h₆ := eq_add_edge_remove_edge G h₅
    have h₇ := degree_after_add_edge (remove_edge G h₅) (v₁ := v₁) (v₂ := v₂)
      (by grind) (by simp [remove_edge])
    have h₈ : ∀ v, G.degree v =
      (remove_edge G h₅).degree v + if v = v₁ ∨ v = v₂ then 1 else 0 := by
      convert h₇
    simp_rw [h₈]
    have h₉ := edgeFinset_after_add_edge (remove_edge G h₅) (v₁ := v₁) (v₂ := v₂)
      (by grind) (by simp [remove_edge])
    have h₁₀ : G.edgeFinset = insert s(v₁, v₂) (remove_edge G h₅).edgeFinset := by
      convert h₉
    have h₁₁ : G.edgeFinset.card = (remove_edge G h₅).edgeFinset.card + 1 := by
      rw [h₁₀, Finset.card_insert_of_notMem (by simp [remove_edge])]
    rw [h₁₁]; rw [h] at h₁₁; simp only [add_right_cancel_iff] at h₁₁; symm at h₁₁
    apply iH at h₁₁
    rw [Finset.sum_add_distrib, h₁₁, Nat.left_distrib]
    simp [Finset.card_eq_two]
    use v₁, v₂; grind

theorem degree_sum_formula {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  have h := rfl (a := G.edgeFinset.card)
  apply degree_sum_formula_aux at h; exact h
