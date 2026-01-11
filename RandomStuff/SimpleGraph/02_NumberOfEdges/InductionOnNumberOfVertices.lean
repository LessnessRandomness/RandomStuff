import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.DepRewrite

import RandomStuff.SimpleGraph.Utils


set_option linter.flexible false
set_option linter.unusedDecidableInType false


lemma upper_limit_of_edgeset_card {n} (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj] :
    G.edgeFinset.card ≤ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n iH =>
    obtain ⟨G', vs, h⟩ := eq_add_vertex_to_smaller G
    subst G
    have inst₀ : DecidableRel G'.Adj := by
      simp only [add_vertex, dite_then_false] at inst
      intros a b; have inst' := inst a.castSucc b.castSucc
      simp at inst'
      exact inst'
    have h := add_vertex_edgeFinset_card (n := n) G' vs
    rw [h]
    have h₀ : vs.card ≤ n := card_finset_fin_le vs
    have h₁ : G'.edgeFinset.card ≤ n.choose 2 := iH G'
    have h₂ : n.choose 2 + n = (n + 1).choose 2 := by
      simp only [Nat.choose, Nat.choose_one_right, Nat.reduceAdd]
      rw [add_comm]
    grind


lemma remove_last_vertex_of_complete_graph n :
    remove_last_vertex (⊤ : SimpleGraph (Fin (n + 1))) = (⊤ : SimpleGraph (Fin n)) := by
  ext x y; simp [remove_last_vertex]

lemma edgeset_card_of_complete_graph n :
    (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2 := by
  induction n with
  | zero => simp [Sym2.diagSet]
  | succ n iH =>
    have h := add_vertex_remove_last_vertex_eq_self (⊤ : SimpleGraph (Fin (n + 1)))
    rw [remove_last_vertex_of_complete_graph] at h
    rw! (castMode := .all) [← h]
    rw [add_vertex_edgeFinset_card, iH]; simp
    have h₀ : ({x : Fin n | ¬ Fin.last n = x.castSucc} : Finset _) = Finset.univ := by
      ext x; simp; grind
    simp [h₀, Nat.choose_succ_left, add_comm]


lemma max_number_of_edges_iff {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.card = n.choose 2) : G = ⊤ := by
  induction n with
  | zero => ext x y; exfalso; cases x; lia
  | succ n iH =>
    ext x y; simp
    rw! (castMode := .all) [← add_vertex_remove_last_vertex_eq_self G] at h
    rw [add_vertex_edgeFinset_card] at h
    have h₀ : Finset.card {x : Fin n | G.Adj (Fin.last n) x.castSucc} ≤ n :=
      card_finset_fin_le {x | G.Adj (Fin.last n) x.castSucc}
    have h₁ := upper_limit_of_edgeset_card (remove_last_vertex G)
    have h₃ : n + n.choose 2 = (n + 1).choose 2 := by
      simp [Nat.choose_succ_left]
    have h₄ : Finset.card {x : Fin n | G.Adj (Fin.last n) x.castSucc} = n := by lia
    have h₅ : (remove_last_vertex G).edgeFinset.card = n.choose 2 := by lia
    have h₆ : remove_last_vertex G = ⊤ := by apply iH _ h₅
    have h₇ : ({x : Fin n | G.Adj (Fin.last n) x.castSucc} : Finset _) = Finset.univ := by
      apply Finset.eq_univ_of_card
      simp; exact h₄
    rw [← add_vertex_remove_last_vertex_eq_self G]
    rw [h₇, h₆]
    simp [add_vertex]
    grind

#min_imports
