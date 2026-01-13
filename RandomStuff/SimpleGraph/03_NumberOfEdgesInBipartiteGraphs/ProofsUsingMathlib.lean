import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Int.Star

set_option linter.flexible false
set_option linter.unusedDecidableInType false

theorem T₀ {V : Type u_1} {G : SimpleGraph V} {s t : Finset V} [Fintype V] [DecidableRel G.Adj]
    (h : G.IsBipartiteWith ↑s ↑t) : G.edgeFinset.card ≤ s.card * t.card := by
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges h]
  have h : ∀ v ∈ s, G.degree v ≤ t.card := by
    intros v hv
    apply SimpleGraph.isBipartiteWith_degree_le' h.symm hv
  apply Finset.sum_le_sum at h
  simp at h; exact h

theorem T₁ {V : Type u_1} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsBipartite) : 4 * G.edgeFinset.card ≤ Fintype.card V ^ 2 := by
  rw [SimpleGraph.isBipartite_iff_exists_isBipartiteWith] at h
  obtain ⟨s, t, h⟩ := h
  have inst_s : Fintype ↑s := Fintype.ofFinite ↑s
  have inst_t : Fintype ↑t := Fintype.ofFinite ↑t
  have h' : G.IsBipartiteWith s.toFinset t.toFinset := by
    simp; exact h
  apply T₀ at h'
  have h₀ : Disjoint s.toFinset t.toFinset := by
    simp; exact h.disjoint
  have h₁ : s.toFinset ∪ t.toFinset ⊆ Finset.univ (α := V) := by simp
  have h₂ : s.toFinset.card + t.toFinset.card ≤ Fintype.card V := by
    rw [← Finset.card_union_eq_card_add_card] at h₀
    exact le_of_eq_of_le h₀.symm (Finset.card_le_card h₁)
  have h₃ : (s.toFinset.card + t.toFinset.card) ^ 2 ≤ Fintype.card V ^ 2 :=
    Nat.pow_le_pow_left h₂ 2
  have h₄ : 4 * (s.toFinset.card * t.toFinset.card) ≤ (s.toFinset.card + t.toFinset.card) ^ 2 := by
    by_cases h₅ : s.toFinset.card ≤ t.toFinset.card <;> nlinarith
  linarith
