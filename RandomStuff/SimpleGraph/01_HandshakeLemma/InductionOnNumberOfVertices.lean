import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Ring

import RandomStuff.SimpleGraph.Utils

set_option linter.flexible false
set_option linter.unusedDecidableInType false



theorem degree_sum_formula_for_fin_n {n} (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by
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
    have h₀ := add_vertex_degree_sum G' vs
    rw [h₀, iH, add_vertex_edgeFinset_card]
    ring

theorem degree_sum_formula {V} [inst : Fintype V] (G : SimpleGraph V) [inst : DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  have f := SimpleGraph.overFinIso G (rfl (a := Fintype.card V))
  have inst₀ : DecidableRel (G.overFin rfl).Adj := by
    intros x y; apply SimpleGraph.Iso.symm at f
    rw [← SimpleGraph.Iso.map_adj_iff f]
    apply inst
  have h : ∀ v, (G.overFin rfl).degree (f v) = G.degree v := by
    simp only [SimpleGraph.Iso.degree_eq, implies_true]
  simp_rw [← h]
  rw [SimpleGraph.Iso.card_edgeFinset_eq f]
  rw [← degree_sum_formula_for_fin_n]
  rw [← Equiv.sum_comp (e := f.toEquiv)]
  simp
