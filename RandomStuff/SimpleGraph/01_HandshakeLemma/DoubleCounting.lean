import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators

-- See https://thebook.zib.de/graph%20theory/2024/10/11/handshaking-lemma.html
-- for much simpler and more beautiful proof outside Mathlib

set_option linter.flexible false
set_option linter.unusedDecidableInType false


namespace HandshakeLemma.DoubleCounting

def sum {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ v₁ : V, ∑ v₂ : V, if G.Adj v₁ v₂ then 1 else 0

lemma sum_eq₁ {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    sum G = ∑ v, G.degree v := by
  simp [sum]; congr; ext x
  unfold SimpleGraph.degree SimpleGraph.neighborFinset; simp

lemma sum_eq₂ {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    sum G = 2 * G.edgeFinset.card := by
  rw [sum, ← Fintype.sum_prod_type']; simp only [Finset.sum_boole, Nat.cast_id]
  rw [← mul_one (({x | _} : Finset _).card), mul_comm 2 _]
  apply (Finset.card_mul_eq_card_mul (r := fun p e => e = Sym2.mk p))
  · simp [Finset.bipartiteAbove]; intros a b hab
    rw [Finset.card_eq_one]
    use s(a, b); ext p; simp; intro hp
    rw [hp, SimpleGraph.mem_edgeSet]
    exact hab
  · simp [Finset.bipartiteBelow]; intros b hb
    cases b; rename_i x y
    rw [Finset.card_eq_two]
    rw [SimpleGraph.mem_edgeSet] at hb
    use ⟨x, y⟩, ⟨y, x⟩
    constructor
    · have hxy : x ≠ y := by intro a; subst a; simp_all only [SimpleGraph.irrefl]
      grind
    · simp; ext p
      simp; constructor <;> intro h
      · grind
      · obtain h | h := h
        · grind
        · apply G.symm at hb; grind

theorem degree_sum_formula {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  rw [← sum_eq₁, sum_eq₂]

end HandshakeLemma.DoubleCounting
