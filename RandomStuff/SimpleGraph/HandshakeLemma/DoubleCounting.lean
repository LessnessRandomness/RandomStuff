import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option linter.flexible false
set_option linter.unusedDecidableInType false


def indicator {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v v₁ v₂ : V) : Prop :=
  v = v₁ ∧ G.Adj v₁ v₂

local instance indicator_dec : ∀ V [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v v₁ v₂ : V), Decidable (indicator G v v₁ v₂) := by
  simp [indicator]
  exact fun V [Fintype V] [DecidableEq V] G [DecidableRel G.Adj] v v₁ v₂ =>
    instDecidableAnd


def sum {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ v, ∑ (p : V × V), (if indicator G v p.1 p.2 then 1 else 0)

def sum_eq₁ {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    sum G = ∑ v, G.degree v := by
  simp [sum]; congr; ext v
  unfold SimpleGraph.degree SimpleGraph.neighborFinset
  simp [indicator]
  rw [Finset.card_bij (i := fun p _ => p.2)]
  · simp; grind
  · simp; grind
  · simp


-- I'm not clever enough to prove this proper way
-- Yet

def aux₀ {V} [Fintype V] [DecidableEq V] (P : Sym2 V → Prop) [DecidablePred P]
    (hP : ∀ x, P s(x, x) → False) :
    Finset.card {x : Sym2 V | P x} * 2 = Finset.card {x : V × V | P (Sym2.mk x)} := by
  sorry


def sum_eq₂ {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    sum G = 2 * G.edgeFinset.card := by
  simp only [sum, indicator]; rw [Finset.sum_comm]
  simp only [Finset.sum_boole, Nat.cast_id]
  have h : ∀ x ∈ Finset.univ (α := V × V),
           Finset.card {x_1 : V | x_1 = x.1 ∧ G.Adj x.1 x.2} =
           if G.Adj x.1 x.2 then 1 else 0 := by
    intro ⟨x₁, x₂⟩; simp
    split_ifs <;> rename_i h
    · rw [Finset.card_eq_one]
      use x₁; ext x; simp; tauto
    · simp; exact h
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_boole, Nat.cast_id]
  simp_rw [← SimpleGraph.mem_edgeSet]
  simp only [Prod.mk.eta]
  rw [← aux₀ _ (by simp)]; simp [mul_comm]
