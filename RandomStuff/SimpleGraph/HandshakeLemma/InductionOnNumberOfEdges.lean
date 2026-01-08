import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option linter.flexible false
set_option linter.unusedDecidableInType false


def add_edge {V} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v₁ v₂ : V} (hv : v₁ ≠ v₂) (_hg : ¬ G.Adj v₁ v₂) :
    SimpleGraph V :=
  ⟨fun x y => G.Adj x y ∨ s(x, y) = s(v₁, v₂),
    by intros x y h; simp at *
       obtain h | h := h
       · left; exact G.symm h
       · right; grind,
    by intros x h; simp at h; grind⟩

def remove_edge {V} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    {v1 v2 : V} (_ : G.Adj v1 v2) :
    SimpleGraph V :=
  ⟨fun x y => G.Adj x y ∧ s(x, y) ≠ s(v1, v2),
   by intros x y h
      simp at *
      exact ⟨G.symm h.1, by grind⟩,
   by intros x h
      simp at *⟩

local instance decidable_remove_edge_adj : ∀ {V} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) {v₁ v₂ : V} (hv : G.Adj v₁ v₂)
    [DecidableRel G.Adj], DecidableRel (remove_edge G hv).Adj := by
  intros V inst₁ inst₂ G v₁ v₂ hv inst₃ a b
  simp [remove_edge]
  exact instDecidableAnd

local instance decidable_add_edge_adj : ∀ {V} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v₁ v₂ : V} (hv : v₁ ≠ v₂) (hg : ¬ G.Adj v₁ v₂),
    DecidableRel (add_edge G hv hg).Adj := by
  intros v inst inst₁ G inst₂ v₁ v₂ hv hg
  simp [add_edge]
  intros x y; exact instDecidableOr

def eq_add_edge_remove_edge {V} [Finite V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {v₁ v₂ : V} (hv : G.Adj v₁ v₂) :
    G = add_edge (remove_edge G hv) (v₁ := v₁) (v₂ := v₂)
      (by intro a; subst a; simp_all only [SimpleGraph.irrefl])
      (by simp [remove_edge]) := by
  ext x y
  simp [add_edge, remove_edge]
  constructor <;> intro h
  · grind
  · obtain h | h | h := h <;> try grind
    apply G.symm; grind


lemma edgeFinset_after_add_edge {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v₁ v₂ : V} (hv : v₁ ≠ v₂) (hg : ¬ G.Adj v₁ v₂) :
    (add_edge G hv hg).edgeFinset = insert s(v₁, v₂) G.edgeFinset := by
  ext x
  simp [add_edge]
  obtain ⟨a, b⟩ := x
  simp; grind

lemma degree_after_add_edge {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v₁ v₂ : V} (hv : v₁ ≠ v₂) (hg : ¬ G.Adj v₁ v₂) :
    ∀ v, (add_edge G hv hg).degree v =
         G.degree v + if v = v₁ ∨ v = v₂ then 1 else 0 := by
    intros v; simp only [add_edge]
    have h₀ u v : ({x | G.Adj u x ∨ x = v} : Finset _) =
                  insert v ({x | G.Adj u x} : Finset _) := by grind
    split_ifs <;> rename_i h <;>
      unfold SimpleGraph.degree SimpleGraph.neighborFinset <;> simp
    · obtain h | h := h
      · simp [h, hv]
        rw [h₀, Finset.card_insert_of_notMem]
        simpa
      · simp [h, hv.symm]
        rw [h₀, Finset.card_insert_of_notMem]
        simp
        exact (fun h => hg (G.symm h))
    · simp at h; obtain ⟨h₁, h₂⟩ := h
      simp [h₁, h₂]


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
