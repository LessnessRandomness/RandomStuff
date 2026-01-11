import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Ring

set_option linter.flexible false
set_option linter.unusedDecidableInType false

/-!
# Utilities

This file contains useful things imported and used in later proofs.
-/

/-!
## `((Finset.univ (α := Fin n)).filter p).card`

A Mathlib lemma to remember: `Fin.univ_castSuccEmb n` which proves
`Finset.univ = Finset.cons (last n) (Finset.map castSuccEmb Finset.univ) ⋯`.
-/

lemma Fin.card_filter_univ_succ_last {n : ℕ} (p : Fin (n + 1) → Prop) [DecidablePred p] :
    ({x : Fin (n + 1) | p x} : Finset _).card =
    if p (Fin.last n)
    then ({x : Fin n | p x.castSucc} : Finset _).card + 1
    else ({x : Fin n | p x.castSucc} : Finset _).card := by
  rw [Fin.univ_castSuccEmb, Finset.filter_cons, apply_ite Finset.card, Finset.card_cons,
      Finset.filter_map, Finset.card_map]; rfl

lemma Fin.card_filter_univ_succ'_last {n : ℕ} (p : Fin (n + 1) → Prop) [DecidablePred p] :
    ({x : Fin (n + 1) | p x} : Finset _).card =
    (if p (Fin.last n) then 1 else 0) +
    ({x : Fin n | p x.castSucc} : Finset _).card := by
  rw [Fin.card_filter_univ_succ_last]; split_ifs <;> simp [add_comm]


/-!
## `Finset.univ (α := Sym2 (Fin (n + 1)))`
-/

/-- The first injective function that acts on `Sym2 (Fin n)`,
increasing the upper limit for both `Fin n` values,
but keeping the values (`.val`) the same. -/
def Fin.sym2_castSucc {n : ℕ} : Sym2 (Fin n) ↪ Sym2 (Fin (n + 1)) :=
  ⟨fun p => p.map Fin.castSucc, by
    intros x y h
    simp at h
    cases x; cases y; simp at *
    exact h⟩

/-- The second injective function that acts on `Fin n`,
increasing the upper limit for the `Fin n` value and
keeping the value same, and bundling it into unordered pair
together with `Fin.last n`. -/
def Fin.sym2_with_fin_last {n} : Fin n ↪ Sym2 (Fin (n + 1)) :=
  ⟨fun x => s(x.castSucc, Fin.last n), by
    intros x y h; cases x ; cases y
    simp at *
    grind⟩

/-- Parts of  Finset.univ (α := Sym2 (Fin (n + 1)))`. -/
lemma Fin.sym2_univ_succ {n : ℕ} :
    Finset.univ (α := Sym2 (Fin (n + 1))) =
    Finset.univ.map Fin.sym2_castSucc ∪
    Finset.univ.map Fin.sym2_with_fin_last ∪
    {s(Fin.last n, Fin.last n)} := by
  ext a; simp; obtain ⟨a, b⟩ := a
  by_cases h₁ : a = Fin.last n <;> by_cases h₂ : b = Fin.last n <;> simp at *
  · tauto
  · right; right; use ⟨b.val, by grind⟩
    simp [Fin.sym2_with_fin_last]; tauto
  · right; right; use ⟨a.val, by grind⟩
    simp [Fin.sym2_with_fin_last]; tauto
  · right; left; use s(⟨a.val, by grind⟩, ⟨b.val, by grind⟩)
    simp [Fin.sym2_castSucc]

/-!
## Removal and addition of vertex to simple graph.
-/

/-- Addition of vertex to `SimpleGraph (Fin n)`, with `vertices` being set of
vertices that will be connected by edge to this new vertex. -/
def add_vertex {n} (G : SimpleGraph (Fin n)) (vertices : Finset (Fin n)) :
    SimpleGraph (Fin (n + 1)) :=
  ⟨fun (x y : Fin (n + 1)) =>
    if h₁ : x = Fin.last n
    then if h₂ : y = Fin.last n
         then False
         else (⟨y.val, by grind⟩ : Fin n) ∈ vertices
    else if h₂ : y = Fin.last n
         then (⟨x.val, by grind⟩ : Fin n) ∈ vertices
         else G.Adj ⟨x.val, by grind⟩ ⟨y.val, by grind⟩,
    by intros x y h; split_ifs at * <;> try grind
       exact G.symm h,
    by intros x h; simp at h; grind⟩

/-- Removal of vertex (`Fin.last n`) from `SimpleGraph (Fin (n + 1))`. -/
def remove_vertex {n} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    SimpleGraph (Fin n) :=
  ⟨fun x y => G.Adj x.castSucc y.castSucc,
   fun _ _ h => G.symm h,
   fun _ h => G.irrefl h⟩

/-- If we remove vertex and then add it back together with all edges
that were connected to it, we get the original simple graph. -/
lemma add_vertex_remove_last_vertex_eq_self {n} (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] :
    add_vertex (remove_vertex G) {x : Fin n | G.Adj (Fin.last n) x.castSucc} = G := by
    ext x y; simp [add_vertex, remove_vertex]; split_ifs
    · rename_i h; subst h; simp; intros h h₀; subst h₀; exact G.irrefl h
    · rename_i h₁ h₂; subst h₂; constructor <;> exact fun h => G.symm h
    · rfl

/-- Given `SimpleGraph (Fin (n + 1))`, there exists smaller simple graph
`SimpleGraph (Fin n)` and set of vertices `Finset (Fin n)` that
the bigger graph is equal to smaller graph with additional vertex
(and corresponding new edges, of course). -/
lemma eq_add_vertex_to_smaller {n} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    ∃ G' vs, G = add_vertex G' vs := by
  use (remove_vertex G), ({x | G.Adj (Fin.last n) x.castSucc} : Finset (Fin n))
  exact (add_vertex_remove_last_vertex_eq_self G).symm

/-- Instance of `DecidableRel` for relation `(add_vertex G vs).Adj`. -/
instance add_vertex_adj_decidable :
    ∀ {n} (G : SimpleGraph (Fin n)) (vs : Finset (Fin n)) [DecidableRel G.Adj]
    [∀ x, Decidable (x ∈ vs)], DecidableRel (add_vertex G vs).Adj := by
  intros n G vs h₁ h₂
  intros x y; simp [add_vertex]
  split_ifs <;> rename_i h₃
  · by_cases h₄ : y = Fin.last n <;> simp [h₄]
    · exact instDecidableFalse
    · apply h₂
  · apply h₂
  · apply h₁

/-- Instance of `DecidableRel` for relation `(remove_vertex G).Adj`. -/
instance remove_vertex_adj_decidable :
    ∀ {n} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj],
    DecidableRel (remove_vertex G).Adj := by
  intros n G inst x y; simp [remove_vertex]
  apply inst

/-- Impact of additional vertex (and additional edges) on the sum of vertex degrees. -/
lemma add_vertex_degree_sum {n} (G : SimpleGraph (Fin n)) (vs : Finset (Fin n))
    [DecidableRel G.Adj] [∀ x, Decidable (x ∈ vs)] [DecidableRel (add_vertex G vs).Adj] :
    ∑ v, (add_vertex G vs).degree v = (∑ v, G.degree v) + 2 * vs.card := by
  simp [add_vertex]
  rw [Fin.sum_univ_castSucc];
  rw [show ∑ v, G.degree v + 2 * vs.card = ∑ v, G.degree v + vs.card + vs.card by ring]
  congr
  · unfold SimpleGraph.degree
    simp_rw [SimpleGraph.neighborFinset_eq_filter]
    simp
    simp_rw [Fin.card_filter_univ_succ'_last]
    simp [Finset.sum_add_distrib]
    have h : ({x | x ∈ vs} : Finset _).card = vs.card := by
      simp [Finset.filter_mem_eq_inter]
    rw [h, add_comm]
  · unfold SimpleGraph.degree SimpleGraph.neighborFinset
    simp
    apply Finset.card_bij (fun a ha => by simp at ha; use a.val; grind)
    · intros a ha; simp at ha; grind
    · intros a ha b hb; simp at ha hb; grind
    · intros a ha; simp
      use a.castSucc; simpa

/-- Impact of additional vertex (and additional edges) on the set of all edges. -/
lemma add_vertex_edgeFinset {n} (G : SimpleGraph (Fin n)) (vs : Finset (Fin n))
    [DecidableRel G.Adj] [∀ x, Decidable (x ∈ vs)] [DecidableRel (add_vertex G vs).Adj] :
    (add_vertex G vs).edgeFinset =
    G.edgeFinset.map Fin.sym2_castSucc ∪ vs.map Fin.sym2_with_fin_last := by
  ext x; simp
  constructor <;> intro h
  · unfold add_vertex at h
    obtain ⟨a, b⟩ := x; simp at h; split_ifs at h
    · rename_i h₀; subst a
      obtain ⟨h, h₀⟩ := h
      right; use ⟨b.val, by lia⟩; simp [h₀]
      ext a
      simp [Fin.sym2_with_fin_last]
      grind
    · rename_i h₀ h₁; subst b
      right; use ⟨a.val, by lia⟩
      simp [h, Fin.sym2_with_fin_last]
    · rename_i h₀ h₁; left
      use s(⟨a.val, by lia⟩, ⟨b.val, by lia⟩)
      simp [h, Fin.sym2_castSucc]
  · obtain h | h := h
    · obtain ⟨y, ⟨h, h₀⟩⟩ := h
      subst x; obtain ⟨a, b⟩ := y
      simp [add_vertex, Fin.sym2_castSucc] at *
      exact h
    · obtain ⟨a, ⟨h, h₀⟩⟩ := h
      subst x
      simp [add_vertex, Fin.sym2_with_fin_last]
      exact h

/-- Impact of additional vertex (and additional edges) on the count/number of all edges. -/
lemma add_vertex_edgeFinset_card {n} (G : SimpleGraph (Fin n)) (vs : Finset (Fin n))
    [DecidableRel G.Adj] [∀ x, Decidable (x ∈ vs)] [DecidableRel (add_vertex G vs).Adj] :
    (add_vertex G vs).edgeFinset.card = G.edgeFinset.card + vs.card := by
  rw [add_vertex_edgeFinset, Finset.card_union_of_disjoint]
  · simp
  · intros x h₁ h₂ t h₃
    simp only [Finset.le_eq_subset, Finset.bot_eq_empty, Finset.notMem_empty] at *
    have h₄ := h₁ h₃; clear h₁
    have h₅ := h₂ h₃; clear h₂
    simp only [Finset.mem_map, Set.mem_toFinset] at *
    obtain ⟨a, ha, h₄⟩ := h₄
    obtain ⟨b, hb, h₅⟩ := h₅
    subst t
    obtain ⟨a₁, a₂⟩ := a
    simp [Fin.sym2_with_fin_last, Fin.sym2_castSucc] at *
    grind

/-!
## Removal and addition of edge to simple graph.
-/

/-- Addition of new edge to simple graph. -/
def add_edge {V} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v₁ v₂ : V} (hv : v₁ ≠ v₂) (_hg : ¬ G.Adj v₁ v₂) :
    SimpleGraph V :=
  ⟨fun x y => G.Adj x y ∨ s(x, y) = s(v₁, v₂),
    by intros x y h; simp at *
       obtain h | h := h
       · left; exact G.symm h
       · right; grind,
    by intros x h; simp at h; grind⟩

/-- Removal of some edge from simple graph. -/
def remove_edge {V} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    {v1 v2 : V} (_ : G.Adj v1 v2) :
    SimpleGraph V :=
  ⟨fun x y => G.Adj x y ∧ s(x, y) ≠ s(v1, v2),
   by intros x y h
      simp at *
      exact ⟨G.symm h.1, by grind⟩,
   by intros x h
      simp at *⟩

/-- Instance of `DecidableRel` for relation `(remove_edge G hv`. -/
instance remove_edge_adj_decidable : ∀ {V} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) {v₁ v₂ : V} (hv : G.Adj v₁ v₂)
    [DecidableRel G.Adj], DecidableRel (remove_edge G hv).Adj := by
  intros V inst₁ inst₂ G v₁ v₂ hv inst₃ a b
  simp [remove_edge]
  exact instDecidableAnd

/-- Instance of  `DecidableRel` for relation `add_edge G hv hg`. -/
instance decidable_add_edge_adj : ∀ {V} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v₁ v₂ : V} (hv : v₁ ≠ v₂) (hg : ¬ G.Adj v₁ v₂),
    DecidableRel (add_edge G hv hg).Adj := by
  intros v inst inst₁ G inst₂ v₁ v₂ hv hg
  simp [add_edge]
  intros x y; exact instDecidableOr

/-- The graph stays the same if an edge is removed and then added back again. -/
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

/-- Set of all edges after adding new edge. -/
lemma edgeFinset_after_add_edge {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v₁ v₂ : V} (hv : v₁ ≠ v₂) (hg : ¬ G.Adj v₁ v₂) :
    (add_edge G hv hg).edgeFinset = insert s(v₁, v₂) G.edgeFinset := by
  ext x
  simp [add_edge]
  obtain ⟨a, b⟩ := x
  simp; grind

/-- Degree of specific vertex after adding new edge. -/
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
