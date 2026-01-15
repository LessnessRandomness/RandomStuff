import Mathlib

open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma stays_bipartite_after_vertex_removal {s t : Finset V} {a : V}
    (hG : G.IsBipartiteWith (insert a ↑s) ↑t) :
    (G.deleteIncidenceSet a).IsBipartiteWith ↑s ↑t := by
  constructor
  · have h₀ := hG.disjoint
    simp only [Set.disjoint_insert_left, SetLike.mem_coe, Finset.disjoint_coe] at h₀
    simp only [Finset.disjoint_coe]; exact h₀.2
  · intros x y hxy; simp only [SetLike.mem_coe]
    have h₀ := hG.mem_of_adj
    simp only [Set.mem_insert_iff, SetLike.mem_coe] at h₀
    rw [G.deleteIncidenceSet_adj] at hxy; grind

lemma edgeSet_decompose (a : V) :
    G.edgeSet = (G.deleteIncidenceSet a).edgeSet ∪ G.incidenceSet a := by
  symm; rw [edgeSet_deleteIncidenceSet];
  simp only [Set.diff_union_self]
  exact Set.union_eq_self_of_subset_right (incidenceSet_subset G a)

def edges_from_set_to_vertex (t : Finset V) (a : V) :=
    ((fun u ↦ s(u, a)) '' {x | x ∈ t ∧ G.Adj a x})

lemma incidenceSet_in_bipartite {s t : Finset V} {a : V}
    (hG : G.IsBipartiteWith (insert a ↑s) ↑t) :
    G.incidenceSet a = edges_from_set_to_vertex (G := G) t a := by
  ext e; cases e; rename_i x y; simp only [mk'_mem_incidenceSet_iff, edges_from_set_to_vertex,
    Set.mem_image, Set.mem_setOf_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  constructor <;> intro h
  · obtain ⟨h, h₀ | h₀⟩ := h
    · subst a; use y; simp only [h, and_true, and_self, or_true]
      have h₀ := hG.mem_of_adj h
      have h₁ := hG.disjoint (x := {x})
      simp at h₁; grind
    · subst a; use x; simp only [h.symm, and_true, and_self, true_or]
      have h₀ := hG.mem_of_adj h
      have h₁ := hG.disjoint (x := {y})
      simp at h₁; grind
  · obtain ⟨w, ⟨h₀, h₁⟩, ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩⟩ := h
    · subst a w; simp [h₁.symm]
    · subst a w; simp [h₁]

lemma disjoint_edgeSet_decompose (t : Finset V) (a : V) :
    Disjoint (G.deleteIncidenceSet a).edgeSet (edges_from_set_to_vertex (G := G) t a) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext e; cases e; rename_i x y;
  simp [SimpleGraph.deleteIncidenceSet_adj, edges_from_set_to_vertex]
  grind

lemma ncard_edges_from_set_to_vertex (t : Finset V) (a : V) :
    Finite ↑(edges_from_set_to_vertex (G := G) t a) ∧
    (edges_from_set_to_vertex (G := G) t a).ncard ≤ t.card := by
  have h₁ : {x | x ∈ t ∧ G.Adj a x}.Finite := by
    apply Set.Finite.inter_of_left
    apply Finset.finite_toSet
  have h₂ : Finite ↑(edges_from_set_to_vertex t a) :=
    Set.Finite.image (fun u => s(u, a)) h₁
  have h₅ : (edges_from_set_to_vertex (G := G) t a).ncard ≤
            {x | x ∈ t ∧ G.Adj a x}.ncard := by
    apply Set.ncard_image_le
    exact h₁
  have h₆ : ({x | x ∈ t ∧ G.Adj a x}).ncard ≤ (SetLike.coe t).ncard := by
    apply Set.ncard_inter_le_ncard_left
    exact Set.finite_mem_finset t
  simp at h₆
  refine ⟨h₂, by linarith⟩


theorem IsBipartiteWith.edgeSet_ncard_le_of_finsets {s t : Finset V}
    (hG : G.IsBipartiteWith ↑s ↑t) :
    G.edgeSet.Finite ∧ G.edgeSet.ncard ≤ s.card * t.card := by
  revert hG G
  induction s using Finset.cons_induction with
  | empty =>
    intros G hG
    have hG₀ : G = ⊥ := by
      ext x y; simp only [bot_adj, iff_false]
      intros hxy; apply hG.mem_of_adj at hxy; simp at hxy
    subst G; simp
  | cons a s h iH =>
    intros G hG
    classical
    simp only [Finset.cons_eq_insert, Finset.coe_insert] at hG
    have hG' : (G.deleteIncidenceSet a).IsBipartiteWith ↑s ↑t :=
      stays_bipartite_after_vertex_removal hG
    obtain ⟨hG'₀, hG'₁⟩ := @iH (G.deleteIncidenceSet a) hG'
    rw [edgeSet_decompose a, incidenceSet_in_bipartite hG]
    simp only [hG'₀, Set.finite_union, Finset.cons_eq_insert, true_and]
    obtain ⟨h₁, h₂⟩ := ncard_edges_from_set_to_vertex (G := G) t a
    refine ⟨h₁, ?_⟩
    rw [Set.ncard_union_eq (hs := hG'₀) (ht := h₁)]
    · simp only [h, not_false_eq_true, Finset.card_insert_of_notMem]
      rw [Nat.succ_mul]
      linarith
    · exact disjoint_edgeSet_decompose t a


theorem IsBipartiteWith.encard_edgeSet_le {s t : Set V} (h : G.IsBipartiteWith s t) :
    G.edgeSet.encard ≤ s.encard * t.encard := by
  by_cases hst : s.Finite ∧ t.Finite
  · obtain ⟨hs, ht⟩ := hst
    have inst_s := hs.fintype; have inst_t := ht.fintype
    have hs' : s = ↑(s.toFinset) := by simp
    have ht' : t = ↑(t.toFinset) := by simp
    rw [hs', ht'] at h
    apply IsBipartiteWith.edgeSet_ncard_le_of_finsets at h
    obtain ⟨h₀, h₁⟩ := h
    have h₂ : G.edgeSet.encard = ↑G.edgeSet.ncard := (Set.Finite.cast_ncard_eq h₀).symm
    have h₃ : s.encard = ↑(s.toFinset.card) := Set.encard_eq_coe_toFinset_card s
    have h₄ : t.encard = ↑(t.toFinset.card) := Set.encard_eq_coe_toFinset_card t
    rw [h₂, h₃, h₄]; norm_cast
  · have hst' : s.Infinite ∨ t.Infinite := by tauto
    obtain hs | ht := hst'
    · simp only [hs, Set.Infinite.encard_eq, ge_iff_le]
      by_cases ht₀ : t.encard = 0
      · simp only [ht₀, mul_zero, nonpos_iff_eq_zero, Set.encard_eq_zero, edgeSet_eq_empty]
        ext x y; simp only [bot_adj, iff_false]; intro hxy
        apply h.mem_of_adj at hxy; simp at ht₀; simp [ht₀] at hxy
      · simp [ht₀]
    · simp only [ht, Set.Infinite.encard_eq, ge_iff_le]
      by_cases hs₀ : s.encard = 0
      · simp only [hs₀, zero_mul, nonpos_iff_eq_zero, Set.encard_eq_zero, edgeSet_eq_empty]
        ext x y; simp only [bot_adj, iff_false]; intro hxy
        apply h.mem_of_adj at hxy; simp at hs₀; simp [hs₀] at hxy
      · simp [hs₀]


theorem IsBipartite.four_mul_encard_edgeSet_le (h : G.IsBipartite) :
    4 * G.edgeSet.encard ≤ ENat.card V ^ 2 := by
  rw [SimpleGraph.isBipartite_iff_exists_isBipartiteWith] at h
  obtain ⟨s, t, h⟩ := h
  have hG := IsBipartiteWith.encard_edgeSet_le h
  have h₀ : s.encard + t.encard ≤ ENat.card V := by
    rw [← Set.encard_union_eq h.disjoint]
    exact Set.encard_le_card
  by_cases hv : Finite V
  · have hs : s.Finite := Set.toFinite s
    have ht : t.Finite := Set.toFinite t
    rw [ENat.card_eq_coe_natCard V] at h₀ ⊢
    have hs' : s.encard = ↑(s.ncard) := (Set.Finite.cast_ncard_eq hs).symm
    have ht' : t.encard = ↑(t.ncard) := (Set.Finite.cast_ncard_eq ht).symm
    rw [hs', ht'] at hG h₀
    have h₁ : G.edgeSet.encard = ↑(G.edgeSet.ncard) := by
      rw [Set.Finite.cast_ncard_eq]
      exact Set.toFinite G.edgeSet
    norm_cast at h₀
    have h₂ : (s.ncard + t.ncard) ^ 2 ≤ Nat.card V ^ 2 :=
      Nat.pow_le_pow_left h₀ 2
    rw [h₁] at hG ⊢; norm_cast at *
    by_cases hst : s.ncard ≤ t.ncard <;> nlinarith
  · simp at hv; simp
