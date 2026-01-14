import Mathlib

open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Classical in
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
    set G' := G.deleteIncidenceSet a
    simp only [Finset.cons_eq_insert, Finset.coe_insert] at hG
    have hG' : G'.IsBipartiteWith ↑s ↑t := by
      constructor
      · have h₀ := hG.disjoint
        simp only [Set.disjoint_insert_left, SetLike.mem_coe, Finset.disjoint_coe] at h₀
        simp only [Finset.disjoint_coe]; exact h₀.2
      · intros x y hxy; simp
        have h₀ := hG.mem_of_adj
        simp only [Set.mem_insert_iff, SetLike.mem_coe] at h₀
        simp only [G'] at hxy; rw [G.deleteIncidenceSet_adj] at hxy
        grind
    obtain ⟨hG'₀, hG'₁⟩ := @iH G' hG'
    have h₀ : G.edgeSet = G'.edgeSet ∪
        (t.filter (G.Adj a)).map ⟨fun u => s(u, a), by intros u w; simp; grind⟩ := by
      simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_filter, G']
      ext e; simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
      constructor <;> intro h₁
      · cases e; rename_i x y; simp only [mem_edgeSet, Sym2.eq, Sym2.rel_iff',
        Prod.mk.injEq, Prod.swap_prod_mk] at *
        rw [G.deleteIncidenceSet_adj]
        simp only [h₁, true_and]
        by_cases h₂ : x = a <;> by_cases h₃ : y = a
        · simp only [h₂, h₃, and_self, and_true, or_self, exists_eq_right,
          SimpleGraph.irrefl, and_false]; subst x y; right; exact G.irrefl h₁
        · simp only [h₂, ne_eq, not_true_eq_false, h₃, not_false_eq_true, and_true, Ne.symm h₃,
            and_false, false_or, exists_eq_right]
          subst a
          have h₄ := hG.mem_of_adj h₁.symm;
          simp only [h₁, and_true]
          simp only [Set.mem_insert_iff, SetLike.mem_coe, true_or, and_true, h₃, false_or] at h₄
          obtain ⟨h₄, h₅⟩ | h₄ := h₄
          · have h₆ := hG.disjoint (x := {x}) (by simp)
              (by simp only [Set.le_eq_subset, Set.singleton_subset_iff, SetLike.mem_coe]
                  exact h₅)
            simp at h₆
          · exact h₄
        · simp only [ne_eq, h₂, not_false_eq_true, h₃, not_true_eq_false, and_false, and_true,
          false_or]
          subst a; use x; simp only [true_or, and_true]
          simp only [h₁.symm, and_true]
          apply hG.mem_of_adj at h₁
          simp only [Set.mem_insert_iff, SetLike.mem_coe, true_or, and_true] at h₁
          obtain ⟨h₃ | h₃, h₄⟩ | h₃ := h₁ <;> try grind
          have h₅ := hG.disjoint (x := {y}) (by simp)
            (by simp only [Set.le_eq_subset, Set.singleton_subset_iff, SetLike.mem_coe]; exact h₄)
          simp at h₅
        · simp [h₂, h₃]
      · cases e; rename_i x y; simp only [mem_edgeSet, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk] at h₁ ⊢
        obtain h₁ | h₁ := h₁
        · exact h₁.1
        · obtain ⟨w, h₁, ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩⟩ := h₁
          · subst w a; exact h₁.2.symm
          · subst w a; exact h₁.2
    rw [h₀]; simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_filter,
      Set.finite_union, hG'₀, true_and, Finset.cons_eq_insert]
    constructor
    · apply Set.Finite.image (fun u => s(u, a))
      apply Set.Finite.inter_of_left
      exact Set.finite_mem_finset t
    · have h₁ : {x | x ∈ t ∧ G.Adj a x}.Finite := by
        apply Set.Finite.inter_of_left
        apply Finset.finite_toSet
      have h₂ : Finite ↑{x | x ∈ t ∧ G.Adj a x} := h₁
      have h₃ : ((fun u => s(u, a)) '' {x | x ∈ t ∧ G.Adj a x}).Finite := by
        exact Set.Finite.image (fun u => s(u, a)) h₁
      have h₄ : Finite ↑((fun u => s(u, a)) '' {x | x ∈ t ∧ G.Adj a x}) := h₃
      rw [Set.ncard_union_eq (hs := hG'₀) (ht := h₄)]
      · simp only [h, not_false_eq_true, Finset.card_insert_of_notMem, ge_iff_le]; rw [Nat.succ_mul]
        have h₅ : ((fun u => s(u, a)) '' {x | x ∈ t ∧ G.Adj a x}).ncard ≤
                  {x | x ∈ t ∧ G.Adj a x}.ncard := by
          apply Set.ncard_image_le
          exact h₁
        have h₆ : {x | x ∈ t ∧ G.Adj a x}.ncard ≤ (SetLike.coe t).ncard := by
          apply Set.ncard_inter_le_ncard_left
          exact Set.finite_mem_finset t
        simp at h₆
        linarith
      · rw [Set.disjoint_iff_inter_eq_empty]
        ext e; cases e; rename_i x y;
        simp [G', SimpleGraph.deleteIncidenceSet_adj]; grind


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
