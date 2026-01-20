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

def edges_from_set_to_vertex (t : Set V) (a : V) :=
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
  simp [deleteIncidenceSet_adj, edges_from_set_to_vertex]
  grind

lemma ncard_edges_from_set_to_vertex (t : Finset V) (a : V) :
    (edges_from_set_to_vertex (G := G) t a).Finite ∧
    (edges_from_set_to_vertex (G := G) t a).ncard ≤ t.card := by
  have h₁ : {x | x ∈ t ∧ G.Adj a x}.Finite := by
    apply Set.Finite.inter_of_left
    apply Finset.finite_toSet
  have h₂ : (edges_from_set_to_vertex t a).Finite :=
    Set.Finite.image (fun u => s(u, a)) h₁
  have h₅ : (edges_from_set_to_vertex (G := G) t a).ncard ≤
            {x | x ∈ t ∧ G.Adj a x}.ncard :=
    Set.ncard_image_le h₁
  have h₆ : ({x | x ∈ t ∧ G.Adj a x}).ncard ≤ (t : Set V).ncard := by
    apply Set.ncard_inter_le_ncard_left
    exact Set.finite_mem_finset t
  simp only [Set.ncard_coe_finset] at h₆
  refine ⟨h₂, Nat.le_trans h₅ h₆⟩


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
      exact Nat.add_le_add hG'₁ h₂
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
  rw [isBipartite_iff_exists_isBipartiteWith] at h
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
    have h₃ : 4 * s.ncard * t.ncard ≤ (s.ncard + t.ncard) ^ 2 :=
      four_mul_le_pow_two_add s.ncard t.ncard
    have h₄ : 4 * G.edgeSet.ncard ≤ 4 * s.ncard * t.ncard := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left 4 hG
    exact Nat.le_trans (Nat.le_trans h₄ h₃) h₂
  · simp at hv; simp


lemma colorable_induce {n} (h : G.Colorable n) (A : Set V) : (G.induce A).Colorable n := by
  simp only [induce, SimpleGraph.comap, Function.Embedding.subtype_apply] at h ⊢
  obtain ⟨colors, property⟩ := h
  use fun a => colors (a.val)
  intros a b hab hab'; simp only [completeGraph_eq_top, top_adj, ne_eq] at property hab
  exact property hab hab'


lemma edgeSet_encard_of_induce_support :
    (G.induce G.support).edgeSet.encard = G.edgeSet.encard := by
  set f := fun (p : Sym2 ↑G.support) => p.map (fun a => a.val)
  rw [← Function.Injective.encard_image (f := f)]
  · congr; ext x; simp only [Set.mem_image, f]
    constructor <;> intro h
    · obtain ⟨y, h₀, h₁⟩ := h
      cases x with | h x₁ y₁ =>
      cases y with | h x₂ y₂ =>
      simp only [mem_edgeSet, comap_adj, Function.Embedding.subtype_apply, Sym2.map_pair_eq,
        Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at *
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h₁
      · exact h₀
      · exact h₀.symm
    · rw [Sym2.exists]; simp only [mem_edgeSet, comap_adj, Function.Embedding.subtype_apply,
      Sym2.map_pair_eq, Subtype.exists, exists_and_left, exists_prop]
      cases x with | h x y =>
      simp only [mem_edgeSet, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at *
      use x; simp only [true_and]; refine ⟨?_, ?_⟩
      · exact (mem_support G).mpr (by use y)
      · use y; exact ⟨h, (mem_support G).mpr (by use x; exact h.symm), by simp⟩
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
    simp only [f, Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at h ⊢
    grind


theorem IsBipartite.four_mul_encard_edgeSet_le_support_encard_sq (h : G.IsBipartite) :
    4 * G.edgeSet.encard ≤ G.support.encard ^ 2 := by
  set G' := G.induce ↑G.support
  have G'_isBipartite : G'.IsBipartite := colorable_induce h _
  have G'_edgeSet_encard : G'.edgeSet.encard = G.edgeSet.encard :=
    edgeSet_encard_of_induce_support
  apply IsBipartite.four_mul_encard_edgeSet_le at G'_isBipartite
  rwa [G'_edgeSet_encard] at G'_isBipartite



--- criterions for equality (not to be added to Mathlib, at least not now)

def IsBipartiteWith.complete {s t : Set V} (h : Disjoint s t) :
    SimpleGraph V :=
  ⟨(fun x y => x ∈ s ∧ y ∈ t ∨ x ∈ t ∧ y ∈ s),
   by intros x y hxy; grind,
   by intros x hx; grind⟩

def IsBipartiteWith.complete_is_bipartite {s t : Set V} (h : Disjoint s t) :
    (IsBipartiteWith.complete h).IsBipartiteWith s t := by
  simp only [IsBipartiteWith.complete]
  refine ⟨h, by simp⟩

lemma disjoint_of_insert_left_of_finsets {s t : Finset V} {a : V} [DecidableEq V]
    (h : Disjoint ↑(insert a s) (t : Set V)) :
    Disjoint (s : Set V) (t : Set V) := by
  simp only [Finset.coe_insert, Set.disjoint_insert_left, SetLike.mem_coe,
    Finset.disjoint_coe] at h
  simp only [Finset.disjoint_coe]
  exact h.2

lemma IsBipartiteWith.complete_decompose {s t : Finset V} {a : V}
    [DecidableEq V] (h : Disjoint ↑(insert a s) ↑t) :
    (complete h).edgeSet =
    (complete (disjoint_of_insert_left_of_finsets h)).edgeSet ∪
    edges_from_set_to_vertex (G := complete h) t a := by
  simp only [complete, Finset.coe_insert, Set.mem_insert_iff, SetLike.mem_coe,
    edges_from_set_to_vertex, true_or, true_and]
  ext x; cases x; rename_i x y; simp; grind

lemma IsBipartiteWith.complete_decompose_disjoint {s t : Finset V} {a : V}
    (ha : a ∉ s) [DecidableEq V] (h : Disjoint ↑(insert a s) ↑t) :
    Disjoint
      (complete (disjoint_of_insert_left_of_finsets h)).edgeSet
      (edges_from_set_to_vertex (G := complete h) t a) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  simp only [complete, SetLike.mem_coe, edges_from_set_to_vertex, Finset.coe_insert,
    Set.mem_insert_iff, true_or, true_and]
  ext e; simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and, not_exists, and_imp]
  cases e; rename_i x y; simp only [mem_edgeSet, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, not_or, not_and]
  simp only [Finset.coe_insert, Set.disjoint_insert_left, SetLike.mem_coe,
    Finset.disjoint_coe] at h
  grind

lemma IsBipartiteWith.complete_edgeSet_finite_of_finsets {s t : Finset V}
    (h : Disjoint (s : Set V) (t : Set V)) :
    (complete h).edgeSet.Finite :=
  (edgeSet_ncard_le_of_finsets (complete_is_bipartite h)).1

lemma IsBipartiteWith.complete_decompose_card_right {s t : Finset V} {a : V}
    [DecidableEq V] (h : Disjoint ↑(insert a s) ↑t) :
    (edges_from_set_to_vertex (G := complete h) t a).encard = ↑t.card := by
  simp only [edges_from_set_to_vertex, SetLike.mem_coe, Finset.coe_insert]
  rw [Function.Injective.encard_image]
  · rw [Set.setOf_and]; simp only [SetLike.setOf_mem_eq, complete, Set.mem_insert_iff,
    SetLike.mem_coe, true_or, true_and]
    have h₀ : ↑t ⊆ {a_1 | a_1 ∈ t ∨ a ∈ t ∧ (a_1 = a ∨ a_1 ∈ s)} := by
      intros x hx; simp at *; tauto
    rw [Set.inter_eq_self_of_subset_left h₀]
    simp
  · intros x y hxy; simp at hxy; grind


def IsBipartiteWith.edgeSet_encard_of_complete_of_finsets {s t : Finset V}
    (h : Disjoint (s : Set V) (t : Set V)) :
    (complete h).edgeSet.Finite ∧ (complete h).edgeSet.encard = ↑s.card * ↑t.card := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h₀ : complete h = ⊥ := by
      ext x y; simp [complete]
    rw [h₀]; simp
  | insert a s ha iH =>
    have h₀ := complete_edgeSet_finite_of_finsets h
    refine ⟨h₀, ?_⟩
    have h₁ : Disjoint (s : Set V) (t : Set V) := disjoint_of_insert_left_of_finsets h
    obtain ⟨h₂, h₃⟩ := iH h₁
    rw [complete_decompose, Set.encard_union_eq (complete_decompose_disjoint ha h)]
    rw [h₃, complete_decompose_card_right, Finset.card_insert_of_notMem ha]
    norm_cast; rw [Nat.succ_mul]



lemma subset_of_inter_eq_self {X Y : Set V}
    (h : (X ∩ Y).ncard = X.ncard) (hX : X.Finite) (hY : Y.Finite) :
    X ⊆ Y := by
  have instX : Finite ↑X := Set.finite_coe_iff.mpr hX
  have instY : Finite ↑Y := Set.finite_coe_iff.mpr hY
  have inst : Finite ↑(X ∩ Y) := Finite.Set.finite_inter_of_left X Y
  rw [← Set.ncard_inter_add_ncard_diff_eq_ncard (s := X) (t := Y) ] at h
  simp only [Nat.left_eq_add] at h
  have inst' : Finite ↑(X \ Y) := Finite.Set.finite_diff X Y
  rw [Set.ncard_eq_zero inst'] at h
  rw [Set.diff_eq_empty] at h; exact h

lemma neighborSet_finite_of_edgeSet_finite {a : V} (h : G.edgeSet.Finite) :
    (G.neighborSet a).Finite := by
  set f : V → Sym2 V := fun x : V => s(x, a)
  have h₀ : f '' G.neighborSet a ⊆ G.edgeSet := by
    intros e h; cases e; rename_i x y; simp only [Set.mem_image, mem_neighborSet, mem_edgeSet] at *
    obtain ⟨v, h⟩ := h; simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
      f] at h;
    obtain ⟨h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
    · exact h.symm
    · exact h
  have h₁ : (f '' G.neighborSet a).Finite := Set.Finite.subset h h₀
  apply Set.Finite.of_finite_image h₁
  intro x hx y hy hxy; simp [f] at hxy; grind

lemma edges_from_set_to_vertex_le (t : Finset V) (a : V) :
    (edges_from_set_to_vertex (G := G) t a).ncard ≤ t.card := by
  simp only [edges_from_set_to_vertex]
  have h₉ : {x | x ∈ t ∧ G.Adj a x}.Finite := by
    rw [@Set.setOf_and]
    exact Set.toFinite ({a | a ∈ t} ∩ {a_1 | G.Adj a a_1})
  have h₁₀ := Set.ncard_image_le (f := fun u ↦ s(u, a)) h₉
  have h₁₁ : {x | x ∈ t ∧ G.Adj a x}.ncard ≤ (t : Set V).ncard := by
    apply Set.ncard_le_ncard (ht := Finset.finite_toSet t)
    exact Set.sep_subset (Membership.mem t.val) (G.Adj a)
  simp only [Set.ncard_coe_finset] at h₁₁
  exact Nat.le_trans h₁₀ h₁₁




lemma IsBipartiteWith.encard_edgeSet_is_max_of_finsets
    {s t : Finset V} (h : G.IsBipartiteWith ↑s ↑t) :
    G.edgeSet.ncard = s.card * t.card ↔ G = IsBipartiteWith.complete h.disjoint := by
  have h₀ : G.edgeSet.Finite := by
    have h₁ := IsBipartiteWith.edgeSet_ncard_le_of_finsets h
    exact h₁.1
  revert G h h₀
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.coe_empty, Finset.card_empty, zero_mul]
    intros G h h₀
    constructor <;> intro h₁
    · rw [Set.ncard_eq_zero (hs := h₀)] at h₁
      simp only [edgeSet_eq_empty] at h₁; subst G
      ext x y; simp [complete]
    · rw [h₁]
      have h₂ := edgeSet_encard_of_complete_of_finsets (s := ∅) (t := t)
        (by convert h.disjoint; simp)
      simp only [Finset.coe_empty, Finset.card_empty, CharP.cast_eq_zero, zero_mul,
        Set.encard_eq_zero, edgeSet_eq_empty] at h₂ ⊢
      rw [h₂.2]; simp
  | cons a s ha iH =>
    simp only [Finset.coe_cons, Finset.card_cons]; intros G h h₀
    constructor <;> intro h₁
    · have h' := edgeSet_decompose (G := G) a
      rw [h'] at h₁
      rw [incidenceSet_in_bipartite h] at h₁
      have h₂ := disjoint_edgeSet_decompose (G := G) t a
      have h₃ : (G.deleteIncidenceSet a).edgeSet.Finite :=
        Set.Finite.subset h₀ (edgeSet_mono (deleteIncidenceSet_le G a))
      have h₄ : (edges_from_set_to_vertex (G := G) t a).Finite :=
        Set.Finite.image _ (Set.toFinite _)
      rw [Set.ncard_union_eq (hs := h₃) (ht := h₄) h₂] at h₁
      have h₅ : (G.deleteIncidenceSet a).IsBipartiteWith ↑s ↑t :=
        stays_bipartite_after_vertex_removal h
      obtain ⟨h₆, h₇⟩ := edgeSet_ncard_le_of_finsets (G := G.deleteIncidenceSet a) h₅
      rw [Nat.succ_mul] at h₁
      have h₈ : (edges_from_set_to_vertex (G := G) ↑t a).ncard ≤ t.card :=
        edges_from_set_to_vertex_le t a
      have h₉ : (G.deleteIncidenceSet a).edgeSet.ncard = s.card * t.card := by
        linarith
      have h₁₀ : (edges_from_set_to_vertex (G := G) ↑t a).ncard = t.card := by
        linarith
      have h₁₁ := (iH h₅ h₆).mp h₉
      have h₁₂ : t.card = (t : Set V).ncard := by simp
      rw [h₁₂] at h₁₀
      simp [edges_from_set_to_vertex] at h₁₀
      have h₁₃ : ((fun u ↦ s(u, a)) '' {x | x ∈ t ∧ G.Adj a x}).ncard ≤
          (↑t ∩ G.neighborSet a).ncard := by
        apply Set.ncard_image_le; rw [Set.setOf_and]; apply Set.toFinite
      have h₁₄ : (↑t ∩ G.neighborSet a).ncard ≤ t.card := by
        rw [h₁₂]
        apply Set.ncard_inter_le_ncard_left
        exact Finset.finite_toSet t
      have h₁₅ : (↑t ∩ G.neighborSet a).ncard = t.card := by linarith
      rw [h₁₂] at h₁₅
      rw [← SimpleGraph.edgeSet_inj, h']
      classical
      have h₁₆ := complete_decompose (by convert h.disjoint; simp; rfl)
      simp only [Finset.coe_insert] at h₁₆; rw [h₁₆]
      rw [h₁₁]; congr
      have h₁₇ := subset_of_inter_eq_self h₁₅ (Finset.finite_toSet t)
        (by apply neighborSet_finite_of_edgeSet_finite; exact h₀)
      simp only [complete, Set.mem_insert_iff, SetLike.mem_coe, edges_from_set_to_vertex, true_or,
        true_and] at h₁₆
      have h₁₈ : ↑t = G.neighborSet a := by
        ext x; simp only [SetLike.mem_coe, mem_neighborSet]
        constructor <;> intros h₁₈
        · apply h₁₇; simp only [SetLike.mem_coe]; exact h₁₈
        · have h₁₉ := h.mem_of_adj h₁₈
          simp only [Set.mem_insert_iff, SetLike.mem_coe, true_or, true_and] at h₁₉
          obtain h₁₉ | h₁₉ := h₁₉
          · exact h₁₉
          · obtain ⟨h₁₉, h₂₀ | h₂₀⟩ := h₁₉
            · subst x; exact h₁₉
            · have h₂₁ := h.disjoint (x := {a}); simp only [Set.le_eq_subset,
              Set.singleton_subset_iff, Set.mem_insert_iff, SetLike.mem_coe, true_or,
              Set.bot_eq_empty, Set.subset_empty_iff, Set.singleton_ne_empty, imp_false,
              forall_const] at h₂₁
              tauto
      simp only at h₁₇; rw! [h₁₈]
      simp only [incidenceSet, edges_from_set_to_vertex, mem_neighborSet, complete,
        Set.mem_insert_iff, SetLike.mem_coe, true_or, true_and, SimpleGraph.irrefl, false_and,
        or_false, and_self]
      ext e; cases e; rename_i x y
      simp only [Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, Set.mem_image, Sym2.eq, Sym2.rel_iff',
        Prod.mk.injEq, Prod.swap_prod_mk]
      constructor <;> intros h₁₈
      · obtain ⟨h₁₈, rfl | rfl⟩  := h₁₈
        · use y; simp [h₁₈]
        · use x; simp only [and_self, true_or, and_true]; exact h₁₈.symm
      · obtain ⟨w, h₁₈, h₁₉⟩ := h₁₈
        obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h₁₉
        · simp only [or_true, and_true]; exact h₁₈.symm
        · simp only [h₁₈, true_or, and_self]
    · rw [h₁]
      classical
      obtain ⟨h₂, h₃⟩ := edgeSet_encard_of_complete_of_finsets (t := t) (s := insert a s)
        (by convert h.disjoint; simp)
      rw [← Set.Finite.cast_ncard_eq h₂] at h₃
      norm_cast at h₃; simp only [Finset.coe_insert, ha, not_false_eq_true,
        Finset.card_insert_of_notMem] at h₃
      exact h₃
