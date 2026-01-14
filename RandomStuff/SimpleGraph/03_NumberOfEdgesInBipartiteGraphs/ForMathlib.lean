import Mathlib

namespace SimpleGraph
variable {V : Type*} [instV : DecidableEq V] {G : SimpleGraph V} [instG : DecidableRel G.Adj]

theorem IsBipartiteWith.edgeSet_ncard_le_of_finsets {s t : Finset V} (hG : G.IsBipartiteWith ↑s ↑t) :
    G.edgeSet.Finite ∧ G.edgeSet.ncard ≤ s.card * t.card := by
  revert instG hG G
  induction s using Finset.cons_induction with
  | empty =>
    intros G instG hG
    have hG₀ : G = ⊥ := by
      ext x y; simp; intros hxy; apply hG.mem_of_adj at hxy; simp at hxy
    subst G; simp
  | cons a s h iH =>
    intros G instG hG
    set G' : SimpleGraph V :=
      ⟨(fun x y => G.Adj x y ∧ x ≠ a ∧ y ≠ a),
       by intros x y hxy; tauto,
       by intros x h; exact G.irrefl h.1⟩
    simp at hG
    have instG' : DecidableRel G'.Adj := by
      simp [G']; intros x y; simp; have inst := instG x y; exact instDecidableAnd
    have hG' : G'.IsBipartiteWith ↑s ↑t := by
      constructor
      · have h₀ := hG.disjoint
        simp at h₀; simp; exact h₀.2
      · intros x y hxy; simp
        have h₀ := hG.mem_of_adj
        simp at h₀; simp [G'] at hxy
        obtain ⟨h₁, h₂, h₃⟩ := hxy
        apply h₀ at h₁
        grind
    obtain ⟨hG'₀, hG'₁⟩ := @iH G' instG' hG'
    have h₀ : G.edgeSet = G'.edgeSet ∪
        (t.filter (G.Adj a)).map ⟨fun u => s(u, a), by intros u w; simp; grind⟩ := by
      simp [G']; ext e; simp; constructor <;> intro h₁
      · cases e; rename_i x y; simp at *; simp [h₁]
        cases (instV x a) <;> cases (instV y a) <;> rename_i h₂ h₃
        · simp [h₂, h₃]
        · simp [Ne.symm h₂, h₃]; subst a
          have h₃ := hG.mem_of_adj h₁.symm; simp [h₂] at h₃
          simp [h₁.symm]; obtain h₃ | ⟨h₃, h₄⟩ := h₃
          · exact h₃
          · have h₅ := hG.disjoint (x := {y}) (by simp) (by simp; exact h₃)
            simp at h₅
        · simp [h₂, Ne.symm h₃]; subst a; simp [h₁]
          have h₄ := hG.mem_of_adj h₁; simp [h₃] at h₄
          obtain h₄ | ⟨h₄, h₅⟩ := h₄
          · exact h₄
          · have h₆ := hG.disjoint (x := {x}) (by simp) (by simp; exact h₄)
            simp at h₆
        · simp [h₂, h₃]; subst x y; exact G.irrefl h₁
      · cases e; rename_i x y; simp at h₁ ⊢
        obtain h₁ | h₁ := h₁
        · exact h₁.1
        · obtain ⟨w, h₁, ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩⟩ := h₁
          · subst w a; exact h₁.2.symm
          · subst w a; exact h₁.2
    rw [h₀]; simp [hG'₀]
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
      · simp [h]; rw [Nat.succ_mul]
        have h₅ : ((fun u => s(u, a)) '' {x | x ∈ t ∧ G.Adj a x}).ncard ≤ {x | x ∈ t ∧ G.Adj a x}.ncard := by
          apply Set.ncard_image_le
          exact h₁
        have h₆ : {x | x ∈ t ∧ G.Adj a x}.ncard ≤ (SetLike.coe t).ncard := by
          apply Set.ncard_inter_le_ncard_left
          exact Set.finite_mem_finset t
        simp at h₆
        linarith
      · rw [Set.disjoint_iff_inter_eq_empty]
        ext e; cases e; rename_i x y; simp; grind


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
    · simp [hs]
      by_cases ht₀ : t.encard = 0
      · simp [ht₀]; ext x y; simp; intro hxy
        apply h.mem_of_adj at hxy; simp at ht₀; simp [ht₀] at hxy
      · simp [ht₀]
    · simp [ht]
      by_cases hs₀ : s.encard = 0
      · simp [hs₀]; ext x y; simp; intro hxy
        apply h.mem_of_adj at hxy; simp at hs₀; simp [hs₀] at hxy
      · simp [hs₀]
