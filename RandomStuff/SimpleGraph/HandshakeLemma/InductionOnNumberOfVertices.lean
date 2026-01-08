import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Ring

set_option linter.flexible false
set_option linter.unusedDecidableInType false


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

def remove_vertex {n} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] : SimpleGraph (Fin n) :=
  ⟨fun x y => G.Adj x.castSucc y.castSucc,
   fun _ _ h => G.symm h,
   fun _ h => G.irrefl h⟩

lemma eq_add_vertex_to_smaller {n} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] :
    ∃ G' vs, G = add_vertex G' vs := by
  use (remove_vertex G), ({x | G.Adj (Fin.last n) x.castSucc} : Finset (Fin n))
  ext x y; simp [add_vertex, remove_vertex]; split_ifs
  · rename_i h; subst h; simp; intros h h₀; subst h₀; exact G.irrefl h
  · rename_i h₁ h₂; subst h₂; constructor <;> exact fun h => G.symm h
  · rfl


local instance add_vertex_decidable_adj :
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



lemma Fin.univ_succ_rev (n : ℕ) :
    Finset.univ = Finset.cons (Fin.last n) (Finset.map
    {toFun := Fin.castSucc, inj' := by intros a b h; simp at h; assumption} Finset.univ)
    (by simp) := by
  simp [Finset.map_eq_image]

lemma Fin.card_filter_univ_succ_rev {n : ℕ} (p : Fin (n + 1) → Prop) [DecidablePred p] :
    ({x : Fin (n + 1) | p x} : Finset _).card =
    if p (Fin.last n)
    then ({x : Fin n | p x.castSucc} : Finset _).card + 1
    else ({x : Fin n | p x.castSucc} : Finset _).card := by
  rw [Fin.univ_succ_rev, Finset.filter_cons, apply_ite Finset.card, Finset.card_cons,
      Finset.filter_map, Finset.card_map]; rfl

lemma Fin.card_filter_univ_succ'_rev {n : ℕ} (p : Fin (n + 1) → Prop) [DecidablePred p] :
    ({x : Fin (n + 1) | p x} : Finset _).card =
    (if p (Fin.last n) then 1 else 0) +
    ({x : Fin n | p x.castSucc} : Finset _).card := by
  rw [Fin.card_filter_univ_succ_rev]; split_ifs <;> simp [add_comm]



def Fin.sym2_castSucc {n : ℕ} : Sym2 (Fin n) ↪ Sym2 (Fin (n + 1)) :=
  ⟨fun p => p.map Fin.castSucc, by
    intros x y h
    simp at h
    cases x; cases y; simp at *
    exact h⟩

def Fin.sym2_with_fin_last {n} : Fin n ↪ Sym2 (Fin (n + 1)) :=
  ⟨fun x => s(x.castSucc, Fin.last n), by
    intros x y h; cases x ; cases y
    simp at *
    grind⟩

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



lemma add_vertex_degree_sum {n} (G : SimpleGraph (Fin n)) (vs : Finset (Fin n))
    [DecidableRel G.Adj] [∀ x, Decidable (x ∈ vs)] :
    ∑ v, (add_vertex G vs).degree v = (∑ v, G.degree v) + 2 * vs.card := by
  unfold add_vertex
  rw [Fin.sum_univ_castSucc];
  rw [show ∑ v, G.degree v + 2 * vs.card = ∑ v, G.degree v + vs.card + vs.card by ring]
  congr
  · unfold SimpleGraph.degree
    simp_rw [SimpleGraph.neighborFinset_eq_filter]
    simp
    simp_rw [Fin.card_filter_univ_succ'_rev]
    simp [Finset.sum_add_distrib]
    have h : ({x | x ∈ vs} : Finset _).card = vs.card := by
      simp [Finset.filter_mem_eq_inter]
    rw [h, add_comm]
  · unfold SimpleGraph.degree SimpleGraph.neighborFinset
    simp
    apply Finset.card_bij (fun a ha => by simp at ha; use a.val; grind)
    · intros a ha
      simp at ha
      grind
    · intros a ha b hb
      simp at ha hb
      grind
    · intros a ha
      simp
      use a.castSucc; simpa

lemma add_vertex_edgeFinset {n} (G : SimpleGraph (Fin n)) (vs : Finset (Fin n))
    [DecidableRel G.Adj] [∀ x, Decidable (x ∈ vs)] :
    (add_vertex G vs).edgeFinset =
    G.edgeFinset.map Fin.sym2_castSucc ∪
    vs.map Fin.sym2_with_fin_last    := by
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

lemma add_vertex_edgeFinset_card {n} (G : SimpleGraph (Fin n)) (vs : Finset (Fin n))
    [DecidableRel G.Adj] [∀ x, Decidable (x ∈ vs)] :
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


theorem degree_sum_formula_for_Fin_n {n} (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj] :
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
    have inst_h : inst = add_vertex_decidable_adj G' vs := by
      ext v a; exact of_decide_eq_true rfl
    rw [inst_h, h₀, iH, add_vertex_edgeFinset_card]
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
  rw [← degree_sum_formula_for_Fin_n]
  rw [← Equiv.sum_comp (e := f.toEquiv)]
  simp
