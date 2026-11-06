import Cycle12.Foundations.TwoScaleCut
import Cycle12.Foundations.StrongRecycling

/-! Two-scale branch cuts for actual finite graphs. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def cutGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  G.between (S : Set V) (S : Set V)ᶜ

def cutSize (G : SimpleGraph V) (S : Finset V) : ℕ := (cutGraph G S).edgeSet.ncard

theorem cutGraph_bipartite (G : SimpleGraph V) (S : Finset V) :
    (cutGraph G S).IsBipartiteWith S (Sᶜ : Finset V) := by
  simpa only [cutGraph, coe_compl] using G.between_isBipartiteWith
    (s := (S : Set V)) (t := (S : Set V)ᶜ) disjoint_compl_right

theorem cutSize_eq_sum (G : SimpleGraph V) (S : Finset V) :
    cutSize G S = ∑ v ∈ S, (cutGraph G S).degree v := by
  have h := (cutGraph G S).isBipartiteWith_sum_degrees_eq_card_edges (cutGraph_bipartite G S)
  simpa only [cutSize, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using h.symm

theorem degree_le_cut_add (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∈ S) :
    G.degree v ≤ (cutGraph G S).degree v + S.card := by
  have hsub : G.neighborSet v ⊆ (cutGraph G S).neighborSet v ∪ (S : Set V) := by
    intro w hw
    by_cases hws : w ∈ S
    · exact Or.inr hws
    · exact Or.inl ⟨hw, Or.inl ⟨hv, hws⟩⟩
  have hn := (Set.ncard_le_ncard hsub).trans
    (Set.ncard_union_le ((cutGraph G S).neighborSet v) (S : Set V))
  simpa only [SimpleGraph.ncard_neighborSet, Set.ncard_coe_finset] using hn

theorem branch_degree_cut (G : SimpleGraph V) (S B : Finset V) {δ : ℝ}
    (hdeg : ∀ v ∈ B, δ ≤ (G.degree v : ℝ)) :
    ((S ∩ B).card : ℝ) * (δ - S.card) ≤ (cutSize G S : ℝ) := by
  classical
  have hpoint : ∀ v ∈ S ∩ B, δ - S.card ≤ ((cutGraph G S).degree v : ℝ) := by
    intro v hv
    have hs := mem_inter.mp hv
    have hd := degree_le_cut_add G S hs.1
    have hdR : (G.degree v : ℝ) ≤ (cutGraph G S).degree v + S.card := by
      exact_mod_cast hd
    have hb := hdeg v hs.2
    linarith
  have hsum : ∑ v ∈ S ∩ B, (cutGraph G S).degree v ≤
      ∑ v ∈ S, (cutGraph G S).degree v :=
    sum_le_sum_of_subset_of_nonneg inter_subset_left (fun _ _ _ => Nat.zero_le _)
  calc
    _ = ∑ _v ∈ S ∩ B, (δ - (S.card : ℝ)) := by simp [mul_sub]
    _ ≤ ∑ v ∈ S ∩ B, ((cutGraph G S).degree v : ℝ) := sum_le_sum hpoint
    _ ≤ ∑ v ∈ S, ((cutGraph G S).degree v : ℝ) := by exact_mod_cast hsum
    _ = (cutSize G S : ℝ) := by rw [cutSize_eq_sum, Nat.cast_sum]

/-- Local expansion controls small sides; global expansion controls larger
sides. The conclusion counts actual edges across each branch cut. -/
theorem graph_two_scale_branch_cut (G : SimpleGraph V) (B : Finset V)
    {δ c h₀ h₁ L : ℝ} (hc : 0 ≤ c) (hh₀ : 0 < h₀) (hh₁ : 0 < h₁)
    (hdeg : ∀ v ∈ B, δ ≤ (G.degree v : ℝ))
    (hglobal : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      h₀ * S.card ≤ (cutSize G S : ℝ))
    (hlocal : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V → (S.card : ℝ) ≤ L →
      h₁ * S.card ≤ (cutSize G S : ℝ))
    (hsmallBudget : c * (B.card + h₁) ≤ h₁ * δ)
    (hlargeBudget : B.card * c ≤ h₀ * L)
    (S : Finset V) (hS : 2 * S.card ≤ Fintype.card V) :
    c * (S ∩ B).card ≤ (cutSize G S : ℝ) := by
  exact two_scale_branch_cut (Nat.cast_nonneg _)
    (by exact_mod_cast card_le_card (inter_subset_right (s₁ := S) (s₂ := B)))
    hc hh₀ hh₁ (branch_degree_cut G S B hdeg) (hglobal S hS)
    (hlocal S hS) hsmallBudget hlargeBudget

theorem cutSize_eq_interedges (G : SimpleGraph V) (S : Finset V) :
    cutSize G S = (G.interedges S Sᶜ).card := by
  classical
  rw [cutSize_eq_sum, OAI.ErdosGallai.Sampling.card_interedges_eq_sum_neighborsIn]
  apply sum_congr rfl
  intro v hv
  rw [← SimpleGraph.ncard_neighborSet]
  have heq : (cutGraph G S).neighborSet v =
      (OAI.ErdosGallai.Sampling.neighborsIn G v Sᶜ : Set V) := by
    ext w
    change (G.Adj v w ∧ (v ∈ (S : Set V) ∧ w ∈ (S : Set V)ᶜ ∨
      v ∈ (S : Set V)ᶜ ∧ w ∈ (S : Set V))) ↔ _
    simp only [mem_coe, Set.mem_compl_iff, hv, true_and, not_true_eq_false,
      false_and, or_false, OAI.ErdosGallai.Sampling.neighborsIn, mem_filter,
      mem_compl, and_comm]
  rw [heq, Set.ncard_coe_finset]

theorem cutSize_mono {G H : SimpleGraph V} (h : G ≤ H) (S : Finset V) :
    cutSize G S ≤ cutSize H S := by
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  apply SimpleGraph.edgeSet_mono
  intro x y hxy
  exact ⟨h hxy.1, hxy.2⟩

theorem cutSize_compl (G : SimpleGraph V) (S : Finset V) :
    cutSize G Sᶜ = cutSize G S := by
  have he : cutGraph G Sᶜ = cutGraph G S := by
    simp only [cutGraph, coe_compl, compl_compl]
    exact SimpleGraph.between_comm
  simp only [cutSize, he]

theorem cutSize_singleton (G : SimpleGraph V) (v : V) : cutSize G {v} = G.degree v := by
  rw [cutSize_eq_sum, sum_singleton, ← SimpleGraph.ncard_neighborSet,
    ← SimpleGraph.ncard_neighborSet]
  congr 1
  ext w
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, Or.inl ⟨by simp, ?_⟩⟩
    simpa using h.ne.symm

theorem cut_retention_implies_degree_retention (H F : SimpleGraph V) {f : ℝ}
    (hcut : ∀ S : Finset V, f * cutSize H S ≤ (cutSize F S : ℝ)) (v : V) :
    f * H.degree v ≤ (F.degree v : ℝ) := by
  simpa only [cutSize_singleton] using hcut {v}

theorem graph_two_scale_all_cuts (G : SimpleGraph V) (B : Finset V)
    {δ c h₀ h₁ L : ℝ} (hc : 0 ≤ c) (hh₀ : 0 < h₀) (hh₁ : 0 < h₁)
    (hdeg : ∀ v ∈ B, δ ≤ (G.degree v : ℝ))
    (hglobal : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V →
      h₀ * S.card ≤ (cutSize G S : ℝ))
    (hlocal : ∀ S : Finset V, 2 * S.card ≤ Fintype.card V → (S.card : ℝ) ≤ L →
      h₁ * S.card ≤ (cutSize G S : ℝ))
    (hsmallBudget : c * (B.card + h₁) ≤ h₁ * δ)
    (hlargeBudget : B.card * c ≤ h₀ * L) (S : Finset V) :
    c * min ((S ∩ B).card : ℝ) (Sᶜ ∩ B).card ≤ (cutSize G S : ℝ) := by
  by_cases hs : 2 * S.card ≤ Fintype.card V
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hc).trans
      (graph_two_scale_branch_cut G B hc hh₀ hh₁ hdeg hglobal hlocal hsmallBudget hlargeBudget S hs)
  · have hcompl : 2 * Sᶜ.card ≤ Fintype.card V := by
      have h := card_add_card_compl S
      omega
    have hb := graph_two_scale_branch_cut G B hc hh₀ hh₁ hdeg hglobal hlocal
      hsmallBudget hlargeBudget Sᶜ hcompl
    rw [cutSize_compl] at hb
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hc).trans hb

end
end Cycle13
