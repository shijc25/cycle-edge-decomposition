import Cycle12.Foundations.TruncatedCutGraph
import Cycle12.Foundations.CappedDegreeSum

namespace Cycle13
open Finset SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem subcut_boundary_bound (G : SimpleGraph V) (S X : Finset V) (hXS : X⊆S) :
    cutSize G X ≤ (G.interedges X Sᶜ).card+X.card*(S.card-X.card) := by
  rw [cutSize_eq_interedges]
  have hsub : G.interedges X Xᶜ ⊆ G.interedges X Sᶜ ∪ G.interedges X (S\X) := by
    intro e he
    obtain ⟨hx,hy,hxy⟩ := G.mem_interedges_iff.mp he
    by_cases hs : e.2∈S
    · exact mem_union_right _ (G.mem_interedges_iff.mpr ⟨hx,mem_sdiff.mpr ⟨hs,mem_compl.mp hy⟩,hxy⟩)
    · exact mem_union_left _ (G.mem_interedges_iff.mpr ⟨hx,mem_compl.mpr hs,hxy⟩)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  have hb := G.card_interedges_le_mul X (S\X)
  rw [card_sdiff_of_subset hXS] at hb
  omega

theorem subcut_degree_lower_bound (G : SimpleGraph V) (S : Finset V) (a : ℝ)
    (hprofile : ∀ X⊆S, a*X.card≤(cutSize G X:ℝ)) (X : Finset V) (hXS : X⊆S) :
    a*X.card ≤ (∑ v∈X, ((neighborsIn G v Sᶜ).card:ℝ))+(X.card:ℝ)*(S.card-X.card) := by
  have hh := subcut_boundary_bound G S X hXS
  have hc : (X.card:ℝ)≤S.card := by exact_mod_cast card_le_card hXS
  have hr : (cutSize G X:ℝ) ≤ ((G.interedges X Sᶜ).card:ℝ)+
      (X.card:ℝ)*((S.card:ℝ)-X.card) := by
    have hr := Nat.cast_le (α:=ℝ).mpr hh
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (card_le_card hXS)] using hr
  rw [card_interedges_eq_sum_neighborsIn,Nat.cast_sum] at hr
  exact (hprofile X hXS).trans hr

theorem truncatedCut_retained_edges (G : SimpleGraph V) (S : Finset V) (k : ℕ) (a : ℝ)
    (hprofile : ∀ X⊆S, a*X.card≤(cutSize G X:ℝ)) :
    a*S.card-(max (a+(S.card:ℝ)-k) 0)^2/4 ≤ ((truncatedCut G S k).edgeSet.ncard:ℝ) := by
  rw [truncatedCut_edge_count,Nat.cast_sum]
  exact capped_degree_sum_lower_bound S (fun v => (neighborsIn G v Sᶜ).card) k a
    (subcut_degree_lower_bound G S a hprofile)

theorem truncatedCut_retained_scaled_cap (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (a L : ℝ) (hcap : L*S.card≤(k:ℝ))
    (hprofile : ∀ X⊆S, a*X.card≤(cutSize G X:ℝ)) :
    a*S.card-(max (a-(L-1)*S.card) 0)^2/4 ≤ ((truncatedCut G S k).edgeSet.ncard:ℝ) := by
  apply le_trans _ (truncatedCut_retained_edges G S k a hprofile)
  have hb : a+(S.card:ℝ)-k ≤ a-(L-1)*S.card := by nlinarith
  have hm := max_le_max hb (le_refl (0:ℝ))
  have hn₁ : 0 ≤ max (a+(S.card:ℝ)-k) 0 := le_max_right _ _
  have hn₂ : 0 ≤ max (a-(L-1)*S.card) 0 := le_max_right _ _
  nlinarith

end
end Cycle13
