import Cycle12.Foundations.SamplingGeometry
import Cycle12.Foundations.SampledCutComparison

namespace Cycle13
open Finset SimpleGraph
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem bad_sampled_cut_size_le (G : SimpleGraph V) (U A : Finset V)
    (hAU : A⊆U) (ha : 0 < (A.card:ℝ)) {δ β : ℝ}
    (hdeg : ∀ v∈A, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ((G.interedges A (U\A)).card:ℝ) ≤ β*A.card) :
    δ-β ≤ (A.card:ℝ) := by
  have hlo : (δ-(A.card:ℝ))*A.card ≤ ((G.interedges A (U\A)).card:ℝ) := by
    apply cut_card_lower_of_neighbors G A (U\A) A (Subset.refl _) (δ-A.card)
    intro v hv
    have hp := neighborsIn_partition_card G v A U hAU
    have hpR : ((neighborsIn G v U).card:ℝ)=((neighborsIn G v A).card:ℝ)+
        ((neighborsIn G v (U\A)).card:ℝ) := by exact_mod_cast hp
    have hc : ((neighborsIn G v A).card:ℝ) ≤ A.card := by
      exact_mod_cast card_le_card (filter_subset (G.Adj v) A)
    have hd := hdeg v hv
    linarith
  have hh := (mul_le_mul_iff_left₀ ha).mp (hlo.trans hbad)
  linarith

theorem classified_both_sides_sample_lower (G : SimpleGraph V) (U A S : Finset V)
    (hAU : A⊆U) (hsmall : 2*A.card ≤ U.card) {δ ε : ℝ} (hδ : 0 < δ)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (herr : sampledErrorWeight G U A (U∩S) ≤ δ*ε*A.card) :
    (1-ε)*A.card ≤ ((U∩S).card:ℝ) ∧ (1-ε)*A.card ≤ ((U\S).card:ℝ) := by
  have he := sampled_error_card_bound G U A (U∩S) hAU inter_subset_left hdeg
  have hdist : ((A ∆ (U∩S)).card:ℝ) ≤ ε*A.card := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    nlinarith
  have hc := card_le_add_symmDiff A (U∩S)
  have hcR : (A.card:ℝ) ≤ (U∩S).card+(A ∆ (U∩S)).card := by exact_mod_cast hc
  have hupper := classified_side_sample_size G U A S hAU hδ hdeg herr
  have hpart : ((U\S).card:ℝ)+((U∩S).card:ℝ)=U.card := by
    exact_mod_cast card_sdiff_add_card_inter U S
  have hsmallR : 2*(A.card:ℝ) ≤ U.card := by exact_mod_cast hsmall
  constructor <;> nlinarith

theorem population_lower_from_affine_bound {a amin ε scale b c u v : ℝ}
    (hamin : 0 < amin) (ha : amin ≤ a) (hscale : 0 < scale) (hb : 0 ≤ b)
    (hc : scale*c+ε+b/amin ≤ 1)
    (hlower : (1-ε)*a ≤ v) (hupper : v ≤ scale*u+b) : c*a ≤ u := by
  have hba : b ≤ (b/amin)*a := by
    have hh := mul_le_mul_of_nonneg_left ha (div_nonneg hb hamin.le)
    simpa only [div_mul_cancel₀ _ hamin.ne'] using hh
  have ha0 : 0 ≤ a := hamin.le.trans ha
  have hca := mul_le_mul_of_nonneg_right hc ha0
  apply (mul_le_mul_iff_right₀ hscale).mp
  nlinarith

theorem classified_both_sides_population (G : SimpleGraph V) (U A S : Finset V)
    (hAU : A⊆U) (hsmall : 2*A.card ≤ U.card) {δ ε amin scale b c : ℝ}
    (hδ : 0 < δ) (hamin : 0 < amin) (ha : amin ≤ (A.card:ℝ))
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (herr : sampledErrorWeight G U A (U∩S) ≤ δ*ε*A.card)
    (hscale : 0 < scale) (hb : 0 ≤ b) (hc : scale*c+ε+b/amin ≤ 1)
    (hup₁ : ((U∩S).card:ℝ) ≤ scale*S.card+b)
    (hup₂ : ((U\S).card:ℝ) ≤ scale*Sᶜ.card+b) :
    c*A.card ≤ (S.card:ℝ) ∧ c*A.card ≤ (Sᶜ.card:ℝ) := by
  have hh := classified_both_sides_sample_lower G U A S hAU hsmall hδ hdeg herr
  exact ⟨population_lower_from_affine_bound hamin ha hscale hb hc hh.1 hup₁,
    population_lower_from_affine_bound hamin ha hscale hb hc hh.2 hup₂⟩

theorem small_cut_implies_truncated_tail (G : SimpleGraph V) (U A S T : Finset V) (k : ℕ)
    (hAU : A⊆U) {β err τ ρ : ℝ}
    (hbad : ((G.interedges A (U\A)).card:ℝ) ≤ β*A.card)
    (herr : sampledErrorWeight G U A (U∩S) ≤ err*A.card)
    (hthreshold : (β+err)*A.card ≤
      τ*(Fintype.card ((truncatedCut G S k).induce (↑(univ\T):Set V)).edgeSet:ℝ)*ρ^2) :
    (sampledEdgeCount ((truncatedCut G S k).induce (↑(univ\T):Set V)) {v | v.val∈U}:ℝ) ≤
      τ*(Fintype.card ((truncatedCut G S k).induce (↑(univ\T):Set V)).edgeSet:ℝ)*ρ^2 := by
  have hc := weighted_cut_perturbation G U A (U∩S) hAU inter_subset_left
  have he : U\(U∩S)=U\S := by ext v; simp
  rw [he] at hc
  have ht : (sampledEdgeCount ((truncatedCut G S k).induce (↑(univ\T):Set V))
      {v | v.val∈U}:ℝ) ≤ ((G.interedges (U∩S) (U\S)).card:ℝ) := by
    exact_mod_cast sampled_truncated_cut_le G S U (univ\T) k
  linarith

end
end Cycle13
