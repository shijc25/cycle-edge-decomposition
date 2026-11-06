import Cycle12.FixedMajorityJointCost

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- For a restricted cut, stable-cut degree bounds are unavailable.
Charge all crossing incidences instead; they total exactly twice the cut. -/
theorem joint_cut_error_to_degree_error (G : SimpleGraph V) (U A B : Finset V)
    (hA : A⊆U) (hB : B⊆U) :
    sampledErrorWeight G U A B ≤ jointCutError G U A B+2*(G.interedges A (U\A)).card := by
  have hwrong : A ∆ B⊆U := by
    intro v hv
    rcases mem_symmDiff.mp hv with hv | hv
    · exact hA hv.1
    · exact hB hv.1
  have hcross := sum_sample_cross_neighbors G U A hA
  simp_rw [fixed_cross_neighbor_set G U A hA] at hcross
  have he : sampledErrorWeight G U A B=jointCutError G U A B+
      ∑ v∈A ∆ B, ((neighborsIn G v (if v∈A then U\A else A)).card:ℝ) := by
    unfold sampledErrorWeight jointCutError
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    rw [same_degree_eq_total_sub_cross G U A hA v]
    ring
  rw [he,← hcross]
  apply add_le_add le_rfl
  exact sum_le_sum_of_subset_of_nonneg hwrong (fun _ _ _ => Nat.cast_nonneg _)

theorem weak_joint_error_fraction (G : SimpleGraph V) (U A B : Finset V)
    (hA : A⊆U) (hB : B⊆U) {z dm beta err : ℝ} (hz : 0 < z) (hdm : 0 < dm)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ((G.interedges A (U\A)).card:ℝ) ≤ beta*z*A.card)
    (herror : jointCutError G U A B ≤ err*z*A.card) :
    ((A ∆ B).card:ℝ) ≤ (err+2*beta)/dm*A.card := by
  have hd := sampled_error_card_bound G U A B hA hB hdeg
  have he := joint_cut_error_to_degree_error G U A B hA hB
  have hpre : z*(dm*(A ∆ B).card) ≤ z*((err+2*beta)*A.card) := by
    nlinarith only [hd,he,hbad,herror]
  have hc := (mul_le_mul_iff_right₀ hz).mp hpre
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hdm).mpr
  nlinarith only [hc]

theorem weak_joint_cut_perturbation (G : SimpleGraph V) (U A B : Finset V)
    (hA : A⊆U) (hB : B⊆U) {z beta err : ℝ}
    (hbad : ((G.interedges A (U\A)).card:ℝ) ≤ beta*z*A.card)
    (herror : jointCutError G U A B ≤ err*z*A.card) :
    ((G.interedges B (U\B)).card:ℝ) ≤ (beta+err)*z*A.card := by
  have hh := joint_cut_perturbation G U A B hA hB
  nlinarith only [hh,hbad,herror]

end
end Cycle12
