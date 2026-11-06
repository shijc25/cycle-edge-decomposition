import Cycle12.StableCut
import Cycle12.JointCutWitness

namespace Cycle12
open SimpleGraph Finset Cycle13
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem stable_cut_same_degree (G : SimpleGraph V) (U A : Finset V)
    {c delta : ℝ} (hc : 0 ≤ c) (hstable : IsStableCut G U A c)
    {v : V} (hvU : v∈U) (hdeg : delta ≤ ((neighborsIn G v U).card:ℝ)) :
    (delta-c)/2 ≤ ((neighborsIn G v (if v∈A then A else U\A)).card:ℝ) := by
  have hb := stable_cut_cross_degree G U A hc hstable hvU
  have hd : ((neighborsIn G v U).card:ℝ)=(neighborsIn G v A).card+
      (neighborsIn G v (U\A)).card := by
    exact_mod_cast neighborsIn_partition_card G v A U hstable.1
  by_cases hv : v∈A
  · simp only [if_pos hv] at hb ⊢
    linarith only [hb,hd,hdeg]
  · simp only [if_neg hv] at hb ⊢
    linarith only [hb,hd,hdeg]

/-- This stronger error-count estimate is used only for a genuinely global
stable cut; arbitrary restricted local cuts cannot use this theorem. -/
theorem stable_joint_cut_error_lower (G : SimpleGraph V) (U A B : Finset V)
    {c delta : ℝ} (hc : 0 ≤ c) (hstable : IsStableCut G U A c) (hBU : B⊆U)
    (hdeg : ∀ v∈U, delta ≤ ((neighborsIn G v U).card:ℝ)) :
    (delta-c)/2*(A ∆ B).card ≤ jointCutError G U A B := by
  calc
    _ = ∑ _v∈A ∆ B, (delta-c)/2 := by simp [mul_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro v hv
      have hvU : v∈U := by
        rcases mem_symmDiff.mp hv with hv | hv
        · exact hstable.1 hv.1
        · exact hBU hv.1
      exact stable_cut_same_degree G U A hc hstable hvU (hdeg v hvU)

theorem stable_joint_error_fraction (G : SimpleGraph V) (U A B : Finset V)
    {z beta tau dm : ℝ} (hz : 0<z) (hbeta : 0 ≤ beta) (hbt : beta<tau)
    (hbd : beta<dm) (hstable : IsStableCut G U A (beta*z)) (hBU : B⊆U)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hbudget : jointCutError G U A B+tau*z*(A ∆ B).card ≤ (tau-beta)*z*A.card) :
    ((A ∆ B).card:ℝ) ≤ (tau-beta)/(tau+(dm-beta)/2)*A.card := by
  have hZ := stable_joint_cut_error_lower G U A B (mul_nonneg hbeta hz.le)
    hstable hBU hdeg
  have ht : 0<tau+(dm-beta)/2 := by linarith only [hbeta,hbt,hbd]
  have hpre : z*((tau+(dm-beta)/2)*(A ∆ B).card) ≤ z*((tau-beta)*A.card) := by
    nlinarith only [hZ,hbudget]
  have hcancel := (mul_le_mul_iff_right₀ hz).mp hpre
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ht).mpr
  nlinarith only [hcancel]

/-- All deterministic consequences of the same joint budget, with the
stable-cut premise explicit and applied to the original cut. -/
theorem stable_joint_cut_witness (G : SimpleGraph V) (U A B : Finset V)
    {z beta tau dm : ℝ} (hz : 0<z) (hbeta : 0<beta) (hbt : beta<tau)
    (hbd : beta<dm) (hstable : IsStableCut G U A (beta*z)) (hBU : B⊆U)
    (hA : A.Nonempty) (hsmall : 2*A.card ≤ U.card)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ((G.interedges A (U\A)).card:ℝ)<beta*z*A.card)
    (hbudget : jointCutError G U A B+tau*z*(A ∆ B).card ≤ (tau-beta)*z*A.card) :
    B.Nonempty ∧ (U\B).Nonempty ∧
      ((G.interedges B (U\B)).card:ℝ)<tau*z*min (B.card:ℝ) (U\B).card ∧
      (dm-tau)*z < min (B.card:ℝ) (U\B).card ∧
      ((A ∆ B).card:ℝ) ≤ (tau-beta)/(tau+(dm-beta)/2)*A.card := by
  obtain ⟨_,hB,hC,hcut⟩ := joint_cut_witness G U A B hstable.1 hBU hA hsmall
    hz hbeta hbt hbad hbudget
  exact ⟨hB,hC,hcut,
    joint_cut_witness_large G U A B hstable.1 hBU hA hsmall hz hbeta hbt hdeg hbad hbudget,
    stable_joint_error_fraction G U A B hz hbeta.le hbt hbd hstable hBU hdeg hbudget⟩

end
end Cycle12
