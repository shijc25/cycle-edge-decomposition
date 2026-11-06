import Cycle12.JointCutError
import Cycle12.Foundations.FiniteJointLaw

namespace Cycle12
open SimpleGraph Finset Cycle13
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The joint witness gives the stronger side-size threshold directly,
without dividing a separate cut bound by a separate error bound. -/
theorem joint_cut_witness_large (G : SimpleGraph V) (U A B : Finset V)
    (hAU : A⊆U) (hBU : B⊆U) (hA : A.Nonempty) (hsmall : 2*A.card ≤ U.card)
    {z beta tau dm : ℝ} (hz : 0<z) (hbeta : 0<beta) (hbt : beta<tau)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ((G.interedges A (U\A)).card:ℝ)<beta*z*A.card)
    (hbudget : jointCutError G U A B+tau*z*(A ∆ B).card ≤ (tau-beta)*z*A.card) :
    (dm-tau)*z < min (B.card:ℝ) (U\B).card := by
  obtain ⟨_,hB,hC,hcut⟩ := joint_cut_witness G U A B hAU hBU hA hsmall hz hbeta hbt hbad hbudget
  have htz := mul_pos (hbeta.trans hbt) hz
  have hb : ((G.interedges B (U\B)).card:ℝ)<tau*z*B.card :=
    hcut.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) htz.le)
  have h₁ := bad_sampled_cut_large G U B hBU
    (by exact_mod_cast card_pos.mpr hB) (fun v hv => hdeg v (hBU hv)) hb
  have hset : U\(U\B)=B := by
    ext v
    simp only [mem_sdiff]
    constructor
    · intro h
      by_contra hv
      exact h.2 ⟨h.1,hv⟩
    · intro hv
      exact ⟨hBU hv,fun h => h.2 hv⟩
  have hcomm : (G.interedges (U\B) B).card=(G.interedges B (U\B)).card := by
    letI : Std.Symm G.Adj := ⟨fun _ _ h => G.adj_symm h⟩
    exact Rel.card_interedges_comm (r:=G.Adj) _ _
  have hc : ((G.interedges (U\B) (U\(U\B))).card:ℝ)<tau*z*(U\B).card := by
    rw [hset,hcomm]
    exact hcut.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) htz.le)
  have h₂ := bad_sampled_cut_large G U (U\B) sdiff_subset
    (by exact_mod_cast card_pos.mpr hC) (fun v hv => hdeg v (mem_sdiff.mp hv).1) hc
  apply lt_min
  · nlinarith only [h₁]
  · nlinarith only [h₂]

/-- One Markov bound for the combined random cost. It applies to any
finite classifier experiment, including dependent choices and fixed-size
sampling; independence between its two costs is never assumed. -/
theorem joint_cut_witness_probability {Ω : Type} [Fintype Ω]
    (mu : FiniteLaw Ω) (G : SimpleGraph V) (U A : Finset V) (B : Ω → Finset V)
    (bad : Ω → Prop) {z beta tau M : ℝ}
    (hz : 0<z) (hbeta : 0<beta) (hbt : beta<tau) (hA : A.Nonempty)
    (hmean : mu.expect (fun w => jointCutError G U A (B w)+tau*z*(A ∆ B w).card) ≤ M) :
    1-M/((tau-beta)*z*A.card)-mu.prob bad ≤
      mu.prob (fun w => jointCutError G U A (B w)+tau*z*(A ∆ B w).card ≤
        (tau-beta)*z*A.card ∧ ¬bad w) := by
  have ha : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have ht : 0<(tau-beta)*z*A.card := mul_pos (mul_pos (sub_pos.mpr hbt) hz) ha
  have hw : ∀ w, 0 ≤ jointCutError G U A (B w)+tau*z*(A ∆ B w).card := by
    intro w
    exact add_nonneg (joint_cut_error_nonneg G U A (B w))
      (mul_nonneg (mul_pos (hbeta.trans hbt) hz).le (Nat.cast_nonneg _))
  have hh := mu.prob_good_weight _ bad hw ht
  have hm := div_le_div_of_nonneg_right hmean ht.le
  linarith only [hh,hm]

end
end Cycle12
