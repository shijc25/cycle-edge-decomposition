import Cycle12.WeakCutError
import Cycle12.MajorityPopulation

namespace Cycle12
open Finset SimpleGraph Cycle13
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Deterministic consequences for a genuinely restricted cut. The
error fraction is (err+2 beta)/dm; the stronger stable-cut fraction is not
used here. -/
theorem weak_cut_witness_geometry (G : SimpleGraph V) (U A B : Finset V)
    (hA : A⊆U) (hB : B⊆U) (hAn : A.Nonempty) (hsmall : 2*A.card ≤ U.card)
    {z dm beta err : ℝ} (hz : 0 < z) (hdm : 0 < dm)
    (hc : (err+2*beta)/dm < 1)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ((G.interedges A (U\A)).card:ℝ) < beta*z*A.card)
    (herror : jointCutError G U A B ≤ err*z*A.card) :
    (dm-beta)*z < (A.card:ℝ) ∧ B.Nonempty ∧ (U\B).Nonempty ∧
    ((A ∆ B).card:ℝ) ≤ (err+2*beta)/dm*A.card ∧
    (1-(err+2*beta)/dm)*A.card ≤ min (B.card:ℝ) (U\B).card ∧
    (B.card:ℝ) ≤ (1+(err+2*beta)/dm)*A.card ∧
    ((G.interedges B (U\B)).card:ℝ) ≤ (beta+err)*z*A.card := by
  have ha : (0:ℝ) < A.card := by exact_mod_cast hAn.card_pos
  have horder := bad_sampled_cut_large G U A hA ha (fun v hv => hdeg v (hA hv)) hbad
  have herr := weak_joint_error_fraction G U A B hA hB hz hdm hdeg hbad.le herror
  have hmin := card_error_min_lower U A B hB hsmall herr
  have hpos := mul_pos (sub_pos.mpr hc) ha
  have hBpos : (0:ℝ) < B.card := hpos.trans_le (hmin.trans (min_le_left _ _))
  have hCpos : (0:ℝ) < (U\B).card := hpos.trans_le (hmin.trans (min_le_right _ _))
  have hupper : (B.card:ℝ) ≤ A.card+(A ∆ B).card := by
    simpa only [symmDiff_comm B A] using
      (show (B.card:ℝ) ≤ A.card+(B ∆ A).card by exact_mod_cast card_le_add_symmDiff B A)
  refine ⟨by nlinarith only [horder],card_pos.mp (by exact_mod_cast hBpos),
    card_pos.mp (by exact_mod_cast hCpos),herr,hmin,?_,
    weak_joint_cut_perturbation G U A B hA hB hbad.le herror⟩
  nlinarith only [hupper,herr]

end
end Cycle12
