import Cycle12.Foundations.NormalizedGlobalSample

namespace Cycle12
open Cycle13 Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The normalized residual lower bound is upgraded to the exact
conditional Bernoulli parameter before invoking the probability theorem. -/
theorem normalized_bad_cut_probability (C : NormalizedGlobalParameters)
    {p : unitInterval} {z R : ℝ} (hC : C.Valid (p:ℝ) z R)
    (G : SimpleGraph V) (hn : (Fintype.card V:ℝ) = R*z/(p:ℝ))
    (hG : GlobalCutProfile G (z/(p:ℝ))) :
    (bernoulliSubset p).prob (BadCutSample G (C.dm*z) (C.beta*z) (C.upper*R*z)) ≤
      (2*exp (-R*C.mgfRate (p:ℝ) z R)+exp (-R*C.jansonRate z R))/C.witness := by
  let q := normalizedMark C.mark z hC.scale_pos hC.mark_nonneg hC.mark_lt.le
  have hq : (q:ℝ) < 1 := (div_lt_one hC.scale_pos).mpr hC.mark_lt
  have hpq : (p:ℝ)*(q:ℝ) < 1 :=
    (mul_le_mul_of_nonneg_right p.2.2 q.2.1).trans_lt (by simpa using hq)
  let ρ := residualProbability p q hpq
  have hρ : (unnormalizedResidual p q:ℝ) ≤ (ρ:ℝ) :=
    residual_lower_of_identity_bound hpq (unnormalizedResidual_lower p q)
  let D := C.parameters (p:ℝ) z R
  have hD := C.valid hC
  have hscale : D.scale 1 = D := by
    cases D
    simp [GlobalCutParameters.scale]
  have hmark : scaledMark q 1 (le_refl 1) = q := by
    apply Subtype.ext
    simp [scaledMark]
  have hvalid : D.Valid p q ρ (Fintype.card V) := by
    have hh := D.valid_scale hD (le_refl 1) hρ (show 0 < D.cap from
      mul_pos hC.cap_pos (by linarith [hC.ratio_lower]))
    rw [hscale,hmark] at hh
    simpa only [one_pow,one_mul,← hn] using hh
  have hbound := D.failureBound_scale hD (le_refl 1) hρ
  rw [hscale,hmark] at hbound
  simp only [one_pow,one_mul] at hbound
  change D.failureBound p q ρ (R*z/(p:ℝ)) ≤ D.failureBound p q (unnormalizedResidual p q) (R*z/(p:ℝ)) at hbound
  have heq := C.failureBound_eq hC
  have hactual := D.global_bad_cut_probability hvalid hpq
    (residualProbability_identity p q hpq) G hG
  change (bernoulliSubset p).prob (BadCutSample G (C.dm*z) (C.beta*z) (C.upper*R*z)) ≤
    D.failureBound p q ρ (Fintype.card V) at hactual
  rw [hn] at hactual
  exact (hactual.trans hbound).trans_eq heq

end
end Cycle12
