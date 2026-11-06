import Cycle12.CoverCycleBudget
import Cycle12.Foundations.FastLogCertificates

namespace Cycle12
open Real Set Cycle13.MixedSample
noncomputable section

def coverGreedyLogGap (x : ℝ) : ℝ := log (coverSampleV x)+1-(47/100)*coverScaleW x

theorem coverGreedyLogGap_eq {x : ℝ} (hx : 0 < x) :
    coverGreedyLogGap x=log ((43/10)^3)+2*log x+log (1+3*x)+1-((47/100)*(43/10)^3)*x^2 := by
  have hx₂ := pow_ne_zero 2 hx.ne'
  have hp : (1+3*x) ≠ 0 := by positivity
  unfold coverGreedyLogGap coverSampleV coverScaleW
  rw [log_mul (by positivity) hp,log_mul (by norm_num : ((43/10)^3:ℝ) ≠ 0) hx₂]
  simp only [log_pow]
  ring

theorem coverGreedyLogGap_concave : ConcaveOn ℝ (Ioi (0:ℝ)) coverGreedyLogGap := by
  refine ⟨convex_Ioi 0,?_⟩
  intro x hx y hy a b ha hb hab
  change 0 < x at hx
  change 0 < y at hy
  have hxy : 0 < a*x+b*y := (convex_Ioi (0:ℝ)) hx hy ha hb hab
  have hc := strictConcaveOn_log_Ioi.concaveOn
  have h₁ := hc.2 hx hy ha hb hab
  have h₂ := hc.2 (show 0 < 1+3*x by linarith [hx])
    (show 0 < 1+3*y by linarith [hy]) ha hb hab
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  have hlin : a*(1+3*x)+b*(1+3*y)=1+3*(a*x+b*y) := by nlinarith only [hab]
  rw [hlin] at h₂
  rw [coverGreedyLogGap_eq hx,coverGreedyLogGap_eq hy,coverGreedyLogGap_eq hxy]
  have hconst : a*(log ((43/10)^3)+1)+b*(log ((43/10)^3)+1)=log ((43/10)^3)+1 := by rw [← add_mul,hab,one_mul]
  have hpoly : a*x^2+b*y^2-(a*x+b*y)^2=a*b*(x-y)^2 := by
    have he : b=1-a := by linarith
    rw [he]
    ring
  have hnon := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
  nlinarith only [h₁,h₂,hconst,hpoly,hnon]

theorem coverGreedyLogGap_xmax_nonneg : 0 ≤ coverGreedyLogGap (17/250) := by
  have hh := Cycle13.log_rational_enclosure
    (q:=(15625000000/6916234423:ℚ)) (l:=0) (u:=41/50) (by decide +kernel) 10
    (by decide +kernel) (by decide +kernel)
  have hi := Cycle13.log_rational_inverse_enclosure hh
  have hl : -(41/50:ℝ) ≤ log (coverSampleV (17/250)) := by
    convert hi.1 using 1 <;> norm_num [coverSampleV,coverScaleW]
  unfold coverGreedyLogGap
  norm_num [coverScaleW] at hl ⊢
  linarith only [hl]

theorem coverGreedyLogGap_upper_nonneg : 0 ≤ coverGreedyLogGap (1/10) := by
  have hv : (1:ℝ) ≤ coverSampleV (1/10) := by norm_num [coverSampleV,coverScaleW]
  have hl := log_nonneg hv
  unfold coverGreedyLogGap
  norm_num [coverScaleW]
  linarith only [hl]

/-- A rational upper endpoint avoids any unformalized root of v(x)=1. -/
theorem coverGreedyLogGap_nonneg {x : ℝ} (hx : (17/250) ≤ x) (hv : coverSampleV x < 1) :
    0 ≤ coverGreedyLogGap x := by
  have hx₀ : 0 < x := (by norm_num [] : (0:ℝ) < (17/250)).trans_le hx
  have hupper : x ≤ 1/10 := by
    by_contra h
    have hh := cover_v_mono (by norm_num : (0:ℝ) ≤ 1/10) (le_of_lt (lt_of_not_ge h))
    have hv₀ : (1:ℝ) < coverSampleV (1/10) := by norm_num [coverSampleV,coverScaleW]
    linarith
  have hh := coverGreedyLogGap_concave.min_le_of_mem_Icc
    (by norm_num [] : (17/250) ∈ Ioi (0:ℝ))
    (by norm_num : (1/10:ℝ) ∈ Ioi (0:ℝ)) ⟨hx,hupper⟩
  exact (le_min coverGreedyLogGap_xmax_nonneg coverGreedyLogGap_upper_nonneg).trans hh

end
end Cycle12
