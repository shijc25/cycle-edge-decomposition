import Cycle12.Foundations.FiniteHarmonicStep
import Cycle12.Foundations.FastLogCertificates

namespace Cycle13
open Real
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem harmonic_256_difference :
    (harmonic 256:ℝ)-(harmonic 7:ℝ) ≤ 3531487819961/1000000000000 := by
  have h : harmonic 256-harmonic 7 ≤ (3531487819961/1000000000000:ℚ) := by decide +kernel
  have hR := (Rat.cast_le (K:=ℝ)).mpr h
  simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat] using hR

theorem terminal_normalized_log :
    log (147247/131072:ℝ) ≤ 116364658272788775612859/1000000000000000000000000 := by
  have hh := log_rational_enclosure (q := (147247/131072:ℚ))
    (l := (58182329136394387806429/500000000000000000000000:ℚ))
    (u := (116364658272788775612859/1000000000000000000000000:ℚ))
    (by decide +kernel) 20 (by decide +kernel) (by decide +kernel)
  norm_num at hh ⊢
  exact hh.2

theorem terminal_log_difference :
    log (294494:ℝ)-log 256 ≤ 28191345855489/4000000000000 := by
  have he : log (294494:ℝ)-log 256=10*log 2+log (147247/131072:ℝ) := by
    rw [← log_div (by norm_num) (by norm_num)]
    rw [show (294494:ℝ)/256=2^10*(147247/131072) by norm_num,
      log_mul (by norm_num) (by norm_num),log_pow]
    norm_num
  rw [he]
  have h₂ := log_two_24_digits.2
  have hy := terminal_normalized_log
  norm_num at h₂ hy ⊢
  linarith

/-- Kernel-certified terminal constant, conditional only on the
weighted small-circumference base bound. -/
theorem weightedAffine_terminal_294494
    (hbase : WeightedAffineBound (19/42) 7) :
    WeightedAffineBound (1435511/250000) 294494 := by
  apply weightedAffine_mono_constant _
    (weightedAffine_harmonic_anchor (a := 256) (by norm_num) (by norm_num) hbase)
  have hH := harmonic_256_difference
  have hL := terminal_log_difference
  norm_num at hH hL ⊢
  linarith

end Cycle13
