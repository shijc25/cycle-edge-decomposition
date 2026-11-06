import Cycle12.Foundations.RationalBounds

/-! Concrete real-number checks via the proved rational series bounds. -/
namespace Cycle13
open Real Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem log_two_24_digits :
    (693147180559945309417232 : ℝ) / 10 ^ 24 ≤ log 2 ∧
      log 2 ≤ (693147180559945309417233 : ℝ) / 10 ^ 24 := by
  have h := ratLog_argument_bounds (q := 2) (by norm_num) 40
  have hlo : (693147180559945309417232 : ℚ) / 10 ^ 24 ≤ ratLogPartial (1/3) 40 := by
    norm_num [ratLogPartial, sum_range_succ]
  have hhi : ratLogUpper (1/3) 40 ≤ (693147180559945309417233 : ℚ) / 10 ^ 24 := by
    norm_num [ratLogUpper, ratLogPartial, sum_range_succ]
  norm_num only [Rat.cast_ofNat, show (2 - 1) / (2 + 1) = (1/3 : ℚ) by norm_num] at h
  have hloR := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR := (Rat.cast_le (K := ℝ)).mpr hhi
  push_cast at hloR hhiR
  constructor
  · exact hloR.trans h.1
  · exact h.2.trans hhiR

theorem exp_quarter_lt_nine_sevenths : exp (1/4 : ℝ) < 9/7 := by
  have h := (ratExp_bounds (q := 1/4) (by norm_num) 20 (by norm_num)).2
  have hrat : ratExpUpper (1/4) 20 < (9/7 : ℚ) := by
    norm_num [ratExpUpper, ratExpPartial, sum_range_succ, Nat.factorial]
  have hreal := (Rat.cast_lt (K := ℝ)).mpr hrat
  push_cast at hreal h
  exact h.trans_lt hreal

end Cycle13
