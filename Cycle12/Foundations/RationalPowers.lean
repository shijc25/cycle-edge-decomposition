import Cycle12.Foundations.BasicCertificates

namespace Cycle13
open Finset Real

/-- Rational exponentials bracket a real exponential at any argument inside
the certified rational interval. -/
theorem exp_interval_bounds {x : ℝ} {l u : ℚ} (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : (l : ℝ) ≤ x) (hhi : x ≤ (u : ℝ)) (N : ℕ) (hN : u < N + 2) :
    (ratExpPartial l (N + 1) : ℝ) ≤ exp x ∧ exp x ≤ (ratExpUpper u N : ℝ) := by
  have hlu : l ≤ u := by exact_mod_cast hlo.trans hhi
  exact ⟨(ratExp_bounds hl N (hlu.trans_lt hN)).1.trans (exp_le_exp.mpr hlo),
    (exp_le_exp.mpr hhi).trans (ratExp_bounds hu N hN).2⟩

theorem power_two_split (n : ℤ) (y : ℝ) :
    (2 : ℝ) ^ ((n : ℝ) + y) = (2 : ℝ) ^ n * exp (log 2 * y) := by
  rw [rpow_add (by norm_num : (0 : ℝ) < 2), rpow_intCast,
    rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Exact base-two power enclosure, including negative integer parts.
The integer split and logarithmic interval are checked premises. -/
theorem power_two_rational_bounds {x : ℝ} (n : ℤ) {y : ℚ} (hy : 0 ≤ y)
    (hx : x = (n : ℝ) + (y : ℝ)) {l u : ℚ} (hl : 0 ≤ l)
    (hloglo : (l : ℝ) ≤ log 2) (hloghi : log 2 ≤ (u : ℝ))
    (N : ℕ) (hN : u * y < N + 2) :
    (((2 : ℚ) ^ n * ratExpPartial (l * y) (N + 1) : ℚ) : ℝ) ≤ (2 : ℝ) ^ x ∧
      (2 : ℝ) ^ x ≤ (((2 : ℚ) ^ n * ratExpUpper (u * y) N : ℚ) : ℝ) := by
  have huR : (0 : ℝ) ≤ (u : ℝ) := (log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hloghi
  have hu : (0 : ℚ) ≤ u := by exact_mod_cast huR
  have hyR : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlo := mul_le_mul_of_nonneg_right hloglo hyR
  have hhi := mul_le_mul_of_nonneg_right hloghi hyR
  have h := exp_interval_bounds (mul_nonneg hl hy) (mul_nonneg hu hy)
    (by simpa only [Rat.cast_mul] using hlo) (by simpa only [Rat.cast_mul] using hhi) N hN
  rw [hx, power_two_split]
  push_cast
  exact ⟨mul_le_mul_of_nonneg_left h.1 (by positivity),
    mul_le_mul_of_nonneg_left h.2 (by positivity)⟩

def logTwoLower : ℚ := 693147180559945309417232 / 10 ^ 24
def logTwoUpper : ℚ := 693147180559945309417233 / 10 ^ 24
def ratPowerTwoLower (n : ℤ) (y : ℚ) : ℚ :=
  (2 : ℚ) ^ n * ratExpPartial (logTwoLower * y) 17
def ratPowerTwoUpper (n : ℤ) (y : ℚ) : ℚ :=
  (2 : ℚ) ^ n * ratExpUpper (logTwoUpper * y) 16

/-- The data generator may choose the integer split and proposed bounds;
each relation between those data is independently checked by the kernel. -/
theorem certified_power_two {q y L U : ℚ} (n : ℤ)
    (hq : q = n + y) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (hL : L ≤ ratPowerTwoLower n y) (hU : ratPowerTwoUpper n y ≤ U) :
    (L : ℝ) ≤ (2 : ℝ) ^ (q : ℝ) ∧ (2 : ℝ) ^ (q : ℝ) ≤ (U : ℝ) := by
  have hloglo : (logTwoLower : ℝ) ≤ log 2 := by
    simpa [logTwoLower] using log_two_24_digits.1
  have hloghi : log 2 ≤ (logTwoUpper : ℝ) := by
    simpa [logTwoUpper] using log_two_24_digits.2
  have hN : logTwoUpper * y < (16 : ℕ) + 2 := by
    have h := mul_le_mul_of_nonneg_left hy' (by norm_num [logTwoUpper] : 0 ≤ logTwoUpper)
    norm_num [logTwoUpper] at h ⊢
    linarith
  have h := power_two_rational_bounds (x := (q : ℝ)) n hy
    (by exact_mod_cast hq) (by norm_num [logTwoLower] : 0 ≤ logTwoLower)
    hloglo hloghi 16 hN
  have hL' := (Rat.cast_le (K := ℝ)).mpr hL
  have hU' := (Rat.cast_le (K := ℝ)).mpr hU
  exact ⟨hL'.trans h.1, h.2.trans hU'⟩

end Cycle13
