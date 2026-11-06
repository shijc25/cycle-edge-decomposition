import Cycle12.Foundations.SeriesBounds

/-! Rational certificates with kernel-checked meaning in the real numbers. -/
namespace Cycle13
open Finset Real

def ratLogPartial (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range n, 2 * q ^ (2 * k + 1) / (2 * k + 1)

def ratLogUpper (q : ℚ) (n : ℕ) : ℚ :=
  ratLogPartial q n + 2 * q ^ (2 * n + 1) / ((2 * n + 1) * (1 - q ^ 2))

def ratExpPartial (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range n, q ^ k / k.factorial

def ratExpUpper (q : ℚ) (n : ℕ) : ℚ :=
  ratExpPartial q (n + 1) + (q ^ (n + 1) / (n + 1).factorial) / (1 - q / (n + 2))

theorem cast_ratLogPartial (q : ℚ) (n : ℕ) :
    (ratLogPartial q n : ℝ) = logPartial (q : ℝ) n := by
  simp only [ratLogPartial, logPartial, logTerm, Rat.cast_sum, Rat.cast_div,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]

theorem cast_ratExpPartial (q : ℚ) (n : ℕ) :
    (ratExpPartial q n : ℝ) = expPartial (q : ℝ) n := by
  simp only [ratExpPartial, expPartial, expTerm, Rat.cast_sum, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast]

theorem ratLog_bounds {q : ℚ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (n : ℕ) :
    (ratLogPartial q n : ℝ) ≤ log ((1 + (q : ℝ)) / (1 - (q : ℝ))) ∧
      log ((1 + (q : ℝ)) / (1 - (q : ℝ))) ≤ (ratLogUpper q n : ℝ) := by
  have h := log_series_bounds (x := (q : ℝ)) (by exact_mod_cast hq₀) (by exact_mod_cast hq₁) n
  simpa only [ratLogUpper, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, cast_ratLogPartial] using h

theorem ratLog_argument_bounds {q : ℚ} (hq : 1 ≤ q) (n : ℕ) :
    (ratLogPartial ((q - 1) / (q + 1)) n : ℝ) ≤ log (q : ℝ) ∧
      log (q : ℝ) ≤ (ratLogUpper ((q - 1) / (q + 1)) n : ℝ) := by
  have hqpos : (0 : ℚ) < q + 1 := by linarith
  have h₀ : (0 : ℚ) ≤ (q - 1) / (q + 1) := div_nonneg (by linarith) hqpos.le
  have h₁ : (q - 1) / (q + 1) < (1 : ℚ) := (div_lt_one hqpos).mpr (by linarith)
  have h := ratLog_bounds h₀ h₁ n
  have hqp : (0 : ℝ) < (q : ℝ) + 1 := by exact_mod_cast hqpos
  have he : (1 + (((q - 1) / (q + 1) : ℚ) : ℝ)) /
      (1 - (((q - 1) / (q + 1) : ℚ) : ℝ)) = (q : ℝ) := by
    push_cast
    field_simp
    ring
  rw [he] at h
  exact h

theorem ratExp_bounds {q : ℚ} (hq : 0 ≤ q) (n : ℕ) (hn : q < n + 2) :
    (ratExpPartial q (n + 1) : ℝ) ≤ exp (q : ℝ) ∧
      exp (q : ℝ) ≤ (ratExpUpper q n : ℝ) := by
  have h := exp_series_bounds (x := (q : ℝ)) (by exact_mod_cast hq) n (by exact_mod_cast hn)
  simpa only [ratExpUpper, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, cast_ratExpPartial] using h

theorem log_scale_bounds {y l₂ u₂ l u : ℝ} (hy : 0 < y) (j : ℕ)
    (h₂lo : l₂ ≤ log 2) (h₂hi : log 2 ≤ u₂) (hlo : l ≤ log y) (hhi : log y ≤ u) :
    j * l₂ + l ≤ log (2 ^ j * y) ∧ log (2 ^ j * y) ≤ j * u₂ + u := by
  rw [Real.log_mul (by positivity) hy.ne', Real.log_pow]
  constructor
  · exact add_le_add (mul_le_mul_of_nonneg_left h₂lo (Nat.cast_nonneg _)) hlo
  · exact add_le_add (mul_le_mul_of_nonneg_left h₂hi (Nat.cast_nonneg _)) hhi

theorem log_reciprocal_bounds {y l u : ℝ} (hlo : l ≤ log y) (hhi : log y ≤ u) :
    -u ≤ log y⁻¹ ∧ log y⁻¹ ≤ -l := by
  rw [Real.log_inv]
  exact ⟨neg_le_neg hhi, neg_le_neg hlo⟩

theorem sqrt_rational_certificate {q l u : ℚ} (hq : 0 ≤ q)
    (hl : 0 ≤ l) (hu : 0 ≤ u) (hlo : l * l ≤ q) (hhi : q ≤ u * u) :
    (l : ℝ) ≤ sqrt (q : ℝ) ∧ sqrt (q : ℝ) ≤ (u : ℝ) := by
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlR : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have huR : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hloR : (l : ℝ) * l ≤ q := by exact_mod_cast hlo
  have hhiR : (q : ℝ) ≤ (u : ℝ) * u := by exact_mod_cast hhi
  have hs := Real.sq_sqrt hqR
  have hs₀ := Real.sqrt_nonneg (q : ℝ)
  constructor <;> nlinarith

theorem root_rational_certificate {q l u : ℚ} {k : ℕ} (hk : k ≠ 0)
    (hq : 0 ≤ q) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : l ^ k ≤ q) (hhi : q ≤ u ^ k) :
    (l : ℝ) ≤ (q : ℝ) ^ (k : ℝ)⁻¹ ∧ (q : ℝ) ^ (k : ℝ)⁻¹ ≤ (u : ℝ) := by
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlR : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have huR : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hloR : (l : ℝ) ^ k ≤ (q : ℝ) := by exact_mod_cast hlo
  have hhiR : (q : ℝ) ≤ (u : ℝ) ^ k := by exact_mod_cast hhi
  constructor
  · have h := Real.rpow_le_rpow (pow_nonneg hlR _) hloR (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    simpa only [Real.pow_rpow_inv_natCast hlR hk] using h
  · have h := Real.rpow_le_rpow hqR hhiR (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    simpa only [Real.pow_rpow_inv_natCast huR hk] using h

end Cycle13
