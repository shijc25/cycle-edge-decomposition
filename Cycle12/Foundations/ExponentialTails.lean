import Cycle12.Foundations.SeriesBounds

namespace Cycle13
open Finset Real Filter
noncomputable section

def expScaleTerm (a r : ℝ) (k : ℕ) : ℝ := exp (-a * r ^ k)

theorem expScaleTerm_step (a r : ℝ) (k : ℕ) :
    expScaleTerm a r (k + 1) = exp (-a * (r - 1) * r ^ k) * expScaleTerm a r k := by
  unfold expScaleTerm
  rw [← exp_add]
  congr 1
  ring

theorem expScaleTerm_ratio_bound {a r : ℝ} (ha : 0 ≤ a) (hr : 1 ≤ r)
    {N k : ℕ} (hk : N ≤ k) :
    expScaleTerm a r (k + 1) ≤ exp (-a * (r - 1) * r ^ N) * expScaleTerm a r k := by
  rw [expScaleTerm_step]
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  apply exp_le_exp.mpr
  have hp : r ^ N ≤ r ^ k := pow_le_pow_right₀ hr hk
  have h := mul_le_mul_of_nonneg_left hp (mul_nonneg ha (by linarith : 0 ≤ r - 1))
  nlinarith

theorem expScaleTerm_summable {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    Summable (expScaleTerm a r) := by
  have hρ : exp (-a * (r - 1)) < 1 := by
    rw [exp_lt_one_iff]
    nlinarith
  apply summable_of_ratio_norm_eventually_le hρ
  filter_upwards [] with k
  simpa only [expScaleTerm, Real.norm_eq_abs, abs_of_pos (exp_pos _), pow_zero, mul_one] using
    expScaleTerm_ratio_bound ha.le hr.le (N := 0) (Nat.zero_le k)

/-- A finite prefix and one verified ratio bound control the entire infinite
scale series used by the global recursion. -/
theorem expScaleSeries_bound {a r ρ : ℝ} (ha : 0 < a) (hr : 1 < r) (N : ℕ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hstep : exp (-a * (r - 1) * r ^ N) ≤ ρ) :
    (∑' k : ℕ, expScaleTerm a r k) ≤
      (∑ k ∈ range N, expScaleTerm a r k) + expScaleTerm a r N / (1 - ρ) := by
  apply geometric_remainder_bound (expScaleTerm_summable ha hr).hasSum N hρ₀ hρ₁
  intro k hk
  exact (expScaleTerm_ratio_bound ha.le hr.le hk).trans
    (mul_le_mul_of_nonneg_right hstep (exp_pos _).le)

theorem expScaleSeries_half_tail {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (N : ℕ)
    (hstep : log 2 ≤ a * (r - 1) * r ^ N) :
    (∑' k : ℕ, expScaleTerm a r k) ≤
      (∑ k ∈ range N, expScaleTerm a r k) + 2 * expScaleTerm a r N := by
  have he : exp (-a * (r - 1) * r ^ N) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ exp (-log 2) := exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have h := expScaleSeries_bound ha hr N (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1) he
  convert h using 1 <;> ring

theorem expScaleSeries_certified_bound {a r B U : ℝ} (ha : 0 < a) (hr : 1 < r)
    (N : ℕ) (v : Fin N → ℝ)
    (hstep : log 2 ≤ a * (r - 1) * r ^ N)
    (hterms : ∀ i : Fin N, expScaleTerm a r i.val ≤ v i)
    (htail : expScaleTerm a r N ≤ B) (htotal : (∑ i, v i) + 2 * B ≤ U) :
    (∑' k : ℕ, expScaleTerm a r k) ≤ U := by
  apply (expScaleSeries_half_tail ha hr N hstep).trans
  have hfinite : (∑ k ∈ range N, expScaleTerm a r k) ≤ ∑ i, v i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_le_sum (fun i _ => hterms i)
  linarith

def powerScaleTerm (z θ : ℝ) (k : ℕ) : ℝ := (2 : ℝ) ^ (-z * θ⁻¹ ^ k)

theorem powerScaleTerm_eq (z θ : ℝ) (k : ℕ) :
    powerScaleTerm z θ k = expScaleTerm (log 2 * z) θ⁻¹ k := by
  unfold powerScaleTerm expScaleTerm
  rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem powerScaleSeries_summable {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < 1) :
    Summable (powerScaleTerm z θ) := by
  change Summable (fun k : ℕ => powerScaleTerm z θ k)
  simp_rw [powerScaleTerm_eq]
  exact expScaleTerm_summable (mul_pos (log_pos (by norm_num)) hz)
    ((one_lt_inv₀ hθ).mpr hθ')

theorem powerScaleSeries_half_tail {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < 1)
    (N : ℕ) (hstep : 1 ≤ z * (θ⁻¹ - 1) * θ⁻¹ ^ N) :
    (∑' k : ℕ, powerScaleTerm z θ k) ≤
      (∑ k ∈ range N, powerScaleTerm z θ k) + 2 * powerScaleTerm z θ N := by
  simp_rw [powerScaleTerm_eq]
  apply expScaleSeries_half_tail (mul_pos (log_pos (by norm_num)) hz)
    ((one_lt_inv₀ hθ).mpr hθ') N
  have h := mul_le_mul_of_nonneg_left hstep (log_pos (by norm_num : (1 : ℝ) < 2)).le
  nlinarith

end
end Cycle13
