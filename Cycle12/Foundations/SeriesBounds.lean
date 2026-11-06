import Mathlib

/-! Exact real bounds underlying the rational certificate generator.
No external evaluation or native-decision axiom is used. -/
namespace Cycle13
open Finset Real
noncomputable section

theorem geometric_remainder_bound {f : ℕ → ℝ} {s r : ℝ}
    (hs : HasSum f s) (n : ℕ) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hstep : ∀ k : ℕ, n ≤ k → f (k + 1) ≤ r * f k) :
    s ≤ (∑ k ∈ range n, f k) + f n / (1 - r) := by
  have hgeom : ∀ k : ℕ, f (k + n) ≤ f n * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        f (k + 1 + n) = f (k + n + 1) := by congr 1; omega
        _ ≤ r * f (k + n) := hstep _ (by omega)
        _ ≤ r * (f n * r ^ k) := mul_le_mul_of_nonneg_left ih hr₀
        _ = f n * r ^ (k + 1) := by ring
  have ht : Summable (fun k : ℕ => f (k + n)) := (summable_nat_add_iff n).mpr hs.summable
  have hg := (hasSum_geometric_of_lt_one hr₀ hr₁).mul_left (f n)
  have hbound := hasSum_le hgeom ht.hasSum hg
  have hsplit := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq] at hsplit
  simpa only [div_eq_mul_inv] using (show s ≤ (∑ k ∈ range n, f k) +
      f n * (1 - r)⁻¹ by linarith)

def logTerm (x : ℝ) (k : ℕ) : ℝ := 2 * x ^ (2 * k + 1) / (2 * k + 1)
def logPartial (x : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, logTerm x k

theorem logTerm_step {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    logTerm x (k + 1) ≤ x ^ 2 * logTerm x k := by
  have hden : (0 : ℝ) < 2 * k + 1 := by positivity
  have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
  unfold logTerm
  rw [he, pow_add]
  push_cast
  calc
    _ ≤ 2 * (x ^ (2 * k + 1) * x ^ 2) / (2 * k + 1) := by
      apply div_le_div_of_nonneg_left (by positivity) hden
      linarith
    _ = _ := by ring

theorem log_series_hasSum {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    HasSum (logTerm x) (log ((1 + x) / (1 - x))) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (by rwa [abs_of_nonneg hx₀])
  have hplus : 1 + x ≠ 0 := by linarith
  have hminus : 1 - x ≠ 0 := by linarith
  rw [Real.log_div hplus hminus]
  convert h using 1
  ext k
  simp only [logTerm]
  ring

/-- The exact denominator `(2n+1)(1-x²)` used by the existing Python
logarithm certificates, including the sharper factor `2n+1`. -/
theorem log_series_bounds {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ) :
    logPartial x n ≤ log ((1 + x) / (1 - x)) ∧
      log ((1 + x) / (1 - x)) ≤
        logPartial x n + 2 * x ^ (2 * n + 1) / ((2 * n + 1) * (1 - x ^ 2)) := by
  have hs := log_series_hasSum hx₀ hx₁
  constructor
  · have hl := hs.summable.sum_le_tsum (range n) (fun k _ =>
      show 0 ≤ logTerm x k by unfold logTerm; positivity)
    simpa only [hs.tsum_eq, logPartial] using hl
  · have hr : x ^ 2 < 1 := by nlinarith
    have hb := geometric_remainder_bound hs n (sq_nonneg x) hr
      (fun k _ => logTerm_step hx₀ k)
    simpa only [logPartial, logTerm, div_div] using hb

def expTerm (x : ℝ) (k : ℕ) : ℝ := x ^ k / k.factorial
def expPartial (x : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, expTerm x k

theorem expTerm_step (x : ℝ) (k : ℕ) :
    expTerm x (k + 1) = expTerm x k * (x / (k + 1)) := by
  simp only [expTerm, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [div_mul_eq_div_div]
  ring

theorem exp_series_bounds {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hn : x < n + 2) :
    expPartial x (n + 1) ≤ exp x ∧
      exp x ≤ expPartial x (n + 1) +
        (x ^ (n + 1) / (n + 1).factorial) / (1 - x / (n + 2)) := by
  have hs : HasSum (expTerm x) (exp x) := by
    unfold expTerm
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  constructor
  · exact Real.sum_le_exp_of_nonneg hx (n + 1)
  · have hden : (0 : ℝ) < n + 2 := by positivity
    have hr : x / (n + 2) < 1 := (div_lt_one hden).mpr hn
    have hb := geometric_remainder_bound hs (n + 1) (div_nonneg hx hden.le) hr (by
      intro k hk
      rw [expTerm_step, mul_comm (x / (n + 2))]
      apply mul_le_mul_of_nonneg_left _ (by unfold expTerm; positivity)
      apply div_le_div_of_nonneg_left hx hden
      have hkn : (n : ℝ) + 1 ≤ k := by exact_mod_cast hk
      linarith)
    exact hb

end
end Cycle13
