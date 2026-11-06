import Cycle12.Foundations.ExponentialTails
import Cycle12.Foundations.RationalPowers

namespace Cycle13
open Finset Real

theorem certified_scale_series_bound {z θ U : ℚ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ' : θ < 1) (N : ℕ) (v : Fin (N + 1) → ℚ)
    (hstep : 1 ≤ z * (θ⁻¹ - 1) * θ⁻¹ ^ N)
    (hpoint : ∀ i : Fin (N + 1),
      (2 : ℝ) ^ ((-z * θ⁻¹ ^ i.val : ℚ) : ℝ) ≤ (v i : ℝ))
    (htotal : (∑ i : Fin N, v i.castSucc) + 2 * v (Fin.last N) ≤ U) :
    (∑' k : ℕ, powerScaleTerm (z : ℝ) (θ : ℝ) k) ≤ (U : ℝ) := by
  have h := powerScaleSeries_half_tail (z := (z : ℝ)) (θ := (θ : ℝ))
    (by exact_mod_cast hz) (by exact_mod_cast hθ)
    (by exact_mod_cast hθ') N (by exact_mod_cast hstep)
  have hpoint' : ∀ i : Fin (N + 1), powerScaleTerm (z : ℝ) (θ : ℝ) i.val ≤ (v i : ℝ) := by
    intro i
    simpa only [powerScaleTerm, Rat.cast_mul, Rat.cast_neg, Rat.cast_pow, Rat.cast_inv] using hpoint i
  have hs : (∑ k ∈ range N, powerScaleTerm (z : ℝ) (θ : ℝ) k) ≤
      ∑ i : Fin N, (v i.castSucc : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_le_sum (fun i _ => hpoint' i.castSucc)
  have ht := hpoint' (Fin.last N)
  have htotal' := (Rat.cast_le (K := ℝ)).mpr htotal
  push_cast at htotal'
  simp only [Fin.val_last] at ht
  exact h.trans (by linarith)

end Cycle13
