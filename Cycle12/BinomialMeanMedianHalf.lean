import Cycle12.BetaReflection
import Cycle12.BinomialCDFPolynomial

namespace Cycle12
open Finset Polynomial Real
noncomputable section

/-- The lower-median half of the integer-mean binomial theorem in the
sampling range p≤1/2. It follows by reflection of the Bernstein density. -/
theorem binomial_integer_mean_lower_half (n k : ℕ) (p : ℝ)
    (hp0 : 0≤p) (hp : p≤1/2) (hmean : (n:ℝ)*p=(k:ℝ)) :
    1/2≤(binomialCDFPolynomial n k).eval p := by
  rcases hp0.eq_or_lt with hz | hpos
  · rw [← hz,binomial_cdf_zero]
    norm_num
  have hkR : (k:ℝ)≤n := by
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg _
    nlinarith
  have hkn : k≤n := by exact_mod_cast hkR
  have hbN : n-1-k+k≤n := by omega
  have hbR : ((n-1-k:ℕ):ℝ)+(k:ℝ)≤n := by exact_mod_cast hbN
  have hab : ((n-1-k:ℕ):ℝ)*p≤(k:ℝ)*(1-p) := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hbR)]
  let F : ℝ → ℝ := (binomialCDFPolynomial n k).eval
  let H : ℝ → ℝ := fun x => F (p+x)+F (p-x)
  have hD (x : ℝ) : HasDerivAt H
      ((n:ℝ)*((bernsteinPolynomial ℝ (n-1) k).eval (p-x)-
        (bernsteinPolynomial ℝ (n-1) k).eval (p+x))) x := by
    have h₁ := (binomial_cdf_derivative n k (p+x)).comp x ((hasDerivAt_id x).const_add p)
    have h₂ := (binomial_cdf_derivative n k (p-x)).comp x ((hasDerivAt_id x).const_sub p)
    convert h₁.add h₂ using 1
    · rfl
    · ring
  have hanti : AntitoneOn H (Set.Icc 0 p) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 p)
    · exact (continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)).continuousOn
    · intro x _
      exact (hD x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hD x).deriv]
      have hx' : x∈Set.Ioo 0 p := by simpa only [interior_Icc] using hx
      have hb := beta_power_reflection k (n-1-k) p (1-p) x hpos (by linarith)
        hx'.1.le hx'.2 hab
      have hB : (bernsteinPolynomial ℝ (n-1) k).eval (p-x) ≤
          (bernsteinPolynomial ℝ (n-1) k).eval (p+x) := by
        rw [bernstein_real_eval,bernstein_real_eval]
        have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg ((n-1).choose k) : (0:ℝ)≤_)
        convert hh using 1 <;> ring
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr hB)
  have hh := hanti (show 0∈Set.Icc (0:ℝ) p from ⟨le_refl _,hp0⟩)
    (show p∈Set.Icc (0:ℝ) p from ⟨hp0,le_refl _⟩) hp0
  have hnonneg := binomial_cdf_nonneg n k (p+p) (by linarith) (by linarith)
  dsimp only [H,F] at hh
  rw [sub_self,binomial_cdf_zero,add_zero,sub_zero] at hh
  linarith

end
end Cycle12
