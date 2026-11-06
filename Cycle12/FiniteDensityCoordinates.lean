import Cycle12.FiniteCoreCoordinates

namespace Cycle12
open Cycle13 Real Cycle13.MixedSample
noncomputable section

def coreDensityA (T t gamma : ℝ) : ℝ :=
  ((43/10)/t)*cubeScale (T^2/(2*(1+gamma)))*powerPerspective (4/3) gamma

def coreDensityB (T gamma : ℝ) : ℝ :=
  (47/200)*(1+gamma)*cubeScale ((4*(43/10)^3)*(1+gamma)/T)

def coreDensityConstant (T t gamma : ℝ) : ℝ :=
  (1/2+2/t)*(1+gamma)+(3*sqrt T/t)*powerPerspective (3/2) gamma

theorem cycleFactor_high_degree {d : ℝ} (hd : (4*(43/10)^3) ≤ d) :
    cycleFactor (d/(4*(43/10)^3))=1/2-(47/200)*(d/(4*(43/10)^3))^(-(1/3:ℝ)) := by
  by_cases hh : d/(4*(43/10)^3) ≤ 1
  · have he : d=(4*(43/10)^3) := by norm_num at hd hh ⊢; linarith
    rw [he]
    norm_num [cycleFactor]
  · simp only [cycleFactor,hh,ite_false]

/-- Exact density substitution at a fixed core endpoint. In particular,
the negative cycle discount has the same coefficient as the certificate. -/
theorem coreFee_density_coordinates {T t d gamma : ℝ}
    (hT : 0 < T) (ht : 0 < t) (hg : 0 < gamma) (hd : (4*(43/10)^3) ≤ d) :
    coreFeeAtDensity T t d gamma = coreDensityConstant T t gamma+
      densityFee (coreDensityA T t gamma) (coreDensityB T gamma) (d*(1+gamma)/T) := by
  have hS : 0 < 1+gamma := by positivity
  have hd₀ : 0 < d := by linarith
  have hX : 0 < d*(1+gamma)/T := by positivity
  have hY : 0 < (4*(43/10)^3)*(1+gamma)/T := by positivity
  have hc : cubeScale (T^2/(2*(1+gamma)))*(d*(1+gamma)/T)^(1/3:ℝ)=cubeScale (d*T/2) := by
    unfold cubeScale
    norm_num only [one_div]
    rw [← mul_rpow (by positivity : 0 ≤ T^2/(2*(1+gamma))) hX.le]
    congr 1
    field_simp <;> ring
  have he : d/(4*(43/10)^3)=(d*(1+gamma)/T)/((4*(43/10)^3)*(1+gamma)/T) := by field_simp
  have hdsc : (d/(4*(43/10)^3))^(-(1/3:ℝ))=
      cubeScale ((4*(43/10)^3)*(1+gamma)/T)*(d*(1+gamma)/T)^(-(1/3:ℝ)) := by
    rw [he,div_rpow hX.le hY.le,rpow_neg hY.le]
    unfold cubeScale
    norm_num only [one_div,div_inv_eq_mul]
    ring
  unfold coreFeeAtDensity coreShapeFee coreDensityConstant densityFee coreDensityA coreDensityB
  rw [cycleFactor_high_degree hd,hdsc]
  rw [← hc]
  ring

theorem coreDensityA_nonneg {T t gamma : ℝ} (hT : 0 < T) (ht : 0 < t) (hg : 0 < gamma) :
    0 ≤ coreDensityA T t gamma := by
  unfold coreDensityA cubeScale powerPerspective positivePerspective
  positivity

theorem coreDensityB_nonneg {T gamma : ℝ} (hT : 0 < T) (hg : 0 < gamma) :
    0 ≤ coreDensityB T gamma := by
  unfold coreDensityB cubeScale
  positivity

/-- A single certified descending tangent pays every high-density
block at this endpoint. The variable density is universally quantified. -/
theorem coreFee_endpoint_of_tangent {T t gamma x value dlo dhi K : ℝ}
    (hT : 0 < T) (ht : (4*(43/10)^3) ≤ t) (hg : 0 < gamma)
    (hx : 0 < x) (hmin : t*(1+gamma)/T ≤ x)
    (hv : densityFee (coreDensityA T t gamma) (coreDensityB T gamma) x ≤ value)
    (hdlo : dlo ≤ densityFeeDeriv (coreDensityA T t gamma) (coreDensityB T gamma) x)
    (hdhi : densityFeeDeriv (coreDensityA T t gamma) (coreDensityB T gamma) x ≤ dhi)
    (hdhi₀ : dhi ≤ 0)
    (hpay : coreDensityConstant T t gamma+value+dlo*(t*(1+gamma)/T-x) ≤ K)
    {d : ℝ} (hd : t ≤ d) : coreFeeAtDensity T t d gamma ≤ K := by
  have ht₀ : 0 < t := by linarith
  have hd₀ : 0 < d := ht₀.trans_le hd
  rw [coreFee_density_coordinates hT ht₀ hg (ht.trans hd)]
  have hbound := densityFee_halfline_bound (coreDensityA_nonneg hT ht₀ hg)
    (coreDensityB_nonneg hT hg) hx hmin hv hdlo hdhi hdhi₀
    (by positivity : 0 < d*(1+gamma)/T)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity)) hT.le)
  linarith

end
end Cycle12
