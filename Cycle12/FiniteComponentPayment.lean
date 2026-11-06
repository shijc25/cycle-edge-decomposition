import Cycle12.FiniteCoreCoordinates
import Cycle12.Foundations.FiniteCoreRounding

namespace Cycle12
open Cycle13 SimpleGraph Real Cycle13.MixedSample
noncomputable section

def componentDensityA (s T t : ℝ) : ℝ := ((43/10)/t)*cubeScale (s*T/2)

theorem terminalBlockFee_coordinates {s T t m : ℝ}
    (hs : 0 < s) (hT : 0 < T) (ht : 0 < t) (hm : 0 ≤ m) :
    terminalBlockFee s T t m =
      s*(1/2+1/t+3*sqrt s/t+densityFee (componentDensityA s T t) 0 (2*m/(s*T))) := by
  have hc : cubeScale (s*T/2)*(2*m/(s*T))^(1/3:ℝ)=cubeScale m := by
    unfold cubeScale
    norm_num only [one_div]
    rw [← mul_rpow (by positivity : 0 ≤ s*T/2) (by positivity : 0 ≤ 2*m/(s*T))]
    congr 1
    field_simp
  unfold terminalBlockFee coverGraphBudget densityFee componentDensityA
  rw [← hc]
  field_simp
  ring

theorem componentDensityA_mono {s M T t : ℝ}
    (hs : 0 < s) (hsM : s ≤ M) (hT : 0 < T) (ht : 0 < t) :
    componentDensityA s T t ≤ componentDensityA M T t := by
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (43/10)/t)
  unfold cubeScale
  apply rpow_le_rpow (by positivity) _ (by norm_num)
  nlinarith

/-- One tangent also controls every boundary-free component, uniformly
over all component orders up to M and including zero density. -/
theorem terminalBlockFee_bound_of_tangent {M T t x value dlo dhi K : ℝ}
    (hM : 0 < M) (hT : 0 < T) (ht : 0 < t) (hx : 0 < x)
    (hv : densityFee (componentDensityA M T t) 0 x ≤ value)
    (hdlo : dlo ≤ densityFeeDeriv (componentDensityA M T t) 0 x)
    (hdhi : densityFeeDeriv (componentDensityA M T t) 0 x ≤ dhi) (hdhi₀ : dhi ≤ 0)
    (hpay : 1/2+1/t+3*sqrt M/t+max 0 (value-dlo*x) ≤ K)
    {s m : ℝ} (hs : 0 < s) (hsM : s ≤ M) (hm : 0 ≤ m) :
    terminalBlockFee s T t m ≤ K*s := by
  have hA : 0 ≤ componentDensityA M T t := by unfold componentDensityA cubeScale; positivity
  have hbound := densityFee_component_bound hA hx hv hdlo hdhi hdhi₀
    (by positivity : 0 ≤ 2*m/(s*T))
  have hmono := mul_le_mul_of_nonneg_right (componentDensityA_mono hs hsM hT ht)
    (rpow_nonneg (by positivity : 0 ≤ 2*m/(s*T)) (1/3:ℝ))
  have hfee : densityFee (componentDensityA s T t) 0 (2*m/(s*T)) ≤
      densityFee (componentDensityA M T t) 0 (2*m/(s*T)) := by
    unfold densityFee
    linarith only [hmono]
  have hroot := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hsM) (by norm_num : (0:ℝ) ≤ 3)) ht.le
  have htotal : 1/2+1/t+3*sqrt s/t+
      densityFee (componentDensityA s T t) 0 (2*m/(s*T)) ≤ K := by
    linarith only [hbound,hfee,hroot,hpay]
  rw [terminalBlockFee_coordinates hs hT ht hm]
  nlinarith only [htotal,hs]

/-- The complete graph-theoretic finite DFS step in terms of two core
endpoint bounds and a component scalar bound. The mixed cover and the
previous affine theorem remain explicit hypotheses. -/
theorem weightedAffine_mixed_dfs_step {C K t b : ℝ} {T : ℕ}
    (hb : 0 < b) (hT : 2^20 ≤ T) (ht : 0 < t)
    (hcover : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      FineCover H 2 ∧ CoarseCover H 1)
    (hsuffix : WeightedAffineBound C t)
    (hsmall : (1+1/b)/2 ≤ K)
    (hleft : ∀ d : ℝ, t < d → coreFeeAtDensity T t d (1/(2*b+1/1048576)) ≤ K)
    (hright : ∀ d : ℝ, t < d → coreFeeAtDensity T t d (1/b) ≤ K)
    (hcomponent : ∀ s m : ℝ, 0 < s → s ≤ b*T+1 → 0 ≤ m →
      terminalBlockFee s T t m ≤ K*s) : WeightedAffineBound (C+K) T := by
  have hTN : 0 < T := by omega
  have hTR : (0:ℝ) < T := by exact_mod_cast hTN
  apply weightedAffine_dfs_step (finiteCoreThreshold_pos hb hTN) (by omega) ht hsuffix
  apply finiteBlockPayment_of_mixed_cover ht hcover
  · intro s hslo hshi m hm
    have hsN : 0 < s := (finiteCoreThreshold_pos hb hTN).trans_le hslo
    have hsR : (0:ℝ) < s := by exact_mod_cast hsN
    exact regularBlockFee_bound_of_core_endpoints hsR hTR ht (by positivity) (by positivity)
      (rounded_core_gamma hb hTN (finite_core_rounding_error hT) hslo hshi)
      hsmall hleft hright hm
  · intro s hs hsk m hm
    exact hcomponent s m (by exact_mod_cast hs) (rounded_component_bound hb hTN hsk) hm

end
end Cycle12
