import Cycle12.FiniteCoverPayment
import Cycle12.Foundations.FiniteCoreCoordinates
import Cycle12.Foundations.FiniteCoreConvexity
import Cycle12.Foundations.FiniteDensityTangent

namespace Cycle12
open Cycle13 Real Set MixedSample
noncomputable section

def coreFeeAtDensity (T t d gamma : ℝ) : ℝ :=
  coreShapeFee (cycleFactor (d/(4*(43/10)^3))+2/t-d/(2*T))
    ((43/10)*cubeScale (d*T/2)/t) (3*sqrt T/t) gamma

theorem coreFeeAtDensity_convex {T t d : ℝ}
    (hT : 0 ≤ T) (ht : 0 < t) (hd : 0 ≤ d) :
    ConvexOn ℝ (Ioi 0) (coreFeeAtDensity T t d) := by
  apply coreShapeFee_convex
  · unfold cubeScale; positivity
  · positivity

/-- Exact conversion of the graph budget to the core-shape function.
The degree is that of the padded block, and gamma is boundary/core. -/
theorem mixed_core_payment_coordinates {s T t m : ℝ}
    (hs : 0 < s) (hT : 0 < T) (ht : 0 < t) (hm : 0 ≤ m) :
    coverCycleBudget (s+T) m+(coverGraphBudget (s+T) m+2*(s+T))/t-m/T =
      s*coreFeeAtDensity T t (2*m/(s+T)) (T/s) := by
  have hn : 0 < s+T := by positivity
  have hz : 0 < (s+T)/T := by positivity
  have hd : 0 ≤ (2*m/(s+T))*T/2 := by positivity
  have hmz : (2*m/(s+T)*T/2)*((s+T)/T)=m := by field_simp <;> ring
  have hc : cubeScale (2*m/(s+T)*T/2)*((s+T)/T)^(1/3:ℝ)=cubeScale m := by
    unfold cubeScale
    norm_num only [one_div]
    rw [← mul_rpow hd hz.le,hmz]
  have hsq : sqrt T*((s+T)/T)^(1/2:ℝ)=sqrt (s+T) := by
    rw [← sqrt_eq_rpow,← sqrt_mul hT.le]
    congr 1
    field_simp
  have h₃ := powerPerspective_scaled (p:=(1/3:ℝ)) hs hT
  have h₂ := powerPerspective_scaled (p:=(1/2:ℝ)) hs hT
  norm_num only at h₃ h₂
  have hu : (2*m/(s+T))/(4*(43/10)^3)=m/((2*(43/10)^3)*(s+T)) := by field_simp <;> ring
  rw [cover_cycle_budget_eq]
  unfold coreFeeAtDensity coreShapeFee coverGraphBudget
  rw [hu]
  have he : s*((1+T/s)*(cycleFactor (m/((2*(43/10)^3)*(s+T)))+2/t-(2*m/(s+T))/(2*T))+
      (43/10)*cubeScale (2*m/(s+T)*T/2)/t*powerPerspective (4/3) (T/s)+
      3*sqrt T/t*powerPerspective (3/2) (T/s)) =
    (s+T)*cycleFactor (m/((2*(43/10)^3)*(s+T)))+2*(s+T)/t-m/T+
      ((43/10)/t)*cubeScale (2*m/(s+T)*T/2)*(s*powerPerspective (4/3) (T/s))+
      (3/t)*sqrt T*(s*powerPerspective (3/2) (T/s)) := by field_simp <;> ring
  rw [he,h₃,h₂]
  rw [← hc,← hsq]
  ring

theorem regularBlockFee_low_density {s T t m : ℝ}
    (hs : 0 < s) (hT : 0 < T) (ht : 0 < t) (hm : 0 ≤ m)
    (hd : 2*m ≤ t*(s+T)) : regularBlockFee s T t m ≤ (s+T)/2 := by
  have hh : m/t ≤ (s+T)/2 := (div_le_iff₀ ht).mpr (by nlinarith)
  have hn : 0 ≤ m/T := div_nonneg hm hT.le
  exact (min_le_left _ _).trans (by linarith)

/-- Convexity fills the complete interval between the two certified
core endpoints; low density is paid by leaving all edges as singles. -/
theorem regularBlockFee_bound_of_core_endpoints {s T t lo hi K : ℝ}
    (hs : 0 < s) (hT : 0 < T) (ht : 0 < t)
    (hlo : 0 < lo) (hhi : 0 < hi) (hgamma : T/s ∈ Icc lo hi)
    (hsmall : (1+hi)/2 ≤ K)
    (hleft : ∀ d : ℝ, t < d → coreFeeAtDensity T t d lo ≤ K)
    (hright : ∀ d : ℝ, t < d → coreFeeAtDensity T t d hi ≤ K)
    {m : ℝ} (hm : 0 ≤ m) : regularBlockFee s T t m ≤ K*s := by
  have hn : 0 < s+T := by positivity
  by_cases hd : 2*m ≤ t*(s+T)
  · have hh := regularBlockFee_low_density hs hT ht hm hd
    have hfrac : (s+T)/2=s*((1+T/s)/2) := by field_simp
    rw [hfrac] at hh
    have hbound : (1+T/s)/2 ≤ K := by linarith [hgamma.2]
    nlinarith
  · have hdeg : t < 2*m/(s+T) := (lt_div_iff₀ hn).mpr (by linarith)
    have hconv := coreFeeAtDensity_convex hT.le ht (le_of_lt (ht.trans hdeg))
    have hbound := hconv.le_max_of_mem_Icc hlo hhi hgamma
    have hh : coreFeeAtDensity T t (2*m/(s+T)) (T/s) ≤ K :=
      hbound.trans (max_le (hleft _ hdeg) (hright _ hdeg))
    calc
      _ ≤ coverCycleBudget (s+T) m+(coverGraphBudget (s+T) m+2*(s+T))/t-m/T := min_le_right _ _
      _ = s*coreFeeAtDensity T t (2*m/(s+T)) (T/s) :=
        mixed_core_payment_coordinates hs hT ht hm
      _ ≤ K*s := by nlinarith

end
end Cycle12
