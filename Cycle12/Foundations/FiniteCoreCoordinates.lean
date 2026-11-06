import Cycle12.Foundations.FiniteCoverPayment
import Cycle12.Foundations.FiniteCoreConvexity
import Cycle12.Foundations.FiniteDensityTangent

namespace Cycle13
open Real Set MixedSample
noncomputable section

theorem powerPerspective_succ {x p : ℝ} (hx : 0 < x) :
    powerPerspective (1+p) x=(1+x)*((1+x)/x)^p := by
  have hz : 0 < (1+x)/x := by positivity
  unfold powerPerspective positivePerspective
  dsimp only
  rw [rpow_add hz,rpow_one]
  field_simp

theorem powerPerspective_scaled {s T p : ℝ} (hs : 0 < s) (hT : 0 < T) :
    s*powerPerspective (1+p) (T/s)=(s+T)*((s+T)/T)^p := by
  rw [powerPerspective_succ (div_pos hT hs)]
  have he : (1+T/s)/(T/s)=(s+T)/T := by field_simp <;> ring
  rw [he]
  field_simp

def coreFeeAtDensity (T t d gamma : ℝ) : ℝ :=
  coreShapeFee (cycleFactor (d/864)+2/t-d/(2*T))
    (6*cubeScale (d*T/2)/t) (2*sqrt T/t) gamma

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
    cycleBudget (s+T) m+(mixedBudget (s+T) m+2*(s+T))/t-m/T =
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
  have hu : (2*m/(s+T))/864=m/(432*(s+T)) := by field_simp <;> ring
  unfold coreFeeAtDensity coreShapeFee mixedBudget cycleBudget
  rw [hu]
  have he : s*((1+T/s)*(cycleFactor (m/(432*(s+T)))+2/t-(2*m/(s+T))/(2*T))+
      6*cubeScale (2*m/(s+T)*T/2)/t*powerPerspective (4/3) (T/s)+
      2*sqrt T/t*powerPerspective (3/2) (T/s)) =
    (s+T)*cycleFactor (m/(432*(s+T)))+2*(s+T)/t-m/T+
      (6/t)*cubeScale (2*m/(s+T)*T/2)*(s*powerPerspective (4/3) (T/s))+
      (2/t)*sqrt T*(s*powerPerspective (3/2) (T/s)) := by field_simp <;> ring
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
      _ ≤ cycleBudget (s+T) m+(mixedBudget (s+T) m+2*(s+T))/t-m/T := min_le_right _ _
      _ = s*coreFeeAtDensity T t (2*m/(s+T)) (T/s) :=
        mixed_core_payment_coordinates hs hT ht hm
      _ ≤ K*s := by nlinarith

end
end Cycle13
