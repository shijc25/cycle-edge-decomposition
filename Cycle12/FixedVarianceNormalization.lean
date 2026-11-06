import Cycle12.FixedSampleEdgeVariance

namespace Cycle12
noncomputable section

def finiteOrderVarianceFactor (n : ℝ) : ℝ := (n/(n-2))^3

theorem fixed_variance_cap_upper {n k m : ℝ} (hn : 2 < n) (hm : 0 ≤ m)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hedges : 2*m ≤ n*(n-1)) :
    fixedEdgeVarianceCap n k m ≤ m*k^3*(n-k)*(n^2-2*m)/(n^2*(n-2)^3) := by
  have hn0 : 0 < n := by linarith
  have hn2 : 0 < n-2 := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hmissing : 0 ≤ n*(n-1)-2*m := sub_nonneg.mpr hedges
  have hsquare : (k-1)^2 ≤ k^2 := by nlinarith only [hk]
  have hmissingUpper : n*(n-1)-2*m ≤ n^2-2*m := by nlinarith only [hn0]
  have hprod := mul_le_mul hsquare hmissingUpper hmissing (sq_nonneg k)
  have hfront := mul_nonneg (mul_nonneg hm hk0) (sub_nonneg.mpr hkn)
  have hnum := mul_le_mul_of_nonneg_left hprod hfront
  have hden : n^2*(n-2)^3 ≤ n^2*(n-2)*(n-1)^2 := by
    have hh : (n-2)^2 ≤ (n-1)^2 := by nlinarith only [hn]
    have hb := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg n) hn2.le)
    nlinarith only [hb]
  have hnum0 : 0 ≤ m*k*(n-k)*k^2*(n^2-2*m) :=
    mul_nonneg (mul_nonneg hfront (sq_nonneg k)) (hmissing.trans hmissingUpper)
  unfold fixedEdgeVarianceCap
  calc
    _ ≤ m*k*(n-k)*k^2*(n^2-2*m)/(n^2*(n-2)*(n-1)^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [hnum]
    _ ≤ m*k*(n-k)*k^2*(n^2-2*m)/(n^2*(n-2)^3) :=
      div_le_div_of_nonneg_left hnum0 (by positivity) hden
    _ = _ := by ring

theorem fixed_internal_variance_normalized {n k m p s : ℝ}
    (hn : 2 < n) (hm : 0 < m) (hp : 0 < p) (hs : 0 < s)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hedges : 2*m ≤ n*(n-1))
    (hk_eq : k=p*n) (hm_eq : m=n^2/(2*s)) :
    fixedEdgeVarianceCap n k m ≤
      (2*(1-p)*(s-1)/(p*n)*finiteOrderVarianceFactor n)*(p^2*m)^2 := by
  have hh := fixed_variance_cap_upper hn hm.le hk hkn hedges
  have hn0 : n≠0 := ne_of_gt (by linarith only [hn])
  have hn2 : n-2≠0 := ne_of_gt (by linarith only [hn])
  apply hh.trans_eq
  rw [hk_eq,hm_eq]
  unfold finiteOrderVarianceFactor
  field_simp
  <;> ring

theorem fixed_incident_variance_normalized {n k m p s w : ℝ}
    (hn : 2 < n) (hm : 0 < m) (hs : 0 < s) (hw : 0 < w)
    (hk0 : 0 ≤ k) (hkcomp : 1 ≤ n-k) (hedges : 2*m ≤ n*(n-1))
    (hk_eq : k=p*n) (hm_eq : m=n^2/(2*s)) :
    fixedEdgeVarianceCap n (n-k) m ≤
      (2*p*(1-p)^3*(s-1)/(w^2*n)*finiteOrderVarianceFactor n)*(w*m)^2 := by
  have hh := fixed_variance_cap_upper hn hm.le hkcomp (by linarith only [hk0]) hedges
  have hn0 : n≠0 := ne_of_gt (by linarith only [hn])
  have hn2 : n-2≠0 := ne_of_gt (by linarith only [hn])
  apply hh.trans_eq
  rw [hk_eq,hm_eq]
  unfold finiteOrderVarianceFactor
  field_simp
  <;> ring

theorem finite_order_variance_factor_antitone {lower n : ℝ}
    (hl : 2 < lower) (hn : lower ≤ n) :
    finiteOrderVarianceFactor n ≤ finiteOrderVarianceFactor lower := by
  have hl0 : 0 < lower-2 := by linarith only [hl]
  have hn0 : 0 < n-2 := by linarith only [hl,hn]
  have hr : n/(n-2) ≤ lower/(lower-2) := by
    apply (div_le_div_iff₀ hn0 hl0).mpr
    nlinarith only [hn]
  exact pow_le_pow_left₀ (div_nonneg (by linarith only [hl,hn]) hn0.le) hr 3

theorem density_variance_quarter {s : ℝ} (hs : 0 < s) : (s-1)/s^2 ≤ 1/4 := by
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  nlinarith [sq_nonneg (s-2)]

theorem density_variance_antitone {lower s : ℝ} (hl : 2 ≤ lower) (hs : lower ≤ s) :
    (s-1)/s^2 ≤ (lower-1)/lower^2 := by
  have hl0 : 0 < lower := by linarith only [hl]
  have hs0 : 0 < s := hl0.trans_le hs
  have hfactor : 0 ≤ s*lower-s-lower := by
    have hh := mul_nonneg (show 0 ≤ s-2 by linarith only [hl,hs]) (sub_nonneg.mpr hl)
    nlinarith only [hh,hl,hs]
  have hh := mul_nonneg (sub_nonneg.mpr hs) hfactor
  apply (div_le_div_iff₀ (sq_pos_of_pos hs0) (sq_pos_of_pos hl0)).mpr
  nlinarith only [hh]

end
end Cycle12
