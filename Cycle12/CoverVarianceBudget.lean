import Cycle12.FixedVarianceNormalization

namespace Cycle12
noncomputable section

theorem cover_internal_variance_identity {n p s w P : ℝ}
    (hw : 0 < w) (hs : 0 < s) (hP : 0 < P)
    (hn : n=4*(43/10)^3*s^2/w^3) (hp : p=w*P) :
    2*(1-p)*(s-1)/(p*n)*finiteOrderVarianceFactor n=
      (1-p)*w^2*((s-1)/s^2)*finiteOrderVarianceFactor n/(2*(43/10)^3*P) := by
  rw [hp,hn]
  field_simp
  <;> ring

theorem cover_incident_variance_identity {n p s w P : ℝ}
    (hw : 0 < w) (hs : 0 < s)
    (hn : n=4*(43/10)^3*s^2/w^3) (hp : p=w*P) :
    2*p*(1-p)^3*(s-1)/(w^2*n)*finiteOrderVarianceFactor n=
      P*w^2*(1-p)^3*((s-1)/s^2)*finiteOrderVarianceFactor n/(2*(43/10)^3) := by
  rw [hp,hn]
  field_simp
  <;> ring

theorem cover_internal_variance_box {n nlo p pl s w wh P Plo density : ℝ}
    (hnlo : 2 < nlo) (hnn : nlo ≤ n) (hw : 0 < w) (hwh : w ≤ wh)
    (hs : 1 ≤ s) (hPlo : 0 < Plo) (hPP : Plo ≤ P)
    (hpl : pl ≤ p) (hp1 : p ≤ 1) (hdensity : (s-1)/s^2 ≤ density)
    (hn : n=4*(43/10)^3*s^2/w^3) (hp : p=w*P) :
    2*(1-p)*(s-1)/(p*n)*finiteOrderVarianceFactor n ≤
      (1-pl)*wh^2*density*finiteOrderVarianceFactor nlo/(2*(43/10)^3*Plo) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hd0 : 0 ≤ (s-1)/s^2 := div_nonneg (sub_nonneg.mpr hs) (sq_nonneg s)
  have hf := finite_order_variance_factor_antitone hnlo hnn
  have hf0 : 0 ≤ finiteOrderVarianceFactor n := by
    unfold finiteOrderVarianceFactor
    have hn0 : 0 < n := by linarith only [hnlo,hnn]
    have hn2 : 0 < n-2 := by linarith only [hnlo,hnn]
    positivity
  have hpl1 : 0 ≤ 1-pl := sub_nonneg.mpr (hpl.trans hp1)
  have hdensity0 := hd0.trans hdensity
  have hfl0 := hf0.trans hf
  rw [cover_internal_variance_identity hw hs0 (hPlo.trans_le hPP) hn hp]
  gcongr

theorem cover_incident_variance_box {n nlo p pl s w wh P Pu density : ℝ}
    (hnlo : 2 < nlo) (hnn : nlo ≤ n) (hw : 0 < w) (hwh : w ≤ wh)
    (hs : 1 ≤ s) (hP : 0 ≤ P) (hPP : P ≤ Pu)
    (hpl : pl ≤ p) (hp1 : p ≤ 1) (hdensity : (s-1)/s^2 ≤ density)
    (hn : n=4*(43/10)^3*s^2/w^3) (hp : p=w*P) :
    2*p*(1-p)^3*(s-1)/(w^2*n)*finiteOrderVarianceFactor n ≤
      Pu*wh^2*(1-pl)^3*density*finiteOrderVarianceFactor nlo/(2*(43/10)^3) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hd0 : 0 ≤ (s-1)/s^2 := div_nonneg (sub_nonneg.mpr hs) (sq_nonneg s)
  have hf := finite_order_variance_factor_antitone hnlo hnn
  have hf0 : 0 ≤ finiteOrderVarianceFactor n := by
    unfold finiteOrderVarianceFactor
    have hn0 : 0 < n := by linarith only [hnlo,hnn]
    have hn2 : 0 < n-2 := by linarith only [hnlo,hnn]
    positivity
  have hpl1 : 0 ≤ 1-pl := sub_nonneg.mpr (hpl.trans hp1)
  have hdensity0 := hd0.trans hdensity
  have hPu0 := hP.trans hPP
  rw [cover_incident_variance_identity hw hs0 hn hp]
  gcongr

theorem cover_density_variance_box {s0 s : ℝ} (hs0 : 0 < s0) (hs : s0 ≤ s) :
    (s-1)/s^2 ≤ if s0 ≤ 2 then 1/4 else (s0-1)/s0^2 := by
  split_ifs with h
  · exact density_variance_quarter (hs0.trans_le hs)
  · exact density_variance_antitone (le_of_not_ge h) hs

end
end Cycle12
