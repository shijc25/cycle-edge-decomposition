import Cycle12.RationalLabelEntropy
import Cycle12.CoverPopulationBounds

namespace Cycle12
open Real Cycle13
noncomputable section

theorem minority_label_budget_from_scales {n N p z R Rlo t qmark ymax cutoff slope intercept cap frac rho E : ℝ}
    (hn : 0 < n) (hp : 0 < p) (hz : 0 < z) (hRlo : 0 < Rlo) (hR : Rlo ≤ R)
    (hq : 0 < qmark) (ht : qmark*R ≤ t) (hym : 0 ≤ ymax)
    (hs : 0 ≤ slope) (hi : 0 ≤ intercept) (hcut0 : 0 ≤ cutoff) (hcut : cutoff ≤ ymax*n)
    (hN : N=p*n) (hNZ : N=z*R) (hcap : frac ≤ cap) (hcap1 : cap < 1)
    (hE : exp 1 ≤ E)
    (hrho : (E-1)*(slope*ymax+intercept/Rlo)/(1-cap)+6/(qmark*Rlo) ≤ rho) :
    (exp 1-1)*(t/N)*((slope*p*cutoff+intercept*z)/(1-frac))+6 ≤ rho*t := by
  have hRp := hRlo.trans_le hR
  have hNp : 0 < N := by rw [hN]; exact mul_pos hp hn
  have htp : 0 < t := (mul_pos hq hRp).trans_le ht
  have hscale : qmark*Rlo ≤ t := (mul_le_mul_of_nonneg_left hR hq.le).trans ht
  have hden : 0 < 1-cap := sub_pos.mpr hcap1
  have hdenActual : 0 < 1-frac := by linarith only [hcap,hcap1]
  have hnum0 : 0 ≤ slope*p*cutoff+intercept*z := by positivity
  have hcount : (slope*p*cutoff+intercept*z)/N ≤ slope*ymax+intercept/Rlo := by
    have hiR := div_le_div_of_nonneg_left hi hRlo hR
    have hsl := mul_le_mul_of_nonneg_left hcut (mul_nonneg hs hp.le)
    have hsl' : slope*p*cutoff ≤ (slope*ymax)*N := by rw [hN]; nlinarith only [hsl]
    have hc := div_le_div_of_nonneg_right hsl' hNp.le
    have he1 : (slope*ymax)*N/N=slope*ymax := by field_simp
    have he2 : intercept*z/N=intercept/R := by rw [hNZ]; field_simp
    rw [he1] at hc
    rw [add_div,he2]
    exact add_le_add hc hiR
  have hfrac := div_le_div_of_nonneg_left (div_nonneg hnum0 hNp.le) hden (sub_le_sub_left hcap 1)
  have hcount' := hfrac.trans (div_le_div_of_nonneg_right hcount hden.le)
  have he0 : 0 ≤ exp 1-1 := sub_nonneg.mpr (one_le_exp_iff.mpr (by norm_num))
  have hbound0 : 0 ≤ (slope*ymax+intercept/Rlo)/(1-cap) := by positivity
  have hcoef : (exp 1-1)*((slope*p*cutoff+intercept*z)/N/(1-frac)) ≤
      (E-1)*(slope*ymax+intercept/Rlo)/(1-cap) := by
    apply (mul_le_mul_of_nonneg_left hcount' he0).trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right (sub_le_sub_right hE 1) hbound0
  have hmiss : 6 ≤ t*(6/(qmark*Rlo)) := by
    have hh := mul_le_mul_of_nonneg_right hscale (by positivity : 0 ≤ 6/(qmark*Rlo))
    have he : (qmark*Rlo)*(6/(qmark*Rlo))=6 := by field_simp
    rwa [he] at hh
  have hmain := mul_le_mul_of_nonneg_left hcoef htp.le
  have hbudget := mul_le_mul_of_nonneg_left hrho htp.le
  have hid : t*((exp 1-1)*((slope*p*cutoff+intercept*z)/N/(1-frac)))=
      (exp 1-1)*(t/N)*((slope*p*cutoff+intercept*z)/(1-frac)) := by ring
  rw [hid] at hmain
  nlinarith only [hmain,hmiss,hbudget]

end
end Cycle12
