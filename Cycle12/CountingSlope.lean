import Cycle12.FixedSamplingGeometry

namespace Cycle12
open Real
noncomputable section

theorem log_affine_div_antitone {a pl p : ℝ} (ha : 0 ≤ a) (hpl : 0 < pl) (hpp : pl ≤ p) :
    log (1+a*p)/p ≤ log (1+a*pl)/pl := by
  have hp : 0 < p := hpl.trans_le hpp
  have hw0 : 0 ≤ pl/p := div_nonneg hpl.le hp.le
  have hw1 : pl/p ≤ 1 := (div_le_one hp).mpr hpp
  have hc : ConcaveOn ℝ (Set.Ioi (0:ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hh := hc.2
    (show (0:ℝ) < 1 by norm_num) (show 0 < 1+a*p by positivity)
    (sub_nonneg.mpr hw1) hw0 (by ring)
  simp only [smul_eq_mul,log_one,mul_zero,zero_add] at hh
  have hx : (1-pl/p)*1+(pl/p)*(1+a*p)=1+a*pl := by field_simp; ring
  rw [hx] at hh
  have hm := mul_le_mul_of_nonneg_right hh hp.le
  have he : ((pl/p)*log (1+a*p))*p=log (1+a*p)*pl := by field_simp
  rw [he] at hm
  exact (div_le_div_iff₀ hp hpl).mpr hm

/-- The count slope checked at the lower sampling endpoint is valid on
the whole interval. The residual sampling fraction may be smaller. -/
theorem fixed_count_mgf_from_lower_sample {pl p residual theta slope : ℝ}
    (hpl : 0 < pl) (hpp : pl ≤ p) (hr : residual ≤ p) (ht : 0 < theta)
    (hs : log (1+pl*(exp theta-1))/(theta*pl) ≤ slope) :
    1-residual+residual*exp theta ≤ exp (theta*slope*p) := by
  have hp : 0 < p := hpl.trans_le hpp
  have ha : 0 ≤ exp theta-1 := sub_nonneg.mpr (one_le_exp_iff.mpr ht.le)
  have hlog := log_affine_div_antitone ha hpl hpp
  have hs' : log (1+pl*(exp theta-1)) ≤ slope*(theta*pl) :=
    (div_le_iff₀ (mul_pos ht hpl)).mp hs
  have hslope : log (1+(exp theta-1)*pl)/pl ≤ theta*slope := by
    apply (div_le_iff₀ hpl).mpr
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hs'
  have hscale := (div_le_iff₀ hp).mp (hlog.trans hslope)
  have hbase : 0 < 1+(exp theta-1)*p := by positivity
  have he := exp_le_exp.mpr hscale
  rw [exp_log hbase] at he
  have hres := mul_le_mul_of_nonneg_right hr ha
  have hid : 1-residual+residual*exp theta=1+(exp theta-1)*residual := by ring
  rw [hid]
  apply (add_le_add le_rfl (by simpa only [mul_comm] using hres)).trans
  convert he using 1 <;> ring

end
end Cycle12
