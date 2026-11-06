import Cycle12.JansonDependencyUpper

namespace Cycle12
noncomputable section

theorem positive_linear_fraction_mono {M m a b : ℝ}
    (hM : 0 ≤ M) (hMm : M ≤ m) (ha : 0<a) (hb : 0 ≤ b) :
    M/(a+b*M) ≤ m/(a+b*m) := by
  have hdM : 0<a+b*M := add_pos_of_pos_of_nonneg ha (mul_nonneg hb hM)
  have hdm : 0<a+b*m := add_pos_of_pos_of_nonneg ha (mul_nonneg hb (hM.trans hMm))
  apply (div_le_div_iff₀ hdM hdm).mpr
  nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hMm)]

theorem janson_edge_rate_cancel (phi m p a b : ℝ) (hm : m≠0) (hp : p≠0) :
    phi*(m*p^2)^2/(m*p^2+(a*m+b*m^2)*p^3)=
      phi*m*p^2/(1+(a+b*m)*p) := by
  have hn : phi*(m*p^2)^2=(m*p^2)*(phi*m*p^2) := by ring
  have hd : m*p^2+(a*m+b*m^2)*p^3=(m*p^2)*(1+(a+b*m)*p) := by ring
  rw [hn,hd]
  exact mul_div_mul_left _ _ (mul_ne_zero hm (pow_ne_zero _ hp))

/-- Both the endpoint and rectangle denominators are increasing linear
fractions after cancellation. A lower bound on m can therefore be used in
the numerator and in its dependent quadratic budget simultaneously. -/
theorem janson_edge_rate_mass_mono {phi M m p a b : ℝ}
    (hphi : 0 ≤ phi) (hM : 0<M) (hMm : M ≤ m) (hp : 0<p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    phi*(M*p^2)^2/(M*p^2+(a*M+b*M^2)*p^3)  ≤ 
      phi*(m*p^2)^2/(m*p^2+(a*m+b*m^2)*p^3) := by
  rw [janson_edge_rate_cancel _ _ _ _ _ hM.ne' hp.ne',
    janson_edge_rate_cancel _ _ _ _ _ (hM.trans_le hMm).ne' hp.ne']
  have hh := positive_linear_fraction_mono hM.le hMm
    (add_pos_of_pos_of_nonneg (by norm_num : (0:ℝ)<1) (mul_nonneg ha hp.le))
    (mul_nonneg hb hp.le)
  have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg hphi (sq_nonneg p))
  convert hmul using 1 <;> ring

theorem janson_edge_exp_mass_mono {phi M m p a b : ℝ}
    (hphi : 0 ≤ phi) (hM : 0<M) (hMm : M ≤ m) (hp : 0<p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.exp (-phi*(m*p^2)^2/(m*p^2+(a*m+b*m^2)*p^3))  ≤ 
      Real.exp (-phi*(M*p^2)^2/(M*p^2+(a*M+b*M^2)*p^3)) := by
  apply Real.exp_le_exp.mpr
  have hh := neg_le_neg (janson_edge_rate_mass_mono hphi hM hMm hp ha hb)
  simpa only [neg_div,neg_mul] using hh

end
end Cycle12
