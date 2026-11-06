import Cycle12.RationalLabelEntropy

namespace Cycle12
open Real
noncomputable section

theorem cover_entropy_union_exponent_bound {R z D M gamma bb entropy upper : ℝ} {t : ℕ}
    (hR : 0 ≤ R) (hD : D*R ≤ z) (hM : 0 ≤ M) (hg : 0 ≤ gamma)
    (ht : (t:ℝ) ≤ M*R) (he : 0 ≤ entropy) (heu : entropy ≤ upper)
    (hb : bb ≤ D*gamma-M*upper) :
    exp ((t:ℝ)*entropy)*(2*exp (-gamma*z)) ≤ 2*exp (-bb*R) := by
  have hu : 0 ≤ upper := he.trans heu
  have hte := (mul_le_mul_of_nonneg_left heu (Nat.cast_nonneg (α:=ℝ) t)).trans
    (mul_le_mul_of_nonneg_right ht hu)
  have hzg := mul_le_mul_of_nonneg_left hD hg
  have hbr := mul_le_mul_of_nonneg_right hb hR
  have harg : (t:ℝ)*entropy+(-gamma*z) ≤ -bb*R := by nlinarith only [hte,hzg,hbr]
  calc
    _ = 2*exp ((t:ℝ)*entropy+(-gamma*z)) := by rw [exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr harg) (by norm_num)

theorem cover_all_labels_exp (t : ℕ) : (2:ℝ)^t=exp ((t:ℝ)*log 2) := by
  rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ) < 2)]

end
end Cycle12
