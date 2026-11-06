import Cycle12.MajorityExponentialCertificate

namespace Cycle12
open Real Cycle13
noncomputable section

theorem global_witness_lower_transfer {dm beta tau K vote tail miss omega : ℝ}
    (hdm : 0 ≤ dm) (htau : 0 ≤ tau) (hgap : beta < tau)
    (hv : exp (-vote) ≤ tail) (hm : exp (-6) ≤ miss)
    (hw : omega ≤ 1-(2*K*beta+(dm+tau)*tail)/(tau-beta)-miss) :
    omega ≤ 1-(2*K*beta+(dm+tau)*exp (-vote))/(tau-beta)-exp (-6) := by
  have hh : (2*K*beta+(dm+tau)*exp (-vote))/(tau-beta) ≤
      (2*K*beta+(dm+tau)*tail)/(tau-beta) := div_le_div_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (add_nonneg hdm htau)))
    (sub_pos.mpr hgap).le
  linarith only [hw,hh,hm]

theorem local_witness_lower_transfer {dm beta err K vote tail miss omega : ℝ}
    (hdm : 0 ≤ dm) (herr : 0 < err)
    (hv : exp (-vote) ≤ tail) (hm : exp (-6) ≤ miss)
    (hw : omega ≤ 1-(2*K*beta+dm*tail)/err-miss) :
    omega ≤ 1-(2*K*beta+dm*exp (-vote))/err-exp (-6) := by
  have hh : (2*K*beta+dm*exp (-vote))/err ≤ (2*K*beta+dm*tail)/err := div_le_div_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hdm)) herr.le
  linarith only [hw,hh,hm]

theorem anchor_witness_lower_transfer {dm beta L ew K full vote tail zlo z omega : ℝ}
    (hdm : 0 < dm) (hb : 0 < beta) (hL : 0 ≤ L) (hew : 0 < ew)
    (hzlo : 0 < zlo) (hz : zlo ≤ z) (hf : 0 ≤ full)
    (hv : exp (-vote) ≤ tail)
    (hw : omega ≤ 1-(2*K+(dm/beta)*tail)/ew-8*(full*L/(dm*zlo)+tail)) :
    omega ≤ 1-(2*K+(dm/beta)*exp (-vote))/ew-
      (full*L/(dm*z)+exp (-vote))/(1/8) := by
  have hh : (2*K+(dm/beta)*exp (-vote))/ew ≤ (2*K+(dm/beta)*tail)/ew := div_le_div_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (div_pos hdm hb).le)) hew.le
  have hzterm : full*L/(dm*z) ≤ full*L/(dm*zlo) := by
    exact div_le_div_of_nonneg_left (mul_nonneg hf hL) (mul_pos hdm hzlo)
      (mul_le_mul_of_nonneg_left hz hdm.le)
  have ht := add_le_add hzterm hv
  linarith only [hw,hh,ht]

theorem full_majority_correction_transfer {lower delta full : ℝ}
    (hl : 2 < lower) (hd : lower ≤ delta)
    (hf : (9/8)*majorityCorrection lower ≤ full) :
    majorityCorrection delta*(9/8) ≤ full := by
  have hh := mul_le_mul_of_nonneg_left (majority_correction_antitone hl hd)
    (by norm_num : (0:ℝ) ≤ 9/8)
  simpa only [mul_comm] using hh.trans hf

end
end Cycle12
