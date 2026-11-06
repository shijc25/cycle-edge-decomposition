import Cycle12.CoverBankScales

namespace Cycle12
open Real
noncomputable section

def coverBankEdges (ac x s P : ℝ) : ℝ := 2*ac*s*(coverRoutingQ x s P)^2
def coverBankDegreeRatio (dm x : ℝ) : ℝ := dm*coverScaleW x*coverScaleH x/coverScaleDen x

theorem cover_bank_edges_pos {ac x s P : ℝ} (ha : 0 < ac) (hx : 0 < x) (hs : 0 < s) (hP : 0 < P) :
    0 < coverBankEdges ac x s P := by
  unfold coverBankEdges
  positivity [cover_routing_q_pos hx hs hP]

theorem cover_bank_average {ac x s P : ℝ} (hx : 0 < x) (hs : 0 < s) (hP : 0 < P) :
    coverBankEdges ac x s P/coverRoutingOrder x s P=ac*coverRoutingQ x s P := by
  have hQ := (cover_routing_q_pos hx hs hP).ne'
  rw [cover_routing_order_identity]
  unfold coverBankEdges
  field_simp
  <;> ring

theorem cover_bank_size_ratio {a x s P : ℝ} (ha : 0 < a) (hx : 0 < x) (hs : 0 < s) (hP : 0 < P) :
    coverRoutingOrder x s P/(a*coverRoutingQ x s P)=2*s/a := by
  have hQ := (cover_routing_q_pos hx hs hP).ne'
  rw [cover_routing_order_identity]
  field_simp

theorem cover_bank_dense_identity {ac gain x s P : ℝ} (hs : 0 < s) :
    (ac*gain*coverRoutingQ x s P)*coverRoutingOrder x s P-(ac*gain*coverRoutingQ x s P)^2/2=
      (gain-gain^2*ac/(4*s))*coverBankEdges ac x s P := by
  rw [cover_routing_order_identity]
  unfold coverBankEdges
  field_simp
  <;> ring

theorem cover_bank_dense_gain_mono {ac gain s sh : ℝ} (ha : 0 ≤ ac) (hs : 0 < s) (hss : s ≤ sh) :
    gain-gain^2*ac/(4*s) ≤ gain-gain^2*ac/(4*sh) := by
  have hh := div_le_div_of_nonneg_left (show 0 ≤ gain^2*ac by positivity)
    (show 0 < 4*s by positivity) (mul_le_mul_of_nonneg_left hss (by norm_num : (0:ℝ) ≤ 4))
  linarith only [hh]

theorem cover_bank_dense {ac gain x s P : ℝ} (ha : 0 < ac) (hx : 0 < x) (hs : 0 < s) (hP : 0 < P)
    (hg : gain-gain^2*ac/(4*s) ≤ 1) :
    (ac*gain*coverRoutingQ x s P)*coverRoutingOrder x s P-(ac*gain*coverRoutingQ x s P)^2/2 ≤
      coverBankEdges ac x s P := by
  rw [cover_bank_dense_identity hs]
  exact mul_le_of_le_one_left (cover_bank_edges_pos ha hx hs hP).le hg

theorem cover_bank_degree_le_order {ac gain x s0 s P : ℝ}
    (hx : 0 < x) (hs0 : 0 < s0) (hss : s0 ≤ s) (hP : 0 < P)
    (hdegree : ac*gain/(2*s0) ≤ 1) :
    ac*gain*coverRoutingQ x s P ≤ coverRoutingOrder x s P := by
  have hs := hs0.trans_le hss
  have hh := (div_le_one (show 0 < 2*s0 by positivity)).mp hdegree
  have hm : ac*gain ≤ 2*s := by linarith only [hh,hss]
  rw [cover_routing_order_identity]
  exact mul_le_mul_of_nonneg_right hm (cover_routing_q_pos hx hs hP).le

theorem cover_bank_strong_stopping {ac a x s sh P : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hs : 0 < s) (hP : 0 < P) (hss : s ≤ sh)
    (hstop : a*(1+log (2*sh/a)) ≤ 2*ac) :
    (a*coverRoutingQ x s P)*(1+log (coverRoutingOrder x s P/(a*coverRoutingQ x s P))) ≤
      2*coverBankEdges ac x s P/coverRoutingOrder x s P := by
  have hlog := log_le_log (show 0 < 2*s/a by positivity)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hss (by norm_num : (0:ℝ) ≤ 2)) ha.le)
  have hh : a*(1+log (2*s/a)) ≤ 2*ac := by nlinarith only [hlog,hstop,ha]
  have hbound := mul_le_mul_of_nonneg_right hh (cover_routing_q_pos hx hs hP).le
  have he : 2*coverBankEdges ac x s P/coverRoutingOrder x s P=2*ac*coverRoutingQ x s P := by
    rw [mul_div_assoc,cover_bank_average hx hs hP]
    ring
  rw [cover_bank_size_ratio ha hx hs hP,he]
  nlinarith only [hbound]

theorem cover_bank_degree_ratio_mono {dm lo x : ℝ} (hdm : 0 ≤ dm) (hlo : 0 ≤ lo)
    (hlx : lo ≤ x) (hxmax : x ≤ 17/250) : coverBankDegreeRatio dm lo ≤ coverBankDegreeRatio dm x := by
  have hHx := cover_h_pos (hlo.trans hlx)
  have hHl := cover_h_pos hlo
  have hden := cover_den_pos (hlo.trans hlx) hxmax
  have hw := cover_w_nonneg x
  have hnum : dm*coverScaleW lo*coverScaleH lo ≤ dm*coverScaleW x*coverScaleH x :=
    mul_le_mul (mul_le_mul_of_nonneg_left (cover_w_mono hlo hlx) hdm)
      (cover_h_mono hlx) hHl.le (mul_nonneg hdm (cover_w_nonneg x))
  unfold coverBankDegreeRatio
  exact (div_le_div_of_nonneg_right hnum (cover_den_pos hlo (hlx.trans hxmax)).le).trans
    (div_le_div_of_nonneg_left (by positivity) hden (cover_den_antitone hlo hlx))

theorem cover_bank_degree_ratio_mul {dm x s P : ℝ} (hx : 0 < x) (hxmax : x ≤ 17/250) :
    coverBankDegreeRatio dm x*coverRoutingQ x s P=dm*coverScaleZ x s P := by
  have hw := (cover_w_pos hx).ne'
  have hd := (cover_den_pos hx.le hxmax).ne'
  unfold coverBankDegreeRatio coverRoutingQ coverScaleZ
  field_simp
  <;> ring

theorem cover_bank_branch_lower {dc a cost g dm lo x s P : ℝ}
    (hdm : 0 ≤ dm) (hlo : 0 ≤ lo) (hx : 0 < x) (hlx : lo ≤ x)
    (hxmax : x ≤ 17/250) (hs : 0 < s) (hP : 0 < P) :
    (max (dc/(1-g)) (coverBankDegreeRatio dm lo)-cost*a)*coverRoutingQ x s P ≤
      max ((dc*coverRoutingQ x s P)/(1-g)) (dm*coverScaleZ x s P)-cost*(a*coverRoutingQ x s P) := by
  have hQ := (cover_routing_q_pos hx hs hP).le
  have hmax := max_le_max_left (dc/(1-g)) (cover_bank_degree_ratio_mono hdm hlo hlx hxmax)
  have hh := mul_le_mul_of_nonneg_right hmax hQ
  have he : max (dc/(1-g)) (coverBankDegreeRatio dm x)*coverRoutingQ x s P=
      max ((dc*coverRoutingQ x s P)/(1-g)) (dm*coverScaleZ x s P) := by
    rw [max_mul_of_nonneg _ _ hQ,cover_bank_degree_ratio_mul hx hxmax]
    congr 1
    ring
  rw [he] at hh
  nlinarith only [hh]

end
end Cycle12
