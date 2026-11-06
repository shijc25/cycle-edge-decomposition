import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs053

def inputs1060 : RatMajorityInputs := ⟨(12803022096375079303027/312500000000000000),(744366683/156250000),(250018307267395363/250000000000000000),(18249179596109409/125000000000000000),(744366683/312500000),(5773007476406769/62500000000000000),26⟩
theorem inputs_valid1060 : inputs1060.Valid := by decide +kernel
def envelope1060 : RatMajorityEnvelope := ⟨491,2,inputs1060,1,(542091886134429767/1000000000000000000)⟩
theorem envelope_sound1060 : envelope1060.Sound := by
  apply rat_majority_inputs_envelopes inputs1060 inputs_valid1060
  · norm_num [envelope1060]
  · intro rho hr0 hr1
    have hh := Batch053.bound2120 rho hr0 hr1
    norm_num [Batch053.certificate2120,envelope1060,inputs1060,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch053.bound2121 rho hr0 hr1
    norm_num [Batch053.certificate2121,envelope1060,inputs1060,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1061 : RatMajorityInputs := ⟨(805477061973135470725617/20000000000000000000),(11494195967/2500000000),(1000074494332884877/1000000000000000000),(32577152858361863/200000000000000000),(11494195967/5000000000),(50187646212220149/500000000000000000),25⟩
theorem inputs_valid1061 : inputs1061.Valid := by decide +kernel
def envelope1061 : RatMajorityEnvelope := ⟨492,0,inputs1061,(728524479/587500000),(378205042645124763/500000000000000000)⟩
theorem envelope_sound1061 : envelope1061.Sound := by
  apply rat_majority_inputs_envelopes inputs1061 inputs_valid1061
  · norm_num [envelope1061]
  · intro rho hr0 hr1
    have hh := Batch053.bound2122 rho hr0 hr1
    norm_num [Batch053.certificate2122,envelope1061,inputs1061,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch053.bound2123 rho hr0 hr1
    norm_num [Batch053.certificate2123,envelope1061,inputs1061,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1062 : RatMajorityInputs := ⟨(805477061973135470725617/20000000000000000000),(1987008049/500000000),(1000074494332884877/1000000000000000000),(24193538497204179/100000000000000000),(1987008049/1000000000),(137105023904087287/1000000000000000000),24⟩
theorem inputs_valid1062 : inputs1062.Valid := by decide +kernel
def envelope1062 : RatMajorityEnvelope := ⟨492,1,inputs1062,1,(554402853441509513/1000000000000000000)⟩
theorem envelope_sound1062 : envelope1062.Sound := by
  apply rat_majority_inputs_envelopes inputs1062 inputs_valid1062
  · norm_num [envelope1062]
  · intro rho hr0 hr1
    have hh := Batch053.bound2124 rho hr0 hr1
    norm_num [Batch053.certificate2124,envelope1062,inputs1062,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch053.bound2125 rho hr0 hr1
    norm_num [Batch053.certificate2125,envelope1062,inputs1062,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1063 : RatMajorityInputs := ⟨(805477061973135470725617/20000000000000000000),(47850083689/10000000000),(1000074494332884877/1000000000000000000),(35991688499093667/250000000000000000),(47850083689/20000000000),(18280102662085037/200000000000000000),26⟩
theorem inputs_valid1063 : inputs1063.Valid := by decide +kernel
def envelope1063 : RatMajorityEnvelope := ⟨492,2,inputs1063,1,(270931736225729173/500000000000000000)⟩
theorem envelope_sound1063 : envelope1063.Sound := by
  apply rat_majority_inputs_envelopes inputs1063 inputs_valid1063
  · norm_num [envelope1063]
  · intro rho hr0 hr1
    have hh := Batch053.bound2126 rho hr0 hr1
    norm_num [Batch053.certificate2126,envelope1063,inputs1063,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch053.bound2127 rho hr0 hr1
    norm_num [Batch053.certificate2127,envelope1063,inputs1063,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1064 : RatMajorityInputs := ⟨(99033108655048168165207/2500000000000000000),(92428114093/20000000000),(200015147341928797/200000000000000000),(80187985814390993/500000000000000000),(92428114093/40000000000),(24797877517514909/250000000000000000),26⟩
theorem inputs_valid1064 : inputs1064.Valid := by decide +kernel
def envelope1064 : RatMajorityEnvelope := ⟨493,0,inputs1064,(145793151/117500000),(18922542911236537/25000000000000000)⟩
theorem envelope_sound1064 : envelope1064.Sound := by
  apply rat_majority_inputs_envelopes inputs1064 inputs_valid1064
  · norm_num [envelope1064]
  · intro rho hr0 hr1
    have hh := Batch053.bound2128 rho hr0 hr1
    norm_num [Batch053.certificate2128,envelope1064,inputs1064,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch053.bound2129 rho hr0 hr1
    norm_num [Batch053.certificate2129,envelope1064,inputs1064,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1065 : RatMajorityInputs := ⟨(99033108655048168165207/2500000000000000000),(4852886911/1250000000),(200015147341928797/200000000000000000),(255860119197146639/1000000000000000000),(4852886911/2500000000),(5741524053948827/40000000000000000),24⟩
theorem inputs_valid1065 : inputs1065.Valid := by decide +kernel
def envelope1065 : RatMajorityEnvelope := ⟨493,1,inputs1065,1,(139114934993200877/250000000000000000)⟩
theorem envelope_sound1065 : envelope1065.Sound := by
  apply rat_majority_inputs_envelopes inputs1065 inputs_valid1065
  · norm_num [envelope1065]
  · intro rho hr0 hr1
    have hh := Batch053.bound2130 rho hr0 hr1
    norm_num [Batch053.certificate2130,envelope1065,inputs1065,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch053.bound2131 rho hr0 hr1
    norm_num [Batch053.certificate2131,envelope1065,inputs1065,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1066 : RatMajorityInputs := ⟨(99033108655048168165207/2500000000000000000),(24032001131/5000000000),(200015147341928797/200000000000000000),(14193356630729821/100000000000000000),(24032001131/10000000000),(90428109592342569/1000000000000000000),27⟩
theorem inputs_valid1066 : inputs1066.Valid := by decide +kernel
def envelope1066 : RatMajorityEnvelope := ⟨493,2,inputs1066,1,(541635478721362307/1000000000000000000)⟩
theorem envelope_sound1066 : envelope1066.Sound := by
  apply rat_majority_inputs_envelopes inputs1066 inputs_valid1066
  · norm_num [envelope1066]
  · intro rho hr0 hr1
    have hh := Batch053.bound2132 rho hr0 hr1
    norm_num [Batch053.certificate2132,envelope1066,inputs1066,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch053.bound2133 rho hr0 hr1
    norm_num [Batch053.certificate2133,envelope1066,inputs1066,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope1060,envelope1061,envelope1062,envelope1063,envelope1064,envelope1065,envelope1066]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound1060
  · exact envelope_sound1061
  · exact envelope_sound1062
  · exact envelope_sound1063
  · exact envelope_sound1064
  · exact envelope_sound1065
  · exact envelope_sound1066

end Cycle12.MajorityCertificates.Inputs053
