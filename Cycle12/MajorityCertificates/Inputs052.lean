import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch052

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs052

def inputs1040 : RatMajorityInputs := ⟨(920051169843907108801951/20000000000000000000),(91929531607/20000000000),(500032608536034437/500000000000000000),(6520551430410119/40000000000000000),(91929531607/40000000000),(50217813193494663/500000000000000000),25⟩
theorem inputs_valid1040 : inputs1040.Valid := by decide +kernel
def envelope1040 : RatMajorityEnvelope := ⟨485,0,inputs1040,(718486179/587500000),(740753409564183597/1000000000000000000)⟩
theorem envelope_sound1040 : envelope1040.Sound := by
  apply rat_majority_inputs_envelopes inputs1040 inputs_valid1040
  · norm_num [envelope1040]
  · intro rho hr0 hr1
    have hh := Batch052.bound2080 rho hr0 hr1
    norm_num [Batch052.certificate2080,envelope1040,inputs1040,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2081 rho hr0 hr1
    norm_num [Batch052.certificate2081,envelope1040,inputs1040,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1041 : RatMajorityInputs := ⟨(920051169843907108801951/20000000000000000000),(40521702031/10000000000),(500032608536034437/500000000000000000),(230558322212976323/1000000000000000000),(40521702031/20000000000),(65925347071833669/500000000000000000),24⟩
theorem inputs_valid1041 : inputs1041.Valid := by decide +kernel
def envelope1041 : RatMajorityEnvelope := ⟨485,1,inputs1041,1,(276387233521628491/500000000000000000)⟩
theorem envelope_sound1041 : envelope1041.Sound := by
  apply rat_majority_inputs_envelopes inputs1041 inputs_valid1041
  · norm_num [envelope1041]
  · intro rho hr0 hr1
    have hh := Batch052.bound2082 rho hr0 hr1
    norm_num [Batch052.certificate2082,envelope1041,inputs1041,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2083 rho hr0 hr1
    norm_num [Batch052.certificate2083,envelope1041,inputs1041,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1042 : RatMajorityInputs := ⟨(920051169843907108801951/20000000000000000000),(23233289429/5000000000),(500032608536034437/500000000000000000),(3943543321843629/25000000000000000),(23233289429/10000000000),(97946982372675211/1000000000000000000),26⟩
theorem inputs_valid1042 : inputs1042.Valid := by decide +kernel
def envelope1042 : RatMajorityEnvelope := ⟨485,2,inputs1042,1,(271719433573326303/500000000000000000)⟩
theorem envelope_sound1042 : envelope1042.Sound := by
  apply rat_majority_inputs_envelopes inputs1042 inputs_valid1042
  · norm_num [envelope1042]
  · intro rho hr0 hr1
    have hh := Batch052.bound2084 rho hr0 hr1
    norm_num [Batch052.certificate2084,envelope1042,inputs1042,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2085 rho hr0 hr1
    norm_num [Batch052.certificate2085,envelope1042,inputs1042,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1043 : RatMajorityInputs := ⟨(900989104209643026835751/20000000000000000000),(23149433533/5000000000),(50003329846474459/50000000000000000),(159487037320999963/1000000000000000000),(23149433533/10000000000),(98771778938992703/1000000000000000000),26⟩
theorem inputs_valid1043 : inputs1043.Valid := by decide +kernel
def envelope1043 : RatMajorityEnvelope := ⟨486,0,inputs1043,(2866425781/2350000000),(737537586632587207/1000000000000000000)⟩
theorem envelope_sound1043 : envelope1043.Sound := by
  apply rat_majority_inputs_envelopes inputs1043 inputs_valid1043
  · norm_num [envelope1043]
  · intro rho hr0 hr1
    have hh := Batch052.bound2086 rho hr0 hr1
    norm_num [Batch052.certificate2086,envelope1043,inputs1043,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2087 rho hr0 hr1
    norm_num [Batch052.certificate2087,envelope1043,inputs1043,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1044 : RatMajorityInputs := ⟨(900989104209643026835751/20000000000000000000),(1266947839/312500000),(50003329846474459/50000000000000000),(230264044311637787/1000000000000000000),(1266947839/625000000),(131714768063533161/1000000000000000000),25⟩
theorem inputs_valid1044 : inputs1044.Valid := by decide +kernel
def envelope1044 : RatMajorityEnvelope := ⟨486,1,inputs1044,1,(138183409460672139/250000000000000000)⟩
theorem envelope_sound1044 : envelope1044.Sound := by
  apply rat_majority_inputs_envelopes inputs1044 inputs_valid1044
  · norm_num [envelope1044]
  · intro rho hr0 hr1
    have hh := Batch052.bound2088 rho hr0 hr1
    norm_num [Batch052.certificate2088,envelope1044,inputs1044,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2089 rho hr0 hr1
    norm_num [Batch052.certificate2089,envelope1044,inputs1044,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1045 : RatMajorityInputs := ⟨(900989104209643026835751/20000000000000000000),(46659132359/10000000000),(50003329846474459/50000000000000000),(38939591475554559/250000000000000000),(46659132359/20000000000),(97008505578179013/1000000000000000000),26⟩
theorem inputs_valid1045 : inputs1045.Valid := by decide +kernel
def envelope1045 : RatMajorityEnvelope := ⟨486,2,inputs1045,1,(271604334164752961/500000000000000000)⟩
theorem envelope_sound1045 : envelope1045.Sound := by
  apply rat_majority_inputs_envelopes inputs1045 inputs_valid1045
  · norm_num [envelope1045]
  · intro rho hr0 hr1
    have hh := Batch052.bound2090 rho hr0 hr1
    norm_num [Batch052.certificate2090,envelope1045,inputs1045,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2091 rho hr0 hr1
    norm_num [Batch052.certificate2091,envelope1045,inputs1045,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1046 : RatMajorityInputs := ⟨(882912744802801707040843/20000000000000000000),(91249510979/20000000000),(1000067960477214149/1000000000000000000),(83335949476821393/500000000000000000),(91249510979/40000000000),(102157680257033837/1000000000000000000),25⟩
theorem inputs_valid1046 : inputs1046.Valid := by decide +kernel
def envelope1046 : RatMajorityEnvelope := ⟨487,0,inputs1046,(2901765303/2350000000),(187973965410387853/250000000000000000)⟩
theorem envelope_sound1046 : envelope1046.Sound := by
  apply rat_majority_inputs_envelopes inputs1046 inputs_valid1046
  · norm_num [envelope1046]
  · intro rho hr0 hr1
    have hh := Batch052.bound2092 rho hr0 hr1
    norm_num [Batch052.certificate2092,envelope1046,inputs1046,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2093 rho hr0 hr1
    norm_num [Batch052.certificate2093,envelope1046,inputs1046,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1047 : RatMajorityInputs := ⟨(882912744802801707040843/20000000000000000000),(80673983733/20000000000),(1000067960477214149/1000000000000000000),(116603505229445543/500000000000000000),(80673983733/40000000000),(66537021370756937/500000000000000000),25⟩
theorem inputs_valid1047 : inputs1047.Valid := by decide +kernel
def envelope1047 : RatMajorityEnvelope := ⟨487,1,inputs1047,1,(553149470068864423/1000000000000000000)⟩
theorem envelope_sound1047 : envelope1047.Sound := by
  apply rat_majority_inputs_envelopes inputs1047 inputs_valid1047
  · norm_num [envelope1047]
  · intro rho hr0 hr1
    have hh := Batch052.bound2094 rho hr0 hr1
    norm_num [Batch052.certificate2094,envelope1047,inputs1047,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2095 rho hr0 hr1
    norm_num [Batch052.certificate2095,envelope1047,inputs1047,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1048 : RatMajorityInputs := ⟨(882912744802801707040843/20000000000000000000),(18750448887/4000000000),(1000067960477214149/1000000000000000000),(153549293853609923/1000000000000000000),(18750448887/8000000000),(95961701398899297/1000000000000000000),26⟩
theorem inputs_valid1048 : inputs1048.Valid := by decide +kernel
def envelope1048 : RatMajorityEnvelope := ⟨487,2,inputs1048,1,(542953550726642647/1000000000000000000)⟩
theorem envelope_sound1048 : envelope1048.Sound := by
  apply rat_majority_inputs_envelopes inputs1048 inputs_valid1048
  · norm_num [envelope1048]
  · intro rho hr0 hr1
    have hh := Batch052.bound2096 rho hr0 hr1
    norm_num [Batch052.certificate2096,envelope1048,inputs1048,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2097 rho hr0 hr1
    norm_num [Batch052.certificate2097,envelope1048,inputs1048,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1049 : RatMajorityInputs := ⟨(432882674453570922630479/10000000000000000000),(45717935739/10000000000),(250017326644675869/250000000000000000),(165662412499411661/1000000000000000000),(45717935739/20000000000),(12710354171002919/125000000000000000),25⟩
theorem inputs_valid1049 : inputs1049.Valid := by decide +kernel
def envelope1049 : RatMajorityEnvelope := ⟨488,0,inputs1049,(1452058739/1175000000),(94091515247740323/125000000000000000)⟩
theorem envelope_sound1049 : envelope1049.Sound := by
  apply rat_majority_inputs_envelopes inputs1049 inputs_valid1049
  · norm_num [envelope1049]
  · intro rho hr0 hr1
    have hh := Batch052.bound2098 rho hr0 hr1
    norm_num [Batch052.certificate2098,envelope1049,inputs1049,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2099 rho hr0 hr1
    norm_num [Batch052.certificate2099,envelope1049,inputs1049,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1050 : RatMajorityInputs := ⟨(432882674453570922630479/10000000000000000000),(20123215957/5000000000),(250017326644675869/250000000000000000),(117257329463804417/500000000000000000),(20123215957/10000000000),(26735593589019223/200000000000000000),24⟩
theorem inputs_valid1050 : inputs1050.Valid := by decide +kernel
def envelope1050 : RatMajorityEnvelope := ⟨488,1,inputs1050,1,(110667113109517851/200000000000000000)⟩
theorem envelope_sound1050 : envelope1050.Sound := by
  apply rat_majority_inputs_envelopes inputs1050 inputs_valid1050
  · norm_num [envelope1050]
  · intro rho hr0 hr1
    have hh := Batch052.bound2100 rho hr0 hr1
    norm_num [Batch052.certificate2100,envelope1050,inputs1050,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2101 rho hr0 hr1
    norm_num [Batch052.certificate2101,envelope1050,inputs1050,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1051 : RatMajorityInputs := ⟨(432882674453570922630479/10000000000000000000),(94165218489/20000000000),(250017326644675869/250000000000000000),(75736255739937403/500000000000000000),(94165218489/40000000000),(23744013976963767/250000000000000000),26⟩
theorem inputs_valid1051 : inputs1051.Valid := by decide +kernel
def envelope1051 : RatMajorityEnvelope := ⟨488,2,inputs1051,1,(542715032704142183/1000000000000000000)⟩
theorem envelope_sound1051 : envelope1051.Sound := by
  apply rat_majority_inputs_envelopes inputs1051 inputs_valid1051
  · norm_num [envelope1051]
  · intro rho hr0 hr1
    have hh := Batch052.bound2102 rho hr0 hr1
    norm_num [Batch052.certificate2102,envelope1051,inputs1051,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2103 rho hr0 hr1
    norm_num [Batch052.certificate2103,envelope1051,inputs1051,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1052 : RatMajorityInputs := ⟨(849494589278618971887583/20000000000000000000),(18325120977/4000000000),(1000070634112331131/1000000000000000000),(82320038563733781/500000000000000000),(18325120977/8000000000),(25300414923497793/250000000000000000),25⟩
theorem inputs_valid1052 : inputs1052.Valid := by decide +kernel
def envelope1052 : RatMajorityEnvelope := ⟨489,0,inputs1052,(363308693/293750000),(753568181897019577/1000000000000000000)⟩
theorem envelope_sound1052 : envelope1052.Sound := by
  apply rat_majority_inputs_envelopes inputs1052 inputs_valid1052
  · norm_num [envelope1052]
  · intro rho hr0 hr1
    have hh := Batch052.bound2104 rho hr0 hr1
    norm_num [Batch052.certificate2104,envelope1052,inputs1052,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2105 rho hr0 hr1
    norm_num [Batch052.certificate2105,envelope1052,inputs1052,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1053 : RatMajorityInputs := ⟨(849494589278618971887583/20000000000000000000),(78781068979/20000000000),(1000070634112331131/1000000000000000000),(9886810088723357/40000000000000000),(78781068979/40000000000),(2180044896137601/15625000000000000),24⟩
theorem inputs_valid1053 : inputs1053.Valid := by decide +kernel
def envelope1053 : RatMajorityEnvelope := ⟨489,1,inputs1053,1,(69395687189971451/125000000000000000)⟩
theorem envelope_sound1053 : envelope1053.Sound := by
  apply rat_majority_inputs_envelopes inputs1053 inputs_valid1053
  · norm_num [envelope1053]
  · intro rho hr0 hr1
    have hh := Batch052.bound2106 rho hr0 hr1
    norm_num [Batch052.certificate2106,envelope1053,inputs1053,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2107 rho hr0 hr1
    norm_num [Batch052.certificate2107,envelope1053,inputs1053,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1054 : RatMajorityInputs := ⟨(849494589278618971887583/20000000000000000000),(2364505281/500000000),(1000070634112331131/1000000000000000000),(29882055587409499/200000000000000000),(2364505281/1000000000),(18799158074240767/200000000000000000),26⟩
theorem inputs_valid1054 : inputs1054.Valid := by decide +kernel
def envelope1054 : RatMajorityEnvelope := ⟨489,2,inputs1054,1,(542479414035274693/1000000000000000000)⟩
theorem envelope_sound1054 : envelope1054.Sound := by
  apply rat_majority_inputs_envelopes inputs1054 inputs_valid1054
  · norm_num [envelope1054]
  · intro rho hr0 hr1
    have hh := Batch052.bound2108 rho hr0 hr1
    norm_num [Batch052.certificate2108,envelope1054,inputs1054,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2109 rho hr0 hr1
    norm_num [Batch052.certificate2109,envelope1054,inputs1054,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1055 : RatMajorityInputs := ⟨(208513039602109761610251/5000000000000000000),(91892724403/20000000000),(500035970986149839/500000000000000000),(32641999434682951/200000000000000000),(91892724403/40000000000),(100528087785767091/1000000000000000000),25⟩
theorem inputs_valid1055 : inputs1055.Valid := by decide +kernel
def envelope1055 : RatMajorityEnvelope := ⟨490,0,inputs1055,(2908665087/2350000000),(754311185387832931/1000000000000000000)⟩
theorem envelope_sound1055 : envelope1055.Sound := by
  apply rat_majority_inputs_envelopes inputs1055 inputs_valid1055
  · norm_num [envelope1055]
  · intro rho hr0 hr1
    have hh := Batch052.bound2110 rho hr0 hr1
    norm_num [Batch052.certificate2110,envelope1055,inputs1055,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2111 rho hr0 hr1
    norm_num [Batch052.certificate2111,envelope1055,inputs1055,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1056 : RatMajorityInputs := ⟨(208513039602109761610251/5000000000000000000),(80257461649/20000000000),(500035970986149839/500000000000000000),(4724462791647421/20000000000000000),(80257461649/40000000000),(33616747377191189/250000000000000000),25⟩
theorem inputs_valid1056 : inputs1056.Valid := by decide +kernel
def envelope1056 : RatMajorityEnvelope := ⟨490,1,inputs1056,1,(138395004018506783/250000000000000000)⟩
theorem envelope_sound1056 : envelope1056.Sound := by
  apply rat_majority_inputs_envelopes inputs1056 inputs_valid1056
  · norm_num [envelope1056]
  · intro rho hr0 hr1
    have hh := Batch052.bound2112 rho hr0 hr1
    norm_num [Batch052.certificate2112,envelope1056,inputs1056,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2113 rho hr0 hr1
    norm_num [Batch052.certificate2113,envelope1056,inputs1056,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1057 : RatMajorityInputs := ⟨(208513039602109761610251/5000000000000000000),(94997113601/20000000000),(500035970986149839/500000000000000000),(29472654084644381/200000000000000000),(94997113601/40000000000),(93021201376051497/1000000000000000000),26⟩
theorem inputs_valid1057 : inputs1057.Valid := by decide +kernel
def envelope1057 : RatMajorityEnvelope := ⟨490,2,inputs1057,1,(33890421103119571/62500000000000000)⟩
theorem envelope_sound1057 : envelope1057.Sound := by
  apply rat_majority_inputs_envelopes inputs1057 inputs_valid1057
  · norm_num [envelope1057]
  · intro rho hr0 hr1
    have hh := Batch052.bound2114 rho hr0 hr1
    norm_num [Batch052.certificate2114,envelope1057,inputs1057,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2115 rho hr0 hr1
    norm_num [Batch052.certificate2115,envelope1057,inputs1057,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1058 : RatMajorityInputs := ⟨(12803022096375079303027/312500000000000000),(91872057469/20000000000),(250018307267395363/250000000000000000),(163320257654068289/1000000000000000000),(91872057469/40000000000),(25145010347504519/250000000000000000),27⟩
theorem inputs_valid1058 : inputs1058.Valid := by decide +kernel
def envelope1058 : RatMajorityEnvelope := ⟨491,0,inputs1058,(90982861/73437500),(188852413399840623/250000000000000000)⟩
theorem envelope_sound1058 : envelope1058.Sound := by
  apply rat_majority_inputs_envelopes inputs1058 inputs_valid1058
  · norm_num [envelope1058]
  · intro rho hr0 hr1
    have hh := Batch052.bound2116 rho hr0 hr1
    norm_num [Batch052.certificate2116,envelope1058,inputs1058,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2117 rho hr0 hr1
    norm_num [Batch052.certificate2117,envelope1058,inputs1058,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1059 : RatMajorityInputs := ⟨(12803022096375079303027/312500000000000000),(8018746939/2000000000),(250018307267395363/250000000000000000),(47346614573689007/200000000000000000),(8018746939/4000000000),(134702486694843923/1000000000000000000),25⟩
theorem inputs_valid1059 : inputs1059.Valid := by decide +kernel
def envelope1059 : RatMajorityEnvelope := ⟨491,1,inputs1059,1,(55365338819621439/100000000000000000)⟩
theorem envelope_sound1059 : envelope1059.Sound := by
  apply rat_majority_inputs_envelopes inputs1059 inputs_valid1059
  · norm_num [envelope1059]
  · intro rho hr0 hr1
    have hh := Batch052.bound2118 rho hr0 hr1
    norm_num [Batch052.certificate2118,envelope1059,inputs1059,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch052.bound2119 rho hr0 hr1
    norm_num [Batch052.certificate2119,envelope1059,inputs1059,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope1040,envelope1041,envelope1042,envelope1043,envelope1044,envelope1045,envelope1046,envelope1047,envelope1048,envelope1049,envelope1050,envelope1051,envelope1052,envelope1053,envelope1054,envelope1055,envelope1056,envelope1057,envelope1058,envelope1059]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound1040
  · exact envelope_sound1041
  · exact envelope_sound1042
  · exact envelope_sound1043
  · exact envelope_sound1044
  · exact envelope_sound1045
  · exact envelope_sound1046
  · exact envelope_sound1047
  · exact envelope_sound1048
  · exact envelope_sound1049
  · exact envelope_sound1050
  · exact envelope_sound1051
  · exact envelope_sound1052
  · exact envelope_sound1053
  · exact envelope_sound1054
  · exact envelope_sound1055
  · exact envelope_sound1056
  · exact envelope_sound1057
  · exact envelope_sound1058
  · exact envelope_sound1059

end Cycle12.MajorityCertificates.Inputs052
