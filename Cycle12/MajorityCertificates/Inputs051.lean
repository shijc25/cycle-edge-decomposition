import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs051

def inputs1020 : RatMajorityInputs := ⟨(1087010969629655165484447/20000000000000000000),(81620968497/20000000000),(1000055199604832851/1000000000000000000),(113233322147182879/500000000000000000),(81620968497/40000000000),(32490141518828367/250000000000000000),25⟩
theorem inputs_valid1020 : inputs1020.Valid := by decide +kernel
def envelope1020 : RatMajorityEnvelope := ⟨478,1,inputs1020,1,(276098957335667393/500000000000000000)⟩
theorem envelope_sound1020 : envelope1020.Sound := by
  apply rat_majority_inputs_envelopes inputs1020 inputs_valid1020
  · norm_num [envelope1020]
  · intro rho hr0 hr1
    have hh := Batch051.bound2040 rho hr0 hr1
    norm_num [Batch051.certificate2040,envelope1020,inputs1020,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2041 rho hr0 hr1
    norm_num [Batch051.certificate2041,envelope1020,inputs1020,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1021 : RatMajorityInputs := ⟨(1087010969629655165484447/20000000000000000000),(90132793/20000000),(1000055199604832851/1000000000000000000),(10802039292554253/62500000000000000),(90132793/40000000),(26262474438488179/250000000000000000),26⟩
theorem inputs_valid1021 : inputs1021.Valid := by decide +kernel
def envelope1021 : RatMajorityEnvelope := ⟨478,2,inputs1021,1,(545229031101170699/1000000000000000000)⟩
theorem envelope_sound1021 : envelope1021.Sound := by
  apply rat_majority_inputs_envelopes inputs1021 inputs_valid1021
  · norm_num [envelope1021]
  · intro rho hr0 hr1
    have hh := Batch051.bound2042 rho hr0 hr1
    norm_num [Batch051.certificate2042,envelope1021,inputs1021,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2043 rho hr0 hr1
    norm_num [Batch051.certificate2043,envelope1021,inputs1021,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1022 : RatMajorityInputs := ⟨(264745271926731373011313/5000000000000000000),(90828724021/20000000000),(1000056660732523499/1000000000000000000),(168970749789879023/1000000000000000000),(90828724021/40000000000),(51619009091690053/500000000000000000),26⟩
theorem inputs_valid1022 : inputs1022.Valid := by decide +kernel
def envelope1022 : RatMajorityEnvelope := ⟨479,0,inputs1022,(2288091/1880000),(735875482742043257/1000000000000000000)⟩
theorem envelope_sound1022 : envelope1022.Sound := by
  apply rat_majority_inputs_envelopes inputs1022 inputs_valid1022
  · norm_num [envelope1022]
  · intro rho hr0 hr1
    have hh := Batch051.bound2044 rho hr0 hr1
    norm_num [Batch051.certificate2044,envelope1022,inputs1022,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2045 rho hr0 hr1
    norm_num [Batch051.certificate2045,envelope1022,inputs1022,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1023 : RatMajorityInputs := ⟨(264745271926731373011313/5000000000000000000),(81544206029/20000000000),(1000056660732523499/1000000000000000000),(113503500508439707/500000000000000000),(81544206029/40000000000),(65105103941289711/500000000000000000),25⟩
theorem inputs_valid1023 : inputs1023.Valid := by decide +kernel
def envelope1023 : RatMajorityEnvelope := ⟨479,1,inputs1023,1,(276136880931338173/500000000000000000)⟩
theorem envelope_sound1023 : envelope1023.Sound := by
  apply rat_majority_inputs_envelopes inputs1023 inputs_valid1023
  · norm_num [envelope1023]
  · intro rho hr0 hr1
    have hh := Batch051.bound2046 rho hr0 hr1
    norm_num [Batch051.certificate2046,envelope1023,inputs1023,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2047 rho hr0 hr1
    norm_num [Batch051.certificate2047,envelope1023,inputs1023,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1024 : RatMajorityInputs := ⟨(264745271926731373011313/5000000000000000000),(45263424589/10000000000),(1000056660732523499/1000000000000000000),(8531835865459271/50000000000000000),(45263424589/20000000000),(1625313899698941/15625000000000000),26⟩
theorem inputs_valid1024 : inputs1024.Valid := by decide +kernel
def envelope1024 : RatMajorityEnvelope := ⟨479,2,inputs1024,1,(13624106345986543/25000000000000000)⟩
theorem envelope_sound1024 : envelope1024.Sound := by
  apply rat_majority_inputs_envelopes inputs1024 inputs_valid1024
  · norm_num [envelope1024]
  · intro rho hr0 hr1
    have hh := Batch051.bound2048 rho hr0 hr1
    norm_num [Batch051.certificate2048,envelope1024,inputs1024,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2049 rho hr0 hr1
    norm_num [Batch051.certificate2049,envelope1024,inputs1024,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1025 : RatMajorityInputs := ⟨(103250272527869409126923/2000000000000000000),(91009825361/20000000000),(1000058113853359197/1000000000000000000),(41994507338072613/250000000000000000),(91009825361/40000000000),(102771661117836917/1000000000000000000),26⟩
theorem inputs_valid1025 : inputs1025.Valid := by decide +kernel
def envelope1025 : RatMajorityEnvelope := ⟨480,0,inputs1025,(114496289/94000000),(368340894508433853/500000000000000000)⟩
theorem envelope_sound1025 : envelope1025.Sound := by
  apply rat_majority_inputs_envelopes inputs1025 inputs_valid1025
  · norm_num [envelope1025]
  · intro rho hr0 hr1
    have hh := Batch051.bound2050 rho hr0 hr1
    norm_num [Batch051.certificate2050,envelope1025,inputs1025,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2051 rho hr0 hr1
    norm_num [Batch051.certificate2051,envelope1025,inputs1025,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1026 : RatMajorityInputs := ⟨(103250272527869409126923/2000000000000000000),(4073462317/1000000000),(1000058113853359197/1000000000000000000),(56883922011883229/250000000000000000),(4073462317/2000000000),(65227224790905709/500000000000000000),25⟩
theorem inputs_valid1026 : inputs1026.Valid := by decide +kernel
def envelope1026 : RatMajorityEnvelope := ⟨480,1,inputs1026,1,(110469616590953897/200000000000000000)⟩
theorem envelope_sound1026 : envelope1026.Sound := by
  apply rat_majority_inputs_envelopes inputs1026 inputs_valid1026
  · norm_num [envelope1026]
  · intro rho hr0 hr1
    have hh := Batch051.bound2052 rho hr0 hr1
    norm_num [Batch051.certificate2052,envelope1026,inputs1026,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2053 rho hr0 hr1
    norm_num [Batch051.certificate2053,envelope1026,inputs1026,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1027 : RatMajorityInputs := ⟨(103250272527869409126923/2000000000000000000),(90922865303/20000000000),(1000058113853359197/1000000000000000000),(21056759884196767/125000000000000000),(90922865303/40000000000),(102995329898158897/1000000000000000000),26⟩
theorem inputs_valid1027 : inputs1027.Valid := by decide +kernel
def envelope1027 : RatMajorityEnvelope := ⟨480,2,inputs1027,1,(136175635106000661/250000000000000000)⟩
theorem envelope_sound1027 : envelope1027.Sound := by
  apply rat_majority_inputs_envelopes inputs1027 inputs_valid1027
  · norm_num [envelope1027]
  · intro rho hr0 hr1
    have hh := Batch051.bound2054 rho hr0 hr1
    norm_num [Batch051.certificate2054,envelope1027,inputs1027,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2055 rho hr0 hr1
    norm_num [Batch051.certificate2055,envelope1027,inputs1027,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1028 : RatMajorityInputs := ⟨(503736120696108674121057/10000000000000000000),(45865719531/10000000000),(1000059557749470313/1000000000000000000),(164072182888396249/1000000000000000000),(45865719531/20000000000),(100934248756081017/1000000000000000000),26⟩
theorem inputs_valid1028 : inputs1028.Valid := by decide +kernel
def envelope1028 : RatMajorityEnvelope := ⟨481,0,inputs1028,(2854790141/2350000000),(733394602007579383/1000000000000000000)⟩
theorem envelope_sound1028 : envelope1028.Sound := by
  apply rat_majority_inputs_envelopes inputs1028 inputs_valid1028
  · norm_num [envelope1028]
  · intro rho hr0 hr1
    have hh := Batch051.bound2056 rho hr0 hr1
    norm_num [Batch051.certificate2056,envelope1028,inputs1028,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2057 rho hr0 hr1
    norm_num [Batch051.certificate2057,envelope1028,inputs1028,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1029 : RatMajorityInputs := ⟨(503736120696108674121057/10000000000000000000),(16268859603/4000000000),(1000059557749470313/1000000000000000000),(456838373948229/2000000000000000),(16268859603/8000000000),(130862588327200527/1000000000000000000),25⟩
theorem inputs_valid1029 : inputs1029.Valid := by decide +kernel
def envelope1029 : RatMajorityEnvelope := ⟨481,1,inputs1029,1,(69059014200840639/125000000000000000)⟩
theorem envelope_sound1029 : envelope1029.Sound := by
  apply rat_majority_inputs_envelopes inputs1029 inputs_valid1029
  · norm_num [envelope1029]
  · intro rho hr0 hr1
    have hh := Batch051.bound2058 rho hr0 hr1
    norm_num [Batch051.certificate2058,envelope1029,inputs1029,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2059 rho hr0 hr1
    norm_num [Batch051.certificate2059,envelope1029,inputs1029,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1030 : RatMajorityInputs := ⟨(503736120696108674121057/10000000000000000000),(18257000117/4000000000),(1000059557749470313/1000000000000000000),(166479249441171239/1000000000000000000),(18257000117/8000000000),(51033541029300861/500000000000000000),26⟩
theorem inputs_valid1030 : inputs1030.Valid := by decide +kernel
def envelope1030 : RatMajorityEnvelope := ⟨481,2,inputs1030,1,(136116762475769427/250000000000000000)⟩
theorem envelope_sound1030 : envelope1030.Sound := by
  apply rat_majority_inputs_envelopes inputs1030 inputs_valid1030
  · norm_num [envelope1030]
  · intro rho hr0 hr1
    have hh := Batch051.bound2060 rho hr0 hr1
    norm_num [Batch051.certificate2060,envelope1030,inputs1030,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2061 rho hr0 hr1
    norm_num [Batch051.certificate2061,envelope1030,inputs1030,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1031 : RatMajorityInputs := ⟨(491897471173195324508091/10000000000000000000),(91371809961/20000000000),(1000060991212358183/1000000000000000000),(166008827734885323/1000000000000000000),(91371809961/40000000000),(20369162551196659/200000000000000000),27⟩
theorem inputs_valid1031 : inputs1031.Valid := by decide +kernel
def envelope1031 : RatMajorityEnvelope := ⟨482,0,inputs1031,(573402831/470000000),(184576527645271549/250000000000000000)⟩
theorem envelope_sound1031 : envelope1031.Sound := by
  apply rat_majority_inputs_envelopes inputs1031 inputs_valid1031
  · norm_num [envelope1031]
  · intro rho hr0 hr1
    have hh := Batch051.bound2062 rho hr0 hr1
    norm_num [Batch051.certificate2062,envelope1031,inputs1031,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2063 rho hr0 hr1
    norm_num [Batch051.certificate2063,envelope1031,inputs1031,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1032 : RatMajorityInputs := ⟨(491897471173195324508091/10000000000000000000),(40667234429/10000000000),(1000060991212358183/1000000000000000000),(11424440362762999/50000000000000000),(40667234429/20000000000),(16361843625199379/125000000000000000),25⟩
theorem inputs_valid1032 : inputs1032.Valid := by decide +kernel
def envelope1032 : RatMajorityEnvelope := ⟨482,1,inputs1032,1,(552482429345435931/1000000000000000000)⟩
theorem envelope_sound1032 : envelope1032.Sound := by
  apply rat_majority_inputs_envelopes inputs1032 inputs_valid1032
  · norm_num [envelope1032]
  · intro rho hr0 hr1
    have hh := Batch051.bound2064 rho hr0 hr1
    norm_num [Batch051.certificate2064,envelope1032,inputs1032,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2065 rho hr0 hr1
    norm_num [Batch051.certificate2065,envelope1032,inputs1032,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1033 : RatMajorityInputs := ⟨(491897471173195324508091/10000000000000000000),(45860331921/10000000000),(1000060991212358183/1000000000000000000),(5129060127168669/31250000000000000),(45860331921/20000000000),(50480721068498443/500000000000000000),26⟩
theorem inputs_valid1033 : inputs1033.Valid := by decide +kernel
def envelope1033 : RatMajorityEnvelope := ⟨482,2,inputs1033,1,(136047078208834831/250000000000000000)⟩
theorem envelope_sound1033 : envelope1033.Sound := by
  apply rat_majority_inputs_envelopes inputs1033 inputs_valid1033
  · norm_num [envelope1033]
  · intro rho hr0 hr1
    have hh := Batch051.bound2066 rho hr0 hr1
    norm_num [Batch051.certificate2066,envelope1033,inputs1033,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2067 rho hr0 hr1
    norm_num [Batch051.certificate2067,envelope1033,inputs1033,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1034 : RatMajorityInputs := ⟨(38455367113451904204297/800000000000000000),(91555567741/20000000000),(250015603260897273/250000000000000000),(165016820708327417/1000000000000000000),(91555567741/40000000000),(50689505897219771/500000000000000000),26⟩
theorem inputs_valid1034 : inputs1034.Valid := by decide +kernel
def envelope1034 : RatMajorityEnvelope := ⟨483,0,inputs1034,(179332621/146875000),(369560304095658153/500000000000000000)⟩
theorem envelope_sound1034 : envelope1034.Sound := by
  apply rat_majority_inputs_envelopes inputs1034 inputs_valid1034
  · norm_num [envelope1034]
  · intro rho hr0 hr1
    have hh := Batch051.bound2068 rho hr0 hr1
    norm_num [Batch051.certificate2068,envelope1034,inputs1034,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2069 rho hr0 hr1
    norm_num [Batch051.certificate2069,envelope1034,inputs1034,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1035 : RatMajorityInputs := ⟨(38455367113451904204297/800000000000000000),(81218295809/20000000000),(250015603260897273/250000000000000000),(22931298332414293/100000000000000000),(81218295809/40000000000),(13127546264453041/100000000000000000),25⟩
theorem inputs_valid1035 : inputs1035.Valid := by decide +kernel
def envelope1035 : RatMajorityEnvelope := ⟨483,1,inputs1035,1,(276299219750931971/500000000000000000)⟩
theorem envelope_sound1035 : envelope1035.Sound := by
  apply rat_majority_inputs_envelopes inputs1035 inputs_valid1035
  · norm_num [envelope1035]
  · intro rho hr0 hr1
    have hh := Batch051.bound2070 rho hr0 hr1
    norm_num [Batch051.certificate2070,envelope1035,inputs1035,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2071 rho hr0 hr1
    norm_num [Batch051.certificate2071,envelope1035,inputs1035,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1036 : RatMajorityInputs := ⟨(38455367113451904204297/800000000000000000),(46061569847/10000000000),(250015603260897273/250000000000000000),(80992527573777541/500000000000000000),(46061569847/20000000000),(99950672234549129/1000000000000000000),26⟩
theorem inputs_valid1036 : inputs1036.Valid := by decide +kernel
def envelope1036 : RatMajorityEnvelope := ⟨483,2,inputs1036,1,(135983832466823693/250000000000000000)⟩
theorem envelope_sound1036 : envelope1036.Sound := by
  apply rat_majority_inputs_envelopes inputs1036 inputs_valid1036
  · norm_num [envelope1036]
  · intro rho hr0 hr1
    have hh := Batch051.bound2072 rho hr0 hr1
    norm_num [Batch051.certificate2072,envelope1036,inputs1036,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2073 rho hr0 hr1
    norm_num [Batch051.certificate2073,envelope1036,inputs1036,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1037 : RatMajorityInputs := ⟨(117520067827369448221227/2500000000000000000),(91741674393/20000000000),(125007977756940237/125000000000000000),(164017351055725541/1000000000000000000),(91741674393/40000000000),(25227106168516473/250000000000000000),26⟩
theorem inputs_valid1037 : inputs1037.Valid := by decide +kernel
def envelope1037 : RatMajorityEnvelope := ⟨484,0,inputs1037,(1435815847/1175000000),(184984027884811653/250000000000000000)⟩
theorem envelope_sound1037 : envelope1037.Sound := by
  apply rat_majority_inputs_envelopes inputs1037 inputs_valid1037
  · norm_num [envelope1037]
  · intro rho hr0 hr1
    have hh := Batch051.bound2074 rho hr0 hr1
    norm_num [Batch051.certificate2074,envelope1037,inputs1037,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2075 rho hr0 hr1
    norm_num [Batch051.certificate2075,envelope1037,inputs1037,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1038 : RatMajorityInputs := ⟨(117520067827369448221227/2500000000000000000),(81124297971/20000000000),(125007977756940237/125000000000000000),(57495405151999399/250000000000000000),(81124297971/40000000000),(131584315638096819/1000000000000000000),25⟩
theorem inputs_valid1038 : inputs1038.Valid := by decide +kernel
def envelope1038 : RatMajorityEnvelope := ⟨484,1,inputs1038,1,(276346420714477933/500000000000000000)⟩
theorem envelope_sound1038 : envelope1038.Sound := by
  apply rat_majority_inputs_envelopes inputs1038 inputs_valid1038
  · norm_num [envelope1038]
  · intro rho hr0 hr1
    have hh := Batch051.bound2076 rho hr0 hr1
    norm_num [Batch051.certificate2076,envelope1038,inputs1038,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2077 rho hr0 hr1
    norm_num [Batch051.certificate2077,envelope1038,inputs1038,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1039 : RatMajorityInputs := ⟨(117520067827369448221227/2500000000000000000),(92527016569/20000000000),(125007977756940237/125000000000000000),(159857129489333141/1000000000000000000),(92527016569/40000000000),(98946555878452861/1000000000000000000),26⟩
theorem inputs_valid1039 : inputs1039.Valid := by decide +kernel
def envelope1039 : RatMajorityEnvelope := ⟨484,2,inputs1039,1,(108737140019444433/200000000000000000)⟩
theorem envelope_sound1039 : envelope1039.Sound := by
  apply rat_majority_inputs_envelopes inputs1039 inputs_valid1039
  · norm_num [envelope1039]
  · intro rho hr0 hr1
    have hh := Batch051.bound2078 rho hr0 hr1
    norm_num [Batch051.certificate2078,envelope1039,inputs1039,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch051.bound2079 rho hr0 hr1
    norm_num [Batch051.certificate2079,envelope1039,inputs1039,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope1020,envelope1021,envelope1022,envelope1023,envelope1024,envelope1025,envelope1026,envelope1027,envelope1028,envelope1029,envelope1030,envelope1031,envelope1032,envelope1033,envelope1034,envelope1035,envelope1036,envelope1037,envelope1038,envelope1039]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound1020
  · exact envelope_sound1021
  · exact envelope_sound1022
  · exact envelope_sound1023
  · exact envelope_sound1024
  · exact envelope_sound1025
  · exact envelope_sound1026
  · exact envelope_sound1027
  · exact envelope_sound1028
  · exact envelope_sound1029
  · exact envelope_sound1030
  · exact envelope_sound1031
  · exact envelope_sound1032
  · exact envelope_sound1033
  · exact envelope_sound1034
  · exact envelope_sound1035
  · exact envelope_sound1036
  · exact envelope_sound1037
  · exact envelope_sound1038
  · exact envelope_sound1039

end Cycle12.MajorityCertificates.Inputs051
