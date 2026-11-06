import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs025

def inputs500 : RatMajorityInputs := ⟨(854814825215941461030044127/20000000000000000000000),(85485224230677/20000000000000),(1000070194472483901/1000000000000000000),(200605687136333003/1000000000000000000),(85485224230677/40000000000000),(117992925964497337/1000000000000000000),25⟩
theorem inputs_valid500 : inputs500.Valid := by decide +kernel
def envelope500 : RatMajorityEnvelope := ⟨250,0,inputs500,(2737749073/2352150000),(21592060841138727/31250000000000000)⟩
theorem envelope_sound500 : envelope500.Sound := by
  apply rat_majority_inputs_envelopes inputs500 inputs_valid500
  · norm_num [envelope500]
  · intro rho hr0 hr1
    have hh := Batch025.bound1000 rho hr0 hr1
    norm_num [Batch025.certificate1000,envelope500,inputs500,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1001 rho hr0 hr1
    norm_num [Batch025.certificate1001,envelope500,inputs500,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs501 : RatMajorityInputs := ⟨(854814825215941461030044127/20000000000000000000000),(92537436503151/20000000000000),(1000070194472483901/1000000000000000000),(159802551284290093/1000000000000000000),(92537436503151/40000000000000),(12365097977558737/125000000000000000),27⟩
theorem inputs_valid501 : inputs501.Valid := by decide +kernel
def envelope501 : RatMajorityEnvelope := ⟨250,1,inputs501,1,(543682109588577781/1000000000000000000)⟩
theorem envelope_sound501 : envelope501.Sound := by
  apply rat_majority_inputs_envelopes inputs501 inputs_valid501
  · norm_num [envelope501]
  · intro rho hr0 hr1
    have hh := Batch025.bound1002 rho hr0 hr1
    norm_num [Batch025.certificate1002,envelope501,inputs501,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1003 rho hr0 hr1
    norm_num [Batch025.certificate1003,envelope501,inputs501,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs502 : RatMajorityInputs := ⟨(984305782737238046449544613/25000000000000000000000),(214082788953063/50000000000000),(1000076200349844867/1000000000000000000),(199667126531443943/1000000000000000000),(214082788953063/100000000000000),(117557478118266851/1000000000000000000),25⟩
theorem inputs_valid502 : inputs502.Valid := by decide +kernel
def envelope502 : RatMajorityEnvelope := ⟨251,0,inputs502,(2736801107/2349780000),(345769600454738933/500000000000000000)⟩
theorem envelope_sound502 : envelope502.Sound := by
  apply rat_majority_inputs_envelopes inputs502 inputs_valid502
  · norm_num [envelope502]
  · intro rho hr0 hr1
    have hh := Batch025.bound1004 rho hr0 hr1
    norm_num [Batch025.certificate1004,envelope502,inputs502,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1005 rho hr0 hr1
    norm_num [Batch025.certificate1005,envelope502,inputs502,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs503 : RatMajorityInputs := ⟨(984305782737238046449544613/25000000000000000000000),(231333006342897/50000000000000),(1000076200349844867/1000000000000000000),(1278597810225211/8000000000000000),(231333006342897/100000000000000),(12366406881938903/125000000000000000),26⟩
theorem inputs_valid503 : inputs503.Valid := by decide +kernel
def envelope503 : RatMajorityEnvelope := ⟨251,1,inputs503,1,(543687358735687069/1000000000000000000)⟩
theorem envelope_sound503 : envelope503.Sound := by
  apply rat_majority_inputs_envelopes inputs503 inputs_valid503
  · norm_num [envelope503]
  · intro rho hr0 hr1
    have hh := Batch025.bound1006 rho hr0 hr1
    norm_num [Batch025.certificate1006,envelope503,inputs503,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1007 rho hr0 hr1
    norm_num [Batch025.certificate1007,envelope503,inputs503,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs504 : RatMajorityInputs := ⟨(906499519409456598655256101/25000000000000000000000),(53515309309703/12500000000000),(1000082741165258953/1000000000000000000),(99860867230959163/500000000000000000),(53515309309703/25000000000000),(58791408250180679/500000000000000000),26⟩
theorem inputs_valid504 : inputs504.Valid := by decide +kernel
def envelope504 : RatMajorityEnvelope := ⟨252,0,inputs504,(2735883743/2347060000),(346202269934224719/500000000000000000)⟩
theorem envelope_sound504 : envelope504.Sound := by
  apply rat_majority_inputs_envelopes inputs504 inputs_valid504
  · norm_num [envelope504]
  · intro rho hr0 hr1
    have hh := Batch025.bound1008 rho hr0 hr1
    norm_num [Batch025.certificate1008,envelope504,inputs504,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1009 rho hr0 hr1
    norm_num [Batch025.certificate1009,envelope504,inputs504,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs505 : RatMajorityInputs := ⟨(906499519409456598655256101/25000000000000000000000),(115866729301179/25000000000000),(1000082741165258953/1000000000000000000),(19873456120678127/125000000000000000),(115866729301179/50000000000000),(98535874792293377/1000000000000000000),26⟩
theorem inputs_valid505 : inputs505.Valid := by decide +kernel
def envelope505 : RatMajorityEnvelope := ⟨252,1,inputs505,1,(135898046252602857/250000000000000000)⟩
theorem envelope_sound505 : envelope505.Sound := by
  apply rat_majority_inputs_envelopes inputs505 inputs_valid505
  · norm_num [envelope505]
  · intro rho hr0 hr1
    have hh := Batch025.bound1010 rho hr0 hr1
    norm_num [Batch025.certificate1010,envelope505,inputs505,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1011 rho hr0 hr1
    norm_num [Batch025.certificate1011,envelope505,inputs505,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs506 : RatMajorityInputs := ⟨(96694904795491109845329231/3125000000000000000000),(106929980342403/25000000000000),(500048480874086511/500000000000000000),(200232336673332119/1000000000000000000),(106929980342403/50000000000000),(29454930369656283/250000000000000000),25⟩
theorem inputs_valid506 : inputs506.Valid := by decide +kernel
def envelope506 : RatMajorityEnvelope := ⟨253,0,inputs506,(2732148311/2341320000),(693592506080164839/1000000000000000000)⟩
theorem envelope_sound506 : envelope506.Sound := by
  apply rat_majority_inputs_envelopes inputs506 inputs_valid506
  · norm_num [envelope506]
  · intro rho hr0 hr1
    have hh := Batch025.bound1012 rho hr0 hr1
    norm_num [Batch025.certificate1012,envelope506,inputs506,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1013 rho hr0 hr1
    norm_num [Batch025.certificate1013,envelope506,inputs506,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs507 : RatMajorityInputs := ⟨(96694904795491109845329231/3125000000000000000000),(23158156324821/5000000000000),(500048480874086511/500000000000000000),(39826178019397577/250000000000000000),(23158156324821/10000000000000),(98685659937811647/1000000000000000000),26⟩
theorem inputs_valid507 : inputs507.Valid := by decide +kernel
def envelope507 : RatMajorityEnvelope := ⟨253,1,inputs507,1,(543635578243001341/1000000000000000000)⟩
theorem envelope_sound507 : envelope507.Sound := by
  apply rat_majority_inputs_envelopes inputs507 inputs_valid507
  · norm_num [envelope507]
  · intro rho hr0 hr1
    have hh := Batch025.bound1014 rho hr0 hr1
    norm_num [Batch025.certificate1014,envelope507,inputs507,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1015 rho hr0 hr1
    norm_num [Batch025.certificate1015,envelope507,inputs507,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs508 : RatMajorityInputs := ⟨(134162486830898446461892533/5000000000000000000000),(21382076864811/5000000000000),(200022362889727213/200000000000000000),(4006637743218007/20000000000000000),(21382076864811/10000000000000),(7366619154808233/62500000000000000),25⟩
theorem inputs_valid508 : inputs508.Valid := by decide +kernel
def envelope508 : RatMajorityEnvelope := ⟨254,0,inputs508,(2730549527/2336100000),(173832280814924241/250000000000000000)⟩
theorem envelope_sound508 : envelope508.Sound := by
  apply rat_majority_inputs_envelopes inputs508 inputs_valid508
  · norm_num [envelope508]
  · intro rho hr0 hr1
    have hh := Batch025.bound1016 rho hr0 hr1
    norm_num [Batch025.certificate1016,envelope508,inputs508,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1017 rho hr0 hr1
    norm_num [Batch025.certificate1017,envelope508,inputs508,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs509 : RatMajorityInputs := ⟨(134162486830898446461892533/5000000000000000000000),(925656007029/200000000000),(200022362889727213/200000000000000000),(39913777946144021/250000000000000000),(925656007029/400000000000),(24712789429379653/250000000000000000),26⟩
theorem inputs_valid509 : inputs509.Valid := by decide +kernel
def envelope509 : RatMajorityEnvelope := ⟨254,1,inputs509,1,(67960397724050811/125000000000000000)⟩
theorem envelope_sound509 : envelope509.Sound := by
  apply rat_majority_inputs_envelopes inputs509 inputs_valid509
  · norm_num [envelope509]
  · intro rho hr0 hr1
    have hh := Batch025.bound1018 rho hr0 hr1
    norm_num [Batch025.certificate1018,envelope509,inputs509,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1019 rho hr0 hr1
    norm_num [Batch025.certificate1019,envelope509,inputs509,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs510 : RatMajorityInputs := ⟨(23510254751382358951036731/1000000000000000000000),(4273741528119/1000000000000),(1000127616557169707/1000000000000000000),(100335893682786819/500000000000000000),(4273741528119/2000000000000),(59011794715747653/500000000000000000),25⟩
theorem inputs_valid510 : inputs510.Valid := by decide +kernel
def envelope510 : RatMajorityEnvelope := ⟨255,0,inputs510,(2727400931/2331000000),(87056417665576471/125000000000000000)⟩
theorem envelope_sound510 : envelope510.Sound := by
  apply rat_majority_inputs_envelopes inputs510 inputs_valid510
  · norm_num [envelope510]
  · intro rho hr0 hr1
    have hh := Batch025.bound1020 rho hr0 hr1
    norm_num [Batch025.certificate1020,envelope510,inputs510,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1021 rho hr0 hr1
    norm_num [Batch025.certificate1021,envelope510,inputs510,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs511 : RatMajorityInputs := ⟨(23510254751382358951036731/1000000000000000000000),(1158899869071/250000000000),(1000127616557169707/1000000000000000000),(158890663557772909/1000000000000000000),(1158899869071/500000000000),(49245025639835791/500000000000000000),26⟩
theorem inputs_valid511 : inputs511.Valid := by decide +kernel
def envelope511 : RatMajorityEnvelope := ⟨255,1,inputs511,1,(543600651388389993/1000000000000000000)⟩
theorem envelope_sound511 : envelope511.Sound := by
  apply rat_majority_inputs_envelopes inputs511 inputs_valid511
  · norm_num [envelope511]
  · intro rho hr0 hr1
    have hh := Batch025.bound1022 rho hr0 hr1
    norm_num [Batch025.certificate1022,envelope511,inputs511,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1023 rho hr0 hr1
    norm_num [Batch025.certificate1023,envelope511,inputs511,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs512 : RatMajorityInputs := ⟨(51964754925555442461453717/2500000000000000000000),(5349205530393/1250000000000),(125018043099631533/125000000000000000),(49989390806989039/250000000000000000),(5349205530393/2500000000000),(117692238242096549/1000000000000000000),25⟩
theorem inputs_valid512 : inputs512.Valid := by decide +kernel
def envelope512 : RatMajorityEnvelope := ⟨256,0,inputs512,(2725756103/2326020000),(697994874536660813/1000000000000000000)⟩
theorem envelope_sound512 : envelope512.Sound := by
  apply rat_majority_inputs_envelopes inputs512 inputs_valid512
  · norm_num [envelope512]
  · intro rho hr0 hr1
    have hh := Batch025.bound1024 rho hr0 hr1
    norm_num [Batch025.certificate1024,envelope512,inputs512,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1025 rho hr0 hr1
    norm_num [Batch025.certificate1025,envelope512,inputs512,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs513 : RatMajorityInputs := ⟨(51964754925555442461453717/2500000000000000000000),(231661323901011/50000000000000),(125018043099631533/125000000000000000),(79569076571717029/500000000000000000),(231661323901011/100000000000000),(1232587237420161/12500000000000000),26⟩
theorem inputs_valid513 : inputs513.Valid := by decide +kernel
def envelope513 : RatMajorityEnvelope := ⟨256,1,inputs513,1,(543636992198291603/1000000000000000000)⟩
theorem envelope_sound513 : envelope513.Sound := by
  apply rat_majority_inputs_envelopes inputs513 inputs_valid513
  · norm_num [envelope513]
  · intro rho hr0 hr1
    have hh := Batch025.bound1026 rho hr0 hr1
    norm_num [Batch025.certificate1026,envelope513,inputs513,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1027 rho hr0 hr1
    norm_num [Batch025.certificate1027,envelope513,inputs513,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs514 : RatMajorityInputs := ⟨(74094321006092595151068359/4000000000000000000000),(85663770981633/20000000000000),(1000161976135265881/1000000000000000000),(3989460815626963/20000000000000000),(85663770981633/40000000000000),(29366854585959819/250000000000000000),26⟩
theorem inputs_valid514 : inputs514.Valid := by decide +kernel
def envelope514 : RatMajorityEnvelope := ⟨257,0,inputs514,(680634763/580287500),(10920542083584767/15625000000000000)⟩
theorem envelope_sound514 : envelope514.Sound := by
  apply rat_majority_inputs_envelopes inputs514 inputs_valid514
  · norm_num [envelope514]
  · intro rho hr0 hr1
    have hh := Batch025.bound1028 rho hr0 hr1
    norm_num [Batch025.certificate1028,envelope514,inputs514,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1029 rho hr0 hr1
    norm_num [Batch025.certificate1029,envelope514,inputs514,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs515 : RatMajorityInputs := ⟨(74094321006092595151068359/4000000000000000000000),(46373638284831/10000000000000),(1000161976135265881/1000000000000000000),(158706868430048851/1000000000000000000),(46373638284831/20000000000000),(49201602011654217/500000000000000000),27⟩
theorem inputs_valid515 : inputs515.Valid := by decide +kernel
def envelope515 : RatMajorityEnvelope := ⟨257,1,inputs515,1,(33974645824764641/62500000000000000)⟩
theorem envelope_sound515 : envelope515.Sound := by
  apply rat_majority_inputs_envelopes inputs515 inputs_valid515
  · norm_num [envelope515]
  · intro rho hr0 hr1
    have hh := Batch025.bound1030 rho hr0 hr1
    norm_num [Batch025.certificate1030,envelope515,inputs515,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1031 rho hr0 hr1
    norm_num [Batch025.certificate1031,envelope515,inputs515,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs516 : RatMajorityInputs := ⟨(1039008386278228303805021/62500000000000000000),(2676765376693/625000000000),(125022560732308487/125000000000000000),(99759555419766637/500000000000000000),(2676765376693/1250000000000),(117488796209296579/1000000000000000000),25⟩
theorem inputs_valid516 : inputs516.Valid := by decide +kernel
def envelope516 : RatMajorityEnvelope := ⟨258,0,inputs516,(1360716893/1158200000),(700655726226355661/1000000000000000000)⟩
theorem envelope_sound516 : envelope516.Sound := by
  apply rat_majority_inputs_envelopes inputs516 inputs_valid516
  · norm_num [envelope516]
  · intro rho hr0 hr1
    have hh := Batch025.bound1032 rho hr0 hr1
    norm_num [Batch025.certificate1032,envelope516,inputs516,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1033 rho hr0 hr1
    norm_num [Batch025.certificate1033,envelope516,inputs516,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs517 : RatMajorityInputs := ⟨(1039008386278228303805021/62500000000000000000),(2319202212781/500000000000),(125022560732308487/125000000000000000),(79299277175024103/500000000000000000),(2319202212781/1000000000000),(614700114356637/6250000000000000),26⟩
theorem inputs_valid517 : inputs517.Valid := by decide +kernel
def envelope517 : RatMajorityEnvelope := ⟨258,1,inputs517,1,(543589849613271307/1000000000000000000)⟩
theorem envelope_sound517 : envelope517.Sound := by
  apply rat_majority_inputs_envelopes inputs517 inputs_valid517
  · norm_num [envelope517]
  · intro rho hr0 hr1
    have hh := Batch025.bound1034 rho hr0 hr1
    norm_num [Batch025.certificate1034,envelope517,inputs517,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1035 rho hr0 hr1
    norm_num [Batch025.certificate1035,envelope517,inputs517,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs518 : RatMajorityInputs := ⟨(2402161581448815670481207/160000000000000000000),(17149291356463/4000000000000),(125024981386235339/125000000000000000),(24868791231777543/125000000000000000),(17149291356463/8000000000000),(117224846956838451/1000000000000000000),26⟩
theorem inputs_valid518 : inputs518.Valid := by decide +kernel
def envelope518 : RatMajorityEnvelope := ⟨259,0,inputs518,(135920921/115587500),(701556848750229649/1000000000000000000)⟩
theorem envelope_sound518 : envelope518.Sound := by
  apply rat_majority_inputs_envelopes inputs518 inputs_valid518
  · norm_num [envelope518]
  · intro rho hr0 hr1
    have hh := Batch025.bound1036 rho hr0 hr1
    norm_num [Batch025.certificate1036,envelope518,inputs518,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1037 rho hr0 hr1
    norm_num [Batch025.certificate1037,envelope518,inputs518,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs519 : RatMajorityInputs := ⟨(2402161581448815670481207/160000000000000000000),(9275717233531/2000000000000),(125024981386235339/125000000000000000),(158655358717666389/1000000000000000000),(9275717233531/4000000000000),(49189431329118731/500000000000000000),26⟩
theorem inputs_valid519 : inputs519.Valid := by decide +kernel
def envelope519 : RatMajorityEnvelope := ⟨259,1,inputs519,1,(543605040794362117/1000000000000000000)⟩
theorem envelope_sound519 : envelope519.Sound := by
  apply rat_majority_inputs_envelopes inputs519 inputs_valid519
  · norm_num [envelope519]
  · intro rho hr0 hr1
    have hh := Batch025.bound1038 rho hr0 hr1
    norm_num [Batch025.certificate1038,envelope519,inputs519,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch025.bound1039 rho hr0 hr1
    norm_num [Batch025.certificate1039,envelope519,inputs519,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope500,envelope501,envelope502,envelope503,envelope504,envelope505,envelope506,envelope507,envelope508,envelope509,envelope510,envelope511,envelope512,envelope513,envelope514,envelope515,envelope516,envelope517,envelope518,envelope519]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound500
  · exact envelope_sound501
  · exact envelope_sound502
  · exact envelope_sound503
  · exact envelope_sound504
  · exact envelope_sound505
  · exact envelope_sound506
  · exact envelope_sound507
  · exact envelope_sound508
  · exact envelope_sound509
  · exact envelope_sound510
  · exact envelope_sound511
  · exact envelope_sound512
  · exact envelope_sound513
  · exact envelope_sound514
  · exact envelope_sound515
  · exact envelope_sound516
  · exact envelope_sound517
  · exact envelope_sound518
  · exact envelope_sound519

end Cycle12.MajorityCertificates.Inputs025
