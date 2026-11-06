import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch026

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs026

def inputs520 : RatMajorityInputs := ⟨(170447051335397639858251/12500000000000000000),(669840241651/156250000000),(1000220047326507061/1000000000000000000),(99496971074419867/500000000000000000),(669840241651/312500000000),(117245087137110483/1000000000000000000),26⟩
theorem inputs_valid520 : inputs520.Valid := by decide +kernel
def envelope520 : RatMajorityEnvelope := ⟨260,0,inputs520,(271753399/230720000),(703307198543795087/1000000000000000000)⟩
theorem envelope_sound520 : envelope520.Sound := by
  apply rat_majority_inputs_envelopes inputs520 inputs_valid520
  · norm_num [envelope520]
  · intro rho hr0 hr1
    have hh := Batch026.bound1040 rho hr0 hr1
    norm_num [Batch026.certificate1040,envelope520,inputs520,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1041 rho hr0 hr1
    norm_num [Batch026.certificate1041,envelope520,inputs520,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs521 : RatMajorityInputs := ⟨(170447051335397639858251/12500000000000000000),(725579574979/156250000000),(1000220047326507061/1000000000000000000),(79023688109202221/500000000000000000),(725579574979/312500000000),(98091492399020637/1000000000000000000),25⟩
theorem inputs_valid521 : inputs521.Valid := by decide +kernel
def envelope521 : RatMajorityEnvelope := ⟨260,1,inputs521,1,(16985717989147731/31250000000000000)⟩
theorem envelope_sound521 : envelope521.Sound := by
  apply rat_majority_inputs_envelopes inputs521 inputs_valid521
  · norm_num [envelope521]
  · intro rho hr0 hr1
    have hh := Batch026.bound1042 rho hr0 hr1
    norm_num [Batch026.certificate1042,envelope521,inputs521,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1043 rho hr0 hr1
    norm_num [Batch026.certificate1043,envelope521,inputs521,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs522 : RatMajorityInputs := ⟨(49791600780207694314188019/4000000000000000000000),(17164222171557/4000000000000),(31257532802705789/31250000000000000),(39695876408605973/200000000000000000),(17164222171557/8000000000000),(29251567044612923/250000000000000000),25⟩
theorem inputs_valid522 : inputs522.Valid := by decide +kernel
def envelope522 : RatMajorityEnvelope := ⟨261,0,inputs522,(542950437/460550000),(70422448435773053/100000000000000000)⟩
theorem envelope_sound522 : envelope522.Sound := by
  apply rat_majority_inputs_envelopes inputs522 inputs_valid522
  · norm_num [envelope522]
  · intro rho hr0 hr1
    have hh := Batch026.bound1044 rho hr0 hr1
    norm_num [Batch026.certificate1044,envelope522,inputs522,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1045 rho hr0 hr1
    norm_num [Batch026.certificate1045,envelope522,inputs522,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs523 : RatMajorityInputs := ⟨(49791600780207694314188019/4000000000000000000000),(4643259490501/1000000000000),(31257532802705789/31250000000000000),(31618809022745529/200000000000000000),(4643259490501/2000000000000),(98113555134843039/1000000000000000000),26⟩
theorem inputs_valid523 : inputs523.Valid := by decide +kernel
def envelope523 : RatMajorityEnvelope := ⟨261,1,inputs523,1,(543557703468385061/1000000000000000000)⟩
theorem envelope_sound523 : envelope523.Sound := by
  apply rat_majority_inputs_envelopes inputs523 inputs_valid523
  · norm_num [envelope523]
  · intro rho hr0 hr1
    have hh := Batch026.bound1046 rho hr0 hr1
    norm_num [Batch026.certificate1046,envelope523,inputs523,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1047 rho hr0 hr1
    norm_num [Batch026.certificate1047,envelope523,inputs523,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs524 : RatMajorityInputs := ⟨(14270535969036438482320423/1250000000000000000000),(335559478943/78125000000),(200052566583222279/200000000000000000),(197962445841726861/1000000000000000000),(335559478943/156250000000),(116766313122443711/1000000000000000000),26⟩
theorem inputs_valid524 : inputs524.Valid := by decide +kernel
def envelope524 : RatMajorityEnvelope := ⟨262,0,inputs524,(84752333/71825000),(705140944145013817/1000000000000000000)⟩
theorem envelope_sound524 : envelope524.Sound := by
  apply rat_majority_inputs_envelopes inputs524 inputs_valid524
  · norm_num [envelope524]
  · intro rho hr0 hr1
    have hh := Batch026.bound1048 rho hr0 hr1
    norm_num [Batch026.certificate1048,envelope524,inputs524,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1049 rho hr0 hr1
    norm_num [Batch026.certificate1049,envelope524,inputs524,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs525 : RatMajorityInputs := ⟨(14270535969036438482320423/1250000000000000000000),(3627222833/781250000),(200052566583222279/200000000000000000),(39534259648860213/250000000000000000),(3627222833/1562500000),(98133879709412597/1000000000000000000),27⟩
theorem inputs_valid525 : inputs525.Valid := by decide +kernel
def envelope525 : RatMajorityEnvelope := ⟨262,1,inputs525,1,(543572347129910561/1000000000000000000)⟩
theorem envelope_sound525 : envelope525.Sound := by
  apply rat_majority_inputs_envelopes inputs525 inputs_valid525
  · norm_num [envelope525]
  · intro rho hr0 hr1
    have hh := Batch026.bound1050 rho hr0 hr1
    norm_num [Batch026.certificate1050,envelope525,inputs525,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1051 rho hr0 hr1
    norm_num [Batch026.certificate1051,envelope525,inputs525,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs526 : RatMajorityInputs := ⟨(26287374104303342633201249/2500000000000000000000),(17172947782711/4000000000000),(1000285371395657569/1000000000000000000),(198204592959136217/1000000000000000000),(17172947782711/8000000000000),(58439359425186577/500000000000000000),26⟩
theorem inputs_valid526 : inputs526.Valid := by decide +kernel
def envelope526 : RatMajorityEnvelope := ⟨263,0,inputs526,(2709787481/2294150000),(706244781084128461/1000000000000000000)⟩
theorem envelope_sound526 : envelope526.Sound := by
  apply rat_majority_inputs_envelopes inputs526 inputs_valid526
  · norm_num [envelope526]
  · intro rho hr0 hr1
    have hh := Batch026.bound1052 rho hr0 hr1
    norm_num [Batch026.certificate1052,envelope526,inputs526,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1053 rho hr0 hr1
    norm_num [Batch026.certificate1053,envelope526,inputs526,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs527 : RatMajorityInputs := ⟨(26287374104303342633201249/2500000000000000000000),(2325417475063/500000000000),(1000285371395657569/1000000000000000000),(157309629121744631/1000000000000000000),(2325417475063/1000000000000),(48871315210906709/500000000000000000),26⟩
theorem inputs_valid527 : inputs527.Valid := by decide +kernel
def envelope527 : RatMajorityEnvelope := ⟨263,1,inputs527,1,(543485886944379273/1000000000000000000)⟩
theorem envelope_sound527 : envelope527.Sound := by
  apply rat_majority_inputs_envelopes inputs527 inputs_valid527
  · norm_num [envelope527]
  · intro rho hr0 hr1
    have hh := Batch026.bound1054 rho hr0 hr1
    norm_num [Batch026.certificate1054,envelope527,inputs527,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1055 rho hr0 hr1
    norm_num [Batch026.certificate1055,envelope527,inputs527,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs528 : RatMajorityInputs := ⟨(60764874291214232757582093/6250000000000000000000),(430020879128367/100000000000000),(1000308640495644903/1000000000000000000),(98664250619506193/500000000000000000),(430020879128367/200000000000000),(29117999492452221/250000000000000000),25⟩
theorem inputs_valid528 : inputs528.Valid := by decide +kernel
def envelope528 : RatMajorityEnvelope := ⟨264,0,inputs528,(1354492409/1144995000),(176945466750944377/250000000000000000)⟩
theorem envelope_sound528 : envelope528.Sound := by
  apply rat_majority_inputs_envelopes inputs528 inputs_valid528
  · norm_num [envelope528]
  · intro rho hr0 hr1
    have hh := Batch026.bound1056 rho hr0 hr1
    norm_num [Batch026.certificate1056,envelope528,inputs528,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1057 rho hr0 hr1
    norm_num [Batch026.certificate1057,envelope528,inputs528,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs529 : RatMajorityInputs := ⟨(60764874291214232757582093/6250000000000000000000),(1815815281641/390625000000),(1000308640495644903/1000000000000000000),(157552377853716119/1000000000000000000),(1815815281641/781250000000),(97857439293763333/1000000000000000000),26⟩
theorem inputs_valid529 : inputs529.Valid := by decide +kernel
def envelope529 : RatMajorityEnvelope := ⟨264,1,inputs529,1,(543524446433821179/1000000000000000000)⟩
theorem envelope_sound529 : envelope529.Sound := by
  apply rat_majority_inputs_envelopes inputs529 inputs_valid529
  · norm_num [envelope529]
  · intro rho hr0 hr1
    have hh := Batch026.bound1058 rho hr0 hr1
    norm_num [Batch026.certificate1058,envelope529,inputs529,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1059 rho hr0 hr1
    norm_num [Batch026.certificate1059,envelope529,inputs529,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs530 : RatMajorityInputs := ⟨(451087606808222110199106183/50000000000000000000000),(5380670737629/1250000000000),(1000332615665066053/1000000000000000000),(196786305042569403/1000000000000000000),(5380670737629/2500000000000),(11622023677333857/100000000000000000),25⟩
theorem inputs_valid530 : inputs530.Valid := by decide +kernel
def envelope530 : RatMajorityEnvelope := ⟨265,0,inputs530,(902195317/761970000),(708695257926969091/1000000000000000000)⟩
theorem envelope_sound530 : envelope530.Sound := by
  apply rat_majority_inputs_envelopes inputs530 inputs_valid530
  · norm_num [envelope530]
  · intro rho hr0 hr1
    have hh := Batch026.bound1060 rho hr0 hr1
    norm_num [Batch026.certificate1060,envelope530,inputs530,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1061 rho hr0 hr1
    norm_num [Batch026.certificate1061,envelope530,inputs530,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs531 : RatMajorityInputs := ⟨(451087606808222110199106183/50000000000000000000000),(93129254195373/20000000000000),(1000332615665066053/1000000000000000000),(78364540057372053/500000000000000000),(93129254195373/40000000000000),(24366995250709057/250000000000000000),26⟩
theorem inputs_valid531 : inputs531.Valid := by decide +kernel
def envelope531 : RatMajorityEnvelope := ⟨265,1,inputs531,1,(33964954429565341/62500000000000000)⟩
theorem envelope_sound531 : envelope531.Sound := by
  apply rat_majority_inputs_envelopes inputs531 inputs_valid531
  · norm_num [envelope531]
  · intro rho hr0 hr1
    have hh := Batch026.bound1062 rho hr0 hr1
    norm_num [Batch026.certificate1062,envelope531,inputs531,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1063 rho hr0 hr1
    norm_num [Batch026.certificate1063,envelope531,inputs531,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs532 : RatMajorityInputs := ⟨(839939625916064624058814783/100000000000000000000000),(107726232493173/25000000000000),(125044658471771523/125000000000000000),(196222279158775719/1000000000000000000),(107726232493173/50000000000000),(57979149153524663/500000000000000000),25⟩
theorem inputs_valid532 : inputs532.Valid := by decide +kernel
def envelope532 : RatMajorityEnvelope := ⟨266,0,inputs532,(2704283719/2281930000),(709602307098842301/1000000000000000000)⟩
theorem envelope_sound532 : envelope532.Sound := by
  apply rat_majority_inputs_envelopes inputs532 inputs_valid532
  · norm_num [envelope532]
  · intro rho hr0 hr1
    have hh := Batch026.bound1064 rho hr0 hr1
    norm_num [Batch026.certificate1064,envelope532,inputs532,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1065 rho hr0 hr1
    norm_num [Batch026.certificate1065,envelope532,inputs532,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs533 : RatMajorityInputs := ⟨(839939625916064624058814783/100000000000000000000000),(232808232861897/50000000000000),(125044658471771523/125000000000000000),(78379889971271379/500000000000000000),(232808232861897/100000000000000),(97482507374415341/1000000000000000000),26⟩
theorem inputs_valid533 : inputs533.Valid := by decide +kernel
def envelope533 : RatMajorityEnvelope := ⟨266,1,inputs533,1,(271726876677877947/500000000000000000)⟩
theorem envelope_sound533 : envelope533.Sound := by
  apply rat_majority_inputs_envelopes inputs533 inputs_valid533
  · norm_num [envelope533]
  · intro rho hr0 hr1
    have hh := Batch026.bound1066 rho hr0 hr1
    norm_num [Batch026.certificate1066,envelope533,inputs533,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1067 rho hr0 hr1
    norm_num [Batch026.certificate1067,envelope533,inputs533,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs534 : RatMajorityInputs := ⟨(196100104455861029732013083/25000000000000000000000),(107839094324867/25000000000000),(500191285762795833/500000000000000000),(19565939591192733/100000000000000000),(107839094324867/50000000000000),(115696848176524459/1000000000000000000),25⟩
theorem inputs_valid534 : inputs534.Valid := by decide +kernel
def envelope534 : RatMajorityEnvelope := ⟨267,0,inputs534,(2702076873/2278040000),(355254663034096621/500000000000000000)⟩
theorem envelope_sound534 : envelope534.Sound := by
  apply rat_majority_inputs_envelopes inputs534 inputs_valid534
  · norm_num [envelope534]
  · intro rho hr0 hr1
    have hh := Batch026.bound1068 rho hr0 hr1
    norm_num [Batch026.certificate1068,envelope534,inputs534,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1069 rho hr0 hr1
    norm_num [Batch026.certificate1069,envelope534,inputs534,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs535 : RatMajorityInputs := ⟨(196100104455861029732013083/25000000000000000000000),(23321130438611/5000000000000),(500191285762795833/500000000000000000),(38982819511812517/250000000000000000),(23321130438611/10000000000000),(2427259349151453/25000000000000000),26⟩
theorem inputs_valid535 : inputs535.Valid := by decide +kernel
def envelope535 : RatMajorityEnvelope := ⟨267,1,inputs535,1,(108673757482605831/200000000000000000)⟩
theorem envelope_sound535 : envelope535.Sound := by
  apply rat_majority_inputs_envelopes inputs535 inputs_valid535
  · norm_num [envelope535]
  · intro rho hr0 hr1
    have hh := Batch026.bound1070 rho hr0 hr1
    norm_num [Batch026.certificate1070,envelope535,inputs535,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1071 rho hr0 hr1
    norm_num [Batch026.certificate1071,envelope535,inputs535,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs536 : RatMajorityInputs := ⟨(367312141944317101699424523/50000000000000000000000),(431909246284887/100000000000000),(500204250881156363/500000000000000000),(97485955041036847/500000000000000000),(431909246284887/200000000000000),(115377463828821489/1000000000000000000),25⟩
theorem inputs_valid536 : inputs536.Valid := by decide +kernel
def envelope536 : RatMajorityEnvelope := ⟨268,0,inputs536,(2699908977/2274230000),(44461636423311999/62500000000000000)⟩
theorem envelope_sound536 : envelope536.Sound := by
  apply rat_majority_inputs_envelopes inputs536 inputs_valid536
  · norm_num [envelope536]
  · intro rho hr0 hr1
    have hh := Batch026.bound1072 rho hr0 hr1
    norm_num [Batch026.certificate1072,envelope536,inputs536,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1073 rho hr0 hr1
    norm_num [Batch026.certificate1073,envelope536,inputs536,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs537 : RatMajorityInputs := ⟨(367312141944317101699424523/50000000000000000000000),(93256596199739/20000000000000),(500204250881156363/500000000000000000),(156074505589251837/1000000000000000000),(93256596199739/40000000000000),(97158180196124359/1000000000000000000),26⟩
theorem inputs_valid537 : inputs537.Valid := by decide +kernel
def envelope537 : RatMajorityEnvelope := ⟨268,1,inputs537,1,(271698444377718167/500000000000000000)⟩
theorem envelope_sound537 : envelope537.Sound := by
  apply rat_majority_inputs_envelopes inputs537 inputs_valid537
  · norm_num [envelope537]
  · intro rho hr0 hr1
    have hh := Batch026.bound1074 rho hr0 hr1
    norm_num [Batch026.certificate1074,envelope537,inputs537,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1075 rho hr0 hr1
    norm_num [Batch026.certificate1075,envelope537,inputs537,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs538 : RatMajorityInputs := ⟨(13796768401679650487581563/2000000000000000000000),(8656137214021/2000000000000),(1000435031589761769/1000000000000000000),(96930037944715651/500000000000000000),(8656137214021/4000000000000),(114860801730277057/1000000000000000000),25⟩
theorem inputs_valid538 : inputs538.Valid := by decide +kernel
def envelope538 : RatMajorityEnvelope := ⟨269,0,inputs538,(107833739/90820000),(142287128031453429/200000000000000000)⟩
theorem envelope_sound538 : envelope538.Sound := by
  apply rat_majority_inputs_envelopes inputs538 inputs_valid538
  · norm_num [envelope538]
  · intro rho hr0 hr1
    have hh := Batch026.bound1076 rho hr0 hr1
    norm_num [Batch026.certificate1076,envelope538,inputs538,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1077 rho hr0 hr1
    norm_num [Batch026.certificate1077,envelope538,inputs538,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs539 : RatMajorityInputs := ⟨(13796768401679650487581563/2000000000000000000000),(9347989742527/2000000000000),(1000435031589761769/1000000000000000000),(154932405032362509/1000000000000000000),(9347989742527/4000000000000),(96617302815382273/1000000000000000000),26⟩
theorem inputs_valid539 : inputs539.Valid := by decide +kernel
def envelope539 : RatMajorityEnvelope := ⟨269,1,inputs539,1,(21731055565535257/40000000000000000)⟩
theorem envelope_sound539 : envelope539.Sound := by
  apply rat_majority_inputs_envelopes inputs539 inputs_valid539
  · norm_num [envelope539]
  · intro rho hr0 hr1
    have hh := Batch026.bound1078 rho hr0 hr1
    norm_num [Batch026.certificate1078,envelope539,inputs539,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch026.bound1079 rho hr0 hr1
    norm_num [Batch026.certificate1079,envelope539,inputs539,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope520,envelope521,envelope522,envelope523,envelope524,envelope525,envelope526,envelope527,envelope528,envelope529,envelope530,envelope531,envelope532,envelope533,envelope534,envelope535,envelope536,envelope537,envelope538,envelope539]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound520
  · exact envelope_sound521
  · exact envelope_sound522
  · exact envelope_sound523
  · exact envelope_sound524
  · exact envelope_sound525
  · exact envelope_sound526
  · exact envelope_sound527
  · exact envelope_sound528
  · exact envelope_sound529
  · exact envelope_sound530
  · exact envelope_sound531
  · exact envelope_sound532
  · exact envelope_sound533
  · exact envelope_sound534
  · exact envelope_sound535
  · exact envelope_sound536
  · exact envelope_sound537
  · exact envelope_sound538
  · exact envelope_sound539

end Cycle12.MajorityCertificates.Inputs026
