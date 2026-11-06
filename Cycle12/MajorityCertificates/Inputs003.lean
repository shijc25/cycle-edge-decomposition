import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs003

def inputs60 : RatMajorityInputs := ⟨(4265057459763191722742247/4000000000000000000000),(4124509693501/1000000000000),(501409865270778433/500000000000000000),(13776332785009393/62500000000000000),(4124509693501/2000000000000),(127166904490839777/1000000000000000000),25⟩
theorem inputs_valid60 : inputs60.Valid := by decide +kernel
def envelope60 : RatMajorityEnvelope := ⟨30,0,inputs60,(249602521/207925000),(45451432068627787/62500000000000000)⟩
theorem envelope_sound60 : envelope60.Sound := by
  apply rat_majority_inputs_envelopes inputs60 inputs_valid60
  · norm_num [envelope60]
  · intro rho hr0 hr1
    have hh := Batch003.bound120 rho hr0 hr1
    norm_num [Batch003.certificate120,envelope60,inputs60,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound121 rho hr0 hr1
    norm_num [Batch003.certificate121,envelope60,inputs60,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs61 : RatMajorityInputs := ⟨(4265057459763191722742247/4000000000000000000000),(2462948083181/500000000000),(501409865270778433/500000000000000000),(1023700949672177/7812500000000000),(2462948083181/1000000000000),(17036690505323649/200000000000000000),26⟩
theorem inputs_valid61 : inputs61.Valid := by decide +kernel
def envelope61 : RatMajorityEnvelope := ⟨30,1,inputs61,1,(541684218568856353/1000000000000000000)⟩
theorem envelope_sound61 : envelope61.Sound := by
  apply rat_majority_inputs_envelopes inputs61 inputs_valid61
  · norm_num [envelope61]
  · intro rho hr0 hr1
    have hh := Batch003.bound122 rho hr0 hr1
    norm_num [Batch003.certificate122,envelope61,inputs61,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound123 rho hr0 hr1
    norm_num [Batch003.certificate123,envelope61,inputs61,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs62 : RatMajorityInputs := ⟨(83368978968895499500677/80000000000000000000),(41370374169453/10000000000000),(1002885227578486383/1000000000000000000),(8748147215590313/40000000000000000),(41370374169453/20000000000000),(63186419071352467/500000000000000000),25⟩
theorem inputs_valid62 : inputs62.Valid := by decide +kernel
def envelope62 : RatMajorityEnvelope := ⟨31,0,inputs62,(166213459/138460000),(727081996092637009/1000000000000000000)⟩
theorem envelope_sound62 : envelope62.Sound := by
  apply rat_majority_inputs_envelopes inputs62 inputs_valid62
  · norm_num [envelope62]
  · intro rho hr0 hr1
    have hh := Batch003.bound124 rho hr0 hr1
    norm_num [Batch003.certificate124,envelope62,inputs62,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound125 rho hr0 hr1
    norm_num [Batch003.certificate125,envelope62,inputs62,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs63 : RatMajorityInputs := ⟨(83368978968895499500677/80000000000000000000),(49340294446107/10000000000000),(1002885227578486383/1000000000000000000),(65159721509280417/500000000000000000),(49340294446107/20000000000000),(2120943639374067/25000000000000000),26⟩
theorem inputs_valid63 : inputs63.Valid := by decide +kernel
def envelope63 : RatMajorityEnvelope := ⟨31,1,inputs63,1,(27081870160435789/50000000000000000)⟩
theorem envelope_sound63 : envelope63.Sound := by
  apply rat_majority_inputs_envelopes inputs63 inputs_valid63
  · norm_num [envelope63]
  · intro rho hr0 hr1
    have hh := Batch003.bound126 rho hr0 hr1
    norm_num [Batch003.certificate126,envelope63,inputs63,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound127 rho hr0 hr1
    norm_num [Batch003.certificate127,envelope63,inputs63,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs64 : RatMajorityInputs := ⟨(20277342612780086810776569/20000000000000000000000),(82641948014703/20000000000000),(125370723982114381/125000000000000000),(219379668080092349/1000000000000000000),(82641948014703/40000000000000),(791783536820763/6250000000000000),25⟩
theorem inputs_valid64 : inputs64.Valid := by decide +kernel
def envelope64 : RatMajorityEnvelope := ⟨32,0,inputs64,(177873799/148115000),(363810743392656071/500000000000000000)⟩
theorem envelope_sound64 : envelope64.Sound := by
  apply rat_majority_inputs_envelopes inputs64 inputs_valid64
  · norm_num [envelope64]
  · intro rho hr0 hr1
    have hh := Batch003.bound128 rho hr0 hr1
    norm_num [Batch003.certificate128,envelope64,inputs64,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound129 rho hr0 hr1
    norm_num [Batch003.certificate129,envelope64,inputs64,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs65 : RatMajorityInputs := ⟨(20277342612780086810776569/20000000000000000000000),(246655250299381/50000000000000),(125370723982114381/125000000000000000),(130400454984073273/1000000000000000000),(246655250299381/100000000000000),(16975393656672653/200000000000000000),26⟩
theorem inputs_valid65 : inputs65.Valid := by decide +kernel
def envelope65 : RatMajorityEnvelope := ⟨32,1,inputs65,1,(541682961649943089/1000000000000000000)⟩
theorem envelope_sound65 : envelope65.Sound := by
  apply rat_majority_inputs_envelopes inputs65 inputs_valid65
  · norm_num [envelope65]
  · intro rho hr0 hr1
    have hh := Batch003.bound130 rho hr0 hr1
    norm_num [Batch003.certificate130,envelope65,inputs65,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound131 rho hr0 hr1
    norm_num [Batch003.certificate131,envelope65,inputs65,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs66 : RatMajorityInputs := ⟨(2467192686794969533425387/2500000000000000000000),(6450016158639/1562500000000),(501523547660046249/500000000000000000),(6873132559125163/31250000000000000),(6450016158639/3125000000000),(126944515886959303/1000000000000000000),26⟩
theorem inputs_valid66 : inputs66.Valid := by decide +kernel
def envelope66 : RatMajorityEnvelope := ⟨33,0,inputs66,(2489231459/2070360000),(364493262323518373/500000000000000000)⟩
theorem envelope_sound66 : envelope66.Sound := by
  apply rat_majority_inputs_envelopes inputs66 inputs_valid66
  · norm_num [envelope66]
  · intro rho hr0 hr1
    have hh := Batch003.bound132 rho hr0 hr1
    norm_num [Batch003.certificate132,envelope66,inputs66,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound133 rho hr0 hr1
    norm_num [Batch003.certificate133,envelope66,inputs66,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs67 : RatMajorityInputs := ⟨(2467192686794969533425387/2500000000000000000000),(123228351880983/25000000000000),(501523547660046249/500000000000000000),(130748949100601049/1000000000000000000),(123228351880983/50000000000000),(85045655971319527/1000000000000000000),26⟩
theorem inputs_valid67 : inputs67.Valid := by decide +kernel
def envelope67 : RatMajorityEnvelope := ⟨33,1,inputs67,1,(541757568598032009/1000000000000000000)⟩
theorem envelope_sound67 : envelope67.Sound := by
  apply rat_majority_inputs_envelopes inputs67 inputs_valid67
  · norm_num [envelope67]
  · intro rho hr0 hr1
    have hh := Batch003.bound134 rho hr0 hr1
    norm_num [Batch003.certificate134,envelope67,inputs67,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound135 rho hr0 hr1
    norm_num [Batch003.certificate135,envelope67,inputs67,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs68 : RatMajorityInputs := ⟨(1201336751797752197549349/1250000000000000000000),(4121704069533/1000000000000),(6269556989220921/6250000000000000),(220807519080500757/1000000000000000000),(4121704069533/2000000000000),(31836355232913509/250000000000000000),25⟩
theorem inputs_valid68 : inputs68.Valid := by decide +kernel
def envelope68 : RatMajorityEnvelope := ⟨34,0,inputs68,(248460887/206715000),(728787372450303757/1000000000000000000)⟩
theorem envelope_sound68 : envelope68.Sound := by
  apply rat_majority_inputs_envelopes inputs68 inputs_valid68
  · norm_num [envelope68]
  · intro rho hr0 hr1
    have hh := Batch003.bound136 rho hr0 hr1
    norm_num [Batch003.certificate136,envelope68,inputs68,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound137 rho hr0 hr1
    norm_num [Batch003.certificate137,envelope68,inputs68,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs69 : RatMajorityInputs := ⟨(1201336751797752197549349/1250000000000000000000),(3944180865717/800000000000),(6269556989220921/6250000000000000),(130653031123419567/1000000000000000000),(3944180865717/1600000000000),(16999846684809169/200000000000000000),27⟩
theorem inputs_valid69 : inputs69.Valid := by decide +kernel
def envelope69 : RatMajorityEnvelope := ⟨34,1,inputs69,1,(541784784486835781/1000000000000000000)⟩
theorem envelope_sound69 : envelope69.Sound := by
  apply rat_majority_inputs_envelopes inputs69 inputs_valid69
  · norm_num [envelope69]
  · intro rho hr0 hr1
    have hh := Batch003.bound138 rho hr0 hr1
    norm_num [Batch003.certificate138,envelope69,inputs69,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound139 rho hr0 hr1
    norm_num [Batch003.certificate139,envelope69,inputs69,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs70 : RatMajorityInputs := ⟨(46818832704700804989119907/50000000000000000000000),(12912199746973/3125000000000),(125401480103727083/125000000000000000),(6856443095254121/31250000000000000),(12912199746973/6250000000000),(63348811067185587/500000000000000000),26⟩
theorem inputs_valid70 : inputs70.Valid := by decide +kernel
def envelope70 : RatMajorityEnvelope := ⟨35,0,inputs70,(1240527081/1031990000),(36440069055013571/50000000000000000)⟩
theorem envelope_sound70 : envelope70.Sound := by
  apply rat_majority_inputs_envelopes inputs70 inputs_valid70
  · norm_num [envelope70]
  · intro rho hr0 hr1
    have hh := Batch003.bound140 rho hr0 hr1
    norm_num [Batch003.certificate140,envelope70,inputs70,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound141 rho hr0 hr1
    norm_num [Batch003.certificate141,envelope70,inputs70,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs71 : RatMajorityInputs := ⟨(46818832704700804989119907/50000000000000000000000),(49289104626969/10000000000000),(125401480103727083/125000000000000000),(130768598105095651/1000000000000000000),(49289104626969/20000000000000),(85055165140578761/1000000000000000000),27⟩
theorem inputs_valid71 : inputs71.Valid := by decide +kernel
def envelope71 : RatMajorityEnvelope := ⟨35,1,inputs71,1,(4233086087274491/7812500000000000)⟩
theorem envelope_sound71 : envelope71.Sound := by
  apply rat_majority_inputs_envelopes inputs71 inputs_valid71
  · norm_num [envelope71]
  · intro rho hr0 hr1
    have hh := Batch003.bound142 rho hr0 hr1
    norm_num [Batch003.certificate142,envelope71,inputs71,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound143 rho hr0 hr1
    norm_num [Batch003.certificate143,envelope71,inputs71,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs72 : RatMajorityInputs := ⟨(46342834441535440771868103/50000000000000000000000),(206816857609791/50000000000000),(100324491363581793/100000000000000000),(218799399178085457/1000000000000000000),(206816857609791/100000000000000),(126417093111723059/1000000000000000000),25⟩
theorem inputs_valid72 : inputs72.Valid := by decide +kernel
def envelope72 : RatMajorityEnvelope := ⟨36,0,inputs72,(1239921521/1031470000),(145754991218990743/200000000000000000)⟩
theorem envelope_sound72 : envelope72.Sound := by
  apply rat_majority_inputs_envelopes inputs72 inputs_valid72
  · norm_num [envelope72]
  · intro rho hr0 hr1
    have hh := Batch003.bound144 rho hr0 hr1
    norm_num [Batch003.certificate144,envelope72,inputs72,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound145 rho hr0 hr1
    norm_num [Batch003.certificate145,envelope72,inputs72,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs73 : RatMajorityInputs := ⟨(46342834441535440771868103/50000000000000000000000),(123294185608913/25000000000000),(100324491363581793/100000000000000000),(26103550209344043/200000000000000000),(123294185608913/50000000000000),(10616719025796183/125000000000000000),26⟩
theorem inputs_valid73 : inputs73.Valid := by decide +kernel
def envelope73 : RatMajorityEnvelope := ⟨36,1,inputs73,1,(270911619806694107/500000000000000000)⟩
theorem envelope_sound73 : envelope73.Sound := by
  apply rat_majority_inputs_envelopes inputs73 inputs_valid73
  · norm_num [envelope73]
  · intro rho hr0 hr1
    have hh := Batch003.bound146 rho hr0 hr1
    norm_num [Batch003.certificate146,envelope73,inputs73,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound147 rho hr0 hr1
    norm_num [Batch003.certificate147,envelope73,inputs73,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs74 : RatMajorityInputs := ⟨(45757146487908746606342793/50000000000000000000000),(412296210525399/100000000000000),(200657310881579737/200000000000000000),(44126856258545293/200000000000000000),(412296210525399/200000000000000),(6363267178755991/50000000000000000),25⟩
theorem inputs_valid74 : inputs74.Valid := by decide +kernel
def envelope74 : RatMajorityEnvelope := ⟨37,0,inputs74,(826353043/687130000),(729456765997304727/1000000000000000000)⟩
theorem envelope_sound74 : envelope74.Sound := by
  apply rat_majority_inputs_envelopes inputs74 inputs_valid74
  · norm_num [envelope74]
  · intro rho hr0 hr1
    have hh := Batch003.bound148 rho hr0 hr1
    norm_num [Batch003.certificate148,envelope74,inputs74,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound149 rho hr0 hr1
    norm_num [Batch003.certificate149,envelope74,inputs74,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs75 : RatMajorityInputs := ⟨(45757146487908746606342793/50000000000000000000000),(493074938198547/100000000000000),(200657310881579737/200000000000000000),(13060708839778419/100000000000000000),(493074938198547/200000000000000),(16995399258150493/200000000000000000),27⟩
theorem inputs_valid75 : inputs75.Valid := by decide +kernel
def envelope75 : RatMajorityEnvelope := ⟨37,1,inputs75,1,(270925933031982247/500000000000000000)⟩
theorem envelope_sound75 : envelope75.Sound := by
  apply rat_majority_inputs_envelopes inputs75 inputs_valid75
  · norm_num [envelope75]
  · intro rho hr0 hr1
    have hh := Batch003.bound150 rho hr0 hr1
    norm_num [Batch003.certificate150,envelope75,inputs75,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound151 rho hr0 hr1
    norm_num [Batch003.certificate151,envelope75,inputs75,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs76 : RatMajorityInputs := ⟨(5563113791324549471866477/6250000000000000000000),(25888215204339/6250000000000),(1003379271248158287/1000000000000000000),(109005370452745521/500000000000000000),(25888215204339/12500000000000),(126052446528329429/1000000000000000000),25⟩
theorem inputs_valid76 : inputs76.Valid := by decide +kernel
def envelope76 : RatMajorityEnvelope := ⟨38,0,inputs76,(2469459337/2057780000),(45433544565925721/62500000000000000)⟩
theorem envelope_sound76 : envelope76.Sound := by
  apply rat_majority_inputs_envelopes inputs76 inputs_valid76
  · norm_num [envelope76]
  · intro rho hr0 hr1
    have hh := Batch003.bound152 rho hr0 hr1
    norm_num [Batch003.certificate152,envelope76,inputs76,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound153 rho hr0 hr1
    norm_num [Batch003.certificate153,envelope76,inputs76,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs77 : RatMajorityInputs := ⟨(5563113791324549471866477/6250000000000000000000),(123286979762921/25000000000000),(1003379271248158287/1000000000000000000),(4079469976565487/31250000000000000),(123286979762921/50000000000000),(4247299673959699/50000000000000000),26⟩
theorem inputs_valid77 : inputs77.Valid := by decide +kernel
def envelope77 : RatMajorityEnvelope := ⟨38,1,inputs77,1,(541887411618084589/1000000000000000000)⟩
theorem envelope_sound77 : envelope77.Sound := by
  apply rat_majority_inputs_envelopes inputs77 inputs_valid77
  · norm_num [envelope77]
  · intro rho hr0 hr1
    have hh := Batch003.bound154 rho hr0 hr1
    norm_num [Batch003.certificate154,envelope77,inputs77,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound155 rho hr0 hr1
    norm_num [Batch003.certificate155,envelope77,inputs77,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs78 : RatMajorityInputs := ⟨(21709881403463438583158383/25000000000000000000000),(207116306525717/50000000000000),(200692790699323307/200000000000000000),(217981886684020403/1000000000000000000),(207116306525717/100000000000000),(63019552360187821/500000000000000000),25⟩
theorem inputs_valid78 : inputs78.Valid := by decide +kernel
def envelope78 : RatMajorityEnvelope := ⟨39,0,inputs78,(2466328067/2054740000),(181801782849014241/250000000000000000)⟩
theorem envelope_sound78 : envelope78.Sound := by
  apply rat_majority_inputs_envelopes inputs78 inputs_valid78
  · norm_num [envelope78]
  · intro rho hr0 hr1
    have hh := Batch003.bound156 rho hr0 hr1
    norm_num [Batch003.certificate156,envelope78,inputs78,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound157 rho hr0 hr1
    norm_num [Batch003.certificate157,envelope78,inputs78,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs79 : RatMajorityInputs := ⟨(21709881403463438583158383/25000000000000000000000),(123271369147131/25000000000000),(200692790699323307/200000000000000000),(32649459506020209/250000000000000000),(123271369147131/50000000000000),(1327695606329489/15625000000000000),27⟩
theorem inputs_valid79 : inputs79.Valid := by decide +kernel
def envelope79 : RatMajorityEnvelope := ⟨39,1,inputs79,1,(135483004571667637/250000000000000000)⟩
theorem envelope_sound79 : envelope79.Sound := by
  apply rat_majority_inputs_envelopes inputs79 inputs_valid79
  · norm_num [envelope79]
  · intro rho hr0 hr1
    have hh := Batch003.bound158 rho hr0 hr1
    norm_num [Batch003.certificate158,envelope79,inputs79,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch003.bound159 rho hr0 hr1
    norm_num [Batch003.certificate159,envelope79,inputs79,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope60,envelope61,envelope62,envelope63,envelope64,envelope65,envelope66,envelope67,envelope68,envelope69,envelope70,envelope71,envelope72,envelope73,envelope74,envelope75,envelope76,envelope77,envelope78,envelope79]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound60
  · exact envelope_sound61
  · exact envelope_sound62
  · exact envelope_sound63
  · exact envelope_sound64
  · exact envelope_sound65
  · exact envelope_sound66
  · exact envelope_sound67
  · exact envelope_sound68
  · exact envelope_sound69
  · exact envelope_sound70
  · exact envelope_sound71
  · exact envelope_sound72
  · exact envelope_sound73
  · exact envelope_sound74
  · exact envelope_sound75
  · exact envelope_sound76
  · exact envelope_sound77
  · exact envelope_sound78
  · exact envelope_sound79

end Cycle12.MajorityCertificates.Inputs003
