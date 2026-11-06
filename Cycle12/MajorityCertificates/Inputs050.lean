import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch050

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs050

def inputs1000 : RatMajorityInputs := ⟨(165374181681685886025689/2500000000000000000),(17574246439/4000000000),(1000045353298101759/1000000000000000000),(46477199644940593/250000000000000000),(17574246439/8000000000),(27790107526188481/250000000000000000),26⟩
theorem inputs_valid1000 : inputs1000.Valid := by decide +kernel
def envelope1000 : RatMajorityEnvelope := ⟨471,2,inputs1000,1,(273418181312679157/500000000000000000)⟩
theorem envelope_sound1000 : envelope1000.Sound := by
  apply rat_majority_inputs_envelopes inputs1000 inputs_valid1000
  · norm_num [envelope1000]
  · intro rho hr0 hr1
    have hh := Batch050.bound2000 rho hr0 hr1
    norm_num [Batch050.certificate2000,envelope1000,inputs1000,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2001 rho hr0 hr1
    norm_num [Batch050.certificate2001,envelope1000,inputs1000,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1001 : RatMajorityInputs := ⟨(1301858874654362467065837/20000000000000000000),(17950490839/4000000000),(25001152239924191/25000000000000000),(87487522512970189/500000000000000000),(17950490839/8000000000),(106053525488976817/1000000000000000000),25⟩
theorem inputs_valid1001 : inputs1001.Valid := by decide +kernel
def envelope1001 : RatMajorityEnvelope := ⟨472,0,inputs1001,(1422574443/1175000000),(730593172656412379/1000000000000000000)⟩
theorem envelope_sound1001 : envelope1001.Sound := by
  apply rat_majority_inputs_envelopes inputs1001 inputs_valid1001
  · norm_num [envelope1001]
  · intro rho hr0 hr1
    have hh := Batch050.bound2002 rho hr0 hr1
    norm_num [Batch050.certificate2002,envelope1001,inputs1001,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2003 rho hr0 hr1
    norm_num [Batch050.certificate2003,envelope1001,inputs1001,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1002 : RatMajorityInputs := ⟨(1301858874654362467065837/20000000000000000000),(3281250339/800000000),(25001152239924191/25000000000000000),(22359636356260689/100000000000000000),(3281250339/1600000000),(25726868293303621/200000000000000000),25⟩
theorem inputs_valid1002 : inputs1002.Valid := by decide +kernel
def envelope1002 : RatMajorityEnvelope := ⟨472,1,inputs1002,1,(275898124452450021/500000000000000000)⟩
theorem envelope_sound1002 : envelope1002.Sound := by
  apply rat_majority_inputs_envelopes inputs1002 inputs_valid1002
  · norm_num [envelope1002]
  · intro rho hr0 hr1
    have hh := Batch050.bound2004 rho hr0 hr1
    norm_num [Batch050.certificate2004,envelope1002,inputs1002,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2005 rho hr0 hr1
    norm_num [Batch050.certificate2005,envelope1002,inputs1002,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1003 : RatMajorityInputs := ⟨(1301858874654362467065837/20000000000000000000),(88064475139/20000000000),(25001152239924191/25000000000000000),(184759496189190169/1000000000000000000),(88064475139/40000000000),(55312350500417877/500000000000000000),26⟩
theorem inputs_valid1003 : inputs1003.Valid := by decide +kernel
def envelope1003 : RatMajorityEnvelope := ⟨472,2,inputs1003,1,(273346432785170621/500000000000000000)⟩
theorem envelope_sound1003 : envelope1003.Sound := by
  apply rat_majority_inputs_envelopes inputs1003 inputs_valid1003
  · norm_num [envelope1003]
  · intro rho hr0 hr1
    have hh := Batch050.bound2006 rho hr0 hr1
    norm_num [Batch050.certificate2006,envelope1003,inputs1003,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2007 rho hr0 hr1
    norm_num [Batch050.certificate2007,envelope1003,inputs1003,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1004 : RatMajorityInputs := ⟨(1254828833533928687375409/20000000000000000000),(89792788843/20000000000),(500023908532324389/500000000000000000),(87373384997226391/500000000000000000),(89792788843/40000000000),(105946638598103787/1000000000000000000),26⟩
theorem inputs_valid1004 : inputs1004.Valid := by decide +kernel
def envelope1004 : RatMajorityEnvelope := ⟨473,0,inputs1004,(2846382657/2350000000),(146210282378992557/200000000000000000)⟩
theorem envelope_sound1004 : envelope1004.Sound := by
  apply rat_majority_inputs_envelopes inputs1004 inputs_valid1004
  · norm_num [envelope1004]
  · intro rho hr0 hr1
    have hh := Batch050.bound2008 rho hr0 hr1
    norm_num [Batch050.certificate2008,envelope1004,inputs1004,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2009 rho hr0 hr1
    norm_num [Batch050.certificate2009,envelope1004,inputs1004,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1005 : RatMajorityInputs := ⟨(1254828833533928687375409/20000000000000000000),(81960172479/20000000000),(500023908532324389/500000000000000000),(56022877051155591/250000000000000000),(81960172479/40000000000),(25168583442273/195312500000000),26⟩
theorem inputs_valid1005 : inputs1005.Valid := by decide +kernel
def envelope1005 : RatMajorityEnvelope := ⟨473,1,inputs1005,1,(13796634774855699/25000000000000000)⟩
theorem envelope_sound1005 : envelope1005.Sound := by
  apply rat_majority_inputs_envelopes inputs1005 inputs_valid1005
  · norm_num [envelope1005]
  · intro rho hr0 hr1
    have hh := Batch050.bound2010 rho hr0 hr1
    norm_num [Batch050.certificate2010,envelope1005,inputs1005,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2011 rho hr0 hr1
    norm_num [Batch050.certificate2011,envelope1005,inputs1005,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1006 : RatMajorityInputs := ⟨(1254828833533928687375409/20000000000000000000),(11023348839/2500000000),(500023908532324389/500000000000000000),(184035155974931429/1000000000000000000),(11023348839/5000000000),(11028693959026161/100000000000000000),25⟩
theorem inputs_valid1006 : inputs1006.Valid := by decide +kernel
def envelope1006 : RatMajorityEnvelope := ⟨473,2,inputs1006,1,(546603184474967013/1000000000000000000)⟩
theorem envelope_sound1006 : envelope1006.Sound := by
  apply rat_majority_inputs_envelopes inputs1006 inputs_valid1006
  · norm_num [envelope1006]
  · intro rho hr0 hr1
    have hh := Batch050.bound2012 rho hr0 hr1
    norm_num [Batch050.certificate2012,envelope1006,inputs1006,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2013 rho hr0 hr1
    norm_num [Batch050.certificate2013,envelope1006,inputs1006,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1007 : RatMajorityInputs := ⟨(243418646401188670479481/4000000000000000000),(89961203191/20000000000),(100004929967488637/100000000000000000),(86898189514036371/500000000000000000),(89961203191/40000000000),(105501502994408197/1000000000000000000),25⟩
theorem inputs_valid1007 : inputs1007.Valid := by decide +kernel
def envelope1007 : RatMajorityEnvelope := ⟨474,0,inputs1007,(2848664371/2350000000),(22870367767652393/31250000000000000)⟩
theorem envelope_sound1007 : envelope1007.Sound := by
  apply rat_majority_inputs_envelopes inputs1007 inputs_valid1007
  · norm_num [envelope1007]
  · intro rho hr0 hr1
    have hh := Batch050.bound2014 rho hr0 hr1
    norm_num [Batch050.certificate2014,envelope1007,inputs1007,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2015 rho hr0 hr1
    norm_num [Batch050.certificate2015,envelope1007,inputs1007,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1008 : RatMajorityInputs := ⟨(243418646401188670479481/4000000000000000000),(40948543623/10000000000),(100004929967488637/100000000000000000),(44906335865073727/200000000000000000),(40948543623/20000000000),(129066541613753169/1000000000000000000),25⟩
theorem inputs_valid1008 : inputs1008.Valid := by decide +kernel
def envelope1008 : RatMajorityEnvelope := ⟨474,1,inputs1008,1,(34495431803370447/62500000000000000)⟩
theorem envelope_sound1008 : envelope1008.Sound := by
  apply rat_majority_inputs_envelopes inputs1008 inputs_valid1008
  · norm_num [envelope1008]
  · intro rho hr0 hr1
    have hh := Batch050.bound2016 rho hr0 hr1
    norm_num [Batch050.certificate2016,envelope1008,inputs1008,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2017 rho hr0 hr1
    norm_num [Batch050.certificate2017,envelope1008,inputs1008,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1009 : RatMajorityInputs := ⟨(243418646401188670479481/4000000000000000000),(88573318007/20000000000),(100004929967488637/100000000000000000),(181762040227369181/1000000000000000000),(88573318007/40000000000),(109226349370668679/1000000000000000000),25⟩
theorem inputs_valid1009 : inputs1009.Valid := by decide +kernel
def envelope1009 : RatMajorityEnvelope := ⟨474,2,inputs1009,1,(273160576397673219/500000000000000000)⟩
theorem envelope_sound1009 : envelope1009.Sound := by
  apply rat_majority_inputs_envelopes inputs1009 inputs_valid1009
  · norm_num [envelope1009]
  · intro rho hr0 hr1
    have hh := Batch050.bound2018 rho hr0 hr1
    norm_num [Batch050.certificate2018,envelope1009,inputs1009,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2019 rho hr0 hr1
    norm_num [Batch050.certificate2019,envelope1009,inputs1009,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1010 : RatMajorityInputs := ⟨(590801449109453439300851/10000000000000000000),(90131445369/20000000000),(40002031219450759/40000000000000000),(43210044970657509/250000000000000000),(90131445369/40000000000),(105053437026041793/1000000000000000000),25⟩
theorem inputs_valid1010 : inputs1010.Valid := by decide +kernel
def envelope1010 : RatMajorityEnvelope := ⟨475,0,inputs1010,(2850948441/2350000000),(366326679764180567/500000000000000000)⟩
theorem envelope_sound1010 : envelope1010.Sound := by
  apply rat_majority_inputs_envelopes inputs1010 inputs_valid1010
  · norm_num [envelope1010]
  · intro rho hr0 hr1
    have hh := Batch050.bound2020 rho hr0 hr1
    norm_num [Batch050.certificate2020,envelope1010,inputs1010,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2021 rho hr0 hr1
    norm_num [Batch050.certificate2021,envelope1010,inputs1010,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1011 : RatMajorityInputs := ⟨(590801449109453439300851/10000000000000000000),(8183186403/2000000000),(40002031219450759/40000000000000000),(224987515430235997/1000000000000000000),(8183186403/4000000000),(129277166660673613/1000000000000000000),25⟩
theorem inputs_valid1011 : inputs1011.Valid := by decide +kernel
def envelope1011 : RatMajorityEnvelope := ⟨475,1,inputs1011,1,(110398133457008629/200000000000000000)⟩
theorem envelope_sound1011 : envelope1011.Sound := by
  apply rat_majority_inputs_envelopes inputs1011 inputs_valid1011
  · norm_num [envelope1011]
  · intro rho hr0 hr1
    have hh := Batch050.bound2022 rho hr0 hr1
    norm_num [Batch050.certificate2022,envelope1011,inputs1011,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2023 rho hr0 hr1
    norm_num [Batch050.certificate2023,envelope1011,inputs1011,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1012 : RatMajorityInputs := ⟨(590801449109453439300851/10000000000000000000),(22240022637/5000000000),(40002031219450759/40000000000000000),(44877867323314633/250000000000000000),(22240022637/10000000000),(27043823807124047/250000000000000000),25⟩
theorem inputs_valid1012 : inputs1012.Valid := by decide +kernel
def envelope1012 : RatMajorityEnvelope := ⟨475,2,inputs1012,1,(109208707424157671/200000000000000000)⟩
theorem envelope_sound1012 : envelope1012.Sound := by
  apply rat_majority_inputs_envelopes inputs1012 inputs_valid1012
  · norm_num [envelope1012]
  · intro rho hr0 hr1
    have hh := Batch050.bound2024 rho hr0 hr1
    norm_num [Batch050.certificate2024,envelope1012,inputs1012,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2025 rho hr0 hr1
    norm_num [Batch050.certificate2025,envelope1012,inputs1012,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1013 : RatMajorityInputs := ⟨(2296381773595009212367/40000000000000000),(1806393159/400000000),(1000052258243293749/1000000000000000000),(34357660489670277/200000000000000000),(1806393159/800000000),(52280144340896653/500000000000000000),25⟩
theorem inputs_valid1013 : inputs1013.Valid := by decide +kernel
def envelope1013 : RatMajorityEnvelope := ⟨476,0,inputs1013,(568894161/470000000),(730054042456525011/1000000000000000000)⟩
theorem envelope_sound1013 : envelope1013.Sound := by
  apply rat_majority_inputs_envelopes inputs1013 inputs_valid1013
  · norm_num [envelope1013]
  · intro rho hr0 hr1
    have hh := Batch050.bound2026 rho hr0 hr1
    norm_num [Batch050.certificate2026,envelope1013,inputs1013,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2027 rho hr0 hr1
    norm_num [Batch050.certificate2027,envelope1013,inputs1013,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1014 : RatMajorityInputs := ⟨(2296381773595009212367/40000000000000000),(81798507049/20000000000),(1000052258243293749/1000000000000000000),(1759538567940577/7812500000000000),(81798507049/40000000000),(129385019024589821/1000000000000000000),25⟩
theorem inputs_valid1014 : inputs1014.Valid := by decide +kernel
def envelope1014 : RatMajorityEnvelope := ⟨476,1,inputs1014,1,(552023635437420207/1000000000000000000)⟩
theorem envelope_sound1014 : envelope1014.Sound := by
  apply rat_majority_inputs_envelopes inputs1014 inputs_valid1014
  · norm_num [envelope1014]
  · intro rho hr0 hr1
    have hh := Batch050.bound2028 rho hr0 hr1
    norm_num [Batch050.certificate2028,envelope1014,inputs1014,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2029 rho hr0 hr1
    norm_num [Batch050.certificate2029,envelope1014,inputs1014,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1015 : RatMajorityInputs := ⟨(2296381773595009212367/40000000000000000),(44713631279/10000000000),(1000052258243293749/1000000000000000000),(35364964101164717/200000000000000000),(44713631279/20000000000),(106919232719323997/1000000000000000000),25⟩
theorem inputs_valid1015 : inputs1015.Valid := by decide +kernel
def envelope1015 : RatMajorityEnvelope := ⟨476,2,inputs1015,1,(545714090904262353/1000000000000000000)⟩
theorem envelope_sound1015 : envelope1015.Sound := by
  apply rat_majority_inputs_envelopes inputs1015 inputs_valid1015
  · norm_num [envelope1015]
  · intro rho hr0 hr1
    have hh := Batch050.bound2030 rho hr0 hr1
    norm_num [Batch050.certificate2030,envelope1015,inputs1015,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2031 rho hr0 hr1
    norm_num [Batch050.certificate2031,envelope1015,inputs1015,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1016 : RatMajorityInputs := ⟨(558352992445663978501721/10000000000000000000),(18095368621/4000000000),(200010746339373559/200000000000000000),(170914046158617307/1000000000000000000),(18095368621/8000000000),(52075105902439561/500000000000000000),25⟩
theorem inputs_valid1016 : inputs1016.Valid := by decide +kernel
def envelope1016 : RatMajorityEnvelope := ⟨477,0,inputs1016,(1427762549/1175000000),(146852230757638411/200000000000000000)⟩
theorem envelope_sound1016 : envelope1016.Sound := by
  apply rat_majority_inputs_envelopes inputs1016 inputs_valid1016
  · norm_num [envelope1016]
  · intro rho hr0 hr1
    have hh := Batch050.bound2032 rho hr0 hr1
    norm_num [Batch050.certificate2032,envelope1016,inputs1016,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2033 rho hr0 hr1
    norm_num [Batch050.certificate2033,envelope1016,inputs1016,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1017 : RatMajorityInputs := ⟨(558352992445663978501721/10000000000000000000),(81694123621/20000000000),(200010746339373559/200000000000000000),(225952664119028751/1000000000000000000),(81694123621/40000000000),(12972310125544827/100000000000000000),25⟩
theorem inputs_valid1017 : inputs1017.Valid := by decide +kernel
def envelope1017 : RatMajorityEnvelope := ⟨477,1,inputs1017,1,(138031459100630113/250000000000000000)⟩
theorem envelope_sound1017 : envelope1017.Sound := by
  apply rat_majority_inputs_envelopes inputs1017 inputs_valid1017
  · norm_num [envelope1017]
  · intro rho hr0 hr1
    have hh := Batch050.bound2034 rho hr0 hr1
    norm_num [Batch050.certificate2034,envelope1017,inputs1017,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2035 rho hr0 hr1
    norm_num [Batch050.certificate2035,envelope1017,inputs1017,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1018 : RatMajorityInputs := ⟨(558352992445663978501721/10000000000000000000),(8974056343/2000000000),(200010746339373559/200000000000000000),(175042389856415349/1000000000000000000),(8974056343/4000000000),(53042528307042439/500000000000000000),25⟩
theorem inputs_valid1018 : inputs1018.Valid := by decide +kernel
def envelope1018 : RatMajorityEnvelope := ⟨477,2,inputs1018,1,(54549697992638711/100000000000000000)⟩
theorem envelope_sound1018 : envelope1018.Sound := by
  apply rat_majority_inputs_envelopes inputs1018 inputs_valid1018
  · norm_num [envelope1018]
  · intro rho hr0 hr1
    have hh := Batch050.bound2036 rho hr0 hr1
    norm_num [Batch050.certificate2036,envelope1018,inputs1018,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2037 rho hr0 hr1
    norm_num [Batch050.certificate2037,envelope1018,inputs1018,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1019 : RatMajorityInputs := ⟨(1087010969629655165484447/20000000000000000000),(45325953953/10000000000),(1000055199604832851/1000000000000000000),(84972422956749547/500000000000000000),(45325953953/20000000000),(51847690968527057/500000000000000000),25⟩
theorem inputs_valid1019 : inputs1019.Valid := by decide +kernel
def envelope1019 : RatMajorityEnvelope := ⟨478,0,inputs1019,(2857818031/2350000000),(735067565987292801/1000000000000000000)⟩
theorem envelope_sound1019 : envelope1019.Sound := by
  apply rat_majority_inputs_envelopes inputs1019 inputs_valid1019
  · norm_num [envelope1019]
  · intro rho hr0 hr1
    have hh := Batch050.bound2038 rho hr0 hr1
    norm_num [Batch050.certificate2038,envelope1019,inputs1019,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch050.bound2039 rho hr0 hr1
    norm_num [Batch050.certificate2039,envelope1019,inputs1019,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope1000,envelope1001,envelope1002,envelope1003,envelope1004,envelope1005,envelope1006,envelope1007,envelope1008,envelope1009,envelope1010,envelope1011,envelope1012,envelope1013,envelope1014,envelope1015,envelope1016,envelope1017,envelope1018,envelope1019]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound1000
  · exact envelope_sound1001
  · exact envelope_sound1002
  · exact envelope_sound1003
  · exact envelope_sound1004
  · exact envelope_sound1005
  · exact envelope_sound1006
  · exact envelope_sound1007
  · exact envelope_sound1008
  · exact envelope_sound1009
  · exact envelope_sound1010
  · exact envelope_sound1011
  · exact envelope_sound1012
  · exact envelope_sound1013
  · exact envelope_sound1014
  · exact envelope_sound1015
  · exact envelope_sound1016
  · exact envelope_sound1017
  · exact envelope_sound1018
  · exact envelope_sound1019

end Cycle12.MajorityCertificates.Inputs050
