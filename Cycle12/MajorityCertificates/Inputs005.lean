import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs005

def inputs100 : RatMajorityInputs := ⟨(3328692713201898370874769/5000000000000000000000),(413626719487379/100000000000000),(1004522118512091303/1000000000000000000),(109404481753331043/500000000000000000),(413626719487379/200000000000000),(252843030179413/2000000000000000),25⟩
theorem inputs_valid100 : inputs100.Valid := by decide +kernel
def envelope100 : RatMajorityEnvelope := ⟨50,0,inputs100,(303662277/252676250),(729200858313781183/1000000000000000000)⟩
theorem envelope_sound100 : envelope100.Sound := by
  apply rat_majority_inputs_envelopes inputs100 inputs_valid100
  · norm_num [envelope100]
  · intro rho hr0 hr1
    have hh := Batch005.bound200 rho hr0 hr1
    norm_num [Batch005.certificate200,envelope100,inputs100,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound201 rho hr0 hr1
    norm_num [Batch005.certificate201,envelope100,inputs100,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs101 : RatMajorityInputs := ⟨(3328692713201898370874769/5000000000000000000000),(246431627148049/50000000000000),(1004522118512091303/1000000000000000000),(130793022763385317/1000000000000000000),(246431627148049/100000000000000),(3402679408653403/40000000000000000),26⟩
theorem inputs_valid101 : inputs101.Valid := by decide +kernel
def envelope101 : RatMajorityEnvelope := ⟨50,1,inputs101,1,(108487366714690953/200000000000000000)⟩
theorem envelope_sound101 : envelope101.Sound := by
  apply rat_majority_inputs_envelopes inputs101 inputs_valid101
  · norm_num [envelope101]
  · intro rho hr0 hr1
    have hh := Batch005.bound202 rho hr0 hr1
    norm_num [Batch005.certificate202,envelope101,inputs101,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound203 rho hr0 hr1
    norm_num [Batch005.certificate203,envelope101,inputs101,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs102 : RatMajorityInputs := ⟨(528803890093883318482117/800000000000000000000),(16575148292793/4000000000000),(125569327198973759/125000000000000000),(43556569525819299/200000000000000000),(16575148292793/8000000000000),(125947070384726447/1000000000000000000),25⟩
theorem inputs_valid102 : inputs102.Valid := by decide +kernel
def envelope102 : RatMajorityEnvelope := ⟨51,0,inputs102,(151739256/126296875),(22775413880068091/31250000000000000)⟩
theorem envelope_sound102 : envelope102.Sound := by
  apply rat_majority_inputs_envelopes inputs102 inputs_valid102
  · norm_num [envelope102]
  · intro rho hr0 hr1
    have hh := Batch005.bound204 rho hr0 hr1
    norm_num [Batch005.certificate204,envelope102,inputs102,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound205 rho hr0 hr1
    norm_num [Batch005.certificate205,envelope102,inputs102,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs103 : RatMajorityInputs := ⟨(528803890093883318482117/800000000000000000000),(19730859578669/4000000000000),(125569327198973759/125000000000000000),(130434655240474511/1000000000000000000),(19730859578669/8000000000000),(21223381407798997/250000000000000000),26⟩
theorem inputs_valid103 : inputs103.Valid := by decide +kernel
def envelope103 : RatMajorityEnvelope := ⟨51,1,inputs103,1,(54241352349893801/100000000000000000)⟩
theorem envelope_sound103 : envelope103.Sound := by
  apply rat_majority_inputs_envelopes inputs103 inputs_valid103
  · norm_num [envelope103]
  · intro rho hr0 hr1
    have hh := Batch005.bound206 rho hr0 hr1
    norm_num [Batch005.certificate206,envelope103,inputs103,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound207 rho hr0 hr1
    norm_num [Batch005.certificate207,envelope103,inputs103,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs104 : RatMajorityInputs := ⟨(32725138099849797084794333/50000000000000000000000),(207195884023117/50000000000000),(1004600026835485771/1000000000000000000),(27220632624910651/125000000000000000),(207195884023117/100000000000000),(25187769170426749/200000000000000000),25⟩
theorem inputs_valid104 : inputs104.Valid := by decide +kernel
def envelope104 : RatMajorityEnvelope := ⟨52,0,inputs104,(2426409839/2019490000),(91109898120746829/125000000000000000)⟩
theorem envelope_sound104 : envelope104.Sound := by
  apply rat_majority_inputs_envelopes inputs104 inputs_valid104
  · norm_num [envelope104]
  · intro rho hr0 hr1
    have hh := Batch005.bound208 rho hr0 hr1
    norm_num [Batch005.certificate208,envelope104,inputs104,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound209 rho hr0 hr1
    norm_num [Batch005.certificate209,envelope104,inputs104,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs105 : RatMajorityInputs := ⟨(32725138099849797084794333/50000000000000000000000),(123332284089399/25000000000000),(1004600026835485771/1000000000000000000),(26076824039515713/200000000000000000),(123332284089399/50000000000000),(33947623967303/400000000000000),26⟩
theorem inputs_valid105 : inputs105.Valid := by decide +kernel
def envelope105 : RatMajorityEnvelope := ⟨52,1,inputs105,1,(271214459839055293/500000000000000000)⟩
theorem envelope_sound105 : envelope105.Sound := by
  apply rat_majority_inputs_envelopes inputs105 inputs_valid105
  · norm_num [envelope105]
  · intro rho hr0 hr1
    have hh := Batch005.bound210 rho hr0 hr1
    norm_num [Batch005.certificate210,envelope105,inputs105,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound211 rho hr0 hr1
    norm_num [Batch005.certificate211,envelope105,inputs105,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs106 : RatMajorityInputs := ⟨(200005072228340030926149/312500000000000000000),(5169206376807/1250000000000),(251176131875265017/250000000000000000),(21893232563209819/100000000000000000),(5169206376807/2500000000000),(63239274980203593/500000000000000000),25⟩
theorem inputs_valid106 : inputs106.Valid := by decide +kernel
def envelope106 : RatMajorityEnvelope := ⟨53,0,inputs106,(2423224117/2016400000),(145857954239871747/200000000000000000)⟩
theorem envelope_sound106 : envelope106.Sound := by
  apply rat_majority_inputs_envelopes inputs106 inputs_valid106
  · norm_num [envelope106]
  · intro rho hr0 hr1
    have hh := Batch005.bound212 rho hr0 hr1
    norm_num [Batch005.certificate212,envelope106,inputs106,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound213 rho hr0 hr1
    norm_num [Batch005.certificate213,envelope106,inputs106,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs107 : RatMajorityInputs := ⟨(200005072228340030926149/312500000000000000000),(2455644596097/500000000000),(251176131875265017/250000000000000000),(66162612197636471/500000000000000000),(2455644596097/1000000000000),(21451966548733347/250000000000000000),27⟩
theorem inputs_valid107 : inputs107.Valid := by decide +kernel
def envelope107 : RatMajorityEnvelope := ⟨53,1,inputs107,1,(542683718097899887/1000000000000000000)⟩
theorem envelope_sound107 : envelope107.Sound := by
  apply rat_majority_inputs_envelopes inputs107 inputs_valid107
  · norm_num [envelope107]
  · intro rho hr0 hr1
    have hh := Batch005.bound214 rho hr0 hr1
    norm_num [Batch005.certificate214,envelope107,inputs107,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound215 rho hr0 hr1
    norm_num [Batch005.certificate215,envelope107,inputs107,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs108 : RatMajorityInputs := ⟨(12556502481831820501989721/20000000000000000000000),(82885501754663/20000000000000),(1004796220582616627/1000000000000000000),(217716393963916477/1000000000000000000),(82885501754663/40000000000000),(5036653685333973/40000000000000000),25⟩
theorem inputs_valid108 : inputs108.Valid := by decide +kernel
def envelope108 : RatMajorityEnvelope := ⟨54,0,inputs108,(2419527359/2013950000),(728880909890272779/1000000000000000000)⟩
theorem envelope_sound108 : envelope108.Sound := by
  apply rat_majority_inputs_envelopes inputs108 inputs_valid108
  · norm_num [envelope108]
  · intro rho hr0 hr1
    have hh := Batch005.bound216 rho hr0 hr1
    norm_num [Batch005.certificate216,envelope108,inputs108,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound217 rho hr0 hr1
    norm_num [Batch005.certificate217,envelope108,inputs108,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs109 : RatMajorityInputs := ⟨(12556502481831820501989721/20000000000000000000000),(19649063016837/4000000000000),(1004796220582616627/1000000000000000000),(132238530333727691/1000000000000000000),(19649063016837/8000000000000),(85765978070985501/1000000000000000000),26⟩
theorem inputs_valid109 : inputs109.Valid := by decide +kernel
def envelope109 : RatMajorityEnvelope := ⟨54,1,inputs109,1,(33919769367404947/62500000000000000)⟩
theorem envelope_sound109 : envelope109.Sound := by
  apply rat_majority_inputs_envelopes inputs109 inputs_valid109
  · norm_num [envelope109]
  · intro rho hr0 hr1
    have hh := Batch005.bound218 rho hr0 hr1
    norm_num [Batch005.certificate218,envelope109,inputs109,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound219 rho hr0 hr1
    norm_num [Batch005.certificate219,envelope109,inputs109,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs110 : RatMajorityInputs := ⟨(779602044704079175220997/1250000000000000000000),(12975181646601/3125000000000),(1004828204316224421/1000000000000000000),(43331766361268201/200000000000000000),(12975181646601/6250000000000),(62713644209762463/500000000000000000),25⟩
theorem inputs_valid110 : inputs110.Valid := by decide +kernel
def envelope110 : RatMajorityEnvelope := ⟨55,0,inputs110,(201490053/167780000),(364186077700955429/500000000000000000)⟩
theorem envelope_sound110 : envelope110.Sound := by
  apply rat_majority_inputs_envelopes inputs110 inputs_valid110
  · norm_num [envelope110]
  · intro rho hr0 hr1
    have hh := Batch005.bound220 rho hr0 hr1
    norm_num [Batch005.certificate220,envelope110,inputs110,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound221 rho hr0 hr1
    norm_num [Batch005.certificate221,envelope110,inputs110,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs111 : RatMajorityInputs := ⟨(779602044704079175220997/1250000000000000000000),(61458469373847/12500000000000),(1004828204316224421/1000000000000000000),(16480937410864353/125000000000000000),(61458469373847/25000000000000),(17115399119813159/200000000000000000),26⟩
theorem inputs_valid111 : inputs111.Valid := by decide +kernel
def envelope111 : RatMajorityEnvelope := ⟨55,1,inputs111,1,(542689167848999299/1000000000000000000)⟩
theorem envelope_sound111 : envelope111.Sound := by
  apply rat_majority_inputs_envelopes inputs111 inputs_valid111
  · norm_num [envelope111]
  · intro rho hr0 hr1
    have hh := Batch005.bound222 rho hr0 hr1
    norm_num [Batch005.certificate222,envelope111,inputs111,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound223 rho hr0 hr1
    norm_num [Batch005.certificate223,envelope111,inputs111,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs112 : RatMajorityInputs := ⟨(7722979885804581279895433/12500000000000000000000),(83045485231633/20000000000000),(200974808071305427/200000000000000000),(216629524154023317/1000000000000000000),(83045485231633/40000000000000),(125413734559149143/1000000000000000000),25⟩
theorem inputs_valid112 : inputs112.Valid := by decide +kernel
def envelope112 : RatMajorityEnvelope := ⟨56,0,inputs112,(2416329033/2012170000),(364169750270954151/500000000000000000)⟩
theorem envelope_sound112 : envelope112.Sound := by
  apply rat_majority_inputs_envelopes inputs112 inputs_valid112
  · norm_num [envelope112]
  · intro rho hr0 hr1
    have hh := Batch005.bound224 rho hr0 hr1
    norm_num [Batch005.certificate224,envelope112,inputs112,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound225 rho hr0 hr1
    norm_num [Batch005.certificate225,envelope112,inputs112,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs113 : RatMajorityInputs := ⟨(7722979885804581279895433/12500000000000000000000),(7682913572693/1562500000000),(200974808071305427/200000000000000000),(131813234983373297/1000000000000000000),(7682913572693/3125000000000),(85560432207959741/1000000000000000000),27⟩
theorem inputs_valid113 : inputs113.Valid := by decide +kernel
def envelope113 : RatMajorityEnvelope := ⟨56,1,inputs113,1,(542706447161716783/1000000000000000000)⟩
theorem envelope_sound113 : envelope113.Sound := by
  apply rat_majority_inputs_envelopes inputs113 inputs_valid113
  · norm_num [envelope113]
  · intro rho hr0 hr1
    have hh := Batch005.bound226 rho hr0 hr1
    norm_num [Batch005.certificate226,envelope113,inputs113,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound227 rho hr0 hr1
    norm_num [Batch005.certificate227,envelope113,inputs113,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs114 : RatMajorityInputs := ⟨(3023441455777068119292143/5000000000000000000000),(207316540173137/50000000000000),(125622555748978741/125000000000000000),(217436648257391719/1000000000000000000),(207316540173137/100000000000000),(15723373065348601/125000000000000000),25⟩
theorem inputs_valid114 : inputs114.Valid := by decide +kernel
def envelope114 : RatMajorityEnvelope := ⟨57,0,inputs114,(2413391677/2009170000),(29151107555377679/40000000000000000)⟩
theorem envelope_sound114 : envelope114.Sound := by
  apply rat_majority_inputs_envelopes inputs114 inputs_valid114
  · norm_num [envelope114]
  · intro rho hr0 hr1
    have hh := Batch005.bound228 rho hr0 hr1
    norm_num [Batch005.certificate228,envelope114,inputs114,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound229 rho hr0 hr1
    norm_num [Batch005.certificate229,envelope114,inputs114,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs115 : RatMajorityInputs := ⟨(3023441455777068119292143/5000000000000000000000),(491315281766721/100000000000000),(125622555748978741/125000000000000000),(33039956244169763/250000000000000000),(491315281766721/200000000000000),(42863973286577737/500000000000000000),27⟩
theorem inputs_valid115 : inputs115.Valid := by decide +kernel
def envelope115 : RatMajorityEnvelope := ⟨57,1,inputs115,1,(678490013188849/1250000000000000)⟩
theorem envelope_sound115 : envelope115.Sound := by
  apply rat_majority_inputs_envelopes inputs115 inputs_valid115
  · norm_num [envelope115]
  · intro rho hr0 hr1
    have hh := Batch005.bound230 rho hr0 hr1
    norm_num [Batch005.certificate230,envelope115,inputs115,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound231 rho hr0 hr1
    norm_num [Batch005.certificate231,envelope115,inputs115,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs116 : RatMajorityInputs := ⟨(12017921023551682343792259/20000000000000000000000),(415339779670309/100000000000000),(125626499988929919/125000000000000000),(216477226765484631/1000000000000000000),(415339779670309/200000000000000),(12534330097690821/100000000000000000),25⟩
theorem inputs_valid116 : inputs116.Valid := by decide +kernel
def envelope116 : RatMajorityEnvelope := ⟨58,0,inputs116,(482326223/401726000),(728199390497361457/1000000000000000000)⟩
theorem envelope_sound116 : envelope116.Sound := by
  apply rat_majority_inputs_envelopes inputs116 inputs_valid116
  · norm_num [envelope116]
  · intro rho hr0 hr1
    have hh := Batch005.bound232 rho hr0 hr1
    norm_num [Batch005.certificate232,envelope116,inputs116,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound233 rho hr0 hr1
    norm_num [Batch005.certificate233,envelope116,inputs116,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs117 : RatMajorityInputs := ⟨(12017921023551682343792259/20000000000000000000000),(122944157349169/25000000000000),(125626499988929919/125000000000000000),(131751157858849909/1000000000000000000),(122944157349169/50000000000000),(42765211276987341/500000000000000000),26⟩
theorem inputs_valid117 : inputs117.Valid := by decide +kernel
def envelope117 : RatMajorityEnvelope := ⟨58,1,inputs117,1,(542762842568877863/1000000000000000000)⟩
theorem envelope_sound117 : envelope117.Sound := by
  apply rat_majority_inputs_envelopes inputs117 inputs_valid117
  · norm_num [envelope117]
  · intro rho hr0 hr1
    have hh := Batch005.bound234 rho hr0 hr1
    norm_num [Batch005.certificate234,envelope117,inputs117,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound235 rho hr0 hr1
    norm_num [Batch005.certificate235,envelope117,inputs117,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs118 : RatMajorityInputs := ⟨(29772015298831546658251363/50000000000000000000000),(207988174546809/50000000000000),(125632262888211321/125000000000000000),(107808009164588369/500000000000000000),(207988174546809/100000000000000),(124944986635902253/1000000000000000000),25⟩
theorem inputs_valid118 : inputs118.Valid := by decide +kernel
def envelope118 : RatMajorityEnvelope := ⟨59,0,inputs118,(481924913/401494000),(45491433205634829/62500000000000000)⟩
theorem envelope_sound118 : envelope118.Sound := by
  apply rat_majority_inputs_envelopes inputs118 inputs_valid118
  · norm_num [envelope118]
  · intro rho hr0 hr1
    have hh := Batch005.bound236 rho hr0 hr1
    norm_num [Batch005.certificate236,envelope118,inputs118,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound237 rho hr0 hr1
    norm_num [Batch005.certificate237,envelope118,inputs118,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs119 : RatMajorityInputs := ⟨(29772015298831546658251363/50000000000000000000000),(245951663750461/50000000000000),(125632262888211321/125000000000000000),(131639122812999457/1000000000000000000),(245951663750461/100000000000000),(3419050280020149/40000000000000000),27⟩
theorem inputs_valid119 : inputs119.Valid := by decide +kernel
def envelope119 : RatMajorityEnvelope := ⟨59,1,inputs119,1,(271385983198156253/500000000000000000)⟩
theorem envelope_sound119 : envelope119.Sound := by
  apply rat_majority_inputs_envelopes inputs119 inputs_valid119
  · norm_num [envelope119]
  · intro rho hr0 hr1
    have hh := Batch005.bound238 rho hr0 hr1
    norm_num [Batch005.certificate238,envelope119,inputs119,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch005.bound239 rho hr0 hr1
    norm_num [Batch005.certificate239,envelope119,inputs119,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope100,envelope101,envelope102,envelope103,envelope104,envelope105,envelope106,envelope107,envelope108,envelope109,envelope110,envelope111,envelope112,envelope113,envelope114,envelope115,envelope116,envelope117,envelope118,envelope119]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound100
  · exact envelope_sound101
  · exact envelope_sound102
  · exact envelope_sound103
  · exact envelope_sound104
  · exact envelope_sound105
  · exact envelope_sound106
  · exact envelope_sound107
  · exact envelope_sound108
  · exact envelope_sound109
  · exact envelope_sound110
  · exact envelope_sound111
  · exact envelope_sound112
  · exact envelope_sound113
  · exact envelope_sound114
  · exact envelope_sound115
  · exact envelope_sound116
  · exact envelope_sound117
  · exact envelope_sound118
  · exact envelope_sound119

end Cycle12.MajorityCertificates.Inputs005
