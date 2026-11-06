import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs004

def inputs80 : RatMajorityInputs := ⟨(1286239423306081918293153/1562500000000000000000),(3228678601731/781250000000),(1003654701653779867/1000000000000000000),(54823984302581073/250000000000000000),(3228678601731/1562500000000),(126646656158223723/1000000000000000000),25⟩
theorem inputs_valid80 : inputs80.Valid := by decide +kernel
def envelope80 : RatMajorityEnvelope := ⟨40,0,inputs80,(1230030691/1023840000),(728417410899779319/1000000000000000000)⟩
theorem envelope_sound80 : envelope80.Sound := by
  apply rat_majority_inputs_envelopes inputs80 inputs_valid80
  · norm_num [envelope80]
  · intro rho hr0 hr1
    have hh := Batch004.bound160 rho hr0 hr1
    norm_num [Batch004.certificate160,envelope80,inputs80,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound161 rho hr0 hr1
    norm_num [Batch004.certificate161,envelope80,inputs80,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs81 : RatMajorityInputs := ⟨(1286239423306081918293153/1562500000000000000000),(3846058140303/781250000000),(1003654701653779867/1000000000000000000),(131292921982155601/1000000000000000000),(3846058140303/1562500000000),(85308838791013173/1000000000000000000),27⟩
theorem inputs_valid81 : inputs81.Valid := by decide +kernel
def envelope81 : RatMajorityEnvelope := ⟨40,1,inputs81,1,(542093716749528063/1000000000000000000)⟩
theorem envelope_sound81 : envelope81.Sound := by
  apply rat_majority_inputs_envelopes inputs81 inputs_valid81
  · norm_num [envelope81]
  · intro rho hr0 hr1
    have hh := Batch004.bound162 rho hr0 hr1
    norm_num [Batch004.certificate162,envelope81,inputs81,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound163 rho hr0 hr1
    norm_num [Batch004.certificate163,envelope81,inputs81,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs82 : RatMajorityInputs := ⟨(80843737205847977721227821/100000000000000000000000),(103581313993487/25000000000000),(50186080072063521/50000000000000000),(43571130475271541/200000000000000000),(103581313993487/50000000000000),(3936897971412237/31250000000000000),25⟩
theorem inputs_valid82 : inputs82.Valid := by decide +kernel
def envelope82 : RatMajorityEnvelope := ⟨41,0,inputs82,(614229943/511467500),(145576390117070903/200000000000000000)⟩
theorem envelope_sound82 : envelope82.Sound := by
  apply rat_majority_inputs_envelopes inputs82 inputs_valid82
  · norm_num [envelope82]
  · intro rho hr0 hr1
    have hh := Batch004.bound164 rho hr0 hr1
    norm_num [Batch004.certificate164,envelope82,inputs82,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound165 rho hr0 hr1
    norm_num [Batch004.certificate165,envelope82,inputs82,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs83 : RatMajorityInputs := ⟨(80843737205847977721227821/100000000000000000000000),(49299611924647/10000000000000),(50186080072063521/50000000000000000),(32669073091626067/250000000000000000),(49299611924647/20000000000000),(21252622969882101/250000000000000000),27⟩
theorem inputs_valid83 : inputs83.Valid := by decide +kernel
def envelope83 : RatMajorityEnvelope := ⟨41,1,inputs83,1,(8469660354196163/15625000000000000)⟩
theorem envelope_sound83 : envelope83.Sound := by
  apply rat_majority_inputs_envelopes inputs83 inputs_valid83
  · norm_num [envelope83]
  · intro rho hr0 hr1
    have hh := Batch004.bound166 rho hr0 hr1
    norm_num [Batch004.certificate166,envelope83,inputs83,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound167 rho hr0 hr1
    norm_num [Batch004.certificate167,envelope83,inputs83,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs84 : RatMajorityInputs := ⟨(39500920063683192605311789/50000000000000000000000),(82877697279061/20000000000000),(501904313016493929/500000000000000000),(217769529972287431/1000000000000000000),(82877697279061/40000000000000),(62970456152869793/500000000000000000),25⟩
theorem inputs_valid84 : inputs84.Valid := by decide +kernel
def envelope84 : RatMajorityEnvelope := ⟨42,0,inputs84,(2454000793/2042990000),(145631886685797881/200000000000000000)⟩
theorem envelope_sound84 : envelope84.Sound := by
  apply rat_majority_inputs_envelopes inputs84 inputs_valid84
  · norm_num [envelope84]
  · intro rho hr0 hr1
    have hh := Batch004.bound168 rho hr0 hr1
    norm_num [Batch004.certificate168,envelope84,inputs84,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound169 rho hr0 hr1
    norm_num [Batch004.certificate169,envelope84,inputs84,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs85 : RatMajorityInputs := ⟨(39500920063683192605311789/50000000000000000000000),(61619198943273/12500000000000),(501904313016493929/500000000000000000),(2614272913107071/20000000000000000),(61619198943273/25000000000000),(42514285152572021/500000000000000000),26⟩
theorem inputs_valid85 : inputs85.Valid := by decide +kernel
def envelope85 : RatMajorityEnvelope := ⟨42,1,inputs85,1,(135525514984154667/250000000000000000)⟩
theorem envelope_sound85 : envelope85.Sound := by
  apply rat_majority_inputs_envelopes inputs85 inputs_valid85
  · norm_num [envelope85]
  · intro rho hr0 hr1
    have hh := Batch004.bound170 rho hr0 hr1
    norm_num [Batch004.certificate170,envelope85,inputs85,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound171 rho hr0 hr1
    norm_num [Batch004.certificate171,envelope85,inputs85,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs86 : RatMajorityInputs := ⟨(3089268300411633258714327/4000000000000000000000),(82468055467371/20000000000000),(100389618324802041/100000000000000000),(220573625629742493/1000000000000000000),(82468055467371/40000000000000),(63618652887286693/500000000000000000),25⟩
theorem inputs_valid86 : inputs86.Valid := by decide +kernel
def envelope86 : RatMajorityEnvelope := ⟨43,0,inputs86,(2451898573/2040150000),(729070435054862411/1000000000000000000)⟩
theorem envelope_sound86 : envelope86.Sound := by
  apply rat_majority_inputs_envelopes inputs86 inputs_valid86
  · norm_num [envelope86]
  · intro rho hr0 hr1
    have hh := Batch004.bound172 rho hr0 hr1
    norm_num [Batch004.certificate172,envelope86,inputs86,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound173 rho hr0 hr1
    norm_num [Batch004.certificate173,envelope86,inputs86,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs87 : RatMajorityInputs := ⟨(3089268300411633258714327/4000000000000000000000),(1971495239427/400000000000),(100389618324802041/100000000000000000),(65391872827251371/500000000000000000),(1971495239427/800000000000),(85062495686200217/1000000000000000000),27⟩
theorem inputs_valid87 : inputs87.Valid := by decide +kernel
def envelope87 : RatMajorityEnvelope := ⟨43,1,inputs87,1,(4235543742142811/7812500000000000)⟩
theorem envelope_sound87 : envelope87.Sound := by
  apply rat_majority_inputs_envelopes inputs87 inputs_valid87
  · norm_num [envelope87]
  · intro rho hr0 hr1
    have hh := Batch004.bound174 rho hr0 hr1
    norm_num [Batch004.certificate174,envelope87,inputs87,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound175 rho hr0 hr1
    norm_num [Batch004.certificate175,envelope87,inputs87,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs88 : RatMajorityInputs := ⟨(4720631037979795705435461/6250000000000000000000),(51514591750869/12500000000000),(501992115944308631/500000000000000000),(110440731776539203/500000000000000000),(51514591750869/25000000000000),(127379600537475917/1000000000000000000),25⟩
theorem inputs_valid88 : inputs88.Valid := by decide +kernel
def envelope88 : RatMajorityEnvelope := ⟨44,0,inputs88,(2448892973/2037360000),(364651939985643181/500000000000000000)⟩
theorem envelope_sound88 : envelope88.Sound := by
  apply rat_majority_inputs_envelopes inputs88 inputs_valid88
  · norm_num [envelope88]
  · intro rho hr0 hr1
    have hh := Batch004.bound176 rho hr0 hr1
    norm_num [Batch004.certificate176,envelope88,inputs88,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound177 rho hr0 hr1
    norm_num [Batch004.certificate177,envelope88,inputs88,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs89 : RatMajorityInputs := ⟨(4720631037979795705435461/6250000000000000000000),(3080365136121/625000000000),(501992115944308631/500000000000000000),(5231890807086153/40000000000000000),(3080365136121/1250000000000),(85069040679317169/1000000000000000000),26⟩
theorem inputs_valid89 : inputs89.Valid := by decide +kernel
def envelope89 : RatMajorityEnvelope := ⟨44,1,inputs89,1,(135547827467195379/250000000000000000)⟩
theorem envelope_sound89 : envelope89.Sound := by
  apply rat_majority_inputs_envelopes inputs89 inputs_valid89
  · norm_num [envelope89]
  · intro rho hr0 hr1
    have hh := Batch004.bound178 rho hr0 hr1
    norm_num [Batch004.certificate178,envelope89,inputs89,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound179 rho hr0 hr1
    norm_num [Batch004.certificate179,envelope89,inputs89,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs90 : RatMajorityInputs := ⟨(147785743047224424666441/200000000000000000000),(20633886510321/5000000000000),(502036394485920073/500000000000000000),(22010959549603713/100000000000000000),(20633886510321/10000000000000),(127022803816467967/1000000000000000000),25⟩
theorem inputs_valid90 : inputs90.Valid := by decide +kernel
def envelope90 : RatMajorityEnvelope := ⟨45,0,inputs90,(489104363/406920000),(729250320145705837/1000000000000000000)⟩
theorem envelope_sound90 : envelope90.Sound := by
  apply rat_majority_inputs_envelopes inputs90 inputs_valid90
  · norm_num [envelope90]
  · intro rho hr0 hr1
    have hh := Batch004.bound180 rho hr0 hr1
    norm_num [Batch004.certificate180,envelope90,inputs90,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound181 rho hr0 hr1
    norm_num [Batch004.certificate181,envelope90,inputs90,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs91 : RatMajorityInputs := ⟨(147785743047224424666441/200000000000000000000),(6160553203611/1250000000000),(502036394485920073/500000000000000000),(26161944253206631/200000000000000000),(6160553203611/2500000000000),(5317191632257953/62500000000000000),26⟩
theorem inputs_valid91 : inputs91.Valid := by decide +kernel
def envelope91 : RatMajorityEnvelope := ⟨45,1,inputs91,1,(542233137317967521/1000000000000000000)⟩
theorem envelope_sound91 : envelope91.Sound := by
  apply rat_majority_inputs_envelopes inputs91 inputs_valid91
  · norm_num [envelope91]
  · intro rho hr0 hr1
    have hh := Batch004.bound182 rho hr0 hr1
    norm_num [Batch004.certificate182,envelope91,inputs91,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound183 rho hr0 hr1
    norm_num [Batch004.certificate183,envelope91,inputs91,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs92 : RatMajorityInputs := ⟨(14463517910288120822873207/20000000000000000000000),(103185660258093/25000000000000),(25104044821896923/25000000000000000),(220020429358793147/1000000000000000000),(103185660258093/50000000000000),(25396316946037959/200000000000000000),25⟩
theorem inputs_valid92 : inputs92.Valid := by decide +kernel
def envelope92 : RatMajorityEnvelope := ⟨46,0,inputs92,(348908201/290270000),(729331423813769287/1000000000000000000)⟩
theorem envelope_sound92 : envelope92.Sound := by
  apply rat_majority_inputs_envelopes inputs92 inputs_valid92
  · norm_num [envelope92]
  · intro rho hr0 hr1
    have hh := Batch004.bound184 rho hr0 hr1
    norm_num [Batch004.certificate184,envelope92,inputs92,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound185 rho hr0 hr1
    norm_num [Batch004.certificate185,envelope92,inputs92,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs93 : RatMajorityInputs := ⟨(14463517910288120822873207/20000000000000000000000),(492850195858587/100000000000000),(25104044821896923/25000000000000000),(65402250207425993/500000000000000000),(492850195858587/200000000000000),(85072539607215751/1000000000000000000),26⟩
theorem inputs_valid93 : inputs93.Valid := by decide +kernel
def envelope93 : RatMajorityEnvelope := ⟨46,1,inputs93,1,(542273280765621441/1000000000000000000)⟩
theorem envelope_sound93 : envelope93.Sound := by
  apply rat_majority_inputs_envelopes inputs93 inputs_valid93
  · norm_num [envelope93]
  · intro rho hr0 hr1
    have hh := Batch004.bound186 rho hr0 hr1
    norm_num [Batch004.certificate186,envelope93,inputs93,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound187 rho hr0 hr1
    norm_num [Batch004.certificate187,envelope93,inputs93,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs94 : RatMajorityInputs := ⟨(4425034314187791942042747/6250000000000000000000),(206525588603947/50000000000000),(1004251262146736551/1000000000000000000),(857800819615257/3906250000000000),(206525588603947/100000000000000),(126785843689417957/1000000000000000000),25⟩
theorem inputs_valid94 : inputs94.Valid := by decide +kernel
def envelope94 : RatMajorityEnvelope := ⟨47,0,inputs94,(609764993/507302500),(729303926947670141/1000000000000000000)⟩
theorem envelope_sound94 : envelope94.Sound := by
  apply rat_majority_inputs_envelopes inputs94 inputs_valid94
  · norm_num [envelope94]
  · intro rho hr0 hr1
    have hh := Batch004.bound188 rho hr0 hr1
    norm_num [Batch004.certificate188,envelope94,inputs94,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound189 rho hr0 hr1
    norm_num [Batch004.certificate189,envelope94,inputs94,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs95 : RatMajorityInputs := ⟨(4425034314187791942042747/6250000000000000000000),(15401677317349/3125000000000),(1004251262146736551/1000000000000000000),(130801443095618039/1000000000000000000),(15401677317349/6250000000000),(85071060082463089/1000000000000000000),26⟩
theorem inputs_valid95 : inputs95.Valid := by decide +kernel
def envelope95 : RatMajorityEnvelope := ⟨47,1,inputs95,1,(271156934251933683/500000000000000000)⟩
theorem envelope_sound95 : envelope95.Sound := by
  apply rat_majority_inputs_envelopes inputs95 inputs_valid95
  · norm_num [envelope95]
  · intro rho hr0 hr1
    have hh := Batch004.bound190 rho hr0 hr1
    norm_num [Batch004.certificate190,envelope95,inputs95,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound191 rho hr0 hr1
    norm_num [Batch004.certificate191,envelope95,inputs95,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs96 : RatMajorityInputs := ⟨(69339310544881911820467363/100000000000000000000000),(41313244828947/10000000000000),(1004341154464232573/1000000000000000000),(10974279476725013/50000000000000000),(41313244828947/20000000000000),(25346866808502543/200000000000000000),25⟩
theorem inputs_valid96 : inputs96.Valid := by decide +kernel
def envelope96 : RatMajorityEnvelope := ⟨48,0,inputs96,(304484473/253321250),(729337185801126103/1000000000000000000)⟩
theorem envelope_sound96 : envelope96.Sound := by
  apply rat_majority_inputs_envelopes inputs96 inputs_valid96
  · norm_num [envelope96]
  · intro rho hr0 hr1
    have hh := Batch004.bound192 rho hr0 hr1
    norm_num [Batch004.certificate192,envelope96,inputs96,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound193 rho hr0 hr1
    norm_num [Batch004.certificate193,envelope96,inputs96,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs97 : RatMajorityInputs := ⟨(69339310544881911820467363/100000000000000000000000),(492883782088607/100000000000000),(1004341154464232573/1000000000000000000),(26154996351648269/200000000000000000),(492883782088607/200000000000000),(85058254477290303/1000000000000000000),27⟩
theorem inputs_valid97 : inputs97.Valid := by decide +kernel
def envelope97 : RatMajorityEnvelope := ⟨48,1,inputs97,1,(271176076625203987/500000000000000000)⟩
theorem envelope_sound97 : envelope97.Sound := by
  apply rat_majority_inputs_envelopes inputs97 inputs_valid97
  · norm_num [envelope97]
  · intro rho hr0 hr1
    have hh := Batch004.bound194 rho hr0 hr1
    norm_num [Batch004.certificate194,envelope97,inputs97,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound195 rho hr0 hr1
    norm_num [Batch004.certificate195,envelope97,inputs97,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs98 : RatMajorityInputs := ⟨(67931238867496234962287673/100000000000000000000000),(206569545510653/50000000000000),(502215723717135781/500000000000000000),(109738242303721149/500000000000000000),(206569545510653/100000000000000),(126730124801437959/1000000000000000000),25⟩
theorem inputs_valid98 : inputs98.Valid := by decide +kernel
def envelope98 : RatMajorityEnvelope := ⟨49,0,inputs98,(1216402679/1011985000),(364705140663476863/500000000000000000)⟩
theorem envelope_sound98 : envelope98.Sound := by
  apply rat_majority_inputs_envelopes inputs98 inputs_valid98
  · norm_num [envelope98]
  · intro rho hr0 hr1
    have hh := Batch004.bound196 rho hr0 hr1
    norm_num [Batch004.certificate196,envelope98,inputs98,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound197 rho hr0 hr1
    norm_num [Batch004.certificate197,envelope98,inputs98,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs99 : RatMajorityInputs := ⟨(67931238867496234962287673/100000000000000000000000),(492831933205781/100000000000000),(502215723717135781/500000000000000000),(130820553780338919/1000000000000000000),(492831933205781/200000000000000),(85080308213169593/1000000000000000000),26⟩
theorem inputs_valid99 : inputs99.Valid := by decide +kernel
def envelope99 : RatMajorityEnvelope := ⟨49,1,inputs99,1,(54239830508883339/100000000000000000)⟩
theorem envelope_sound99 : envelope99.Sound := by
  apply rat_majority_inputs_envelopes inputs99 inputs_valid99
  · norm_num [envelope99]
  · intro rho hr0 hr1
    have hh := Batch004.bound198 rho hr0 hr1
    norm_num [Batch004.certificate198,envelope99,inputs99,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch004.bound199 rho hr0 hr1
    norm_num [Batch004.certificate199,envelope99,inputs99,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope80,envelope81,envelope82,envelope83,envelope84,envelope85,envelope86,envelope87,envelope88,envelope89,envelope90,envelope91,envelope92,envelope93,envelope94,envelope95,envelope96,envelope97,envelope98,envelope99]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound80
  · exact envelope_sound81
  · exact envelope_sound82
  · exact envelope_sound83
  · exact envelope_sound84
  · exact envelope_sound85
  · exact envelope_sound86
  · exact envelope_sound87
  · exact envelope_sound88
  · exact envelope_sound89
  · exact envelope_sound90
  · exact envelope_sound91
  · exact envelope_sound92
  · exact envelope_sound93
  · exact envelope_sound94
  · exact envelope_sound95
  · exact envelope_sound96
  · exact envelope_sound97
  · exact envelope_sound98
  · exact envelope_sound99

end Cycle12.MajorityCertificates.Inputs004
