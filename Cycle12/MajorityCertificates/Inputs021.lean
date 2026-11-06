import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs021

def inputs420 : RatMajorityInputs := ⟨(23231245129774846665758751/20000000000000000000000),(44063657067573/10000000000000),(1002587926292467181/1000000000000000000),(46096766991435601/250000000000000000),(44063657067573/20000000000000),(110451048809171109/1000000000000000000),25⟩
theorem inputs_valid420 : inputs420.Valid := by decide +kernel
def envelope420 : RatMajorityEnvelope := ⟨210,0,inputs420,(623195993/526987500),(707431232967566163/1000000000000000000)⟩
theorem envelope_sound420 : envelope420.Sound := by
  apply rat_majority_inputs_envelopes inputs420 inputs_valid420
  · norm_num [envelope420]
  · intro rho hr0 hr1
    have hh := Batch021.bound840 rho hr0 hr1
    norm_num [Batch021.certificate840,envelope420,inputs420,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound841 rho hr0 hr1
    norm_num [Batch021.certificate841,envelope420,inputs420,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs421 : RatMajorityInputs := ⟨(23231245129774846665758751/20000000000000000000000),(100068482963553/20000000000000),(1002587926292467181/1000000000000000000),(3886372467731149/31250000000000000),(100068482963553/40000000000000),(20486145814931421/250000000000000000),26⟩
theorem inputs_valid421 : inputs421.Valid := by decide +kernel
def envelope421 : RatMajorityEnvelope := ⟨210,1,inputs421,1,(540865717897297179/1000000000000000000)⟩
theorem envelope_sound421 : envelope421.Sound := by
  apply rat_majority_inputs_envelopes inputs421 inputs_valid421
  · norm_num [envelope421]
  · intro rho hr0 hr1
    have hh := Batch021.bound842 rho hr0 hr1
    norm_num [Batch021.certificate842,envelope421,inputs421,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound843 rho hr0 hr1
    norm_num [Batch021.certificate843,envelope421,inputs421,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs422 : RatMajorityInputs := ⟨(2809356770621158271339431/2500000000000000000000),(4418836775187/1000000000000),(250668801021381187/250000000000000000),(182915110656040273/1000000000000000000),(4418836775187/2000000000000),(109764470331670061/1000000000000000000),25⟩
theorem inputs_valid422 : inputs422.Valid := by decide +kernel
def envelope422 : RatMajorityEnvelope := ⟨211,0,inputs422,(621361963/526150000),(352947755515845973/500000000000000000)⟩
theorem envelope_sound422 : envelope422.Sound := by
  apply rat_majority_inputs_envelopes inputs422 inputs_valid422
  · norm_num [envelope422]
  · intro rho hr0 hr1
    have hh := Batch021.bound844 rho hr0 hr1
    norm_num [Batch021.certificate844,envelope422,inputs422,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound845 rho hr0 hr1
    norm_num [Batch021.certificate845,envelope422,inputs422,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs423 : RatMajorityInputs := ⟨(2809356770621158271339431/2500000000000000000000),(25078532709837/5000000000000),(250668801021381187/250000000000000000),(3854230140602043/31250000000000000),(25078532709837/10000000000000),(20360721880592263/250000000000000000),28⟩
theorem inputs_valid423 : inputs423.Valid := by decide +kernel
def envelope423 : RatMajorityEnvelope := ⟨211,1,inputs423,1,(108159433543566773/200000000000000000)⟩
theorem envelope_sound423 : envelope423.Sound := by
  apply rat_majority_inputs_envelopes inputs423 inputs_valid423
  · norm_num [envelope423]
  · intro rho hr0 hr1
    have hh := Batch021.bound846 rho hr0 hr1
    norm_num [Batch021.certificate846,envelope423,inputs423,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound847 rho hr0 hr1
    norm_num [Batch021.certificate847,envelope423,inputs423,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs424 : RatMajorityInputs := ⟨(34824388362392004127461/32000000000000000000),(22146360185391/5000000000000),(1002762611013538417/1000000000000000000),(45422784123738217/250000000000000000),(22146360185391/10000000000000),(54596625667692669/500000000000000000),26⟩
theorem inputs_valid424 : inputs424.Valid := by decide +kernel
def envelope424 : RatMajorityEnvelope := ⟨212,0,inputs424,(2480118571/2101350000),(705189757419314451/1000000000000000000)⟩
theorem envelope_sound424 : envelope424.Sound := by
  apply rat_majority_inputs_envelopes inputs424 inputs_valid424
  · norm_num [envelope424]
  · intro rho hr0 hr1
    have hh := Batch021.bound848 rho hr0 hr1
    norm_num [Batch021.certificate848,envelope424,inputs424,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound849 rho hr0 hr1
    norm_num [Batch021.certificate849,envelope424,inputs424,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs425 : RatMajorityInputs := ⟨(34824388362392004127461/32000000000000000000),(12543870009819/2500000000000),(1002762611013538417/1000000000000000000),(61590904937286189/500000000000000000),(12543870009819/5000000000000),(81367935043548103/1000000000000000000),26⟩
theorem inputs_valid425 : inputs425.Valid := by decide +kernel
def envelope425 : RatMajorityEnvelope := ⟨212,1,inputs425,1,(6760266168366397/12500000000000000)⟩
theorem envelope_sound425 : envelope425.Sound := by
  apply rat_majority_inputs_envelopes inputs425 inputs_valid425
  · norm_num [envelope425]
  · intro rho hr0 hr1
    have hh := Batch021.bound850 rho hr0 hr1
    norm_num [Batch021.certificate850,envelope425,inputs425,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound851 rho hr0 hr1
    norm_num [Batch021.certificate851,envelope425,inputs425,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs426 : RatMajorityInputs := ⟨(21098915522157158154693947/20000000000000000000000),(444543578730847/100000000000000),(1002850050670708613/1000000000000000000),(44952258901544281/250000000000000000),(444543578730847/200000000000000),(108314321598920761/1000000000000000000),25⟩
theorem inputs_valid426 : inputs426.Valid := by decide +kernel
def envelope426 : RatMajorityEnvelope := ⟨213,0,inputs426,(154559528/131138125),(351787786994736347/500000000000000000)⟩
theorem envelope_sound426 : envelope426.Sound := by
  apply rat_majority_inputs_envelopes inputs426 inputs_valid426
  · norm_num [envelope426]
  · intro rho hr0 hr1
    have hh := Batch021.bound852 rho hr0 hr1
    norm_num [Batch021.certificate852,envelope426,inputs426,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound853 rho hr0 hr1
    norm_num [Batch021.certificate853,envelope426,inputs426,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs427 : RatMajorityInputs := ⟨(21098915522157158154693947/20000000000000000000000),(804685146563/160000000000),(1002850050670708613/1000000000000000000),(122207315196632739/1000000000000000000),(804685146563/320000000000),(20222985122216573/250000000000000000),27⟩
theorem inputs_valid427 : inputs427.Valid := by decide +kernel
def envelope427 : RatMajorityEnvelope := ⟨213,1,inputs427,1,(108151796864470167/200000000000000000)⟩
theorem envelope_sound427 : envelope427.Sound := by
  apply rat_majority_inputs_envelopes inputs427 inputs_valid427
  · norm_num [envelope427]
  · intro rho hr0 hr1
    have hh := Batch021.bound854 rho hr0 hr1
    norm_num [Batch021.certificate854,envelope427,inputs427,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound855 rho hr0 hr1
    norm_num [Batch021.certificate855,envelope427,inputs427,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs428 : RatMajorityInputs := ⟨(51181295694738270831116193/50000000000000000000000),(6966905587257/1562500000000),(100293745277393243/100000000000000000),(35652649142454553/200000000000000000),(6966905587257/3125000000000),(107591913446429137/1000000000000000000),25⟩
theorem inputs_valid428 : inputs428.Valid := by decide +kernel
def envelope428 : RatMajorityEnvelope := ⟨214,0,inputs428,(616498931/523792500),(702028431458928999/1000000000000000000)⟩
theorem envelope_sound428 : envelope428.Sound := by
  apply rat_majority_inputs_envelopes inputs428 inputs_valid428
  · norm_num [envelope428]
  · intro rho hr0 hr1
    have hh := Batch021.bound856 rho hr0 hr1
    norm_num [Batch021.certificate856,envelope428,inputs428,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound857 rho hr0 hr1
    norm_num [Batch021.certificate857,envelope428,inputs428,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs429 : RatMajorityInputs := ⟨(51181295694738270831116193/50000000000000000000000),(100668639953343/20000000000000),(100293745277393243/100000000000000000),(60932163080985733/500000000000000000),(100668639953343/40000000000000),(16144854106434867/200000000000000000),26⟩
theorem inputs_valid429 : inputs429.Valid := by decide +kernel
def envelope429 : RatMajorityEnvelope := ⟨214,1,inputs429,1,(270381655872858727/500000000000000000)⟩
theorem envelope_sound429 : envelope429.Sound := by
  apply rat_majority_inputs_envelopes inputs429 inputs_valid429
  · norm_num [envelope429]
  · intro rho hr0 hr1
    have hh := Batch021.bound858 rho hr0 hr1
    norm_num [Batch021.certificate858,envelope429,inputs429,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound859 rho hr0 hr1
    norm_num [Batch021.certificate859,envelope429,inputs429,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs430 : RatMajorityInputs := ⟨(49707779546513197068393987/50000000000000000000000),(218639499561/48828125000),(1003024734143526871/1000000000000000000),(17609771654655249/100000000000000000),(218639499561/97656250000),(416324347509217/3906250000000000),26⟩
theorem inputs_valid430 : inputs430.Valid := by decide +kernel
def envelope430 : RatMajorityEnvelope := ⟨215,0,inputs430,(819002323/697410000),(699493764586730747/1000000000000000000)⟩
theorem envelope_sound430 : envelope430.Sound := by
  apply rat_majority_inputs_envelopes inputs430 inputs_valid430
  · norm_num [envelope430]
  · intro rho hr0 hr1
    have hh := Batch021.bound860 rho hr0 hr1
    norm_num [Batch021.certificate860,envelope430,inputs430,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound861 rho hr0 hr1
    norm_num [Batch021.certificate861,envelope430,inputs430,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs431 : RatMajorityInputs := ⟨(49707779546513197068393987/50000000000000000000000),(252428671144503/50000000000000),(1003024734143526871/1000000000000000000),(24124024116121603/200000000000000000),(252428671144503/100000000000000),(40057718917930693/500000000000000000),27⟩
theorem inputs_valid431 : inputs431.Valid := by decide +kernel
def envelope431 : RatMajorityEnvelope := ⟨215,1,inputs431,1,(27033658741031683/50000000000000000)⟩
theorem envelope_sound431 : envelope431.Sound := by
  apply rat_majority_inputs_envelopes inputs431 inputs_valid431
  · norm_num [envelope431]
  · intro rho hr0 hr1
    have hh := Batch021.bound862 rho hr0 hr1
    norm_num [Batch021.certificate862,envelope431,inputs431,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound863 rho hr0 hr1
    norm_num [Batch021.certificate863,envelope431,inputs431,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs432 : RatMajorityInputs := ⟨(4832030869104126414537891/5000000000000000000000),(22462789707569/5000000000000),(125388974572502011/125000000000000000),(87208437601981643/500000000000000000),(22462789707569/10000000000000),(52896074373239449/500000000000000000),25⟩
theorem inputs_valid432 : inputs432.Valid := by decide +kernel
def envelope432 : RatMajorityEnvelope := ⟨216,0,inputs432,(76567891/65293750),(697872145685072637/1000000000000000000)⟩
theorem envelope_sound432 : envelope432.Sound := by
  apply rat_majority_inputs_envelopes inputs432 inputs_valid432
  · norm_num [envelope432]
  · intro rho hr0 hr1
    have hh := Batch021.bound864 rho hr0 hr1
    norm_num [Batch021.certificate864,envelope432,inputs432,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound865 rho hr0 hr1
    norm_num [Batch021.certificate865,envelope432,inputs432,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs433 : RatMajorityInputs := ⟨(4832030869104126414537891/5000000000000000000000),(12632307565671/2500000000000),(125388974572502011/125000000000000000),(7516550063770207/62500000000000000),(12632307565671/5000000000000),(79941391972545753/1000000000000000000),26⟩
theorem inputs_valid433 : inputs433.Valid := by decide +kernel
def envelope433 : RatMajorityEnvelope := ⟨216,1,inputs433,1,(270338154323677179/500000000000000000)⟩
theorem envelope_sound433 : envelope433.Sound := by
  apply rat_majority_inputs_envelopes inputs433 inputs_valid433
  · norm_num [envelope433]
  · intro rho hr0 hr1
    have hh := Batch021.bound866 rho hr0 hr1
    norm_num [Batch021.certificate866,envelope433,inputs433,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound867 rho hr0 hr1
    norm_num [Batch021.certificate867,envelope433,inputs433,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs434 : RatMajorityInputs := ⟨(47012361909260441679520797/50000000000000000000000),(112480194637541/25000000000000),(501599293107539959/500000000000000000),(86833598845296003/500000000000000000),(112480194637541/50000000000000),(52720491114241243/500000000000000000),25⟩
theorem inputs_valid434 : inputs434.Valid := by decide +kernel
def envelope434 : RatMajorityEnvelope := ⟨217,0,inputs434,(305468227/260832500),(696463442869509629/1000000000000000000)⟩
theorem envelope_sound434 : envelope434.Sound := by
  apply rat_majority_inputs_envelopes inputs434 inputs_valid434
  · norm_num [envelope434]
  · intro rho hr0 hr1
    have hh := Batch021.bound868 rho hr0 hr1
    norm_num [Batch021.certificate868,envelope434,inputs434,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound869 rho hr0 hr1
    norm_num [Batch021.certificate869,envelope434,inputs434,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs435 : RatMajorityInputs := ⟨(47012361909260441679520797/50000000000000000000000),(3957301966489/781250000000),(501599293107539959/500000000000000000),(11925505387401939/100000000000000000),(3957301966489/1562500000000),(39723177754606153/500000000000000000),26⟩
theorem inputs_valid435 : inputs435.Valid := by decide +kernel
def envelope435 : RatMajorityEnvelope := ⟨217,1,inputs435,1,(540611099238681007/1000000000000000000)⟩
theorem envelope_sound435 : envelope435.Sound := by
  apply rat_majority_inputs_envelopes inputs435 inputs_valid435
  · norm_num [envelope435]
  · intro rho hr0 hr1
    have hh := Batch021.bound870 rho hr0 hr1
    norm_num [Batch021.certificate870,envelope435,inputs435,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound871 rho hr0 hr1
    norm_num [Batch021.certificate871,envelope435,inputs435,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs436 : RatMajorityInputs := ⟨(2861166802561773269996917/3125000000000000000000),(28298999172679/6250000000000),(100328500532319339/100000000000000000),(34094162563648717/200000000000000000),(28298999172679/12500000000000),(103942238433069859/1000000000000000000),25⟩
theorem inputs_valid436 : inputs436.Valid := by decide +kernel
def envelope436 : RatMajorityEnvelope := ⟨218,0,inputs436,(2434899669/2084020000),(138745852274881951/200000000000000000)⟩
theorem envelope_sound436 : envelope436.Sound := by
  apply rat_majority_inputs_envelopes inputs436 inputs_valid436
  · norm_num [envelope436]
  · intro rho hr0 hr1
    have hh := Batch021.bound872 rho hr0 hr1
    norm_num [Batch021.certificate872,envelope436,inputs436,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound873 rho hr0 hr1
    norm_num [Batch021.certificate873,envelope436,inputs436,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs437 : RatMajorityInputs := ⟨(2861166802561773269996917/3125000000000000000000),(63402720755369/12500000000000),(100328500532319339/100000000000000000),(118699837316286509/1000000000000000000),(63402720755369/25000000000000),(39586940091925173/500000000000000000),27⟩
theorem inputs_valid437 : inputs437.Valid := by decide +kernel
def envelope437 : RatMajorityEnvelope := ⟨218,1,inputs437,1,(540593354293462753/1000000000000000000)⟩
theorem envelope_sound437 : envelope437.Sound := by
  apply rat_majority_inputs_envelopes inputs437 inputs_valid437
  · norm_num [envelope437]
  · intro rho hr0 hr1
    have hh := Batch021.bound874 rho hr0 hr1
    norm_num [Batch021.certificate874,envelope437,inputs437,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound875 rho hr0 hr1
    norm_num [Batch021.certificate875,envelope437,inputs437,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs438 : RatMajorityInputs := ⟨(90950559266268024525870011/100000000000000000000000),(455145011833827/100000000000000),(1003306977646147329/1000000000000000000),(167873203734803059/1000000000000000000),(455145011833827/200000000000000),(20544480321691943/200000000000000000),26⟩
theorem inputs_valid438 : inputs438.Valid := by decide +kernel
def envelope438 : RatMajorityEnvelope := ⟨219,0,inputs438,(607621827/520982500),(345820680831067613/500000000000000000)⟩
theorem envelope_sound438 : envelope438.Sound := by
  apply rat_majority_inputs_envelopes inputs438 inputs_valid438
  · norm_num [envelope438]
  · intro rho hr0 hr1
    have hh := Batch021.bound876 rho hr0 hr1
    norm_num [Batch021.certificate876,envelope438,inputs438,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound877 rho hr0 hr1
    norm_num [Batch021.certificate877,envelope438,inputs438,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs439 : RatMajorityInputs := ⟨(90950559266268024525870011/100000000000000000000000),(10179493530547/2000000000000),(1003306977646147329/1000000000000000000),(117293841047769963/1000000000000000000),(10179493530547/4000000000000),(39241494330356767/500000000000000000),26⟩
theorem inputs_valid439 : inputs439.Valid := by decide +kernel
def envelope439 : RatMajorityEnvelope := ⟨219,1,inputs439,1,(135114377722909053/250000000000000000)⟩
theorem envelope_sound439 : envelope439.Sound := by
  apply rat_majority_inputs_envelopes inputs439 inputs_valid439
  · norm_num [envelope439]
  · intro rho hr0 hr1
    have hh := Batch021.bound878 rho hr0 hr1
    norm_num [Batch021.certificate878,envelope439,inputs439,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch021.bound879 rho hr0 hr1
    norm_num [Batch021.certificate879,envelope439,inputs439,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope420,envelope421,envelope422,envelope423,envelope424,envelope425,envelope426,envelope427,envelope428,envelope429,envelope430,envelope431,envelope432,envelope433,envelope434,envelope435,envelope436,envelope437,envelope438,envelope439]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound420
  · exact envelope_sound421
  · exact envelope_sound422
  · exact envelope_sound423
  · exact envelope_sound424
  · exact envelope_sound425
  · exact envelope_sound426
  · exact envelope_sound427
  · exact envelope_sound428
  · exact envelope_sound429
  · exact envelope_sound430
  · exact envelope_sound431
  · exact envelope_sound432
  · exact envelope_sound433
  · exact envelope_sound434
  · exact envelope_sound435
  · exact envelope_sound436
  · exact envelope_sound437
  · exact envelope_sound438
  · exact envelope_sound439

end Cycle12.MajorityCertificates.Inputs021
