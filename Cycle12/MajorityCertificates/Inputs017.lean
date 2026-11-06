import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs017

def inputs340 : RatMajorityInputs := ⟨(1021297476743366763906207123/25000000000000000000000),(26599303847583/6250000000000),(1000073440193184911/1000000000000000000),(40590735604130361/200000000000000000),(26599303847583/12500000000000),(119081838017309771/1000000000000000000),25⟩
theorem inputs_valid340 : inputs340.Valid := by decide +kernel
def envelope340 : RatMajorityEnvelope := ⟨170,0,inputs340,(2717847551/2347080000),(685877942554350021/1000000000000000000)⟩
theorem envelope_sound340 : envelope340.Sound := by
  apply rat_majority_inputs_envelopes inputs340 inputs_valid340
  · norm_num [envelope340]
  · intro rho hr0 hr1
    have hh := Batch017.bound680 rho hr0 hr1
    norm_num [Batch017.certificate680,envelope340,inputs340,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound681 rho hr0 hr1
    norm_num [Batch017.certificate681,envelope340,inputs340,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs341 : RatMajorityInputs := ⟨(1021297476743366763906207123/25000000000000000000000),(121862289864609/25000000000000),(1000073440193184911/1000000000000000000),(6781435213167403/50000000000000000),(121862289864609/50000000000000),(5462577562743659/62500000000000000),27⟩
theorem inputs_valid341 : inputs341.Valid := by decide +kernel
def envelope341 : RatMajorityEnvelope := ⟨170,1,inputs341,1,(540933025443764317/1000000000000000000)⟩
theorem envelope_sound341 : envelope341.Sound := by
  apply rat_majority_inputs_envelopes inputs341 inputs_valid341
  · norm_num [envelope341]
  · intro rho hr0 hr1
    have hh := Batch017.bound682 rho hr0 hr1
    norm_num [Batch017.certificate682,envelope341,inputs341,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound683 rho hr0 hr1
    norm_num [Batch017.certificate683,envelope341,inputs341,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs342 : RatMajorityInputs := ⟨(78472564364857074075660521/2500000000000000000000),(26598315387839/6250000000000),(1000095581909658037/1000000000000000000),(40594797873687707/200000000000000000),(26598315387839/12500000000000),(119091254997886843/1000000000000000000),25⟩
theorem inputs_valid342 : inputs342.Valid := by decide +kernel
def envelope342 : RatMajorityEnvelope := ⟨171,0,inputs342,(2710212041/2337640000),(343573639948479363/500000000000000000)⟩
theorem envelope_sound342 : envelope342.Sound := by
  apply rat_majority_inputs_envelopes inputs342 inputs_valid342
  · norm_num [envelope342]
  · intro rho hr0 hr1
    have hh := Batch017.bound684 rho hr0 hr1
    norm_num [Batch017.certificate684,envelope342,inputs342,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound685 rho hr0 hr1
    norm_num [Batch017.certificate685,envelope342,inputs342,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs343 : RatMajorityInputs := ⟨(78472564364857074075660521/2500000000000000000000),(60911760357819/12500000000000),(1000095581909658037/1000000000000000000),(135769506220830663/1000000000000000000),(60911760357819/25000000000000),(87469036718978257/1000000000000000000),26⟩
theorem inputs_valid343 : inputs343.Valid := by decide +kernel
def envelope343 : RatMajorityEnvelope := ⟨171,1,inputs343,1,(10819172669111307/20000000000000000)⟩
theorem envelope_sound343 : envelope343.Sound := by
  apply rat_majority_inputs_envelopes inputs343 inputs_valid343
  · norm_num [envelope343]
  · intro rho hr0 hr1
    have hh := Batch017.bound686 rho hr0 hr1
    norm_num [Batch017.certificate686,envelope343,inputs343,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound687 rho hr0 hr1
    norm_num [Batch017.certificate687,envelope343,inputs343,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs344 : RatMajorityInputs := ⟨(2489389774332574149624930481/100000000000000000000000),(425095947794589/100000000000000),(500060261379084793/500000000000000000),(50896879561876173/250000000000000000),(425095947794589/200000000000000),(59687842679353967/500000000000000000),25⟩
theorem inputs_valid344 : inputs344.Valid := by decide +kernel
def envelope344 : RatMajorityEnvelope := ⟨172,0,inputs344,(2704848773/2328490000),(137846464708761689/200000000000000000)⟩
theorem envelope_sound344 : envelope344.Sound := by
  apply rat_majority_inputs_envelopes inputs344 inputs_valid344
  · norm_num [envelope344]
  · intro rho hr0 hr1
    have hh := Batch017.bound688 rho hr0 hr1
    norm_num [Batch017.certificate688,envelope344,inputs344,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound689 rho hr0 hr1
    norm_num [Batch017.certificate689,envelope344,inputs344,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs345 : RatMajorityInputs := ⟨(2489389774332574149624930481/100000000000000000000000),(243455416549229/50000000000000),(500060261379084793/500000000000000000),(68059015442104227/500000000000000000),(243455416549229/100000000000000),(43818404926807807/500000000000000000),26⟩
theorem inputs_valid345 : inputs345.Valid := by decide +kernel
def envelope345 : RatMajorityEnvelope := ⟨172,1,inputs345,1,(270504230096160467/500000000000000000)⟩
theorem envelope_sound345 : envelope345.Sound := by
  apply rat_majority_inputs_envelopes inputs345 inputs_valid345
  · norm_num [envelope345]
  · intro rho hr0 hr1
    have hh := Batch017.bound690 rho hr0 hr1
    norm_num [Batch017.certificate690,envelope345,inputs345,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound691 rho hr0 hr1
    norm_num [Batch017.certificate691,envelope345,inputs345,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs346 : RatMajorityInputs := ⟨(50606224308644093371924347/2500000000000000000000),(10626422184903/2500000000000),(20002964403968943/20000000000000000),(20363781700677337/100000000000000000),(10626422184903/5000000000000),(119399001944709777/1000000000000000000),25⟩
theorem inputs_valid346 : inputs346.Valid := by decide +kernel
def envelope346 : RatMajorityEnvelope := ⟨173,0,inputs346,(179853121/154640000),(172627738406148649/250000000000000000)⟩
theorem envelope_sound346 : envelope346.Sound := by
  apply rat_majority_inputs_envelopes inputs346 inputs_valid346
  · norm_num [envelope346]
  · intro rho hr0 hr1
    have hh := Batch017.bound692 rho hr0 hr1
    norm_num [Batch017.certificate692,envelope346,inputs346,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound693 rho hr0 hr1
    norm_num [Batch017.certificate693,envelope346,inputs346,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs347 : RatMajorityInputs := ⟨(50606224308644093371924347/2500000000000000000000),(488170797507/100000000000),(20002964403968943/20000000000000000),(134975183759938933/1000000000000000000),(488170797507/200000000000),(21771612238805307/250000000000000000),26⟩
theorem inputs_valid347 : inputs347.Valid := by decide +kernel
def envelope347 : RatMajorityEnvelope := ⟨173,1,inputs347,1,(4225741961460787/7812500000000000)⟩
theorem envelope_sound347 : envelope347.Sound := by
  apply rat_majority_inputs_envelopes inputs347 inputs_valid347
  · norm_num [envelope347]
  · intro rho hr0 hr1
    have hh := Batch017.bound694 rho hr0 hr1
    norm_num [Batch017.certificate694,envelope347,inputs347,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound695 rho hr0 hr1
    norm_num [Batch017.certificate695,envelope347,inputs347,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs348 : RatMajorityInputs := ⟨(26245172397150043298806269/1562500000000000000000),(53129999730471/12500000000000),(200035725817865169/200000000000000000),(12728723075055563/62500000000000000),(53129999730471/25000000000000),(29852271337233713/250000000000000000),25⟩
theorem inputs_valid348 : inputs348.Valid := by decide +kernel
def envelope348 : RatMajorityEnvelope := ⟨174,0,inputs348,(1345496651/1155480000),(345890917910679707/500000000000000000)⟩
theorem envelope_sound348 : envelope348.Sound := by
  apply rat_majority_inputs_envelopes inputs348 inputs_valid348
  · norm_num [envelope348]
  · intro rho hr0 hr1
    have hh := Batch017.bound696 rho hr0 hr1
    norm_num [Batch017.certificate696,envelope348,inputs348,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound697 rho hr0 hr1
    norm_num [Batch017.certificate697,envelope348,inputs348,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs349 : RatMajorityInputs := ⟨(26245172397150043298806269/1562500000000000000000),(60990478275831/12500000000000),(200035725817865169/200000000000000000),(135198529579225899/1000000000000000000),(60990478275831/25000000000000),(10899256831006219/125000000000000000),26⟩
theorem inputs_valid349 : inputs349.Valid := by decide +kernel
def envelope349 : RatMajorityEnvelope := ⟨174,1,inputs349,1,(6761667651999731/12500000000000000)⟩
theorem envelope_sound349 : envelope349.Sound := by
  apply rat_majority_inputs_envelopes inputs349 inputs_valid349
  · norm_num [envelope349]
  · intro rho hr0 hr1
    have hh := Batch017.bound698 rho hr0 hr1
    norm_num [Batch017.certificate698,envelope349,inputs349,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound699 rho hr0 hr1
    norm_num [Batch017.certificate699,envelope349,inputs349,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs350 : RatMajorityInputs := ⟨(44291144912213246696834211/3125000000000000000000),(6634574322597/1562500000000),(200042340488878737/200000000000000000),(204210463931084109/1000000000000000000),(6634574322597/3125000000000),(119664440400443239/1000000000000000000),25⟩
theorem inputs_valid350 : inputs350.Valid := by decide +kernel
def envelope350 : RatMajorityEnvelope := ⟨175,0,inputs350,(99496377/85280000),(173467192281189761/250000000000000000)⟩
theorem envelope_sound350 : envelope350.Sound := by
  apply rat_majority_inputs_envelopes inputs350 inputs_valid350
  · norm_num [envelope350]
  · intro rho hr0 hr1
    have hh := Batch017.bound700 rho hr0 hr1
    norm_num [Batch017.certificate700,envelope350,inputs350,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound701 rho hr0 hr1
    norm_num [Batch017.certificate701,envelope350,inputs350,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs351 : RatMajorityInputs := ⟨(44291144912213246696834211/3125000000000000000000),(15237645224607/3125000000000),(200042340488878737/200000000000000000),(67743829116076827/500000000000000000),(15237645224607/6250000000000),(87333318307811903/1000000000000000000),27⟩
theorem inputs_valid351 : inputs351.Valid := by decide +kernel
def envelope351 : RatMajorityEnvelope := ⟨175,1,inputs351,1,(67622540466099439/125000000000000000)⟩
theorem envelope_sound351 : envelope351.Sound := by
  apply rat_majority_inputs_envelopes inputs351 inputs_valid351
  · norm_num [envelope351]
  · intro rho hr0 hr1
    have hh := Batch017.bound702 rho hr0 hr1
    norm_num [Batch017.certificate702,envelope351,inputs351,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound703 rho hr0 hr1
    norm_num [Batch017.certificate703,envelope351,inputs351,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs352 : RatMajorityInputs := ⟨(151609408215620981093743509/12500000000000000000000),(424672830655749/100000000000000),(100024739372033897/100000000000000000),(20413292783677837/100000000000000000),(424672830655749/200000000000000),(119628502184423597/1000000000000000000),25⟩
theorem inputs_valid352 : inputs352.Valid := by decide +kernel
def envelope352 : RatMajorityEnvelope := ⟨176,0,inputs352,(89334449/76479000),(695119763554619681/1000000000000000000)⟩
theorem envelope_sound352 : envelope352.Sound := by
  apply rat_majority_inputs_envelopes inputs352 inputs_valid352
  · norm_num [envelope352]
  · intro rho hr0 hr1
    have hh := Batch017.bound704 rho hr0 hr1
    norm_num [Batch017.certificate704,envelope352,inputs352,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound705 rho hr0 hr1
    norm_num [Batch017.certificate705,envelope352,inputs352,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs353 : RatMajorityInputs := ⟨(151609408215620981093743509/12500000000000000000000),(487541588964417/100000000000000),(100024739372033897/100000000000000000),(6777242200900139/50000000000000000),(487541588964417/200000000000000),(43680429034206827/500000000000000000),26⟩
theorem inputs_valid353 : inputs353.Valid := by decide +kernel
def envelope353 : RatMajorityEnvelope := ⟨176,1,inputs353,1,(135250714090014519/250000000000000000)⟩
theorem envelope_sound353 : envelope353.Sound := by
  apply rat_majority_inputs_envelopes inputs353 inputs_valid353
  · norm_num [envelope353]
  · intro rho hr0 hr1
    have hh := Batch017.bound706 rho hr0 hr1
    norm_num [Batch017.certificate706,envelope353,inputs353,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound707 rho hr0 hr1
    norm_num [Batch017.certificate707,envelope353,inputs353,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs354 : RatMajorityInputs := ⟨(6565408470284147660750299/625000000000000000000),(2654235144591/625000000000),(8002285209306379/8000000000000000),(102063371679849341/500000000000000000),(2654235144591/1250000000000),(59812817816729447/500000000000000000),25⟩
theorem inputs_valid354 : inputs354.Valid := by decide +kernel
def envelope354 : RatMajorityEnvelope := ⟨177,0,inputs354,(2673920307/2286400000),(696388439195317673/1000000000000000000)⟩
theorem envelope_sound354 : envelope354.Sound := by
  apply rat_majority_inputs_envelopes inputs354 inputs_valid354
  · norm_num [envelope354]
  · intro rho hr0 hr1
    have hh := Batch017.bound708 rho hr0 hr1
    norm_num [Batch017.certificate708,envelope354,inputs354,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound709 rho hr0 hr1
    norm_num [Batch017.certificate709,envelope354,inputs354,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs355 : RatMajorityInputs := ⟨(6565408470284147660750299/625000000000000000000),(3054324269617/625000000000),(8002285209306379/8000000000000000),(134505012672367387/1000000000000000000),(3054324269617/1250000000000),(86859846794891581/1000000000000000000),26⟩
theorem inputs_valid355 : inputs355.Valid := by decide +kernel
def envelope355 : RatMajorityEnvelope := ⟨177,1,inputs355,1,(108181153972638807/200000000000000000)⟩
theorem envelope_sound355 : envelope355.Sound := by
  apply rat_majority_inputs_envelopes inputs355 inputs_valid355
  · norm_num [envelope355]
  · intro rho hr0 hr1
    have hh := Batch017.bound710 rho hr0 hr1
    norm_num [Batch017.certificate710,envelope355,inputs355,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound711 rho hr0 hr1
    norm_num [Batch017.certificate711,envelope355,inputs355,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs356 : RatMajorityInputs := ⟨(459638908741035633382638003/50000000000000000000000),(42469054340373/10000000000000),(1000326425982197787/1000000000000000000),(25513758889760573/125000000000000000),(42469054340373/20000000000000),(23923581581202459/200000000000000000),25⟩
theorem inputs_valid356 : inputs356.Valid := by decide +kernel
def envelope356 : RatMajorityEnvelope := ⟨178,0,inputs356,(111166757/94942500),(697655974021238117/1000000000000000000)⟩
theorem envelope_sound356 : envelope356.Sound := by
  apply rat_majority_inputs_envelopes inputs356 inputs_valid356
  · norm_num [envelope356]
  · intro rho hr0 hr1
    have hh := Batch017.bound712 rho hr0 hr1
    norm_num [Batch017.certificate712,envelope356,inputs356,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound713 rho hr0 hr1
    norm_num [Batch017.certificate713,envelope356,inputs356,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs357 : RatMajorityInputs := ⟨(459638908741035633382638003/50000000000000000000000),(15270367093803/3125000000000),(1000326425982197787/1000000000000000000),(67270587876952003/500000000000000000),(15270367093803/6250000000000),(86877279637614703/1000000000000000000),26⟩
theorem inputs_valid357 : inputs357.Valid := by decide +kernel
def envelope357 : RatMajorityEnvelope := ⟨178,1,inputs357,1,(540928306998872201/1000000000000000000)⟩
theorem envelope_sound357 : envelope357.Sound := by
  apply rat_majority_inputs_envelopes inputs357 inputs_valid357
  · norm_num [envelope357]
  · intro rho hr0 hr1
    have hh := Batch017.bound714 rho hr0 hr1
    norm_num [Batch017.certificate714,envelope357,inputs357,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound715 rho hr0 hr1
    norm_num [Batch017.certificate715,envelope357,inputs357,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs358 : RatMajorityInputs := ⟨(5073644030447200559507203/625000000000000000000),(6637647789229/1562500000000),(1000369663119474637/1000000000000000000),(407913354499063/2000000000000000),(6637647789229/3125000000000),(7471675447746453/62500000000000000),25⟩
theorem inputs_valid358 : inputs358.Valid := by decide +kernel
def envelope358 : RatMajorityEnvelope := ⟨179,0,inputs358,(28321723/24160000),(349444846088226261/500000000000000000)⟩
theorem envelope_sound358 : envelope358.Sound := by
  apply rat_majority_inputs_envelopes inputs358 inputs_valid358
  · norm_num [envelope358]
  · intro rho hr0 hr1
    have hh := Batch017.bound716 rho hr0 hr1
    norm_num [Batch017.certificate716,envelope358,inputs358,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound717 rho hr0 hr1
    norm_num [Batch017.certificate717,envelope358,inputs358,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs359 : RatMajorityInputs := ⟨(5073644030447200559507203/625000000000000000000),(7634237272079/1562500000000),(1000369663119474637/1000000000000000000),(134595758613555007/1000000000000000000),(7634237272079/3125000000000),(2715737210980583/31250000000000000),27⟩
theorem inputs_valid359 : inputs359.Valid := by decide +kernel
def envelope359 : RatMajorityEnvelope := ⟨179,1,inputs359,1,(540953988497993133/1000000000000000000)⟩
theorem envelope_sound359 : envelope359.Sound := by
  apply rat_majority_inputs_envelopes inputs359 inputs_valid359
  · norm_num [envelope359]
  · intro rho hr0 hr1
    have hh := Batch017.bound718 rho hr0 hr1
    norm_num [Batch017.certificate718,envelope359,inputs359,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch017.bound719 rho hr0 hr1
    norm_num [Batch017.certificate719,envelope359,inputs359,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope340,envelope341,envelope342,envelope343,envelope344,envelope345,envelope346,envelope347,envelope348,envelope349,envelope350,envelope351,envelope352,envelope353,envelope354,envelope355,envelope356,envelope357,envelope358,envelope359]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound340
  · exact envelope_sound341
  · exact envelope_sound342
  · exact envelope_sound343
  · exact envelope_sound344
  · exact envelope_sound345
  · exact envelope_sound346
  · exact envelope_sound347
  · exact envelope_sound348
  · exact envelope_sound349
  · exact envelope_sound350
  · exact envelope_sound351
  · exact envelope_sound352
  · exact envelope_sound353
  · exact envelope_sound354
  · exact envelope_sound355
  · exact envelope_sound356
  · exact envelope_sound357
  · exact envelope_sound358
  · exact envelope_sound359

end Cycle12.MajorityCertificates.Inputs017
