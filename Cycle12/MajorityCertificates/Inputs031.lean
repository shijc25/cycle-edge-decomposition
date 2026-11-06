import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs031

def inputs620 : RatMajorityInputs := ⟨(211316731408288802366985819/100000000000000000000000),(241128309918879/50000000000000),(250355309764807189/250000000000000000),(70206913842783073/500000000000000000),(241128309918879/100000000000000),(11212515817805547/125000000000000000),26⟩
theorem inputs_valid620 : inputs620.Valid := by decide +kernel
def envelope620 : RatMajorityEnvelope := ⟨310,0,inputs620,(2528641673/2191270000),(338506157266019787/500000000000000000)⟩
theorem envelope_sound620 : envelope620.Sound := by
  apply rat_majority_inputs_envelopes inputs620 inputs_valid620
  · norm_num [envelope620]
  · intro rho hr0 hr1
    have hh := Batch031.bound1240 rho hr0 hr1
    norm_num [Batch031.certificate1240,envelope620,inputs620,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1241 rho hr0 hr1
    norm_num [Batch031.certificate1241,envelope620,inputs620,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs621 : RatMajorityInputs := ⟨(211316731408288802366985819/100000000000000000000000),(496922303266691/100000000000000),(250355309764807189/250000000000000000),(12726823761016103/100000000000000000),(496922303266691/200000000000000),(41678965708779507/500000000000000000),26⟩
theorem inputs_valid621 : inputs621.Valid := by decide +kernel
def envelope621 : RatMajorityEnvelope := ⟨310,1,inputs621,1,(540638710442496913/1000000000000000000)⟩
theorem envelope_sound621 : envelope621.Sound := by
  apply rat_majority_inputs_envelopes inputs621 inputs_valid621
  · norm_num [envelope621]
  · intro rho hr0 hr1
    have hh := Batch031.bound1242 rho hr0 hr1
    norm_num [Batch031.certificate1242,envelope621,inputs621,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1243 rho hr0 hr1
    norm_num [Batch031.certificate1243,envelope621,inputs621,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs622 : RatMajorityInputs := ⟨(52277465450937732673123421/25000000000000000000000),(60454686095419/12500000000000),(250359063763244259/250000000000000000),(139127030847751323/1000000000000000000),(60454686095419/25000000000000),(89082939044988163/1000000000000000000),26⟩
theorem inputs_valid622 : inputs622.Valid := by decide +kernel
def envelope622 : RatMajorityEnvelope := ⟨311,0,inputs622,(360596011/312940000),(675399130069886999/1000000000000000000)⟩
theorem envelope_sound622 : envelope622.Sound := by
  apply rat_majority_inputs_envelopes inputs622 inputs_valid622
  · norm_num [envelope622]
  · intro rho hr0 hr1
    have hh := Batch031.bound1244 rho hr0 hr1
    norm_num [Batch031.certificate1244,envelope622,inputs622,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1245 rho hr0 hr1
    norm_num [Batch031.certificate1245,envelope622,inputs622,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs623 : RatMajorityInputs := ⟨(52277465450937732673123421/25000000000000000000000),(248995518525103/50000000000000),(250359063763244259/250000000000000000),(6317714241011013/50000000000000000),(248995518525103/100000000000000),(82913682247769707/1000000000000000000),26⟩
theorem inputs_valid623 : inputs623.Valid := by decide +kernel
def envelope623 : RatMajorityEnvelope := ⟨311,1,inputs623,1,(527878518766241/976562500000000)⟩
theorem envelope_sound623 : envelope623.Sound := by
  apply rat_majority_inputs_envelopes inputs623 inputs_valid623
  · norm_num [envelope623]
  · intro rho hr0 hr1
    have hh := Batch031.bound1246 rho hr0 hr1
    norm_num [Batch031.certificate1246,envelope623,inputs623,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1247 rho hr0 hr1
    norm_num [Batch031.certificate1247,envelope623,inputs623,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs624 : RatMajorityInputs := ⟨(20696125040949814283516017/10000000000000000000000),(12123671975693/2500000000000),(500725591330549761/500000000000000000),(27583286205381401/200000000000000000),(12123671975693/5000000000000),(44250811190897439/500000000000000000),27⟩
theorem inputs_valid624 : inputs624.Valid := by decide +kernel
def envelope624 : RatMajorityEnvelope := ⟨312,0,inputs624,(3149677/2737375),(84225431495097947/125000000000000000)⟩
theorem envelope_sound624 : envelope624.Sound := by
  apply rat_majority_inputs_envelopes inputs624 inputs_valid624
  · norm_num [envelope624]
  · intro rho hr0 hr1
    have hh := Batch031.bound1248 rho hr0 hr1
    norm_num [Batch031.certificate1248,envelope624,inputs624,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1249 rho hr0 hr1
    norm_num [Batch031.certificate1249,envelope624,inputs624,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs625 : RatMajorityInputs := ⟨(20696125040949814283516017/10000000000000000000000),(49908516358947/10000000000000),(500725591330549761/500000000000000000),(125424652084568221/1000000000000000000),(49908516358947/20000000000000),(41230665200127319/500000000000000000),26⟩
theorem inputs_valid625 : inputs625.Valid := by decide +kernel
def envelope625 : RatMajorityEnvelope := ⟨312,1,inputs625,1,(21618200723668247/40000000000000000)⟩
theorem envelope_sound625 : envelope625.Sound := by
  apply rat_majority_inputs_envelopes inputs625 inputs_valid625
  · norm_num [envelope625]
  · intro rho hr0 hr1
    have hh := Batch031.bound1250 rho hr0 hr1
    norm_num [Batch031.certificate1250,envelope625,inputs625,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1251 rho hr0 hr1
    norm_num [Batch031.certificate1251,envelope625,inputs625,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs626 : RatMajorityInputs := ⟨(645607828478203098664257/312500000000000000000),(121546373604291/25000000000000),(500726880851974343/500000000000000000),(34194951693725593/250000000000000000),(121546373604291/50000000000000),(5497201170672711/62500000000000000),26⟩
theorem inputs_valid626 : inputs626.Valid := by decide +kernel
def envelope626 : RatMajorityEnvelope := ⟨313,0,inputs626,(503570583/438008000),(336431988516153173/500000000000000000)⟩
theorem envelope_sound626 : envelope626.Sound := by
  apply rat_majority_inputs_envelopes inputs626 inputs_valid626
  · norm_num [envelope626]
  · intro rho hr0 hr1
    have hh := Batch031.bound1252 rho hr0 hr1
    norm_num [Batch031.certificate1252,envelope626,inputs626,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1253 rho hr0 hr1
    norm_num [Batch031.certificate1253,envelope626,inputs626,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs627 : RatMajorityInputs := ⟨(645607828478203098664257/312500000000000000000),(12487386502703/2500000000000),(500726880851974343/500000000000000000),(31269402143744239/250000000000000000),(12487386502703/5000000000000),(41146167910155387/500000000000000000),26⟩
theorem inputs_valid627 : inputs627.Valid := by decide +kernel
def envelope627 : RatMajorityEnvelope := ⟨313,1,inputs627,1,(540419139393352273/1000000000000000000)⟩
theorem envelope_sound627 : envelope627.Sound := by
  apply rat_majority_inputs_envelopes inputs627 inputs_valid627
  · norm_num [envelope627]
  · intro rho hr0 hr1
    have hh := Batch031.bound1254 rho hr0 hr1
    norm_num [Batch031.certificate1254,envelope627,inputs627,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1255 rho hr0 hr1
    norm_num [Batch031.certificate1255,envelope627,inputs627,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs628 : RatMajorityInputs := ⟨(205554087091720858609129749/100000000000000000000000),(486792150392919/100000000000000),(1001461128321935677/1000000000000000000),(532133280599949/3906250000000000),(486792150392919/200000000000000),(43844415077677817/500000000000000000),26⟩
theorem inputs_valid628 : inputs628.Valid := by decide +kernel
def envelope628 : RatMajorityEnvelope := ⟨314,0,inputs628,(2515669263/2189710000),(33603937210470561/50000000000000000)⟩
theorem envelope_sound628 : envelope628.Sound := by
  apply rat_majority_inputs_envelopes inputs628 inputs_valid628
  · norm_num [envelope628]
  · intro rho hr0 hr1
    have hh := Batch031.bound1256 rho hr0 hr1
    norm_num [Batch031.certificate1256,envelope628,inputs628,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1257 rho hr0 hr1
    norm_num [Batch031.certificate1257,envelope628,inputs628,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs629 : RatMajorityInputs := ⟨(205554087091720858609129749/100000000000000000000000),(500324820958119/100000000000000),(1001461128321935677/1000000000000000000),(62189353820145433/500000000000000000),(500324820958119/200000000000000),(1024397402303577/12500000000000000),26⟩
theorem inputs_valid629 : inputs629.Valid := by decide +kernel
def envelope629 : RatMajorityEnvelope := ⟨314,1,inputs629,1,(108069597169435423/200000000000000000)⟩
theorem envelope_sound629 : envelope629.Sound := by
  apply rat_majority_inputs_envelopes inputs629 inputs_valid629
  · norm_num [envelope629]
  · intro rho hr0 hr1
    have hh := Batch031.bound1258 rho hr0 hr1
    norm_num [Batch031.certificate1258,envelope629,inputs629,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1259 rho hr0 hr1
    norm_num [Batch031.certificate1259,envelope629,inputs629,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs630 : RatMajorityInputs := ⟨(2556589947132223276067233/1250000000000000000000),(121893099754401/25000000000000),(500734236370344571/500000000000000000),(67758450281149631/500000000000000000),(121893099754401/50000000000000),(87347401141544099/1000000000000000000),26⟩
theorem inputs_valid630 : inputs630.Valid := by decide +kernel
def envelope630 : RatMajorityEnvelope := ⟨315,0,inputs630,(62836261/54734500),(671265471129192551/1000000000000000000)⟩
theorem envelope_sound630 : envelope630.Sound := by
  apply rat_majority_inputs_envelopes inputs630 inputs_valid630
  · norm_num [envelope630]
  · intro rho hr0 hr1
    have hh := Batch031.bound1260 rho hr0 hr1
    norm_num [Batch031.certificate1260,envelope630,inputs630,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1261 rho hr0 hr1
    norm_num [Batch031.certificate1261,envelope630,inputs630,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs631 : RatMajorityInputs := ⟨(2556589947132223276067233/1250000000000000000000),(125148355324221/25000000000000),(500734236370344571/500000000000000000),(124153103291150063/1000000000000000000),(125148355324221/50000000000000),(20460451165454193/250000000000000000),27⟩
theorem inputs_valid631 : inputs631.Valid := by decide +kernel
def envelope631 : RatMajorityEnvelope := ⟨315,1,inputs631,1,(135081833990635961/250000000000000000)⟩
theorem envelope_sound631 : envelope631.Sound := by
  apply rat_majority_inputs_envelopes inputs631 inputs_valid631
  · norm_num [envelope631]
  · intro rho hr0 hr1
    have hh := Batch031.bound1262 rho hr0 hr1
    norm_num [Batch031.certificate1262,envelope631,inputs631,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1263 rho hr0 hr1
    norm_num [Batch031.certificate1263,envelope631,inputs631,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs632 : RatMajorityInputs := ⟨(101757282742067782633344909/50000000000000000000000),(244129782388129/50000000000000),(500737893913241227/500000000000000000),(67447493775743281/500000000000000000),(244129782388129/100000000000000),(10880975675030883/125000000000000000),26⟩
theorem inputs_valid632 : inputs632.Valid := by decide +kernel
def envelope632 : RatMajorityEnvelope := ⟨316,0,inputs632,(2511264683/2189060000),(670468530351266337/1000000000000000000)⟩
theorem envelope_sound632 : envelope632.Sound := by
  apply rat_majority_inputs_envelopes inputs632 inputs_valid632
  · norm_num [envelope632]
  · intro rho hr0 hr1
    have hh := Batch031.bound1264 rho hr0 hr1
    norm_num [Batch031.certificate1264,envelope632,inputs632,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1265 rho hr0 hr1
    norm_num [Batch031.certificate1265,envelope632,inputs632,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs633 : RatMajorityInputs := ⟨(101757282742067782633344909/50000000000000000000000),(7824952691773/1562500000000),(500737893913241227/500000000000000000),(61991188883379553/500000000000000000),(7824952691773/3125000000000),(1635171042760223/20000000000000000),27⟩
theorem inputs_valid633 : inputs633.Valid := by decide +kernel
def envelope633 : RatMajorityEnvelope := ⟨316,1,inputs633,1,(270156264814551641/500000000000000000)⟩
theorem envelope_sound633 : envelope633.Sound := by
  apply rat_majority_inputs_envelopes inputs633 inputs_valid633
  · norm_num [envelope633]
  · intro rho hr0 hr1
    have hh := Batch031.bound1266 rho hr0 hr1
    norm_num [Batch031.certificate1266,envelope633,inputs633,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1267 rho hr0 hr1
    norm_num [Batch031.certificate1267,envelope633,inputs633,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs634 : RatMajorityInputs := ⟨(50628766550045995019940813/25000000000000000000000),(244431401203419/50000000000000),(40059323195068479/40000000000000000),(134351108587654899/1000000000000000000),(244431401203419/100000000000000),(86785648397031909/1000000000000000000),26⟩
theorem inputs_valid634 : inputs634.Valid := by decide +kernel
def envelope634 : RatMajorityEnvelope := ⟨317,0,inputs634,(627275531/547185000),(26787511164796519/40000000000000000)⟩
theorem envelope_sound634 : envelope634.Sound := by
  apply rat_majority_inputs_envelopes inputs634 inputs_valid634
  · norm_num [envelope634]
  · intro rho hr0 hr1
    have hh := Batch031.bound1268 rho hr0 hr1
    norm_num [Batch031.certificate1268,envelope634,inputs634,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1269 rho hr0 hr1
    norm_num [Batch031.certificate1269,envelope634,inputs634,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs635 : RatMajorityInputs := ⟨(50628766550045995019940813/25000000000000000000000),(250831957223811/50000000000000),(40059323195068479/40000000000000000),(61628788000495123/500000000000000000),(250831957223811/100000000000000),(81404919454721357/1000000000000000000),26⟩
theorem inputs_valid635 : inputs635.Valid := by decide +kernel
def envelope635 : RatMajorityEnvelope := ⟨317,1,inputs635,1,(540238805450822753/1000000000000000000)⟩
theorem envelope_sound635 : envelope635.Sound := by
  apply rat_majority_inputs_envelopes inputs635 inputs_valid635
  · norm_num [envelope635]
  · intro rho hr0 hr1
    have hh := Batch031.bound1270 rho hr0 hr1
    norm_num [Batch031.certificate1270,envelope635,inputs635,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1271 rho hr0 hr1
    norm_num [Batch031.certificate1271,envelope635,inputs635,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs636 : RatMajorityInputs := ⟨(201529431280214394110570289/100000000000000000000000),(489512946148657/100000000000000),(500745170845787897/500000000000000000),(16720888208735149/125000000000000000),(489512946148657/200000000000000),(86503990709091673/1000000000000000000),26⟩
theorem inputs_valid636 : inputs636.Valid := by decide +kernel
def envelope636 : RatMajorityEnvelope := ⟨318,0,inputs636,(2506938113/2188430000),(66889814388740311/100000000000000000)⟩
theorem envelope_sound636 : envelope636.Sound := by
  apply rat_majority_inputs_envelopes inputs636 inputs_valid636
  · norm_num [envelope636]
  · intro rho hr0 hr1
    have hh := Batch031.bound1272 rho hr0 hr1
    norm_num [Batch031.certificate1272,envelope636,inputs636,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1273 rho hr0 hr1
    norm_num [Batch031.certificate1273,envelope636,inputs636,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs637 : RatMajorityInputs := ⟨(201529431280214394110570289/100000000000000000000000),(501937652866703/100000000000000),(500745170845787897/500000000000000000),(123029502224255999/1000000000000000000),(501937652866703/200000000000000),(20323394349703523/250000000000000000),26⟩
theorem inputs_valid637 : inputs637.Valid := by decide +kernel
def envelope637 : RatMajorityEnvelope := ⟨318,1,inputs637,1,(2110226287156371/3906250000000000)⟩
theorem envelope_sound637 : envelope637.Sound := by
  apply rat_majority_inputs_envelopes inputs637 inputs_valid637
  · norm_num [envelope637]
  · intro rho hr0 hr1
    have hh := Batch031.bound1274 rho hr0 hr1
    norm_num [Batch031.certificate1274,envelope637,inputs637,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1275 rho hr0 hr1
    norm_num [Batch031.certificate1275,envelope637,inputs637,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs638 : RatMajorityInputs := ⟨(198920851874024237699637351/100000000000000000000000),(49189291460997/10000000000000),(500754954232798727/500000000000000000),(32912081855026759/250000000000000000),(49189291460997/20000000000000),(21370176847767989/250000000000000000),26⟩
theorem inputs_valid638 : inputs638.Valid := by decide +kernel
def envelope638 : RatMajorityEnvelope := ⟨319,0,inputs638,(1250987321/1093665000),(333601928615426543/500000000000000000)⟩
theorem envelope_sound638 : envelope638.Sound := by
  apply rat_majority_inputs_envelopes inputs638 inputs_valid638
  · norm_num [envelope638]
  · intro rho hr0 hr1
    have hh := Batch031.bound1276 rho hr0 hr1
    norm_num [Batch031.certificate1276,envelope638,inputs638,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1277 rho hr0 hr1
    norm_num [Batch031.certificate1277,envelope638,inputs638,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs639 : RatMajorityInputs := ⟨(198920851874024237699637351/100000000000000000000000),(502277458238607/100000000000000),(500754954232798727/500000000000000000),(122746904662947999/1000000000000000000),(502277458238607/200000000000000),(40577787347827163/500000000000000000),26⟩
theorem inputs_valid639 : inputs639.Valid := by decide +kernel
def envelope639 : RatMajorityEnvelope := ⟨319,1,inputs639,1,(270098482465613537/500000000000000000)⟩
theorem envelope_sound639 : envelope639.Sound := by
  apply rat_majority_inputs_envelopes inputs639 inputs_valid639
  · norm_num [envelope639]
  · intro rho hr0 hr1
    have hh := Batch031.bound1278 rho hr0 hr1
    norm_num [Batch031.certificate1278,envelope639,inputs639,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch031.bound1279 rho hr0 hr1
    norm_num [Batch031.certificate1279,envelope639,inputs639,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope620,envelope621,envelope622,envelope623,envelope624,envelope625,envelope626,envelope627,envelope628,envelope629,envelope630,envelope631,envelope632,envelope633,envelope634,envelope635,envelope636,envelope637,envelope638,envelope639]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound620
  · exact envelope_sound621
  · exact envelope_sound622
  · exact envelope_sound623
  · exact envelope_sound624
  · exact envelope_sound625
  · exact envelope_sound626
  · exact envelope_sound627
  · exact envelope_sound628
  · exact envelope_sound629
  · exact envelope_sound630
  · exact envelope_sound631
  · exact envelope_sound632
  · exact envelope_sound633
  · exact envelope_sound634
  · exact envelope_sound635
  · exact envelope_sound636
  · exact envelope_sound637
  · exact envelope_sound638
  · exact envelope_sound639

end Cycle12.MajorityCertificates.Inputs031
