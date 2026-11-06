import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs012

def inputs240 : RatMajorityInputs := ⟨(18884906444825218523574107/50000000000000000000000),(10825410690801/2500000000000),(201598440031808861/200000000000000000),(193601266561622897/1000000000000000000),(10825410690801/5000000000000),(57370254817923831/500000000000000000),25⟩
theorem inputs_valid240 : inputs240.Valid := by decide +kernel
def envelope240 : RatMajorityEnvelope := ⟨120,0,inputs240,(2298915859/1943060000),(88979128890748239/125000000000000000)⟩
theorem envelope_sound240 : envelope240.Sound := by
  apply rat_majority_inputs_envelopes inputs240 inputs_valid240
  · norm_num [envelope240]
  · intro rho hr0 hr1
    have hh := Batch012.bound480 rho hr0 hr1
    norm_num [Batch012.certificate480,envelope240,inputs240,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound481 rho hr0 hr1
    norm_num [Batch012.certificate481,envelope240,inputs240,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs241 : RatMajorityInputs := ⟨(18884906444825218523574107/50000000000000000000000),(49971937393441/10000000000000),(201598440031808861/200000000000000000),(12488857399701043/100000000000000000),(49971937393441/20000000000000),(82200255416178543/1000000000000000000),26⟩
theorem inputs_valid241 : inputs241.Valid := by decide +kernel
def envelope241 : RatMajorityEnvelope := ⟨120,1,inputs241,1,(33963155489013881/62500000000000000)⟩
theorem envelope_sound241 : envelope241.Sound := by
  apply rat_majority_inputs_envelopes inputs241 inputs_valid241
  · norm_num [envelope241]
  · intro rho hr0 hr1
    have hh := Batch012.bound482 rho hr0 hr1
    norm_num [Batch012.certificate482,envelope241,inputs241,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound483 rho hr0 hr1
    norm_num [Batch012.certificate483,envelope241,inputs241,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs242 : RatMajorityInputs := ⟨(18781669146036551228479943/50000000000000000000000),(216816001757967/50000000000000),(1008036405239811669/1000000000000000000),(24105341693027779/125000000000000000),(216816001757967/100000000000000),(28596973778380101/250000000000000000),25⟩
theorem inputs_valid242 : inputs242.Valid := by decide +kernel
def envelope242 : RatMajorityEnvelope := ⟨121,0,inputs242,(574062159/485605000),(710897510264681539/1000000000000000000)⟩
theorem envelope_sound242 : envelope242.Sound := by
  apply rat_majority_inputs_envelopes inputs242 inputs_valid242
  · norm_num [envelope242]
  · intro rho hr0 hr1
    have hh := Batch012.bound484 rho hr0 hr1
    norm_num [Batch012.certificate484,envelope242,inputs242,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound485 rho hr0 hr1
    norm_num [Batch012.certificate485,envelope242,inputs242,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs243 : RatMajorityInputs := ⟨(18781669146036551228479943/50000000000000000000000),(24993649100507/5000000000000),(1008036405239811669/1000000000000000000),(6237952015838181/50000000000000000),(24993649100507/10000000000000),(20534286634767191/250000000000000000),26⟩
theorem inputs_valid243 : inputs243.Valid := by decide +kernel
def envelope243 : RatMajorityEnvelope := ⟨121,1,inputs243,1,(67927187736467961/125000000000000000)⟩
theorem envelope_sound243 : envelope243.Sound := by
  apply rat_majority_inputs_envelopes inputs243 inputs_valid243
  · norm_num [envelope243]
  · intro rho hr0 hr1
    have hh := Batch012.bound486 rho hr0 hr1
    norm_num [Batch012.certificate486,envelope243,inputs243,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound487 rho hr0 hr1
    norm_num [Batch012.certificate487,envelope243,inputs243,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs244 : RatMajorityInputs := ⟨(37535212315517378494471803/100000000000000000000000),(3433506590683/781250000000),(1008042464728441601/1000000000000000000),(185750615147060811/1000000000000000000),(3433506590683/1562500000000),(22217341853741161/200000000000000000),25⟩
theorem inputs_valid244 : inputs244.Valid := by decide +kernel
def envelope244 : RatMajorityEnvelope := ⟨122,0,inputs244,(573036133/487727500),(351845739950111871/500000000000000000)⟩
theorem envelope_sound244 : envelope244.Sound := by
  apply rat_majority_inputs_envelopes inputs244 inputs_valid244
  · norm_num [envelope244]
  · intro rho hr0 hr1
    have hh := Batch012.bound488 rho hr0 hr1
    norm_num [Batch012.certificate488,envelope244,inputs244,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound489 rho hr0 hr1
    norm_num [Batch012.certificate489,envelope244,inputs244,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs245 : RatMajorityInputs := ⟨(37535212315517378494471803/100000000000000000000000),(502122525690201/100000000000000),(1008042464728441601/1000000000000000000),(122875681937871621/1000000000000000000),(502122525690201/200000000000000),(81218467252794301/1000000000000000000),27⟩
theorem inputs_valid245 : inputs245.Valid := by decide +kernel
def envelope245 : RatMajorityEnvelope := ⟨122,1,inputs245,1,(543226744548104253/1000000000000000000)⟩
theorem envelope_sound245 : envelope245.Sound := by
  apply rat_majority_inputs_envelopes inputs245 inputs_valid245
  · norm_num [envelope245]
  · intro rho hr0 hr1
    have hh := Batch012.bound490 rho hr0 hr1
    norm_num [Batch012.certificate490,envelope245,inputs245,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound491 rho hr0 hr1
    norm_num [Batch012.certificate491,envelope245,inputs245,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs246 : RatMajorityInputs := ⟨(933353596761949374851587/2500000000000000000000),(54662595774699/12500000000000),(1008086050717773037/1000000000000000000),(37674774257858663/200000000000000000),(54662595774699/25000000000000),(22461742654772199/200000000000000000),25⟩
theorem inputs_valid246 : inputs246.Valid := by decide +kernel
def envelope246 : RatMajorityEnvelope := ⟨123,0,inputs246,(458260487/390064000),(703888767887983901/1000000000000000000)⟩
theorem envelope_sound246 : envelope246.Sound := by
  apply rat_majority_inputs_envelopes inputs246 inputs_valid246
  · norm_num [envelope246]
  · intro rho hr0 hr1
    have hh := Batch012.bound492 rho hr0 hr1
    norm_num [Batch012.certificate492,envelope246,inputs246,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound493 rho hr0 hr1
    norm_num [Batch012.certificate493,envelope246,inputs246,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs247 : RatMajorityInputs := ⟨(933353596761949374851587/2500000000000000000000),(62774372472143/12500000000000),(1008086050717773037/1000000000000000000),(61407722199796733/500000000000000000),(62774372472143/25000000000000),(81189049532262679/1000000000000000000),27⟩
theorem inputs_valid247 : inputs247.Valid := by decide +kernel
def envelope247 : RatMajorityEnvelope := ⟨123,1,inputs247,1,(543240695215622333/1000000000000000000)⟩
theorem envelope_sound247 : envelope247.Sound := by
  apply rat_majority_inputs_envelopes inputs247 inputs_valid247
  · norm_num [envelope247]
  · intro rho hr0 hr1
    have hh := Batch012.bound494 rho hr0 hr1
    norm_num [Batch012.certificate494,envelope247,inputs247,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound495 rho hr0 hr1
    norm_num [Batch012.certificate495,envelope247,inputs247,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs248 : RatMajorityInputs := ⟨(37300012946368452613633777/100000000000000000000000),(109388013056371/25000000000000),(63005843518075071/62500000000000000),(376142039745793/2000000000000000),(109388013056371/50000000000000),(22433538766134077/200000000000000000),25⟩
theorem inputs_valid248 : inputs248.Valid := by decide +kernel
def envelope248 : RatMajorityEnvelope := ⟨124,0,inputs248,(572608151/487607500),(28136082759520533/40000000000000000)⟩
theorem envelope_sound248 : envelope248.Sound := by
  apply rat_majority_inputs_envelopes inputs248 inputs_valid248
  · norm_num [envelope248]
  · intro rho hr0 hr1
    have hh := Batch012.bound496 rho hr0 hr1
    norm_num [Batch012.certificate496,envelope248,inputs248,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound497 rho hr0 hr1
    norm_num [Batch012.certificate497,envelope248,inputs248,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs249 : RatMajorityInputs := ⟨(37300012946368452613633777/100000000000000000000000),(125732162006181/25000000000000),(63005843518075071/62500000000000000),(122206958174537523/1000000000000000000),(125732162006181/50000000000000),(80891765995897359/1000000000000000000),26⟩
theorem inputs_valid249 : inputs249.Valid := by decide +kernel
def envelope249 : RatMajorityEnvelope := ⟨124,1,inputs249,1,(54318182652457681/100000000000000000)⟩
theorem envelope_sound249 : envelope249.Sound := by
  apply rat_majority_inputs_envelopes inputs249 inputs_valid249
  · norm_num [envelope249]
  · intro rho hr0 hr1
    have hh := Batch012.bound498 rho hr0 hr1
    norm_num [Batch012.certificate498,envelope249,inputs249,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound499 rho hr0 hr1
    norm_num [Batch012.certificate499,envelope249,inputs249,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs250 : RatMajorityInputs := ⟨(3720110940455545284845987/10000000000000000000000),(876863972317/200000000000),(50405757473966601/50000000000000000),(187013770195056327/1000000000000000000),(876863972317/400000000000),(111675277060597389/1000000000000000000),25⟩
theorem inputs_valid250 : inputs250.Valid := by decide +kernel
def envelope250 : RatMajorityEnvelope := ⟨125,0,inputs250,(1144564021/975070000),(702869606123862459/1000000000000000000)⟩
theorem envelope_sound250 : envelope250.Sound := by
  apply rat_majority_inputs_envelopes inputs250 inputs_valid250
  · norm_num [envelope250]
  · intro rho hr0 hr1
    have hh := Batch012.bound500 rho hr0 hr1
    norm_num [Batch012.certificate500,envelope250,inputs250,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound501 rho hr0 hr1
    norm_num [Batch012.certificate501,envelope250,inputs250,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs251 : RatMajorityInputs := ⟨(3720110940455545284845987/10000000000000000000000),(251563553909009/50000000000000),(50405757473966601/50000000000000000),(122042821983149421/1000000000000000000),(251563553909009/100000000000000),(80811536992265561/1000000000000000000),27⟩
theorem inputs_valid251 : inputs251.Valid := by decide +kernel
def envelope251 : RatMajorityEnvelope := ⟨125,1,inputs251,1,(271587521914008453/500000000000000000)⟩
theorem envelope_sound251 : envelope251.Sound := by
  apply rat_majority_inputs_envelopes inputs251 inputs_valid251
  · norm_num [envelope251]
  · intro rho hr0 hr1
    have hh := Batch012.bound502 rho hr0 hr1
    norm_num [Batch012.certificate502,envelope251,inputs251,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound503 rho hr0 hr1
    norm_num [Batch012.certificate503,envelope251,inputs251,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs252 : RatMajorityInputs := ⟨(7387997995670680181415391/20000000000000000000000),(548415299929/125000000000),(100817287768269059/100000000000000000),(186654167910882499/1000000000000000000),(548415299929/250000000000),(27876937055501867/250000000000000000),25⟩
theorem inputs_valid252 : inputs252.Valid := by decide +kernel
def envelope252 : RatMajorityEnvelope := ⟨126,0,inputs252,(1143592029/974575000),(1756264745220661/2500000000000000)⟩
theorem envelope_sound252 : envelope252.Sound := by
  apply rat_majority_inputs_envelopes inputs252 inputs_valid252
  · norm_num [envelope252]
  · intro rho hr0 hr1
    have hh := Batch012.bound504 rho hr0 hr1
    norm_num [Batch012.certificate504,envelope252,inputs252,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound505 rho hr0 hr1
    norm_num [Batch012.certificate505,envelope252,inputs252,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs253 : RatMajorityInputs := ⟨(7387997995670680181415391/20000000000000000000000),(100577460627091/20000000000000),(100817287768269059/100000000000000000),(15280147146657757/125000000000000000),(100577460627091/40000000000000),(40454245015005259/500000000000000000),26⟩
theorem inputs_valid253 : inputs253.Valid := by decide +kernel
def envelope253 : RatMajorityEnvelope := ⟨126,1,inputs253,1,(543222007346310511/1000000000000000000)⟩
theorem envelope_sound253 : envelope253.Sound := by
  apply rat_majority_inputs_envelopes inputs253 inputs_valid253
  · norm_num [envelope253]
  · intro rho hr0 hr1
    have hh := Batch012.bound506 rho hr0 hr1
    norm_num [Batch012.certificate506,envelope253,inputs253,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound507 rho hr0 hr1
    norm_num [Batch012.certificate507,envelope253,inputs253,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs254 : RatMajorityInputs := ⟨(2306776826937426443581869/6250000000000000000000),(27397468319871/6250000000000),(504089955402502797/500000000000000000),(93550340169145161/500000000000000000),(27397468319871/12500000000000),(111715762799439653/1000000000000000000),26⟩
theorem inputs_valid254 : inputs254.Valid := by decide +kernel
def envelope254 : RatMajorityEnvelope := ⟨127,0,inputs254,(71456341/60915000),(351105533180546337/500000000000000000)⟩
theorem envelope_sound254 : envelope254.Sound := by
  apply rat_majority_inputs_envelopes inputs254 inputs_valid254
  · norm_num [envelope254]
  · intro rho hr0 hr1
    have hh := Batch012.bound508 rho hr0 hr1
    norm_num [Batch012.certificate508,envelope254,inputs254,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound509 rho hr0 hr1
    norm_num [Batch012.certificate509,envelope254,inputs254,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs255 : RatMajorityInputs := ⟨(2306776826937426443581869/6250000000000000000000),(1966304901873/390625000000),(504089955402502797/500000000000000000),(121838858244523903/1000000000000000000),(1966304901873/781250000000),(4035590885521407/50000000000000000),27⟩
theorem inputs_valid255 : inputs255.Valid := by decide +kernel
def envelope255 : RatMajorityEnvelope := ⟨127,1,inputs255,1,(271592065079843011/500000000000000000)⟩
theorem envelope_sound255 : envelope255.Sound := by
  apply rat_majority_inputs_envelopes inputs255 inputs_valid255
  · norm_num [envelope255]
  · intro rho hr0 hr1
    have hh := Batch012.bound510 rho hr0 hr1
    norm_num [Batch012.certificate510,envelope255,inputs255,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound511 rho hr0 hr1
    norm_num [Batch012.certificate511,envelope255,inputs255,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs256 : RatMajorityInputs := ⟨(23007661912668503882211/62500000000000000000),(2190718685049/500000000000),(201640283316484777/200000000000000000),(37471909574802923/200000000000000000),(2190718685049/1000000000000),(111836344619401279/1000000000000000000),25⟩
theorem inputs_valid256 : inputs256.Valid := by decide +kernel
def envelope256 : RatMajorityEnvelope := ⟨128,0,inputs256,(571292137/487250000),(701734456392772893/1000000000000000000)⟩
theorem envelope_sound256 : envelope256.Sound := by
  apply rat_majority_inputs_envelopes inputs256 inputs_valid256
  · norm_num [envelope256]
  · intro rho hr0 hr1
    have hh := Batch012.bound512 rho hr0 hr1
    norm_num [Batch012.certificate512,envelope256,inputs256,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound513 rho hr0 hr1
    norm_num [Batch012.certificate513,envelope256,inputs256,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs257 : RatMajorityInputs := ⟨(23007661912668503882211/62500000000000000000),(5035201878779/1000000000000),(201640283316484777/200000000000000000),(121718303871911271/1000000000000000000),(5035201878779/2000000000000),(80652865950397961/1000000000000000000),26⟩
theorem inputs_valid257 : inputs257.Valid := by decide +kernel
def envelope257 : RatMajorityEnvelope := ⟨128,1,inputs257,1,(271590879055425407/500000000000000000)⟩
theorem envelope_sound257 : envelope257.Sound := by
  apply rat_majority_inputs_envelopes inputs257 inputs_valid257
  · norm_num [envelope257]
  · intro rho hr0 hr1
    have hh := Batch012.bound514 rho hr0 hr1
    norm_num [Batch012.certificate514,envelope257,inputs257,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound515 rho hr0 hr1
    norm_num [Batch012.certificate515,envelope257,inputs257,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs258 : RatMajorityInputs := ⟨(8964041135407089899681/24414062500000000000),(27485045350827/6250000000000),(31506965474555557/31250000000000000),(74170734466413/400000000000000),(27485045350827/12500000000000),(2218715989588269/20000000000000000),25⟩
theorem inputs_valid258 : inputs258.Valid := by decide +kernel
def envelope258 : RatMajorityEnvelope := ⟨129,0,inputs258,(571042377/487180000),(1402513578780353/2000000000000000)⟩
theorem envelope_sound258 : envelope258.Sound := by
  apply rat_majority_inputs_envelopes inputs258 inputs_valid258
  · norm_num [envelope258]
  · intro rho hr0 hr1
    have hh := Batch012.bound516 rho hr0 hr1
    norm_num [Batch012.certificate516,envelope258,inputs258,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound517 rho hr0 hr1
    norm_num [Batch012.certificate517,envelope258,inputs258,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs259 : RatMajorityInputs := ⟨(8964041135407089899681/24414062500000000000),(31378725295587/6250000000000),(31506965474555557/31250000000000000),(24585603009661711/200000000000000000),(31378725295587/12500000000000),(16248804598507533/200000000000000000),26⟩
theorem inputs_valid259 : inputs259.Valid := by decide +kernel
def envelope259 : RatMajorityEnvelope := ⟨129,1,inputs259,1,(21732616492704143/40000000000000000)⟩
theorem envelope_sound259 : envelope259.Sound := by
  apply rat_majority_inputs_envelopes inputs259 inputs_valid259
  · norm_num [envelope259]
  · intro rho hr0 hr1
    have hh := Batch012.bound518 rho hr0 hr1
    norm_num [Batch012.certificate518,envelope259,inputs259,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch012.bound519 rho hr0 hr1
    norm_num [Batch012.certificate519,envelope259,inputs259,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope240,envelope241,envelope242,envelope243,envelope244,envelope245,envelope246,envelope247,envelope248,envelope249,envelope250,envelope251,envelope252,envelope253,envelope254,envelope255,envelope256,envelope257,envelope258,envelope259]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound240
  · exact envelope_sound241
  · exact envelope_sound242
  · exact envelope_sound243
  · exact envelope_sound244
  · exact envelope_sound245
  · exact envelope_sound246
  · exact envelope_sound247
  · exact envelope_sound248
  · exact envelope_sound249
  · exact envelope_sound250
  · exact envelope_sound251
  · exact envelope_sound252
  · exact envelope_sound253
  · exact envelope_sound254
  · exact envelope_sound255
  · exact envelope_sound256
  · exact envelope_sound257
  · exact envelope_sound258
  · exact envelope_sound259

end Cycle12.MajorityCertificates.Inputs012
