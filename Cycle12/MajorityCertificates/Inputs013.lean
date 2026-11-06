import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs013

def inputs260 : RatMajorityInputs := ⟨(4577723117343193810630833/12500000000000000000000),(21968254701549/5000000000000),(1008244346335177707/1000000000000000000),(92949072526874423/500000000000000000),(21968254701549/10000000000000),(111155465203909659/1000000000000000000),27⟩
theorem inputs_valid260 : inputs260.Valid := by decide +kernel
def envelope260 : RatMajorityEnvelope := ⟨130,0,inputs260,(380603461/324740000),(701209875935287391/1000000000000000000)⟩
theorem envelope_sound260 : envelope260.Sound := by
  apply rat_majority_inputs_envelopes inputs260 inputs_valid260
  · norm_num [envelope260]
  · intro rho hr0 hr1
    have hh := Batch013.bound520 rho hr0 hr1
    norm_num [Batch013.certificate520,envelope260,inputs260,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound521 rho hr0 hr1
    norm_num [Batch013.certificate521,envelope260,inputs260,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs261 : RatMajorityInputs := ⟨(4577723117343193810630833/12500000000000000000000),(125577588953583/25000000000000),(1008244346335177707/1000000000000000000),(122719576213021101/1000000000000000000),(125577588953583/50000000000000),(40571113342578553/500000000000000000),26⟩
theorem inputs_valid261 : inputs261.Valid := by decide +kernel
def envelope261 : RatMajorityEnvelope := ⟨130,1,inputs261,1,(108660794602500853/200000000000000000)⟩
theorem envelope_sound261 : envelope261.Sound := by
  apply rat_majority_inputs_envelopes inputs261 inputs_valid261
  · norm_num [envelope261]
  · intro rho hr0 hr1
    have hh := Batch013.bound522 rho hr0 hr1
    norm_num [Batch013.certificate522,envelope261,inputs261,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound523 rho hr0 hr1
    norm_num [Batch013.certificate523,envelope261,inputs261,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs262 : RatMajorityInputs := ⟨(35671359245253700719297/97656250000000000000),(430140507147/97656250000),(252066442437751919/250000000000000000),(184591687058681853/1000000000000000000),(430140507147/195312500000),(110546459702451081/1000000000000000000),25⟩
theorem inputs_valid262 : inputs262.Valid := by decide +kernel
def envelope262 : RatMajorityEnvelope := ⟨131,0,inputs262,(2282264741/1948160000),(175156192071340867/250000000000000000)⟩
theorem envelope_sound262 : envelope262.Sound := by
  apply rat_majority_inputs_envelopes inputs262 inputs_valid262
  · norm_num [envelope262]
  · intro rho hr0 hr1
    have hh := Batch013.bound524 rho hr0 hr1
    norm_num [Batch013.certificate524,envelope262,inputs262,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound525 rho hr0 hr1
    norm_num [Batch013.certificate525,envelope262,inputs262,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs263 : RatMajorityInputs := ⟨(35671359245253700719297/97656250000000000000),(392477099713/78125000000),(252066442437751919/250000000000000000),(122669471834565637/1000000000000000000),(392477099713/156250000000),(20279438271574279/250000000000000000),26⟩
theorem inputs_valid263 : inputs263.Valid := by decide +kernel
def envelope263 : RatMajorityEnvelope := ⟨131,1,inputs263,1,(271654369132777803/500000000000000000)⟩
theorem envelope_sound263 : envelope263.Sound := by
  apply rat_majority_inputs_envelopes inputs263 inputs_valid263
  · norm_num [envelope263]
  · intro rho hr0 hr1
    have hh := Batch013.bound526 rho hr0 hr1
    norm_num [Batch013.certificate526,envelope263,inputs263,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound527 rho hr0 hr1
    norm_num [Batch013.certificate527,envelope263,inputs263,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs264 : RatMajorityInputs := ⟨(1821688439181577677837379/5000000000000000000000),(54965777325129/12500000000000),(1008287165153929489/1000000000000000000),(185467903312828019/1000000000000000000),(54965777325129/25000000000000),(110954941445626383/1000000000000000000),25⟩
theorem inputs_valid264 : inputs264.Valid := by decide +kernel
def envelope264 : RatMajorityEnvelope := ⟨132,0,inputs264,(1140828207/973940000),(140117467097485699/200000000000000000)⟩
theorem envelope_sound264 : envelope264.Sound := by
  apply rat_majority_inputs_envelopes inputs264 inputs_valid264
  · norm_num [envelope264]
  · intro rho hr0 hr1
    have hh := Batch013.bound528 rho hr0 hr1
    norm_num [Batch013.certificate528,envelope264,inputs264,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound529 rho hr0 hr1
    norm_num [Batch013.certificate529,envelope264,inputs264,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs265 : RatMajorityInputs := ⟨(1821688439181577677837379/5000000000000000000000),(5023190850029/1000000000000),(1008287165153929489/1000000000000000000),(122712325669263311/1000000000000000000),(5023190850029/2000000000000),(10142335654181857/125000000000000000),27⟩
theorem inputs_valid265 : inputs265.Valid := by decide +kernel
def envelope265 : RatMajorityEnvelope := ⟨132,1,inputs265,1,(543323004787396899/1000000000000000000)⟩
theorem envelope_sound265 : envelope265.Sound := by
  apply rat_majority_inputs_envelopes inputs265 inputs_valid265
  · norm_num [envelope265]
  · intro rho hr0 hr1
    have hh := Batch013.bound530 rho hr0 hr1
    norm_num [Batch013.certificate530,envelope265,inputs265,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound531 rho hr0 hr1
    norm_num [Batch013.certificate531,envelope265,inputs265,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs266 : RatMajorityInputs := ⟨(4522978622681109352880661/12500000000000000000000),(27504280624449/6250000000000),(1008344779890064423/1000000000000000000),(185060904250709073/1000000000000000000),(27504280624449/12500000000000),(110765220321947791/1000000000000000000),25⟩
theorem inputs_valid266 : inputs266.Valid := by decide +kernel
def envelope266 : RatMajorityEnvelope := ⟨133,0,inputs266,(1139867563/973460000),(10940812598656853/15625000000000000)⟩
theorem envelope_sound266 : envelope266.Sound := by
  apply rat_majority_inputs_envelopes inputs266 inputs_valid266
  · norm_num [envelope266]
  · intro rho hr0 hr1
    have hh := Batch013.bound532 rho hr0 hr1
    norm_num [Batch013.certificate532,envelope266,inputs266,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound533 rho hr0 hr1
    norm_num [Batch013.certificate533,envelope266,inputs266,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs267 : RatMajorityInputs := ⟨(4522978622681109352880661/12500000000000000000000),(15697583695087/3125000000000),(1008344779890064423/1000000000000000000),(122709341202063989/1000000000000000000),(15697583695087/6250000000000),(16227445498550069/200000000000000000),26⟩
theorem inputs_valid267 : inputs267.Valid := by decide +kernel
def envelope267 : RatMajorityEnvelope := ⟨133,1,inputs267,1,(271674653143205409/500000000000000000)⟩
theorem envelope_sound267 : envelope267.Sound := by
  apply rat_majority_inputs_envelopes inputs267 inputs_valid267
  · norm_num [envelope267]
  · intro rho hr0 hr1
    have hh := Batch013.bound534 rho hr0 hr1
    norm_num [Batch013.certificate534,envelope267,inputs267,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound535 rho hr0 hr1
    norm_num [Batch013.certificate535,envelope267,inputs267,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs268 : RatMajorityInputs := ⟨(36156832304448235534032663/100000000000000000000000),(440122782930641/100000000000000),(1008351050988186007/1000000000000000000),(184996413650107231/1000000000000000000),(440122782930641/200000000000000),(55367577777944663/500000000000000000),25⟩
theorem inputs_valid268 : inputs268.Valid := by decide +kernel
def envelope268 : RatMajorityEnvelope := ⟨134,0,inputs268,(2278993881/1947070000),(87473032958300997/125000000000000000)⟩
theorem envelope_sound268 : envelope268.Sound := by
  apply rat_majority_inputs_envelopes inputs268 inputs_valid268
  · norm_num [envelope268]
  · intro rho hr0 hr1
    have hh := Batch013.bound536 rho hr0 hr1
    norm_num [Batch013.certificate536,envelope268,inputs268,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound537 rho hr0 hr1
    norm_num [Batch013.certificate537,envelope268,inputs268,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs269 : RatMajorityInputs := ⟨(36156832304448235534032663/100000000000000000000000),(502661717266341/100000000000000),(1008351050988186007/1000000000000000000),(30607008231281569/250000000000000000),(502661717266341/200000000000000),(80999800576462949/1000000000000000000),27⟩
theorem inputs_valid269 : inputs269.Valid := by decide +kernel
def envelope269 : RatMajorityEnvelope := ⟨134,1,inputs269,1,(67915429170024747/125000000000000000)⟩
theorem envelope_sound269 : envelope269.Sound := by
  apply rat_majority_inputs_envelopes inputs269 inputs_valid269
  · norm_num [envelope269]
  · intro rho hr0 hr1
    have hh := Batch013.bound538 rho hr0 hr1
    norm_num [Batch013.certificate538,envelope269,inputs269,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound539 rho hr0 hr1
    norm_num [Batch013.certificate539,envelope269,inputs269,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs270 : RatMajorityInputs := ⟨(450821363358710787076941/1250000000000000000000),(68834676981/15625000000),(126046535989451013/125000000000000000),(46124794761509453/250000000000000000),(68834676981/31250000000),(55251662753456059/500000000000000000),25⟩
theorem inputs_valid270 : inputs270.Valid := by decide +kernel
def envelope270 : RatMajorityEnvelope := ⟨135,0,inputs270,(2277910693/1946800000),(349697155256122249/500000000000000000)⟩
theorem envelope_sound270 : envelope270.Sound := by
  apply rat_majority_inputs_envelopes inputs270 inputs_valid270
  · norm_num [envelope270]
  · intro rho hr0 hr1
    have hh := Batch013.bound540 rho hr0 hr1
    norm_num [Batch013.certificate540,envelope270,inputs270,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound541 rho hr0 hr1
    norm_num [Batch013.certificate541,envelope270,inputs270,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs271 : RatMajorityInputs := ⟨(450821363358710787076941/1250000000000000000000),(1572264624049/312500000000),(126046535989451013/125000000000000000),(3051120724410173/25000000000000000),(1572264624049/625000000000),(80812518099711867/1000000000000000000),26⟩
theorem inputs_valid271 : inputs271.Valid := by decide +kernel
def envelope271 : RatMajorityEnvelope := ⟨135,1,inputs271,1,(21731763690415881/40000000000000000)⟩
theorem envelope_sound271 : envelope271.Sound := by
  apply rat_majority_inputs_envelopes inputs271 inputs_valid271
  · norm_num [envelope271]
  · intro rho hr0 hr1
    have hh := Batch013.bound542 rho hr0 hr1
    norm_num [Batch013.certificate542,envelope271,inputs271,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound543 rho hr0 hr1
    norm_num [Batch013.certificate543,envelope271,inputs271,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs272 : RatMajorityInputs := ⟨(17910602085561672797094939/50000000000000000000000),(221104805965869/50000000000000),(7878357882430273/7812500000000000),(182532063474932839/1000000000000000000),(221104805965869/100000000000000),(21917147183883379/200000000000000000),25⟩
theorem inputs_valid272 : inputs272.Valid := by decide +kernel
def envelope272 : RatMajorityEnvelope := ⟨136,0,inputs272,(91018379/77834400),(139723640142389359/200000000000000000)⟩
theorem envelope_sound272 : envelope272.Sound := by
  apply rat_majority_inputs_envelopes inputs272 inputs_valid272
  · norm_num [envelope272]
  · intro rho hr0 hr1
    have hh := Batch013.bound544 rho hr0 hr1
    norm_num [Batch013.certificate544,envelope272,inputs272,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound545 rho hr0 hr1
    norm_num [Batch013.certificate545,envelope272,inputs272,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs273 : RatMajorityInputs := ⟨(17910602085561672797094939/50000000000000000000000),(1005996096273/200000000000),(7878357882430273/7812500000000000),(1221495384920473/10000000000000000),(1005996096273/400000000000),(80863701377388749/1000000000000000000),27⟩
theorem inputs_valid273 : inputs273.Valid := by decide +kernel
def envelope273 : RatMajorityEnvelope := ⟨136,1,inputs273,1,(543331368094990163/1000000000000000000)⟩
theorem envelope_sound273 : envelope273.Sound := by
  apply rat_majority_inputs_envelopes inputs273 inputs_valid273
  · norm_num [envelope273]
  · intro rho hr0 hr1
    have hh := Batch013.bound546 rho hr0 hr1
    norm_num [Batch013.certificate546,envelope273,inputs273,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound547 rho hr0 hr1
    norm_num [Batch013.certificate547,envelope273,inputs273,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs274 : RatMajorityInputs := ⟨(3579639826272971328645387/10000000000000000000000),(110301414535387/25000000000000),(504217844430377297/500000000000000000),(183714130260658087/1000000000000000000),(110301414535387/50000000000000),(4405488559290619/40000000000000000),25⟩
theorem inputs_valid274 : inputs274.Valid := by decide +kernel
def envelope274 : RatMajorityEnvelope := ⟨137,0,inputs274,(1137474191/973010000),(43650373838235571/62500000000000000)⟩
theorem envelope_sound274 : envelope274.Sound := by
  apply rat_majority_inputs_envelopes inputs274 inputs_valid274
  · norm_num [envelope274]
  · intro rho hr0 hr1
    have hh := Batch013.bound548 rho hr0 hr1
    norm_num [Batch013.certificate548,envelope274,inputs274,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound549 rho hr0 hr1
    norm_num [Batch013.certificate549,envelope274,inputs274,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs275 : RatMajorityInputs := ⟨(3579639826272971328645387/10000000000000000000000),(125844749158247/25000000000000),(504217844430377297/500000000000000000),(951834216749717/7812500000000000),(125844749158247/50000000000000),(40354911722763923/500000000000000000),27⟩
theorem inputs_valid275 : inputs275.Valid := by decide +kernel
def envelope275 : RatMajorityEnvelope := ⟨137,1,inputs275,1,(543301957736796067/1000000000000000000)⟩
theorem envelope_sound275 : envelope275.Sound := by
  apply rat_majority_inputs_envelopes inputs275 inputs_valid275
  · norm_num [envelope275]
  · intro rho hr0 hr1
    have hh := Batch013.bound550 rho hr0 hr1
    norm_num [Batch013.certificate550,envelope275,inputs275,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound551 rho hr0 hr1
    norm_num [Batch013.certificate551,envelope275,inputs275,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs276 : RatMajorityInputs := ⟨(17435440114219323648223/48828125000000000000),(3460701750741/781250000000),(10084567614771157/10000000000000000),(90820647392214849/500000000000000000),(3460701750741/1562500000000),(109169984521411131/1000000000000000000),25⟩
theorem inputs_valid276 : inputs276.Valid := by decide +kernel
def envelope276 : RatMajorityEnvelope := ⟨138,0,inputs276,(1136653447/972880000),(697606698000547713/1000000000000000000)⟩
theorem envelope_sound276 : envelope276.Sound := by
  apply rat_majority_inputs_envelopes inputs276 inputs_valid276
  · norm_num [envelope276]
  · intro rho hr0 hr1
    have hh := Batch013.bound552 rho hr0 hr1
    norm_num [Batch013.certificate552,envelope276,inputs276,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound553 rho hr0 hr1
    norm_num [Batch013.certificate553,envelope276,inputs276,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs277 : RatMajorityInputs := ⟨(17435440114219323648223/48828125000000000000),(31505568600459/6250000000000),(10084567614771157/10000000000000000),(30312496131108107/250000000000000000),(31505568600459/12500000000000),(80423770940091181/1000000000000000000),27⟩
theorem inputs_valid277 : inputs277.Valid := by decide +kernel
def envelope277 : RatMajorityEnvelope := ⟨138,1,inputs277,1,(10865041695731703/20000000000000000)⟩
theorem envelope_sound277 : envelope277.Sound := by
  apply rat_majority_inputs_envelopes inputs277 inputs_valid277
  · norm_num [envelope277]
  · intro rho hr0 hr1
    have hh := Batch013.bound554 rho hr0 hr1
    norm_num [Batch013.certificate554,envelope277,inputs277,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound555 rho hr0 hr1
    norm_num [Batch013.certificate555,envelope277,inputs277,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs278 : RatMajorityInputs := ⟨(22262333920802476033551/62500000000000000000),(8861886556623/2000000000000),(1008477803117348361/1000000000000000000),(2268697033216861/12500000000000000),(8861886556623/4000000000000),(54551022657746439/500000000000000000),25⟩
theorem inputs_valid278 : inputs278.Valid := by decide +kernel
def envelope278 : RatMajorityEnvelope := ⟨139,0,inputs278,(2272365823/1945500000),(69730919062826343/100000000000000000)⟩
theorem envelope_sound278 : envelope278.Sound := by
  apply rat_majority_inputs_envelopes inputs278 inputs_valid278
  · norm_num [envelope278]
  · intro rho hr0 hr1
    have hh := Batch013.bound556 rho hr0 hr1
    norm_num [Batch013.certificate556,envelope278,inputs278,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound557 rho hr0 hr1
    norm_num [Batch013.certificate557,envelope278,inputs278,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs279 : RatMajorityInputs := ⟨(22262333920802476033551/62500000000000000000),(10084576801521/2000000000000),(1008477803117348361/1000000000000000000),(121135195903283681/1000000000000000000),(10084576801521/4000000000000),(80367597485450497/1000000000000000000),26⟩
theorem inputs_valid279 : inputs279.Valid := by decide +kernel
def envelope279 : RatMajorityEnvelope := ⟨139,1,inputs279,1,(543250129162458233/1000000000000000000)⟩
theorem envelope_sound279 : envelope279.Sound := by
  apply rat_majority_inputs_envelopes inputs279 inputs_valid279
  · norm_num [envelope279]
  · intro rho hr0 hr1
    have hh := Batch013.bound558 rho hr0 hr1
    norm_num [Batch013.certificate558,envelope279,inputs279,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch013.bound559 rho hr0 hr1
    norm_num [Batch013.certificate559,envelope279,inputs279,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope260,envelope261,envelope262,envelope263,envelope264,envelope265,envelope266,envelope267,envelope268,envelope269,envelope270,envelope271,envelope272,envelope273,envelope274,envelope275,envelope276,envelope277,envelope278,envelope279]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound260
  · exact envelope_sound261
  · exact envelope_sound262
  · exact envelope_sound263
  · exact envelope_sound264
  · exact envelope_sound265
  · exact envelope_sound266
  · exact envelope_sound267
  · exact envelope_sound268
  · exact envelope_sound269
  · exact envelope_sound270
  · exact envelope_sound271
  · exact envelope_sound272
  · exact envelope_sound273
  · exact envelope_sound274
  · exact envelope_sound275
  · exact envelope_sound276
  · exact envelope_sound277
  · exact envelope_sound278
  · exact envelope_sound279

end Cycle12.MajorityCertificates.Inputs013
