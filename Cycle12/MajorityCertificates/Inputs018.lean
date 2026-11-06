import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch018

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs018

def inputs360 : RatMajorityInputs := ⟨(180646184676799949773251911/25000000000000000000000),(106207676321967/25000000000000),(200083062065142663/200000000000000000),(159319750196833/781250000000000),(106207676321967/50000000000000),(119534107916609297/1000000000000000000),25⟩
theorem inputs_valid360 : inputs360.Valid := by decide +kernel
def envelope360 : RatMajorityEnvelope := ⟨180,0,inputs360,(2656717367/2263640000),(700156289567224529/1000000000000000000)⟩
theorem envelope_sound360 : envelope360.Sound := by
  apply rat_majority_inputs_envelopes inputs360 inputs_valid360
  · norm_num [envelope360]
  · intro rho hr0 hr1
    have hh := Batch018.bound720 rho hr0 hr1
    norm_num [Batch018.certificate720,envelope360,inputs360,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound721 rho hr0 hr1
    norm_num [Batch018.certificate721,envelope360,inputs360,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs361 : RatMajorityInputs := ⟨(180646184676799949773251911/25000000000000000000000),(12215530494447/2500000000000),(200083062065142663/200000000000000000),(6728434342238749/50000000000000000),(12215530494447/5000000000000),(86890541260490393/1000000000000000000),26⟩
theorem inputs_valid361 : inputs361.Valid := by decide +kernel
def envelope361 : RatMajorityEnvelope := ⟨180,1,inputs361,1,(2163887162281563/4000000000000000)⟩
theorem envelope_sound361 : envelope361.Sound := by
  apply rat_majority_inputs_envelopes inputs361 inputs_valid361
  · norm_num [envelope361]
  · intro rho hr0 hr1
    have hh := Batch018.bound722 rho hr0 hr1
    norm_num [Batch018.certificate722,envelope361,inputs361,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound723 rho hr0 hr1
    norm_num [Batch018.certificate723,envelope361,inputs361,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs362 : RatMajorityInputs := ⟨(20242076835061994262335097/3125000000000000000000),(4248711033807/1000000000000),(250115827766672933/250000000000000000),(101938598389954021/500000000000000000),(4248711033807/2000000000000),(119509965605008717/1000000000000000000),25⟩
theorem inputs_valid362 : inputs362.Valid := by decide +kernel
def envelope362 : RatMajorityEnvelope := ⟨181,0,inputs362,(2651372087/2256420000),(701417651176898647/1000000000000000000)⟩
theorem envelope_sound362 : envelope362.Sound := by
  apply rat_majority_inputs_envelopes inputs362 inputs_valid362
  · norm_num [envelope362]
  · intro rho hr0 hr1
    have hh := Batch018.bound724 rho hr0 hr1
    norm_num [Batch018.certificate724,envelope362,inputs362,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound725 rho hr0 hr1
    norm_num [Batch018.certificate725,envelope362,inputs362,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs363 : RatMajorityInputs := ⟨(20242076835061994262335097/3125000000000000000000),(24494315831991/5000000000000),(250115827766672933/250000000000000000),(66716366358750857/500000000000000000),(24494315831991/10000000000000),(3453706046680653/40000000000000000),26⟩
theorem inputs_valid363 : inputs363.Valid := by decide +kernel
def envelope363 : RatMajorityEnvelope := ⟨181,1,inputs363,1,(540869008393896019/1000000000000000000)⟩
theorem envelope_sound363 : envelope363.Sound := by
  apply rat_majority_inputs_envelopes inputs363 inputs_valid363
  · norm_num [envelope363]
  · intro rho hr0 hr1
    have hh := Batch018.bound726 rho hr0 hr1
    norm_num [Batch018.certificate726,envelope363,inputs363,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound727 rho hr0 hr1
    norm_num [Batch018.certificate727,envelope363,inputs363,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs364 : RatMajorityInputs := ⟨(584334875862019462107767877/100000000000000000000000),(425014938761643/100000000000000),(1000513609320040983/1000000000000000000),(203691846584134489/1000000000000000000),(425014938761643/200000000000000),(59712023848326589/500000000000000000),25⟩
theorem inputs_valid364 : inputs364.Valid := by decide +kernel
def envelope364 : RatMajorityEnvelope := ⟨182,0,inputs364,(165384781/140585625),(702647177541326503/1000000000000000000)⟩
theorem envelope_sound364 : envelope364.Sound := by
  apply rat_majority_inputs_envelopes inputs364 inputs_valid364
  · norm_num [envelope364]
  · intro rho hr0 hr1
    have hh := Batch018.bound728 rho hr0 hr1
    norm_num [Batch018.certificate728,envelope364,inputs364,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound729 rho hr0 hr1
    norm_num [Batch018.certificate729,envelope364,inputs364,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs365 : RatMajorityInputs := ⟨(584334875862019462107767877/100000000000000000000000),(489840804135567/100000000000000),(1000513609320040983/1000000000000000000),(66736726022444599/500000000000000000),(489840804135567/200000000000000),(10795287719274047/125000000000000000),27⟩
theorem inputs_valid365 : inputs365.Valid := by decide +kernel
def envelope365 : RatMajorityEnvelope := ⟨182,1,inputs365,1,(270448197820992961/500000000000000000)⟩
theorem envelope_sound365 : envelope365.Sound := by
  apply rat_majority_inputs_envelopes inputs365 inputs_valid365
  · norm_num [envelope365]
  · intro rho hr0 hr1
    have hh := Batch018.bound730 rho hr0 hr1
    norm_num [Batch018.certificate730,envelope365,inputs365,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound731 rho hr0 hr1
    norm_num [Batch018.certificate731,envelope365,inputs365,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs366 : RatMajorityInputs := ⟨(8283278847036736079721047/1562500000000000000000),(1660422367727/390625000000),(1000566148272280889/1000000000000000000),(20362334361585649/100000000000000000),(1660422367727/781250000000),(59696146330168269/500000000000000000),25⟩
theorem inputs_valid366 : inputs366.Valid := by decide +kernel
def envelope366 : RatMajorityEnvelope := ⟨183,0,inputs366,(165072021/140155000),(351953748669375053/500000000000000000)⟩
theorem envelope_sound366 : envelope366.Sound := by
  apply rat_majority_inputs_envelopes inputs366 inputs_valid366
  · norm_num [envelope366]
  · intro rho hr0 hr1
    have hh := Batch018.bound732 rho hr0 hr1
    norm_num [Batch018.certificate732,envelope366,inputs366,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound733 rho hr0 hr1
    norm_num [Batch018.certificate733,envelope366,inputs366,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs367 : RatMajorityInputs := ⟨(8283278847036736079721047/1562500000000000000000),(12246669814067/2500000000000),(1000566148272280889/1000000000000000000),(133450199261574153/1000000000000000000),(12246669814067/5000000000000),(86351080381350493/1000000000000000000),26⟩
theorem inputs_valid367 : inputs367.Valid := by decide +kernel
def envelope367 : RatMajorityEnvelope := ⟨183,1,inputs367,1,(540917796337272989/1000000000000000000)⟩
theorem envelope_sound367 : envelope367.Sound := by
  apply rat_majority_inputs_envelopes inputs367 inputs_valid367
  · norm_num [envelope367]
  · intro rho hr0 hr1
    have hh := Batch018.bound734 rho hr0 hr1
    norm_num [Batch018.certificate734,envelope367,inputs367,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound735 rho hr0 hr1
    norm_num [Batch018.certificate735,envelope367,inputs367,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs368 : RatMajorityInputs := ⟨(60428779957077446733055477/12500000000000000000000),(6614231832903/1562500000000),(1000620864890410821/1000000000000000000),(205896882426059029/1000000000000000000),(6614231832903/3125000000000),(15055743567342653/125000000000000000),25⟩
theorem inputs_valid368 : inputs368.Valid := by decide +kernel
def envelope368 : RatMajorityEnvelope := ⟨184,0,inputs368,(2637198737/2235760000),(352879258801965617/500000000000000000)⟩
theorem envelope_sound368 : envelope368.Sound := by
  apply rat_majority_inputs_envelopes inputs368 inputs_valid368
  · norm_num [envelope368]
  · intro rho hr0 hr1
    have hh := Batch018.bound736 rho hr0 hr1
    norm_num [Batch018.certificate736,envelope368,inputs368,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound737 rho hr0 hr1
    norm_num [Batch018.certificate737,envelope368,inputs368,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs369 : RatMajorityInputs := ⟨(60428779957077446733055477/12500000000000000000000),(153096824011/31250000000),(1000620864890410821/1000000000000000000),(66705846931639547/500000000000000000),(153096824011/62500000000),(17266499556785307/200000000000000000),26⟩
theorem inputs_valid369 : inputs369.Valid := by decide +kernel
def envelope369 : RatMajorityEnvelope := ⟨184,1,inputs369,1,(108187704300413353/200000000000000000)⟩
theorem envelope_sound369 : envelope369.Sound := by
  apply rat_majority_inputs_envelopes inputs369 inputs_valid369
  · norm_num [envelope369]
  · intro rho hr0 hr1
    have hh := Batch018.bound738 rho hr0 hr1
    norm_num [Batch018.certificate738,envelope369,inputs369,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound739 rho hr0 hr1
    norm_num [Batch018.certificate739,envelope369,inputs369,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs370 : RatMajorityInputs := ⟨(2768170915682489972881673/625000000000000000000),(10632497588397/2500000000000),(500338849790443061/500000000000000000),(203325049802571093/1000000000000000000),(10632497588397/5000000000000),(119254010627905067/1000000000000000000),25⟩
theorem inputs_valid370 : inputs370.Valid := by decide +kernel
def envelope370 : RatMajorityEnvelope := ⟨185,0,inputs370,(657902569/557300000),(706390327959591827/1000000000000000000)⟩
theorem envelope_sound370 : envelope370.Sound := by
  apply rat_majority_inputs_envelopes inputs370 inputs_valid370
  · norm_num [envelope370]
  · intro rho hr0 hr1
    have hh := Batch018.bound740 rho hr0 hr1
    norm_num [Batch018.certificate740,envelope370,inputs370,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound741 rho hr0 hr1
    norm_num [Batch018.certificate741,envelope370,inputs370,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs371 : RatMajorityInputs := ⟨(2768170915682489972881673/625000000000000000000),(3069762376417/625000000000),(500338849790443061/500000000000000000),(26459173788949337/200000000000000000),(3069762376417/1250000000000),(85793682894789239/1000000000000000000),26⟩
theorem inputs_valid371 : inputs371.Valid := by decide +kernel
def envelope371 : RatMajorityEnvelope := ⟨185,1,inputs371,1,(10816849762381749/20000000000000000)⟩
theorem envelope_sound371 : envelope371.Sound := by
  apply rat_majority_inputs_envelopes inputs371 inputs_valid371
  · norm_num [envelope371]
  · intro rho hr0 hr1
    have hh := Batch018.bound742 rho hr0 hr1
    norm_num [Batch018.certificate742,envelope371,inputs371,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound743 rho hr0 hr1
    norm_num [Batch018.certificate743,envelope371,inputs371,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs372 : RatMajorityInputs := ⟨(407514306465183535833901563/100000000000000000000000),(85074982439049/20000000000000),(1000736592209693337/1000000000000000000),(25403574157866251/125000000000000000),(85074982439049/40000000000000),(119209293596535157/1000000000000000000),25⟩
theorem inputs_valid372 : inputs372.Valid := by decide +kernel
def envelope372 : RatMajorityEnvelope := ⟨186,0,inputs372,(54731267/46308125),(70764672354015013/100000000000000000)⟩
theorem envelope_sound372 : envelope372.Sound := by
  apply rat_majority_inputs_envelopes inputs372 inputs_valid372
  · norm_num [envelope372]
  · intro rho hr0 hr1
    have hh := Batch018.bound744 rho hr0 hr1
    norm_num [Batch018.certificate744,envelope372,inputs372,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound745 rho hr0 hr1
    norm_num [Batch018.certificate745,envelope372,inputs372,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs373 : RatMajorityInputs := ⟨(407514306465183535833901563/100000000000000000000000),(245617506576387/50000000000000),(1000736592209693337/1000000000000000000),(3305776052815777/25000000000000000),(245617506576387/100000000000000),(42881179897843739/500000000000000000),27⟩
theorem inputs_valid373 : inputs373.Valid := by decide +kernel
def envelope373 : RatMajorityEnvelope := ⟨186,1,inputs373,1,(67607787251007919/125000000000000000)⟩
theorem envelope_sound373 : envelope373.Sound := by
  apply rat_majority_inputs_envelopes inputs373 inputs_valid373
  · norm_num [envelope373]
  · intro rho hr0 hr1
    have hh := Batch018.bound746 rho hr0 hr1
    norm_num [Batch018.certificate746,envelope373,inputs373,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound747 rho hr0 hr1
    norm_num [Batch018.certificate747,envelope373,inputs373,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs374 : RatMajorityInputs := ⟨(23526078324570141269446611/6250000000000000000000),(106070658542037/25000000000000),(500398741114046147/500000000000000000),(51159246270905249/250000000000000000),(106070658542037/50000000000000),(2996553077808269/25000000000000000),25⟩
theorem inputs_valid374 : inputs374.Valid := by decide +kernel
def envelope374 : RatMajorityEnvelope := ⟨187,0,inputs374,(327685583/277065000),(354274883702549447/500000000000000000)⟩
theorem envelope_sound374 : envelope374.Sound := by
  apply rat_majority_inputs_envelopes inputs374 inputs_valid374
  · norm_num [envelope374]
  · intro rho hr0 hr1
    have hh := Batch018.bound748 rho hr0 hr1
    norm_num [Batch018.certificate748,envelope374,inputs374,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound749 rho hr0 hr1
    norm_num [Batch018.certificate749,envelope374,inputs374,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs375 : RatMajorityInputs := ⟨(23526078324570141269446611/6250000000000000000000),(24577136216433/5000000000000),(500398741114046147/500000000000000000),(26391642788865519/200000000000000000),(24577136216433/10000000000000),(21407627766779289/250000000000000000),26⟩
theorem inputs_valid375 : inputs375.Valid := by decide +kernel
def envelope375 : RatMajorityEnvelope := ⟨187,1,inputs375,1,(108172070574812269/200000000000000000)⟩
theorem envelope_sound375 : envelope375.Sound := by
  apply rat_majority_inputs_envelopes inputs375 inputs_valid375
  · norm_num [envelope375]
  · intro rho hr0 hr1
    have hh := Batch018.bound750 rho hr0 hr1
    norm_num [Batch018.certificate750,envelope375,inputs375,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound751 rho hr0 hr1
    norm_num [Batch018.certificate751,envelope375,inputs375,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs376 : RatMajorityInputs := ⟨(69790011138675741916395877/20000000000000000000000),(213035186090997/50000000000000),(500430148555839663/500000000000000000),(202336098130386937/1000000000000000000),(213035186090997/100000000000000),(14849435876198071/125000000000000000),27⟩
theorem inputs_valid376 : inputs376.Valid := by decide +kernel
def envelope376 : RatMajorityEnvelope := ⟨188,0,inputs376,(2616471959/2210410000),(35462488002484803/50000000000000000)⟩
theorem envelope_sound376 : envelope376.Sound := by
  apply rat_majority_inputs_envelopes inputs376 inputs_valid376
  · norm_num [envelope376]
  · intro rho hr0 hr1
    have hh := Batch018.bound752 rho hr0 hr1
    norm_num [Batch018.certificate752,envelope376,inputs376,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound753 rho hr0 hr1
    norm_num [Batch018.certificate753,envelope376,inputs376,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs377 : RatMajorityInputs := ⟨(69790011138675741916395877/20000000000000000000000),(123114480513447/25000000000000),(500430148555839663/500000000000000000),(5245988122725837/40000000000000000),(123114480513447/50000000000000),(10654945249239697/125000000000000000),26⟩
theorem inputs_valid377 : inputs377.Valid := by decide +kernel
def envelope377 : RatMajorityEnvelope := ⟨188,1,inputs377,1,(135200262102132739/250000000000000000)⟩
theorem envelope_sound377 : envelope377.Sound := by
  apply rat_majority_inputs_envelopes inputs377 inputs_valid377
  · norm_num [envelope377]
  · intro rho hr0 hr1
    have hh := Batch018.bound754 rho hr0 hr1
    norm_num [Batch018.certificate754,envelope377,inputs377,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound755 rho hr0 hr1
    norm_num [Batch018.certificate755,envelope377,inputs377,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs378 : RatMajorityInputs := ⟨(4057051602754700542890243/1250000000000000000000),(213292418324139/50000000000000),(1000924981506722401/1000000000000000000),(5041949831034121/25000000000000000),(213292418324139/100000000000000),(118490299414192843/1000000000000000000),25⟩
theorem inputs_valid378 : inputs378.Valid := by decide +kernel
def envelope378 : RatMajorityEnvelope := ⟨189,0,inputs378,(2610387209/2204430000),(22175746524567637/31250000000000000)⟩
theorem envelope_sound378 : envelope378.Sound := by
  apply rat_majority_inputs_envelopes inputs378 inputs_valid378
  · norm_num [envelope378]
  · intro rho hr0 hr1
    have hh := Batch018.bound756 rho hr0 hr1
    norm_num [Batch018.certificate756,envelope378,inputs378,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound757 rho hr0 hr1
    norm_num [Batch018.certificate757,envelope378,inputs378,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs379 : RatMajorityInputs := ⟨(4057051602754700542890243/1250000000000000000000),(492448465744221/100000000000000),(1000924981506722401/1000000000000000000),(16394754324271677/125000000000000000),(492448465744221/200000000000000),(21310898086906339/250000000000000000),26⟩
theorem inputs_valid379 : inputs379.Valid := by decide +kernel
def envelope379 : RatMajorityEnvelope := ⟨189,1,inputs379,1,(540831520732436853/1000000000000000000)⟩
theorem envelope_sound379 : envelope379.Sound := by
  apply rat_majority_inputs_envelopes inputs379 inputs_valid379
  · norm_num [envelope379]
  · intro rho hr0 hr1
    have hh := Batch018.bound758 rho hr0 hr1
    norm_num [Batch018.certificate758,envelope379,inputs379,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch018.bound759 rho hr0 hr1
    norm_num [Batch018.certificate759,envelope379,inputs379,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope360,envelope361,envelope362,envelope363,envelope364,envelope365,envelope366,envelope367,envelope368,envelope369,envelope370,envelope371,envelope372,envelope373,envelope374,envelope375,envelope376,envelope377,envelope378,envelope379]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound360
  · exact envelope_sound361
  · exact envelope_sound362
  · exact envelope_sound363
  · exact envelope_sound364
  · exact envelope_sound365
  · exact envelope_sound366
  · exact envelope_sound367
  · exact envelope_sound368
  · exact envelope_sound369
  · exact envelope_sound370
  · exact envelope_sound371
  · exact envelope_sound372
  · exact envelope_sound373
  · exact envelope_sound374
  · exact envelope_sound375
  · exact envelope_sound376
  · exact envelope_sound377
  · exact envelope_sound378
  · exact envelope_sound379

end Cycle12.MajorityCertificates.Inputs018
