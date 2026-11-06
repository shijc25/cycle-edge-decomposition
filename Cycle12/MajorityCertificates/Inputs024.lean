import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs024

def inputs480 : RatMajorityInputs := ⟨(7049362783727912996279857/10000000000000000000000),(95278271453581/20000000000000),(251067458273058393/250000000000000000),(145996650954306927/1000000000000000000),(95278271453581/40000000000000),(2309241321942773/25000000000000000),26⟩
theorem inputs_valid480 : inputs480.Valid := by decide +kernel
def envelope480 : RatMajorityEnvelope := ⟨240,0,inputs480,(93531409/82426000),(661828700734875467/1000000000000000000)⟩
theorem envelope_sound480 : envelope480.Sound := by
  apply rat_majority_inputs_envelopes inputs480 inputs_valid480
  · norm_num [envelope480]
  · intro rho hr0 hr1
    have hh := Batch024.bound960 rho hr0 hr1
    norm_num [Batch024.certificate960,envelope480,inputs480,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound961 rho hr0 hr1
    norm_num [Batch024.certificate961,envelope480,inputs480,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs481 : RatMajorityInputs := ⟨(7049362783727912996279857/10000000000000000000000),(26289711333843/5000000000000),(251067458273058393/250000000000000000),(104541399240524057/1000000000000000000),(26289711333843/10000000000000),(72152659525284863/1000000000000000000),27⟩
theorem inputs_valid481 : inputs481.Valid := by decide +kernel
def envelope481 : RatMajorityEnvelope := ⟨240,1,inputs481,1,(269805206313151857/500000000000000000)⟩
theorem envelope_sound481 : envelope481.Sound := by
  apply rat_majority_inputs_envelopes inputs481 inputs_valid481
  · norm_num [envelope481]
  · intro rho hr0 hr1
    have hh := Batch024.bound962 rho hr0 hr1
    norm_num [Batch024.certificate962,envelope481,inputs481,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound963 rho hr0 hr1
    norm_num [Batch024.certificate963,envelope481,inputs481,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs482 : RatMajorityInputs := ⟨(1397955086454767173444527/2000000000000000000000),(239120795293341/50000000000000),(1004306354975158643/1000000000000000000),(72107440176513633/500000000000000000),(239120795293341/100000000000000),(11439883294488509/125000000000000000),26⟩
theorem inputs_valid482 : inputs482.Valid := by decide +kernel
def envelope482 : RatMajorityEnvelope := ⟨241,0,inputs482,(2333812171/2059980000),(660074045320724617/1000000000000000000)⟩
theorem envelope_sound482 : envelope482.Sound := by
  apply rat_majority_inputs_envelopes inputs482 inputs_valid482
  · norm_num [envelope482]
  · intro rho hr0 hr1
    have hh := Batch024.bound964 rho hr0 hr1
    norm_num [Batch024.certificate964,envelope482,inputs482,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound965 rho hr0 hr1
    norm_num [Batch024.certificate965,envelope482,inputs482,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs483 : RatMajorityInputs := ⟨(1397955086454767173444527/2000000000000000000000),(131755224169647/25000000000000),(1004306354975158643/1000000000000000000),(51831002269060251/500000000000000000),(131755224169647/50000000000000),(71711476358785269/1000000000000000000),27⟩
theorem inputs_valid483 : inputs483.Valid := by decide +kernel
def envelope483 : RatMajorityEnvelope := ⟨241,1,inputs483,1,(539539901550843587/1000000000000000000)⟩
theorem envelope_sound483 : envelope483.Sound := by
  apply rat_majority_inputs_envelopes inputs483 inputs_valid483
  · norm_num [envelope483]
  · intro rho hr0 hr1
    have hh := Batch024.bound966 rho hr0 hr1
    norm_num [Batch024.certificate966,envelope483,inputs483,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound967 rho hr0 hr1
    norm_num [Batch024.certificate967,envelope483,inputs483,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs484 : RatMajorityInputs := ⟨(195057160181916029837227377/625000000000000000000),(334164296571/78125000000),(50000480631938011/50000000000000000),(200219159061551533/1000000000000000000),(334164296571/156250000000),(58906803914885321/500000000000000000),25⟩
theorem inputs_valid484 : inputs484.Valid := by decide +kernel
def envelope484 : RatMajorityEnvelope := ⟨242,0,inputs484,(34494439/29940000),(340174393341370181/500000000000000000)⟩
theorem envelope_sound484 : envelope484.Sound := by
  apply rat_majority_inputs_envelopes inputs484 inputs_valid484
  · norm_num [envelope484]
  · intro rho hr0 hr1
    have hh := Batch024.bound968 rho hr0 hr1
    norm_num [Batch024.certificate968,envelope484,inputs484,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound969 rho hr0 hr1
    norm_num [Batch024.certificate969,envelope484,inputs484,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs485 : RatMajorityInputs := ⟨(195057160181916029837227377/625000000000000000000),(2893607582709/625000000000),(50000480631938011/50000000000000000),(159499017896987697/1000000000000000000),(2893607582709/1250000000000),(1975548749061763/20000000000000000),26⟩
theorem inputs_valid485 : inputs485.Valid := by decide +kernel
def envelope485 : RatMajorityEnvelope := ⟨242,1,inputs485,1,(543619800084044591/1000000000000000000)⟩
theorem envelope_sound485 : envelope485.Sound := by
  apply rat_majority_inputs_envelopes inputs485 inputs_valid485
  · norm_num [envelope485]
  · intro rho hr0 hr1
    have hh := Batch024.bound970 rho hr0 hr1
    norm_num [Batch024.certificate970,envelope485,inputs485,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound971 rho hr0 hr1
    norm_num [Batch024.certificate971,envelope485,inputs485,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs486 : RatMajorityInputs := ⟨(5016548379112111551208790017/25000000000000000000000),(106190950664021/25000000000000),(500007475346239577/500000000000000000),(51003889836482287/250000000000000000),(106190950664021/50000000000000),(29893525084317431/250000000000000000),25⟩
theorem inputs_valid486 : inputs486.Valid := by decide +kernel
def envelope486 : RatMajorityEnvelope := ⟨243,0,inputs486,(2755984897/2388440000),(682326444642234657/1000000000000000000)⟩
theorem envelope_sound486 : envelope486.Sound := by
  apply rat_majority_inputs_envelopes inputs486 inputs_valid486
  · norm_num [envelope486]
  · intro rho hr0 hr1
    have hh := Batch024.bound972 rho hr0 hr1
    norm_num [Batch024.certificate972,envelope486,inputs486,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound973 rho hr0 hr1
    norm_num [Batch024.certificate973,envelope486,inputs486,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs487 : RatMajorityInputs := ⟨(5016548379112111551208790017/25000000000000000000000),(115890678263869/25000000000000),(500007475346239577/500000000000000000),(158887781349647581/1000000000000000000),(115890678263869/50000000000000),(98488689453814051/1000000000000000000),26⟩
theorem inputs_valid487 : inputs487.Valid := by decide +kernel
def envelope487 : RatMajorityEnvelope := ⟨243,1,inputs487,1,(54355056770696903/100000000000000000)⟩
theorem envelope_sound487 : envelope487.Sound := by
  apply rat_majority_inputs_envelopes inputs487 inputs_valid487
  · norm_num [envelope487]
  · intro rho hr0 hr1
    have hh := Batch024.bound974 rho hr0 hr1
    norm_num [Batch024.certificate974,envelope487,inputs487,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound975 rho hr0 hr1
    norm_num [Batch024.certificate975,envelope487,inputs487,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs488 : RatMajorityInputs := ⟨(109385243453743783707658821/781250000000000000000),(2669797109421/625000000000),(100002142692181721/100000000000000000),(100467384470150689/500000000000000000),(2669797109421/1250000000000),(118145579832722027/1000000000000000000),25⟩
theorem inputs_valid488 : inputs488.Valid := by decide +kernel
def envelope488 : RatMajorityEnvelope := ⟨244,0,inputs488,(343972341/297740000),(341620167527938647/500000000000000000)⟩
theorem envelope_sound488 : envelope488.Sound := by
  apply rat_majority_inputs_envelopes inputs488 inputs_valid488
  · norm_num [envelope488]
  · intro rho hr0 hr1
    have hh := Batch024.bound976 rho hr0 hr1
    norm_num [Batch024.certificate976,envelope488,inputs488,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound977 rho hr0 hr1
    norm_num [Batch024.certificate977,envelope488,inputs488,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs489 : RatMajorityInputs := ⟨(109385243453743783707658821/781250000000000000000),(7231762839141/1562500000000),(100002142692181721/100000000000000000),(159650069227665029/1000000000000000000),(7231762839141/3125000000000),(49424388163823349/500000000000000000),25⟩
theorem inputs_valid489 : inputs489.Valid := by decide +kernel
def envelope489 : RatMajorityEnvelope := ⟨244,1,inputs489,1,(543642719927484319/1000000000000000000)⟩
theorem envelope_sound489 : envelope489.Sound := by
  apply rat_majority_inputs_envelopes inputs489 inputs_valid489
  · norm_num [envelope489]
  · intro rho hr0 hr1
    have hh := Batch024.bound978 rho hr0 hr1
    norm_num [Batch024.certificate978,envelope489,inputs489,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound979 rho hr0 hr1
    norm_num [Batch024.certificate979,envelope489,inputs489,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs490 : RatMajorityInputs := ⟨(1292139886022631976230957111/12500000000000000000000),(106863802863837/25000000000000),(1000029022280704499/1000000000000000000),(200568694210386499/1000000000000000000),(106863802863837/50000000000000),(11797576496334533/100000000000000000),25⟩
theorem inputs_valid490 : inputs490.Valid := by decide +kernel
def envelope490 : RatMajorityEnvelope := ⟨245,0,inputs490,(2748824071/2375610000),(684830005865720979/1000000000000000000)⟩
theorem envelope_sound490 : envelope490.Sound := by
  apply rat_majority_inputs_envelopes inputs490 inputs_valid490
  · norm_num [envelope490]
  · intro rho hr0 hr1
    have hh := Batch024.bound980 rho hr0 hr1
    norm_num [Batch024.certificate980,envelope490,inputs490,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound981 rho hr0 hr1
    norm_num [Batch024.certificate981,envelope490,inputs490,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs491 : RatMajorityInputs := ⟨(1292139886022631976230957111/12500000000000000000000),(463284154110957/100000000000000),(1000029022280704499/1000000000000000000),(159178331246925949/1000000000000000000),(463284154110957/200000000000000),(24656489888266233/250000000000000000),25⟩
theorem inputs_valid491 : inputs491.Valid := by decide +kernel
def envelope491 : RatMajorityEnvelope := ⟨245,1,inputs491,1,(21743631751661729/40000000000000000)⟩
theorem envelope_sound491 : envelope491.Sound := by
  apply rat_majority_inputs_envelopes inputs491 inputs_valid491
  · norm_num [envelope491]
  · intro rho hr0 hr1
    have hh := Batch024.bound982 rho hr0 hr1
    norm_num [Batch024.certificate982,envelope491,inputs491,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound983 rho hr0 hr1
    norm_num [Batch024.certificate983,envelope491,inputs491,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs492 : RatMajorityInputs := ⟨(1132878843256457054853011751/12500000000000000000000),(53513771382549/12500000000000),(1000033102361922243/1000000000000000000),(199737324018529339/1000000000000000000),(53513771382549/25000000000000),(58795025037553443/500000000000000000),25⟩
theorem inputs_valid492 : inputs492.Valid := by decide +kernel
def envelope492 : RatMajorityEnvelope := ⟨246,0,inputs492,(457922309/395480000),(85680753027996917/125000000000000000)⟩
theorem envelope_sound492 : envelope492.Sound := by
  apply rat_majority_inputs_envelopes inputs492 inputs_valid492
  · norm_num [envelope492]
  · intro rho hr0 hr1
    have hh := Batch024.bound984 rho hr0 hr1
    norm_num [Batch024.certificate984,envelope492,inputs492,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound985 rho hr0 hr1
    norm_num [Batch024.certificate985,envelope492,inputs492,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs493 : RatMajorityInputs := ⟨(1132878843256457054853011751/12500000000000000000000),(57959641113237/12500000000000),(1000033102361922243/1000000000000000000),(79384286778524157/500000000000000000),(57959641113237/25000000000000),(12304045278920607/125000000000000000),26⟩
theorem inputs_valid493 : inputs493.Valid := by decide +kernel
def envelope493 : RatMajorityEnvelope := ⟨246,1,inputs493,1,(271772317471279659/500000000000000000)⟩
theorem envelope_sound493 : envelope493.Sound := by
  apply rat_majority_inputs_envelopes inputs493 inputs_valid493
  · norm_num [envelope493]
  · intro rho hr0 hr1
    have hh := Batch024.bound986 rho hr0 hr1
    norm_num [Batch024.certificate986,envelope493,inputs493,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound987 rho hr0 hr1
    norm_num [Batch024.certificate987,envelope493,inputs493,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs494 : RatMajorityInputs := ⟨(798582525549814768618914093/10000000000000000000000),(85609724672241/20000000000000),(20000751353194361/20000000000000000),(24976915742041451/125000000000000000),(85609724672241/40000000000000),(29406560657222331/250000000000000000),26⟩
theorem inputs_valid494 : inputs494.Valid := by decide +kernel
def envelope494 : RatMajorityEnvelope := ⟨247,0,inputs494,(2746290341/2369850000),(686308024633436699/1000000000000000000)⟩
theorem envelope_sound494 : envelope494.Sound := by
  apply rat_majority_inputs_envelopes inputs494 inputs_valid494
  · norm_num [envelope494]
  · intro rho hr0 hr1
    have hh := Batch024.bound988 rho hr0 hr1
    norm_num [Batch024.certificate988,envelope494,inputs494,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound989 rho hr0 hr1
    norm_num [Batch024.certificate989,envelope494,inputs494,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs495 : RatMajorityInputs := ⟨(798582525549814768618914093/10000000000000000000000),(92589344707377/20000000000000),(20000751353194361/20000000000000000),(159530903560342569/1000000000000000000),(92589344707377/40000000000000),(49396248535719547/500000000000000000),26⟩
theorem inputs_valid495 : inputs495.Valid := by decide +kernel
def envelope495 : RatMajorityEnvelope := ⟨247,1,inputs495,1,(108727174150171223/200000000000000000)⟩
theorem envelope_sound495 : envelope495.Sound := by
  apply rat_majority_inputs_envelopes inputs495 inputs_valid495
  · norm_num [envelope495]
  · intro rho hr0 hr1
    have hh := Batch024.bound990 rho hr0 hr1
    norm_num [Batch024.certificate990,envelope495,inputs495,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound991 rho hr0 hr1
    norm_num [Batch024.certificate991,envelope495,inputs495,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs496 : RatMajorityInputs := ⟨(7896476792165319383009733/125000000000000000000),(85526965222083/20000000000000),(250011872821938637/250000000000000000),(626063789156221/3125000000000000),(85526965222083/40000000000000),(23573972328656641/200000000000000000),25⟩
theorem inputs_valid496 : inputs496.Valid := by decide +kernel
def envelope496 : RatMajorityEnvelope := ⟨248,0,inputs496,(2741967449/2363550000),(687491150607215387/1000000000000000000)⟩
theorem envelope_sound496 : envelope496.Sound := by
  apply rat_majority_inputs_envelopes inputs496 inputs_valid496
  · norm_num [envelope496]
  · intro rho hr0 hr1
    have hh := Batch024.bound992 rho hr0 hr1
    norm_num [Batch024.certificate992,envelope496,inputs496,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound993 rho hr0 hr1
    norm_num [Batch024.certificate993,envelope496,inputs496,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs497 : RatMajorityInputs := ⟨(7896476792165319383009733/125000000000000000000),(92492039621499/20000000000000),(250011872821938637/250000000000000000),(32008090416132787/200000000000000000),(92492039621499/40000000000000),(3094784841557471/31250000000000000),26⟩
theorem inputs_valid497 : inputs497.Valid := by decide +kernel
def envelope497 : RatMajorityEnvelope := ⟨248,1,inputs497,1,(6796250080435803/12500000000000000)⟩
theorem envelope_sound497 : envelope497.Sound := by
  apply rat_majority_inputs_envelopes inputs497 inputs_valid497
  · norm_num [envelope497]
  · intro rho hr0 hr1
    have hh := Batch024.bound994 rho hr0 hr1
    norm_num [Batch024.certificate994,envelope497,inputs497,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound995 rho hr0 hr1
    norm_num [Batch024.certificate995,envelope497,inputs497,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs498 : RatMajorityInputs := ⟨(1285979838475037182077883261/25000000000000000000000),(53440140339107/12500000000000),(250014580983304097/250000000000000000),(200484898791050733/1000000000000000000),(53440140339107/25000000000000),(14742111464254751/125000000000000000),25⟩
theorem inputs_valid498 : inputs498.Valid := by decide +kernel
def envelope498 : RatMajorityEnvelope := ⟨249,0,inputs498,(1369892903/1178890000),(344609128905663251/500000000000000000)⟩
theorem envelope_sound498 : envelope498.Sound := by
  apply rat_majority_inputs_envelopes inputs498 inputs_valid498
  · norm_num [envelope498]
  · intro rho hr0 hr1
    have hh := Batch024.bound996 rho hr0 hr1
    norm_num [Batch024.certificate996,envelope498,inputs498,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound997 rho hr0 hr1
    norm_num [Batch024.certificate997,envelope498,inputs498,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs499 : RatMajorityInputs := ⟨(1285979838475037182077883261/25000000000000000000000),(231495091097443/50000000000000),(250014580983304097/250000000000000000),(7974272841360381/50000000000000000),(231495091097443/100000000000000),(12346379057108181/125000000000000000),26⟩
theorem inputs_valid499 : inputs499.Valid := by decide +kernel
def envelope499 : RatMajorityEnvelope := ⟨249,1,inputs499,1,(849437034629871/1562500000000000)⟩
theorem envelope_sound499 : envelope499.Sound := by
  apply rat_majority_inputs_envelopes inputs499 inputs_valid499
  · norm_num [envelope499]
  · intro rho hr0 hr1
    have hh := Batch024.bound998 rho hr0 hr1
    norm_num [Batch024.certificate998,envelope499,inputs499,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch024.bound999 rho hr0 hr1
    norm_num [Batch024.certificate999,envelope499,inputs499,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope480,envelope481,envelope482,envelope483,envelope484,envelope485,envelope486,envelope487,envelope488,envelope489,envelope490,envelope491,envelope492,envelope493,envelope494,envelope495,envelope496,envelope497,envelope498,envelope499]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound480
  · exact envelope_sound481
  · exact envelope_sound482
  · exact envelope_sound483
  · exact envelope_sound484
  · exact envelope_sound485
  · exact envelope_sound486
  · exact envelope_sound487
  · exact envelope_sound488
  · exact envelope_sound489
  · exact envelope_sound490
  · exact envelope_sound491
  · exact envelope_sound492
  · exact envelope_sound493
  · exact envelope_sound494
  · exact envelope_sound495
  · exact envelope_sound496
  · exact envelope_sound497
  · exact envelope_sound498
  · exact envelope_sound499

end Cycle12.MajorityCertificates.Inputs024
