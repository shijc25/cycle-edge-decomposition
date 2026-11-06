import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs011

def inputs220 : RatMajorityInputs := ⟨(1255647060981649833258289/3125000000000000000000),(216998296027667/50000000000000),(1007509859805086087/1000000000000000000),(192394660077351721/1000000000000000000),(216998296027667/100000000000000),(114179562482415079/1000000000000000000),25⟩
theorem inputs_valid220 : inputs220.Valid := by decide +kernel
def envelope220 : RatMajorityEnvelope := ⟨110,0,inputs220,(1157434067/979330000),(710296386059502789/1000000000000000000)⟩
theorem envelope_sound220 : envelope220.Sound := by
  apply rat_majority_inputs_envelopes inputs220 inputs_valid220
  · norm_num [envelope220]
  · intro rho hr0 hr1
    have hh := Batch011.bound440 rho hr0 hr1
    norm_num [Batch011.certificate440,envelope220,inputs220,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound441 rho hr0 hr1
    norm_num [Batch011.certificate441,envelope220,inputs220,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs221 : RatMajorityInputs := ⟨(1255647060981649833258289/3125000000000000000000),(249581786003781/50000000000000),(1007509859805086087/1000000000000000000),(62679132724576489/500000000000000000),(249581786003781/100000000000000),(82429008424103941/1000000000000000000),26⟩
theorem inputs_valid221 : inputs221.Valid := by decide +kernel
def envelope221 : RatMajorityEnvelope := ⟨110,1,inputs221,1,(67904611631354251/125000000000000000)⟩
theorem envelope_sound221 : envelope221.Sound := by
  apply rat_majority_inputs_envelopes inputs221 inputs_valid221
  · norm_num [envelope221]
  · intro rho hr0 hr1
    have hh := Batch011.bound442 rho hr0 hr1
    norm_num [Batch011.certificate442,envelope221,inputs221,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound443 rho hr0 hr1
    norm_num [Batch011.certificate443,envelope221,inputs221,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs222 : RatMajorityInputs := ⟨(39942851216249263610543887/100000000000000000000000),(217142675181943/50000000000000),(1007554842616099643/1000000000000000000),(38408081048415531/200000000000000000),(217142675181943/100000000000000),(114014829944085641/1000000000000000000),25⟩
theorem inputs_valid222 : inputs222.Valid := by decide +kernel
def envelope222 : RatMajorityEnvelope := ⟨111,0,inputs222,(144561282/122373125),(709793239327513341/1000000000000000000)⟩
theorem envelope_sound222 : envelope222.Sound := by
  apply rat_majority_inputs_envelopes inputs222 inputs_valid222
  · norm_num [envelope222]
  · intro rho hr0 hr1
    have hh := Batch011.bound444 rho hr0 hr1
    norm_num [Batch011.certificate444,envelope222,inputs222,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound445 rho hr0 hr1
    norm_num [Batch011.certificate445,envelope222,inputs222,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs223 : RatMajorityInputs := ⟨(39942851216249263610543887/100000000000000000000000),(249746002168439/50000000000000),(1007554842616099643/1000000000000000000),(6254026401355829/50000000000000000),(249746002168439/100000000000000),(41146878875016611/500000000000000000),27⟩
theorem inputs_valid223 : inputs223.Valid := by decide +kernel
def envelope223 : RatMajorityEnvelope := ⟨111,1,inputs223,1,(543228879864249283/1000000000000000000)⟩
theorem envelope_sound223 : envelope223.Sound := by
  apply rat_majority_inputs_envelopes inputs223 inputs_valid223
  · norm_num [envelope223]
  · intro rho hr0 hr1
    have hh := Batch011.bound446 rho hr0 hr1
    norm_num [Batch011.certificate446,envelope223,inputs223,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound447 rho hr0 hr1
    norm_num [Batch011.certificate447,envelope223,inputs223,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs224 : RatMajorityInputs := ⟨(2481772999440661367728989/6250000000000000000000),(434913833024619/100000000000000),(503799859209192939/500000000000000000),(47817818691526381/250000000000000000),(434913833024619/200000000000000),(113657110571078673/1000000000000000000),26⟩
theorem inputs_valid224 : inputs224.Valid := by decide +kernel
def envelope224 : RatMajorityEnvelope := ⟨112,0,inputs224,(2310975469/1957290000),(709191443579303783/1000000000000000000)⟩
theorem envelope_sound224 : envelope224.Sound := by
  apply rat_majority_inputs_envelopes inputs224 inputs_valid224
  · norm_num [envelope224]
  · intro rho hr0 hr1
    have hh := Batch011.bound448 rho hr0 hr1
    norm_num [Batch011.certificate448,envelope224,inputs224,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound449 rho hr0 hr1
    norm_num [Batch011.certificate449,envelope224,inputs224,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs225 : RatMajorityInputs := ⟨(2481772999440661367728989/6250000000000000000000),(49955861193273/10000000000000),(503799859209192939/500000000000000000),(25004853652551421/200000000000000000),(49955861193273/20000000000000),(20566588841629233/250000000000000000),27⟩
theorem inputs_valid225 : inputs225.Valid := by decide +kernel
def envelope225 : RatMajorityEnvelope := ⟨112,1,inputs225,1,(543243730882188723/1000000000000000000)⟩
theorem envelope_sound225 : envelope225.Sound := by
  apply rat_majority_inputs_envelopes inputs225 inputs_valid225
  · norm_num [envelope225]
  · intro rho hr0 hr1
    have hh := Batch011.bound450 rho hr0 hr1
    norm_num [Batch011.certificate450,envelope225,inputs225,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound451 rho hr0 hr1
    norm_num [Batch011.certificate451,envelope225,inputs225,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs226 : RatMajorityInputs := ⟨(1982996544310217923694049/5000000000000000000000),(86991511697283/20000000000000),(1007609054914311749/1000000000000000000),(38243572210145959/200000000000000000),(86991511697283/40000000000000),(113632264738935751/1000000000000000000),26⟩
theorem inputs_valid226 : inputs226.Valid := by decide +kernel
def envelope226 : RatMajorityEnvelope := ⟨113,0,inputs226,(9241387/7829400),(708868521549395381/1000000000000000000)⟩
theorem envelope_sound226 : envelope226.Sound := by
  apply rat_majority_inputs_envelopes inputs226 inputs_valid226
  · norm_num [envelope226]
  · intro rho hr0 hr1
    have hh := Batch011.bound452 rho hr0 hr1
    norm_num [Batch011.certificate452,envelope226,inputs226,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound453 rho hr0 hr1
    norm_num [Batch011.certificate453,envelope226,inputs226,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs227 : RatMajorityInputs := ⟨(1982996544310217923694049/5000000000000000000000),(20000568285303/4000000000000),(1007609054914311749/1000000000000000000),(124640054129784273/1000000000000000000),(20000568285303/8000000000000),(16415833573741537/200000000000000000),27⟩
theorem inputs_valid227 : inputs227.Valid := by decide +kernel
def envelope227 : RatMajorityEnvelope := ⟨113,1,inputs227,1,(543208350460567919/1000000000000000000)⟩
theorem envelope_sound227 : envelope227.Sound := by
  apply rat_majority_inputs_envelopes inputs227 inputs_valid227
  · norm_num [envelope227]
  · intro rho hr0 hr1
    have hh := Batch011.bound454 rho hr0 hr1
    norm_num [Batch011.certificate454,envelope227,inputs227,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound455 rho hr0 hr1
    norm_num [Batch011.certificate455,envelope227,inputs227,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs228 : RatMajorityInputs := ⟨(7908903609438682395433559/20000000000000000000000),(217385576308527/50000000000000),(25190784851077311/25000000000000000),(47861414161443919/250000000000000000),(217385576308527/100000000000000),(113738222714717547/1000000000000000000),25⟩
theorem inputs_valid228 : inputs228.Valid := by decide +kernel
def envelope228 : RatMajorityEnvelope := ⟨114,0,inputs228,(461889581/391402000),(708672269556265717/1000000000000000000)⟩
theorem envelope_sound228 : envelope228.Sound := by
  apply rat_majority_inputs_envelopes inputs228 inputs_valid228
  · norm_num [envelope228]
  · intro rho hr0 hr1
    have hh := Batch011.bound456 rho hr0 hr1
    norm_num [Batch011.certificate456,envelope228,inputs228,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound457 rho hr0 hr1
    norm_num [Batch011.certificate457,envelope228,inputs228,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs229 : RatMajorityInputs := ⟨(7908903609438682395433559/20000000000000000000000),(500192360269591/100000000000000),(25190784851077311/25000000000000000),(4979603951508661/40000000000000000),(500192360269591/200000000000000),(5125380444765989/62500000000000000),27⟩
theorem inputs_valid229 : inputs229.Valid := by decide +kernel
def envelope229 : RatMajorityEnvelope := ⟨114,1,inputs229,1,(135800792132831507/250000000000000000)⟩
theorem envelope_sound229 : envelope229.Sound := by
  apply rat_majority_inputs_envelopes inputs229 inputs_valid229
  · norm_num [envelope229]
  · intro rho hr0 hr1
    have hh := Batch011.bound458 rho hr0 hr1
    norm_num [Batch011.certificate458,envelope229,inputs229,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound459 rho hr0 hr1
    norm_num [Batch011.certificate459,envelope229,inputs229,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs230 : RatMajorityInputs := ⟨(3924910199840754029013473/10000000000000000000000),(87129065956093/20000000000000),(503844588202218837/500000000000000000),(190379358720382763/1000000000000000000),(87129065956093/40000000000000),(56621085406524229/500000000000000000),25⟩
theorem inputs_valid230 : inputs230.Valid := by decide +kernel
def envelope230 : RatMajorityEnvelope := ⟨115,0,inputs230,(2307403363/1955950000),(88529799454754543/125000000000000000)⟩
theorem envelope_sound230 : envelope230.Sound := by
  apply rat_majority_inputs_envelopes inputs230 inputs_valid230
  · norm_num [envelope230]
  · intro rho hr0 hr1
    have hh := Batch011.bound460 rho hr0 hr1
    norm_num [Batch011.certificate460,envelope230,inputs230,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound461 rho hr0 hr1
    norm_num [Batch011.certificate461,envelope230,inputs230,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs231 : RatMajorityInputs := ⟨(3924910199840754029013473/10000000000000000000000),(99986115377089/20000000000000),(503844588202218837/500000000000000000),(124710502820443909/1000000000000000000),(99986115377089/40000000000000),(41056748275481681/500000000000000000),27⟩
theorem inputs_valid231 : inputs231.Valid := by decide +kernel
def envelope231 : RatMajorityEnvelope := ⟨115,1,inputs231,1,(271626267412090611/500000000000000000)⟩
theorem envelope_sound231 : envelope231.Sound := by
  apply rat_majority_inputs_envelopes inputs231 inputs_valid231
  · norm_num [envelope231]
  · intro rho hr0 hr1
    have hh := Batch011.bound462 rho hr0 hr1
    norm_num [Batch011.certificate462,envelope231,inputs231,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound463 rho hr0 hr1
    norm_num [Batch011.certificate463,envelope231,inputs231,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs232 : RatMajorityInputs := ⟨(3902421752685593863575529/10000000000000000000000),(87002603979487/20000000000000),(503866876508971011/500000000000000000),(191150129198640063/1000000000000000000),(87002603979487/40000000000000),(22720151615789621/200000000000000000),26⟩
theorem inputs_valid232 : inputs232.Valid := by decide +kernel
def envelope232 : RatMajorityEnvelope := ⟨116,0,inputs232,(1152978537/977645000),(708026018612808923/1000000000000000000)⟩
theorem envelope_sound232 : envelope232.Sound := by
  apply rat_majority_inputs_envelopes inputs232 inputs_valid232
  · norm_num [envelope232]
  · intro rho hr0 hr1
    have hh := Batch011.bound464 rho hr0 hr1
    norm_num [Batch011.certificate464,envelope232,inputs232,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound465 rho hr0 hr1
    norm_num [Batch011.certificate465,envelope232,inputs232,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs233 : RatMajorityInputs := ⟨(3902421752685593863575529/10000000000000000000000),(500265488052083/100000000000000),(503866876508971011/500000000000000000),(124428591950368567/1000000000000000000),(500265488052083/200000000000000),(40988053990425383/500000000000000000),27⟩
theorem inputs_valid233 : inputs233.Valid := by decide +kernel
def envelope233 : RatMajorityEnvelope := ⟨116,1,inputs233,1,(271621997769384597/500000000000000000)⟩
theorem envelope_sound233 : envelope233.Sound := by
  apply rat_majority_inputs_envelopes inputs233 inputs_valid233
  · norm_num [envelope233]
  · intro rho hr0 hr1
    have hh := Batch011.bound466 rho hr0 hr1
    norm_num [Batch011.certificate466,envelope233,inputs233,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound467 rho hr0 hr1
    norm_num [Batch011.certificate467,envelope233,inputs233,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs234 : RatMajorityInputs := ⟨(97006247231959898094853/250000000000000000000),(5449107203221/1250000000000),(251944552748274553/250000000000000000),(95017470968455991/500000000000000000),(5449107203221/2500000000000),(56540953547697071/500000000000000000),26⟩
theorem inputs_valid234 : inputs234.Valid := by decide +kernel
def envelope234 : RatMajorityEnvelope := ⟨117,0,inputs234,(2303845921/1954640000),(707325227637123699/1000000000000000000)⟩
theorem envelope_sound234 : envelope234.Sound := by
  apply rat_majority_inputs_envelopes inputs234 inputs_valid234
  · norm_num [envelope234]
  · intro rho hr0 hr1
    have hh := Batch011.bound468 rho hr0 hr1
    norm_num [Batch011.certificate468,envelope234,inputs234,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound469 rho hr0 hr1
    norm_num [Batch011.certificate469,envelope234,inputs234,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs235 : RatMajorityInputs := ⟨(97006247231959898094853/250000000000000000000),(15641889785827/3125000000000),(251944552748274553/250000000000000000),(15524693377747153/125000000000000000),(15641889785827/6250000000000),(20465868597759951/250000000000000000),26⟩
theorem inputs_valid235 : inputs235.Valid := by decide +kernel
def envelope235 : RatMajorityEnvelope := ⟨117,1,inputs235,1,(543240676075739313/1000000000000000000)⟩
theorem envelope_sound235 : envelope235.Sound := by
  apply rat_majority_inputs_envelopes inputs235 inputs_valid235
  · norm_num [envelope235]
  · intro rho hr0 hr1
    have hh := Batch011.bound470 rho hr0 hr1
    norm_num [Batch011.certificate470,envelope235,inputs235,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound471 rho hr0 hr1
    norm_num [Batch011.certificate471,envelope235,inputs235,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs236 : RatMajorityInputs := ⟨(192919484145064011289859/500000000000000000000),(2196231264957/500000000000),(1007822547311514569/1000000000000000000),(93019958414391437/500000000000000000),(2196231264957/1000000000000),(111221533986371831/1000000000000000000),26⟩
theorem inputs_valid236 : inputs236.Valid := by decide +kernel
def envelope236 : RatMajorityEnvelope := ⟨118,0,inputs236,(2300755627/1954000000),(22059388010058807/31250000000000000)⟩
theorem envelope_sound236 : envelope236.Sound := by
  apply rat_majority_inputs_envelopes inputs236 inputs_valid236
  · norm_num [envelope236]
  · intro rho hr0 hr1
    have hh := Batch011.bound472 rho hr0 hr1
    norm_num [Batch011.certificate472,envelope236,inputs236,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound473 rho hr0 hr1
    norm_num [Batch011.certificate473,envelope236,inputs236,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs237 : RatMajorityInputs := ⟨(192919484145064011289859/500000000000000000000),(313055696891/62500000000),(1007822547311514569/1000000000000000000),(3872036341443953/31250000000000000),(313055696891/125000000000),(81720893523578213/1000000000000000000),26⟩
theorem inputs_valid237 : inputs237.Valid := by decide +kernel
def envelope237 : RatMajorityEnvelope := ⟨118,1,inputs237,1,(543231012909283037/1000000000000000000)⟩
theorem envelope_sound237 : envelope237.Sound := by
  apply rat_majority_inputs_envelopes inputs237 inputs_valid237
  · norm_num [envelope237]
  · intro rho hr0 hr1
    have hh := Batch011.bound474 rho hr0 hr1
    norm_num [Batch011.certificate474,envelope237,inputs237,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound475 rho hr0 hr1
    norm_num [Batch011.certificate475,envelope237,inputs237,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs238 : RatMajorityInputs := ⟨(37847512596173927606077659/100000000000000000000000),(53321825099481/12500000000000),(1007975690753832627/1000000000000000000),(100845534731125517/500000000000000000),(53321825099481/25000000000000),(59248181907736631/500000000000000000),25⟩
theorem inputs_valid238 : inputs238.Valid := by decide +kernel
def envelope238 : RatMajorityEnvelope := ⟨119,0,inputs238,(143974483/121430625),(44678421616491321/62500000000000000)⟩
theorem envelope_sound238 : envelope238.Sound := by
  apply rat_majority_inputs_envelopes inputs238 inputs_valid238
  · norm_num [envelope238]
  · intro rho hr0 hr1
    have hh := Batch011.bound476 rho hr0 hr1
    norm_num [Batch011.certificate476,envelope238,inputs238,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound477 rho hr0 hr1
    norm_num [Batch011.certificate477,envelope238,inputs238,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs239 : RatMajorityInputs := ⟨(37847512596173927606077659/100000000000000000000000),(124685053374339/25000000000000),(1007975690753832627/1000000000000000000),(125717084258078919/1000000000000000000),(124685053374339/50000000000000),(82603678339891289/1000000000000000000),27⟩
theorem inputs_valid239 : inputs239.Valid := by decide +kernel
def envelope239 : RatMajorityEnvelope := ⟨119,1,inputs239,1,(67936047914669581/125000000000000000)⟩
theorem envelope_sound239 : envelope239.Sound := by
  apply rat_majority_inputs_envelopes inputs239 inputs_valid239
  · norm_num [envelope239]
  · intro rho hr0 hr1
    have hh := Batch011.bound478 rho hr0 hr1
    norm_num [Batch011.certificate478,envelope239,inputs239,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch011.bound479 rho hr0 hr1
    norm_num [Batch011.certificate479,envelope239,inputs239,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope220,envelope221,envelope222,envelope223,envelope224,envelope225,envelope226,envelope227,envelope228,envelope229,envelope230,envelope231,envelope232,envelope233,envelope234,envelope235,envelope236,envelope237,envelope238,envelope239]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound220
  · exact envelope_sound221
  · exact envelope_sound222
  · exact envelope_sound223
  · exact envelope_sound224
  · exact envelope_sound225
  · exact envelope_sound226
  · exact envelope_sound227
  · exact envelope_sound228
  · exact envelope_sound229
  · exact envelope_sound230
  · exact envelope_sound231
  · exact envelope_sound232
  · exact envelope_sound233
  · exact envelope_sound234
  · exact envelope_sound235
  · exact envelope_sound236
  · exact envelope_sound237
  · exact envelope_sound238
  · exact envelope_sound239

end Cycle12.MajorityCertificates.Inputs011
