import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch008

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs008

def inputs160 : RatMajorityInputs := ⟨(49373119306001186485829347/100000000000000000000000),(208940340579817/50000000000000),(1006105021496533967/1000000000000000000),(53264152808703873/250000000000000000),(208940340579817/100000000000000),(123760948861552211/1000000000000000000),25⟩
theorem inputs_valid160 : inputs160.Valid := by decide +kernel
def envelope160 : RatMajorityEnvelope := ⟨80,0,inputs160,(69812903/58135000),(728683346211374957/1000000000000000000)⟩
theorem envelope_sound160 : envelope160.Sound := by
  apply rat_majority_inputs_envelopes inputs160 inputs_valid160
  · norm_num [envelope160]
  · intro rho hr0 hr1
    have hh := Batch008.bound320 rho hr0 hr1
    norm_num [Batch008.certificate320,envelope160,inputs160,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound321 rho hr0 hr1
    norm_num [Batch008.certificate321,envelope160,inputs160,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs161 : RatMajorityInputs := ⟨(49373119306001186485829347/100000000000000000000000),(492449797163709/100000000000000),(1006105021496533967/1000000000000000000),(131156861512469561/1000000000000000000),(492449797163709/200000000000000),(42621512437306913/500000000000000000),26⟩
theorem inputs_valid161 : inputs161.Valid := by decide +kernel
def envelope161 : RatMajorityEnvelope := ⟨80,1,inputs161,1,(271599591717148627/500000000000000000)⟩
theorem envelope_sound161 : envelope161.Sound := by
  apply rat_majority_inputs_envelopes inputs161 inputs_valid161
  · norm_num [envelope161]
  · intro rho hr0 hr1
    have hh := Batch008.bound322 rho hr0 hr1
    norm_num [Batch008.certificate322,envelope161,inputs161,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound323 rho hr0 hr1
    norm_num [Batch008.certificate323,envelope161,inputs161,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs162 : RatMajorityInputs := ⟨(12249494702334080451073/25000000000000000000),(2613170467281/625000000000),(1006151986511642219/1000000000000000000),(53188439374370287/250000000000000000),(2613170467281/1250000000000),(123620811064358719/1000000000000000000),25⟩
theorem inputs_valid162 : inputs162.Valid := by decide +kernel
def envelope162 : RatMajorityEnvelope := ⟨81,0,inputs162,(237260623/197560000),(364375718389096899/500000000000000000)⟩
theorem envelope_sound162 : envelope162.Sound := by
  apply rat_majority_inputs_envelopes inputs162 inputs_valid162
  · norm_num [envelope162]
  · intro rho hr0 hr1
    have hh := Batch008.bound324 rho hr0 hr1
    norm_num [Batch008.certificate324,envelope162,inputs162,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound325 rho hr0 hr1
    norm_num [Batch008.certificate325,envelope162,inputs162,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs163 : RatMajorityInputs := ⟨(12249494702334080451073/25000000000000000000),(6155308016011/1250000000000),(1006151986511642219/1000000000000000000),(131179027324106831/1000000000000000000),(6155308016011/2500000000000),(341014989466651/4000000000000000),26⟩
theorem inputs_valid163 : inputs163.Valid := by decide +kernel
def envelope163 : RatMajorityEnvelope := ⟨81,1,inputs163,1,(13580574903548503/25000000000000000)⟩
theorem envelope_sound163 : envelope163.Sound := by
  apply rat_majority_inputs_envelopes inputs163 inputs_valid163
  · norm_num [envelope163]
  · intro rho hr0 hr1
    have hh := Batch008.bound326 rho hr0 hr1
    norm_num [Batch008.certificate326,envelope163,inputs163,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound327 rho hr0 hr1
    norm_num [Batch008.certificate327,envelope163,inputs163,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs164 : RatMajorityInputs := ⟨(24314310246764313982993487/50000000000000000000000),(205628918037473/50000000000000),(503099469496617661/500000000000000000),(13879221048836747/62500000000000000),(205628918037473/100000000000000),(127927807206286917/1000000000000000000),25⟩
theorem inputs_valid164 : inputs164.Valid := by decide +kernel
def envelope164 : RatMajorityEnvelope := ⟨82,0,inputs164,(2375581607/1974620000),(22862477654785629/31250000000000000)⟩
theorem envelope_sound164 : envelope164.Sound := by
  apply rat_majority_inputs_envelopes inputs164 inputs_valid164
  · norm_num [envelope164]
  · intro rho hr0 hr1
    have hh := Batch008.bound328 rho hr0 hr1
    norm_num [Batch008.certificate328,envelope164,inputs164,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound329 rho hr0 hr1
    norm_num [Batch008.certificate329,envelope164,inputs164,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs165 : RatMajorityInputs := ⟨(24314310246764313982993487/50000000000000000000000),(246342085187991/50000000000000),(503099469496617661/500000000000000000),(32737626346176089/250000000000000000),(246342085187991/100000000000000),(85143189974785621/1000000000000000000),26⟩
theorem inputs_valid165 : inputs165.Valid := by decide +kernel
def envelope165 : RatMajorityEnvelope := ⟨82,1,inputs165,1,(67902537242180051/125000000000000000)⟩
theorem envelope_sound165 : envelope165.Sound := by
  apply rat_majority_inputs_envelopes inputs165 inputs_valid165
  · norm_num [envelope165]
  · intro rho hr0 hr1
    have hh := Batch008.bound330 rho hr0 hr1
    norm_num [Batch008.certificate330,envelope165,inputs165,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound331 rho hr0 hr1
    norm_num [Batch008.certificate331,envelope165,inputs165,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs166 : RatMajorityInputs := ⟨(48454703465557801048063197/100000000000000000000000),(2107121151873/500000000000),(1006221296237558437/1000000000000000000),(10418065101838599/50000000000000000),(2107121151873/1000000000000),(15198436875550601/125000000000000000),25⟩
theorem inputs_valid166 : inputs166.Valid := by decide +kernel
def envelope166 : RatMajorityEnvelope := ⟨83,0,inputs166,(789001693/660470000),(722621634883513943/1000000000000000000)⟩
theorem envelope_sound166 : envelope166.Sound := by
  apply rat_majority_inputs_envelopes inputs166 inputs_valid166
  · norm_num [envelope166]
  · intro rho hr0 hr1
    have hh := Batch008.bound332 rho hr0 hr1
    norm_num [Batch008.certificate332,envelope166,inputs166,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound333 rho hr0 hr1
    norm_num [Batch008.certificate333,envelope166,inputs166,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs167 : RatMajorityInputs := ⟨(48454703465557801048063197/100000000000000000000000),(494344032253773/100000000000000),(1006221296237558437/1000000000000000000),(129497263413152377/1000000000000000000),(494344032253773/200000000000000),(84439484472841089/1000000000000000000),26⟩
theorem inputs_valid167 : inputs167.Valid := by decide +kernel
def envelope167 : RatMajorityEnvelope := ⟨83,1,inputs167,1,(543077226223952569/1000000000000000000)⟩
theorem envelope_sound167 : envelope167.Sound := by
  apply rat_majority_inputs_envelopes inputs167 inputs_valid167
  · norm_num [envelope167]
  · intro rho hr0 hr1
    have hh := Batch008.bound334 rho hr0 hr1
    norm_num [Batch008.certificate334,envelope167,inputs167,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound335 rho hr0 hr1
    norm_num [Batch008.certificate335,envelope167,inputs167,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs168 : RatMajorityInputs := ⟨(300599982561129827825607/625000000000000000000),(3304767691569/781250000000),(503133960750343231/500000000000000000),(206287873742639851/1000000000000000000),(3304767691569/1562500000000),(60313549248730973/500000000000000000),25⟩
theorem inputs_valid168 : inputs168.Valid := by decide +kernel
def envelope168 : RatMajorityEnvelope := ⟨84,0,inputs168,(1182319897/990240000),(28874971334208299/40000000000000000)⟩
theorem envelope_sound168 : envelope168.Sound := by
  apply rat_majority_inputs_envelopes inputs168 inputs_valid168
  · norm_num [envelope168]
  · intro rho hr0 hr1
    have hh := Batch008.bound336 rho hr0 hr1
    norm_num [Batch008.certificate336,envelope168,inputs168,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound337 rho hr0 hr1
    norm_num [Batch008.certificate337,envelope168,inputs168,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs169 : RatMajorityInputs := ⟨(300599982561129827825607/625000000000000000000),(15448365418923/3125000000000),(503133960750343231/500000000000000000),(129494073838729221/1000000000000000000),(15448365418923/6250000000000),(84437938758151649/1000000000000000000),26⟩
theorem inputs_valid169 : inputs169.Valid := by decide +kernel
def envelope169 : RatMajorityEnvelope := ⟨84,1,inputs169,1,(543098246332260281/1000000000000000000)⟩
theorem envelope_sound169 : envelope169.Sound := by
  apply rat_majority_inputs_envelopes inputs169 inputs_valid169
  · norm_num [envelope169]
  · intro rho hr0 hr1
    have hh := Batch008.bound338 rho hr0 hr1
    norm_num [Batch008.certificate338,envelope169,inputs169,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound339 rho hr0 hr1
    norm_num [Batch008.certificate339,envelope169,inputs169,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs170 : RatMajorityInputs := ⟨(11935690780987560791301867/25000000000000000000000),(105591260946303/25000000000000),(1006314523509792583/1000000000000000000),(207129285185029963/1000000000000000000),(105591260946303/50000000000000),(60508441213611811/500000000000000000),25⟩
theorem inputs_valid170 : inputs170.Valid := by decide +kernel
def envelope170 : RatMajorityEnvelope := ⟨85,0,inputs170,(2363211317/1979560000),(90228827115929721/125000000000000000)⟩
theorem envelope_sound170 : envelope170.Sound := by
  apply rat_majority_inputs_envelopes inputs170 inputs_valid170
  · norm_num [envelope170]
  · intro rho hr0 hr1
    have hh := Batch008.bound340 rho hr0 hr1
    norm_num [Batch008.certificate340,envelope170,inputs170,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound341 rho hr0 hr1
    norm_num [Batch008.certificate341,envelope170,inputs170,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs171 : RatMajorityInputs := ⟨(11935690780987560791301867/25000000000000000000000),(61822936556491/12500000000000),(1006314523509792583/1000000000000000000),(64644396728893369/500000000000000000),(61822936556491/25000000000000),(84338445493526443/1000000000000000000),27⟩
theorem inputs_valid171 : inputs171.Valid := by decide +kernel
def envelope171 : RatMajorityEnvelope := ⟨85,1,inputs171,1,(135774498584397983/250000000000000000)⟩
theorem envelope_sound171 : envelope171.Sound := by
  apply rat_majority_inputs_envelopes inputs171 inputs_valid171
  · norm_num [envelope171]
  · intro rho hr0 hr1
    have hh := Batch008.bound342 rho hr0 hr1
    norm_num [Batch008.certificate342,envelope171,inputs171,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound343 rho hr0 hr1
    norm_num [Batch008.certificate343,envelope171,inputs171,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs172 : RatMajorityInputs := ⟨(592436246882639068498221/1250000000000000000000),(8474183549847/2000000000000),(1006361099205123483/1000000000000000000),(205379667634775061/1000000000000000000),(8474183549847/4000000000000),(3756446717782123/31250000000000000),25⟩
theorem inputs_valid172 : inputs172.Valid := by decide +kernel
def envelope172 : RatMajorityEnvelope := ⟨86,0,inputs172,(590249611/494662500),(180293227268081231/250000000000000000)⟩
theorem envelope_sound172 : envelope172.Sound := by
  apply rat_majority_inputs_envelopes inputs172 inputs_valid172
  · norm_num [envelope172]
  · intro rho hr0 hr1
    have hh := Batch008.bound344 rho hr0 hr1
    norm_num [Batch008.certificate344,envelope172,inputs172,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound345 rho hr0 hr1
    norm_num [Batch008.certificate345,envelope172,inputs172,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs173 : RatMajorityInputs := ⟨(592436246882639068498221/1250000000000000000000),(98917244331489/20000000000000),(1006361099205123483/1000000000000000000),(6464320958561703/50000000000000000),(98917244331489/40000000000000),(8433729461662523/100000000000000000),26⟩
theorem inputs_valid173 : inputs173.Valid := by decide +kernel
def envelope173 : RatMajorityEnvelope := ⟨86,1,inputs173,1,(67889885404007741/125000000000000000)⟩
theorem envelope_sound173 : envelope173.Sound := by
  apply rat_majority_inputs_envelopes inputs173 inputs_valid173
  · norm_num [envelope173]
  · intro rho hr0 hr1
    have hh := Batch008.bound346 rho hr0 hr1
    norm_num [Batch008.certificate346,envelope173,inputs173,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound347 rho hr0 hr1
    norm_num [Batch008.certificate347,envelope173,inputs173,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs174 : RatMajorityInputs := ⟨(3764184644842171373529/8000000000000000000),(2117075138181/500000000000),(1006407645524895643/1000000000000000000),(205761494096417987/1000000000000000000),(2117075138181/1000000000000),(30095804590995307/250000000000000000),25⟩
theorem inputs_valid174 : inputs174.Valid := by decide +kernel
def envelope174 : RatMajorityEnvelope := ⟨87,0,inputs174,(98308697/82406250),(720999644089700869/1000000000000000000)⟩
theorem envelope_sound174 : envelope174.Sound := by
  apply rat_majority_inputs_envelopes inputs174 inputs_valid174
  · norm_num [envelope174]
  · intro rho hr0 hr1
    have hh := Batch008.bound348 rho hr0 hr1
    norm_num [Batch008.certificate348,envelope174,inputs174,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound349 rho hr0 hr1
    norm_num [Batch008.certificate349,envelope174,inputs174,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs175 : RatMajorityInputs := ⟨(3764184644842171373529/8000000000000000000),(9896489972091/2000000000000),(1006407645524895643/1000000000000000000),(25815855525290237/200000000000000000),(9896489972091/4000000000000),(42118438140748561/500000000000000000),26⟩
theorem inputs_valid175 : inputs175.Valid := by decide +kernel
def envelope175 : RatMajorityEnvelope := ⟨87,1,inputs175,1,(54311863761822323/100000000000000000)⟩
theorem envelope_sound175 : envelope175.Sound := by
  apply rat_majority_inputs_envelopes inputs175 inputs_valid175
  · norm_num [envelope175]
  · intro rho hr0 hr1
    have hh := Batch008.bound350 rho hr0 hr1
    norm_num [Batch008.certificate350,envelope175,inputs175,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound351 rho hr0 hr1
    norm_num [Batch008.certificate351,envelope175,inputs175,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs176 : RatMajorityInputs := ⟨(5839361422988938177295819/12500000000000000000000),(212203857113007/50000000000000),(251613539851378817/250000000000000000),(102237646465659967/500000000000000000),(212203857113007/100000000000000),(59893592370769257/500000000000000000),25⟩
theorem inputs_valid176 : inputs176.Valid := by decide +kernel
def envelope176 : RatMajorityEnvelope := ⟨88,0,inputs176,(1178699991/988430000),(72046861052378831/100000000000000000)⟩
theorem envelope_sound176 : envelope176.Sound := by
  apply rat_majority_inputs_envelopes inputs176 inputs_valid176
  · norm_num [envelope176]
  · intro rho hr0 hr1
    have hh := Batch008.bound352 rho hr0 hr1
    norm_num [Batch008.certificate352,envelope176,inputs176,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound353 rho hr0 hr1
    norm_num [Batch008.certificate353,envelope176,inputs176,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs177 : RatMajorityInputs := ⟨(5839361422988938177295819/12500000000000000000000),(123706700350101/25000000000000),(251613539851378817/250000000000000000),(129077277168819047/1000000000000000000),(123706700350101/50000000000000),(84235906385433539/1000000000000000000),27⟩
theorem inputs_valid177 : inputs177.Valid := by decide +kernel
def envelope177 : RatMajorityEnvelope := ⟨88,1,inputs177,1,(108627948630465081/200000000000000000)⟩
theorem envelope_sound177 : envelope177.Sound := by
  apply rat_majority_inputs_envelopes inputs177 inputs_valid177
  · norm_num [envelope177]
  · intro rho hr0 hr1
    have hh := Batch008.bound354 rho hr0 hr1
    norm_num [Batch008.certificate354,envelope177,inputs177,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound355 rho hr0 hr1
    norm_num [Batch008.certificate355,envelope177,inputs177,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs178 : RatMajorityInputs := ⟨(46382320612022465741286027/100000000000000000000000),(106094939751211/25000000000000),(100650067084646431/100000000000000000),(40902284325501317/200000000000000000),(106094939751211/50000000000000),(23960785859593921/200000000000000000),25⟩
theorem inputs_valid178 : inputs178.Valid := by decide +kernel
def envelope178 : RatMajorityEnvelope := ⟨89,0,inputs178,(588921587/493992500),(720199355866020947/1000000000000000000)⟩
theorem envelope_sound178 : envelope178.Sound := by
  apply rat_majority_inputs_envelopes inputs178 inputs_valid178
  · norm_num [envelope178]
  · intro rho hr0 hr1
    have hh := Batch008.bound356 rho hr0 hr1
    norm_num [Batch008.certificate356,envelope178,inputs178,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound357 rho hr0 hr1
    norm_num [Batch008.certificate357,envelope178,inputs178,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs179 : RatMajorityInputs := ⟨(46382320612022465741286027/100000000000000000000000),(495067362670587/100000000000000),(100650067084646431/100000000000000000),(128868450763854803/1000000000000000000),(495067362670587/200000000000000),(5258415488230861/62500000000000000),27⟩
theorem inputs_valid179 : inputs179.Valid := by decide +kernel
def envelope179 : RatMajorityEnvelope := ⟨89,1,inputs179,1,(543139132450287921/1000000000000000000)⟩
theorem envelope_sound179 : envelope179.Sound := by
  apply rat_majority_inputs_envelopes inputs179 inputs_valid179
  · norm_num [envelope179]
  · intro rho hr0 hr1
    have hh := Batch008.bound358 rho hr0 hr1
    norm_num [Batch008.certificate358,envelope179,inputs179,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch008.bound359 rho hr0 hr1
    norm_num [Batch008.certificate359,envelope179,inputs179,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope160,envelope161,envelope162,envelope163,envelope164,envelope165,envelope166,envelope167,envelope168,envelope169,envelope170,envelope171,envelope172,envelope173,envelope174,envelope175,envelope176,envelope177,envelope178,envelope179]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound160
  · exact envelope_sound161
  · exact envelope_sound162
  · exact envelope_sound163
  · exact envelope_sound164
  · exact envelope_sound165
  · exact envelope_sound166
  · exact envelope_sound167
  · exact envelope_sound168
  · exact envelope_sound169
  · exact envelope_sound170
  · exact envelope_sound171
  · exact envelope_sound172
  · exact envelope_sound173
  · exact envelope_sound174
  · exact envelope_sound175
  · exact envelope_sound176
  · exact envelope_sound177
  · exact envelope_sound178
  · exact envelope_sound179

end Cycle12.MajorityCertificates.Inputs008
