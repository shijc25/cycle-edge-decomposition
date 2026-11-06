import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch016

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs016

def inputs320 : RatMajorityInputs := ⟨(84761124691040147511303/250000000000000000000),(5609200254873/1250000000000),(1008909678696544539/1000000000000000000),(175004776982235091/1000000000000000000),(5609200254873/2500000000000),(106067446238038187/1000000000000000000),25⟩
theorem inputs_valid320 : inputs320.Valid := by decide +kernel
def envelope320 : RatMajorityEnvelope := ⟨160,0,inputs320,(1125965561/970275000),(69014065371773783/100000000000000000)⟩
theorem envelope_sound320 : envelope320.Sound := by
  apply rat_majority_inputs_envelopes inputs320 inputs_valid320
  · norm_num [envelope320]
  · intro rho hr0 hr1
    have hh := Batch016.bound640 rho hr0 hr1
    norm_num [Batch016.certificate640,envelope320,inputs320,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound641 rho hr0 hr1
    norm_num [Batch016.certificate641,envelope320,inputs320,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs321 : RatMajorityInputs := ⟨(84761124691040147511303/250000000000000000000),(5084209213791/1000000000000),(1008909678696544539/1000000000000000000),(58868194935002261/500000000000000000),(5084209213791/2000000000000),(78700591563623387/1000000000000000000),27⟩
theorem inputs_valid321 : inputs321.Valid := by decide +kernel
def envelope321 : RatMajorityEnvelope := ⟨160,1,inputs321,1,(543106189370015597/1000000000000000000)⟩
theorem envelope_sound321 : envelope321.Sound := by
  apply rat_majority_inputs_envelopes inputs321 inputs_valid321
  · norm_num [envelope321]
  · intro rho hr0 hr1
    have hh := Batch016.bound642 rho hr0 hr1
    norm_num [Batch016.certificate642,envelope321,inputs321,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound643 rho hr0 hr1
    norm_num [Batch016.certificate643,envelope321,inputs321,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs322 : RatMajorityInputs := ⟨(4228604194227424983145629/12500000000000000000000),(112296438327477/25000000000000),(504464866165454599/500000000000000000),(174495997702400563/1000000000000000000),(112296438327477/50000000000000),(105829204090165487/1000000000000000000),25⟩
theorem inputs_valid322 : inputs322.Valid := by decide +kernel
def envelope322 : RatMajorityEnvelope := ⟨161,0,inputs322,(30834529/26580000),(68974907736119761/100000000000000000)⟩
theorem envelope_sound322 : envelope322.Sound := by
  apply rat_majority_inputs_envelopes inputs322 inputs_valid322
  · norm_num [envelope322]
  · intro rho hr0 hr1
    have hh := Batch016.bound644 rho hr0 hr1
    norm_num [Batch016.certificate644,envelope322,inputs322,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound645 rho hr0 hr1
    norm_num [Batch016.certificate645,envelope322,inputs322,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs323 : RatMajorityInputs := ⟨(4228604194227424983145629/12500000000000000000000),(127151909357427/25000000000000),(504464866165454599/500000000000000000),(117587004342296011/1000000000000000000),(127151909357427/50000000000000),(39313576265693061/500000000000000000),29⟩
theorem inputs_valid323 : inputs323.Valid := by decide +kernel
def envelope323 : RatMajorityEnvelope := ⟨161,1,inputs323,1,(543100466852331251/1000000000000000000)⟩
theorem envelope_sound323 : envelope323.Sound := by
  apply rat_majority_inputs_envelopes inputs323 inputs_valid323
  · norm_num [envelope323]
  · intro rho hr0 hr1
    have hh := Batch016.bound646 rho hr0 hr1
    norm_num [Batch016.certificate646,envelope323,inputs323,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound647 rho hr0 hr1
    norm_num [Batch016.certificate647,envelope323,inputs323,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs324 : RatMajorityInputs := ⟨(33753699630737474386122081/100000000000000000000000),(44913812188779/10000000000000),(1008949747642008609/1000000000000000000),(174549822689817037/1000000000000000000),(44913812188779/20000000000000),(21170882213823827/200000000000000000),25⟩
theorem inputs_valid324 : inputs324.Valid := by decide +kernel
def envelope324 : RatMajorityEnvelope := ⟨162,0,inputs324,(281262653/242516250),(689497200867490629/1000000000000000000)⟩
theorem envelope_sound324 : envelope324.Sound := by
  apply rat_majority_inputs_envelopes inputs324 inputs_valid324
  · norm_num [envelope324]
  · intro rho hr0 hr1
    have hh := Batch016.bound648 rho hr0 hr1
    norm_num [Batch016.certificate648,envelope324,inputs324,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound649 rho hr0 hr1
    norm_num [Batch016.certificate649,envelope324,inputs324,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs325 : RatMajorityInputs := ⟨(33753699630737474386122081/100000000000000000000000),(6359920945713/1250000000000),(1008949747642008609/1000000000000000000),(117438329347916833/1000000000000000000),(6359920945713/2500000000000),(78554048256745931/1000000000000000000),27⟩
theorem inputs_valid325 : inputs325.Valid := by decide +kernel
def envelope325 : RatMajorityEnvelope := ⟨162,1,inputs325,1,(543094807086635051/1000000000000000000)⟩
theorem envelope_sound325 : envelope325.Sound := by
  apply rat_majority_inputs_envelopes inputs325 inputs_valid325
  · norm_num [envelope325]
  · intro rho hr0 hr1
    have hh := Batch016.bound650 rho hr0 hr1
    norm_num [Batch016.certificate650,envelope325,inputs325,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound651 rho hr0 hr1
    norm_num [Batch016.certificate651,envelope325,inputs325,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs326 : RatMajorityInputs := ⟨(4209880612543447466207901/12500000000000000000000),(14032605530241/3125000000000),(50448486218276981/50000000000000000),(174656929680335101/1000000000000000000),(14032605530241/6250000000000),(52952284393618423/500000000000000000),25⟩
theorem inputs_valid326 : inputs326.Valid := by decide +kernel
def envelope326 : RatMajorityEnvelope := ⟨163,0,inputs326,(187441677/161660000),(344629298808358149/500000000000000000)⟩
theorem envelope_sound326 : envelope326.Sound := by
  apply rat_majority_inputs_envelopes inputs326 inputs_valid326
  · norm_num [envelope326]
  · intro rho hr0 hr1
    have hh := Batch016.bound652 rho hr0 hr1
    norm_num [Batch016.certificate652,envelope326,inputs326,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound653 rho hr0 hr1
    norm_num [Batch016.certificate653,envelope326,inputs326,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs327 : RatMajorityInputs := ⟨(4209880612543447466207901/12500000000000000000000),(63616296162147/12500000000000),(50448486218276981/50000000000000000),(117329195688412897/1000000000000000000),(63616296162147/25000000000000),(78500377405976931/1000000000000000000),28⟩
theorem inputs_valid327 : inputs327.Valid := by decide +kernel
def envelope327 : RatMajorityEnvelope := ⟨163,1,inputs327,1,(271546557278438607/500000000000000000)⟩
theorem envelope_sound327 : envelope327.Sound := by
  apply rat_majority_inputs_envelopes inputs327 inputs_valid327
  · norm_num [envelope327]
  · intro rho hr0 hr1
    have hh := Batch016.bound654 rho hr0 hr1
    norm_num [Batch016.certificate654,envelope327,inputs327,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound655 rho hr0 hr1
    norm_num [Batch016.certificate655,envelope327,inputs327,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs328 : RatMajorityInputs := ⟨(840121654654954752819159/2500000000000000000000),(89860607854431/20000000000000),(50449483111882777/50000000000000000),(43590880383494419/250000000000000000),(89860607854431/40000000000000),(52883580441879353/500000000000000000),25⟩
theorem inputs_valid328 : inputs328.Valid := by decide +kernel
def envelope328 : RatMajorityEnvelope := ⟨164,0,inputs328,(149891021/129314000),(344460742716788117/500000000000000000)⟩
theorem envelope_sound328 : envelope328.Sound := by
  apply rat_majority_inputs_envelopes inputs328 inputs_valid328
  · norm_num [envelope328]
  · intro rho hr0 hr1
    have hh := Batch016.bound656 rho hr0 hr1
    norm_num [Batch016.certificate656,envelope328,inputs328,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound657 rho hr0 hr1
    norm_num [Batch016.certificate657,envelope328,inputs328,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs329 : RatMajorityInputs := ⟨(840121654654954752819159/2500000000000000000000),(101822983308939/20000000000000),(50449483111882777/50000000000000000),(14647750022933887/125000000000000000),(101822983308939/40000000000000),(78427975672068481/1000000000000000000),27⟩
theorem inputs_valid329 : inputs329.Valid := by decide +kernel
def envelope329 : RatMajorityEnvelope := ⟨164,1,inputs329,1,(33942973971399099/62500000000000000)⟩
theorem envelope_sound329 : envelope329.Sound := by
  apply rat_majority_inputs_envelopes inputs329 inputs_valid329
  · norm_num [envelope329]
  · intro rho hr0 hr1
    have hh := Batch016.bound658 rho hr0 hr1
    norm_num [Batch016.certificate658,envelope329,inputs329,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound659 rho hr0 hr1
    norm_num [Batch016.certificate659,envelope329,inputs329,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs330 : RatMajorityInputs := ⟨(6591247114767456415289669/20000000000000000000000),(44580145377889/10000000000000),(504583926555805491/500000000000000000),(89177951744438919/500000000000000000),(44580145377889/20000000000000),(107635229956102489/1000000000000000000),26⟩
theorem inputs_valid330 : inputs330.Valid := by decide +kernel
def envelope330 : RatMajorityEnvelope := ⟨165,0,inputs330,(2245786591/1927630000),(138946164767612497/200000000000000000)⟩
theorem envelope_sound330 : envelope330.Sound := by
  apply rat_majority_inputs_envelopes inputs330 inputs_valid330
  · norm_num [envelope330]
  · intro rho hr0 hr1
    have hh := Batch016.bound660 rho hr0 hr1
    norm_num [Batch016.certificate660,envelope330,inputs330,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound661 rho hr0 hr1
    norm_num [Batch016.certificate661,envelope330,inputs330,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs331 : RatMajorityInputs := ⟨(6591247114767456415289669/20000000000000000000000),(15830693566421/3125000000000),(504583926555805491/500000000000000000),(11921656324158951/100000000000000000),(15830693566421/6250000000000),(19856868098925413/250000000000000000),26⟩
theorem inputs_valid331 : inputs331.Valid := by decide +kernel
def envelope331 : RatMajorityEnvelope := ⟨165,1,inputs331,1,(21735010186180659/40000000000000000)⟩
theorem envelope_sound331 : envelope331.Sound := by
  apply rat_majority_inputs_envelopes inputs331 inputs_valid331
  · norm_num [envelope331]
  · intro rho hr0 hr1
    have hh := Batch016.bound662 rho hr0 hr1
    norm_num [Batch016.certificate662,envelope331,inputs331,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound663 rho hr0 hr1
    norm_num [Batch016.certificate663,envelope331,inputs331,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs332 : RatMajorityInputs := ⟨(8168368239732491003200587/25000000000000000000000),(111748858791297/25000000000000),(1009247763510066357/1000000000000000000),(176985874927019853/1000000000000000000),(111748858791297/50000000000000),(53497285943988947/500000000000000000),25⟩
theorem inputs_valid332 : inputs332.Valid := by decide +kernel
def envelope332 : RatMajorityEnvelope := ⟨166,0,inputs332,(448212971/385356000),(69290194296159687/100000000000000000)⟩
theorem envelope_sound332 : envelope332.Sound := by
  apply rat_majority_inputs_envelopes inputs332 inputs_valid332
  · norm_num [envelope332]
  · intro rho hr0 hr1
    have hh := Batch016.bound664 rho hr0 hr1
    norm_num [Batch016.certificate664,envelope332,inputs332,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound665 rho hr0 hr1
    norm_num [Batch016.certificate665,envelope332,inputs332,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs333 : RatMajorityInputs := ⟨(8168368239732491003200587/25000000000000000000000),(253718323059039/50000000000000),(1009247763510066357/1000000000000000000),(118526679078321653/1000000000000000000),(253718323059039/100000000000000),(9886107677189541/125000000000000000),27⟩
theorem inputs_valid333 : inputs333.Valid := by decide +kernel
def envelope333 : RatMajorityEnvelope := ⟨166,1,inputs333,1,(8489730736124957/15625000000000000)⟩
theorem envelope_sound333 : envelope333.Sound := by
  apply rat_majority_inputs_envelopes inputs333 inputs_valid333
  · norm_num [envelope333]
  · intro rho hr0 hr1
    have hh := Batch016.bound666 rho hr0 hr1
    norm_num [Batch016.certificate666,envelope333,inputs333,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound667 rho hr0 hr1
    norm_num [Batch016.certificate667,envelope333,inputs333,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs334 : RatMajorityInputs := ⟨(123911461451568698084019233/1000000000000000000000),(85598816217681/20000000000000),(1000024211291334813/1000000000000000000),(49971117742477117/250000000000000000),(85598816217681/40000000000000),(23531665003275167/200000000000000000),25⟩
theorem inputs_valid334 : inputs334.Valid := by decide +kernel
def envelope334 : RatMajorityEnvelope := ⟨167,0,inputs334,(2740003739/2377450000),(680657092636126727/1000000000000000000)⟩
theorem envelope_sound334 : envelope334.Sound := by
  apply rat_majority_inputs_envelopes inputs334 inputs_valid334
  · norm_num [envelope334]
  · intro rho hr0 hr1
    have hh := Batch016.bound668 rho hr0 hr1
    norm_num [Batch016.certificate668,envelope334,inputs334,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound669 rho hr0 hr1
    norm_num [Batch016.certificate669,envelope334,inputs334,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs335 : RatMajorityInputs := ⟨(123911461451568698084019233/1000000000000000000000),(1522092132627/312500000000),(1000024211291334813/1000000000000000000),(135973660777477027/1000000000000000000),(1522092132627/625000000000),(21891829951865923/250000000000000000),26⟩
theorem inputs_valid335 : inputs335.Valid := by decide +kernel
def envelope335 : RatMajorityEnvelope := ⟨167,1,inputs335,1,(67618593501901901/125000000000000000)⟩
theorem envelope_sound335 : envelope335.Sound := by
  apply rat_majority_inputs_envelopes inputs335 inputs_valid335
  · norm_num [envelope335]
  · intro rho hr0 hr1
    have hh := Batch016.bound670 rho hr0 hr1
    norm_num [Batch016.certificate670,envelope335,inputs335,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound671 rho hr0 hr1
    norm_num [Batch016.certificate671,envelope335,inputs335,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs336 : RatMajorityInputs := ⟨(397711274593824256782216669/5000000000000000000000),(213062530568541/50000000000000),(40001508676367787/40000000000000000),(158020355011827/781250000000000),(213062530568541/100000000000000),(59381503722600961/500000000000000000),25⟩
theorem inputs_valid336 : inputs336.Valid := by decide +kernel
def envelope336 : RatMajorityEnvelope := ⟨168,0,inputs336,(683037811/591735000),(34125890082390087/50000000000000000)⟩
theorem envelope_sound336 : envelope336.Sound := by
  apply rat_majority_inputs_envelopes inputs336 inputs_valid336
  · norm_num [envelope336]
  · intro rho hr0 hr1
    have hh := Batch016.bound672 rho hr0 hr1
    norm_num [Batch016.certificate672,envelope336,inputs336,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound673 rho hr0 hr1
    norm_num [Batch016.certificate673,envelope336,inputs336,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs337 : RatMajorityInputs := ⟨(397711274593824256782216669/5000000000000000000000),(122054871985317/25000000000000),(40001508676367787/40000000000000000),(134931189502082927/1000000000000000000),(122054871985317/50000000000000),(87065250150680989/1000000000000000000),27⟩
theorem inputs_valid337 : inputs337.Valid := by decide +kernel
def envelope337 : RatMajorityEnvelope := ⟨168,1,inputs337,1,(54083984792946873/100000000000000000)⟩
theorem envelope_sound337 : envelope337.Sound := by
  apply rat_majority_inputs_envelopes inputs337 inputs_valid337
  · norm_num [envelope337]
  · intro rho hr0 hr1
    have hh := Batch016.bound674 rho hr0 hr1
    norm_num [Batch016.certificate674,envelope337,inputs337,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound675 rho hr0 hr1
    norm_num [Batch016.certificate675,envelope337,inputs337,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs338 : RatMajorityInputs := ⟨(5541531173336199638321900217/100000000000000000000000),(42544519668063/10000000000000),(500027069470782717/500000000000000000),(20313824650273667/100000000000000000),(42544519668063/20000000000000),(23833481627488671/200000000000000000),25⟩
theorem inputs_valid338 : inputs338.Valid := by decide +kernel
def envelope338 : RatMajorityEnvelope := ⟨169,0,inputs338,(2725879747/2356830000),(21395529313434383/31250000000000000)⟩
theorem envelope_sound338 : envelope338.Sound := by
  apply rat_majority_inputs_envelopes inputs338 inputs_valid338
  · norm_num [envelope338]
  · intro rho hr0 hr1
    have hh := Batch016.bound676 rho hr0 hr1
    norm_num [Batch016.certificate676,envelope338,inputs338,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound677 rho hr0 hr1
    norm_num [Batch016.certificate677,envelope338,inputs338,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs339 : RatMajorityInputs := ⟨(5541531173336199638321900217/100000000000000000000000),(487620358652637/100000000000000),(500027069470782717/500000000000000000),(135473413241614767/1000000000000000000),(487620358652637/200000000000000),(2728951809541257/31250000000000000),26⟩
theorem inputs_valid339 : inputs339.Valid := by decide +kernel
def envelope339 : RatMajorityEnvelope := ⟨169,1,inputs339,1,(540907112027960153/1000000000000000000)⟩
theorem envelope_sound339 : envelope339.Sound := by
  apply rat_majority_inputs_envelopes inputs339 inputs_valid339
  · norm_num [envelope339]
  · intro rho hr0 hr1
    have hh := Batch016.bound678 rho hr0 hr1
    norm_num [Batch016.certificate678,envelope339,inputs339,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch016.bound679 rho hr0 hr1
    norm_num [Batch016.certificate679,envelope339,inputs339,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope320,envelope321,envelope322,envelope323,envelope324,envelope325,envelope326,envelope327,envelope328,envelope329,envelope330,envelope331,envelope332,envelope333,envelope334,envelope335,envelope336,envelope337,envelope338,envelope339]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound320
  · exact envelope_sound321
  · exact envelope_sound322
  · exact envelope_sound323
  · exact envelope_sound324
  · exact envelope_sound325
  · exact envelope_sound326
  · exact envelope_sound327
  · exact envelope_sound328
  · exact envelope_sound329
  · exact envelope_sound330
  · exact envelope_sound331
  · exact envelope_sound332
  · exact envelope_sound333
  · exact envelope_sound334
  · exact envelope_sound335
  · exact envelope_sound336
  · exact envelope_sound337
  · exact envelope_sound338
  · exact envelope_sound339

end Cycle12.MajorityCertificates.Inputs016
