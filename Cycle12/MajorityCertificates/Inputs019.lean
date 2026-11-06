import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs019

def inputs380 : RatMajorityInputs := ⟨(15140872712691000383903061/5000000000000000000000),(5309438901681/1250000000000),(250247864944575197/250000000000000000),(204026769074007201/1000000000000000000),(5309438901681/2500000000000),(119579296256668331/1000000000000000000),25⟩
theorem inputs_valid380 : inputs380.Valid := by decide +kernel
def envelope380 : RatMajorityEnvelope := ⟨190,0,inputs380,(16296159/13741250),(2845966391142649/4000000000000000)⟩
theorem envelope_sound380 : envelope380.Sound := by
  apply rat_majority_inputs_envelopes inputs380 inputs_valid380
  · norm_num [envelope380]
  · intro rho hr0 hr1
    have hh := Batch019.bound760 rho hr0 hr1
    norm_num [Batch019.certificate760,envelope380,inputs380,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound761 rho hr0 hr1
    norm_num [Batch019.certificate761,envelope380,inputs380,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs381 : RatMajorityInputs := ⟨(15140872712691000383903061/5000000000000000000000),(12305748321757/2500000000000),(250247864944575197/250000000000000000),(13135070440018017/100000000000000000),(12305748321757/5000000000000),(17067357177817657/200000000000000000),26⟩
theorem inputs_valid381 : inputs381.Valid := by decide +kernel
def envelope381 : RatMajorityEnvelope := ⟨190,1,inputs381,1,(540882845335342503/1000000000000000000)⟩
theorem envelope_sound381 : envelope381.Sound := by
  apply rat_majority_inputs_envelopes inputs381 inputs_valid381
  · norm_num [envelope381]
  · intro rho hr0 hr1
    have hh := Batch019.bound762 rho hr0 hr1
    norm_num [Batch019.certificate762,envelope381,inputs381,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound763 rho hr0 hr1
    norm_num [Batch019.certificate763,envelope381,inputs381,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs382 : RatMajorityInputs := ⟨(3541748148237391688258457/1250000000000000000000),(21366247848873/5000000000000),(20021193435243843/20000000000000000),(200734377994137651/1000000000000000000),(21366247848873/10000000000000),(118052624347169601/1000000000000000000),25⟩
theorem inputs_valid382 : inputs382.Valid := by decide +kernel
def envelope382 : RatMajorityEnvelope := ⟨191,0,inputs382,(650154533/548225000),(711195297471065987/1000000000000000000)⟩
theorem envelope_sound382 : envelope382.Sound := by
  apply rat_majority_inputs_envelopes inputs382 inputs_valid382
  · norm_num [envelope382]
  · intro rho hr0 hr1
    have hh := Batch019.bound764 rho hr0 hr1
    norm_num [Batch019.certificate764,envelope382,inputs382,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound765 rho hr0 hr1
    norm_num [Batch019.certificate765,envelope382,inputs382,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs383 : RatMajorityInputs := ⟨(3541748148237391688258457/1250000000000000000000),(49223023114037/10000000000000),(20021193435243843/20000000000000000),(32837610314884801/250000000000000000),(49223023114037/20000000000000),(21334164655532287/250000000000000000),26⟩
theorem inputs_valid383 : inputs383.Valid := by decide +kernel
def envelope383 : RatMajorityEnvelope := ⟨191,1,inputs383,1,(108182797680497211/200000000000000000)⟩
theorem envelope_sound383 : envelope383.Sound := by
  apply rat_majority_inputs_envelopes inputs383 inputs_valid383
  · norm_num [envelope383]
  · intro rho hr0 hr1
    have hh := Batch019.bound766 rho hr0 hr1
    norm_num [Batch019.certificate766,envelope383,inputs383,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound767 rho hr0 hr1
    norm_num [Batch019.certificate767,envelope383,inputs383,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs384 : RatMajorityInputs := ⟨(132913719069173121153827603/50000000000000000000000),(106918914744923/25000000000000),(1001129543072239339/1000000000000000000),(200288546335538107/1000000000000000000),(106918914744923/50000000000000),(23569159855288919/200000000000000000),25⟩
theorem inputs_valid384 : inputs384.Valid := by decide +kernel
def envelope384 : RatMajorityEnvelope := ⟨192,0,inputs384,(2595037939/2187340000),(711606056937455259/1000000000000000000)⟩
theorem envelope_sound384 : envelope384.Sound := by
  apply rat_majority_inputs_envelopes inputs384 inputs_valid384
  · norm_num [envelope384]
  · intro rho hr0 hr1
    have hh := Batch019.bound768 rho hr0 hr1
    norm_num [Batch019.certificate768,envelope384,inputs384,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound769 rho hr0 hr1
    norm_num [Batch019.certificate769,envelope384,inputs384,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs385 : RatMajorityInputs := ⟨(132913719069173121153827603/50000000000000000000000),(49322854512233/10000000000000),(1001129543072239339/1000000000000000000),(130472312836609701/1000000000000000000),(49322854512233/20000000000000),(10613969509046233/125000000000000000),26⟩
theorem inputs_valid385 : inputs385.Valid := by decide +kernel
def envelope385 : RatMajorityEnvelope := ⟨192,1,inputs385,1,(540850638160452761/1000000000000000000)⟩
theorem envelope_sound385 : envelope385.Sound := by
  apply rat_majority_inputs_envelopes inputs385 inputs_valid385
  · norm_num [envelope385]
  · intro rho hr0 hr1
    have hh := Batch019.bound770 rho hr0 hr1
    norm_num [Batch019.certificate770,envelope385,inputs385,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound771 rho hr0 hr1
    norm_num [Batch019.certificate771,envelope385,inputs385,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs386 : RatMajorityInputs := ⟨(31252943311741200486746009/12500000000000000000000),(85424325189071/20000000000000),(1001201007737049293/1000000000000000000),(20099324478835527/100000000000000000),(85424325189071/40000000000000),(11817270418647707/100000000000000000),25⟩
theorem inputs_valid386 : inputs386.Valid := by decide +kernel
def envelope386 : RatMajorityEnvelope := ⟨193,0,inputs386,(647960739/545477500),(713054341547953739/1000000000000000000)⟩
theorem envelope_sound386 : envelope386.Sound := by
  apply rat_majority_inputs_envelopes inputs386 inputs_valid386
  · norm_num [envelope386]
  · intro rho hr0 hr1
    have hh := Batch019.bound772 rho hr0 hr1
    norm_num [Batch019.certificate772,envelope386,inputs386,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound773 rho hr0 hr1
    norm_num [Batch019.certificate773,envelope386,inputs386,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs387 : RatMajorityInputs := ⟨(31252943311741200486746009/12500000000000000000000),(246451634851669/50000000000000),(1001201007737049293/1000000000000000000),(26151571391455553/200000000000000000),(246451634851669/100000000000000),(42524983484295789/500000000000000000),26⟩
theorem inputs_valid387 : inputs387.Valid := by decide +kernel
def envelope387 : RatMajorityEnvelope := ⟨193,1,inputs387,1,(540914279576251667/1000000000000000000)⟩
theorem envelope_sound387 : envelope387.Sound := by
  apply rat_majority_inputs_envelopes inputs387 inputs_valid387
  · norm_num [envelope387]
  · intro rho hr0 hr1
    have hh := Batch019.bound774 rho hr0 hr1
    norm_num [Batch019.certificate774,envelope387,inputs387,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound775 rho hr0 hr1
    norm_num [Batch019.certificate775,envelope387,inputs387,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs388 : RatMajorityInputs := ⟨(235713219503829406739438027/100000000000000000000000),(107017118105919/25000000000000),(1001273994058899993/1000000000000000000),(199790167612785663/1000000000000000000),(107017118105919/50000000000000),(23522913870993383/200000000000000000),25⟩
theorem inputs_valid388 : inputs388.Valid := by decide +kernel
def envelope388 : RatMajorityEnvelope := ⟨194,0,inputs388,(258625719/217661000),(71326879292871441/100000000000000000)⟩
theorem envelope_sound388 : envelope388.Sound := by
  apply rat_majority_inputs_envelopes inputs388 inputs_valid388
  · norm_num [envelope388]
  · intro rho hr0 hr1
    have hh := Batch019.bound776 rho hr0 hr1
    norm_num [Batch019.certificate776,envelope388,inputs388,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound777 rho hr0 hr1
    norm_num [Batch019.certificate777,envelope388,inputs388,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs389 : RatMajorityInputs := ⟨(235713219503829406739438027/100000000000000000000000),(492788967574127/100000000000000),(1001273994058899993/1000000000000000000),(130858328602759771/1000000000000000000),(492788967574127/200000000000000),(85098587822505173/1000000000000000000),27⟩
theorem inputs_valid389 : inputs389.Valid := by decide +kernel
def envelope389 : RatMajorityEnvelope := ⟨194,1,inputs389,1,(270479273915730863/500000000000000000)⟩
theorem envelope_sound389 : envelope389.Sound := by
  apply rat_majority_inputs_envelopes inputs389 inputs_valid389
  · norm_num [envelope389]
  · intro rho hr0 hr1
    have hh := Batch019.bound778 rho hr0 hr1
    norm_num [Batch019.certificate778,envelope389,inputs389,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound779 rho hr0 hr1
    norm_num [Batch019.certificate779,envelope389,inputs389,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs390 : RatMajorityInputs := ⟨(222713386539865335905350779/100000000000000000000000),(428506301946141/100000000000000),(125168554421373349/125000000000000000),(99617951476971613/500000000000000000),(428506301946141/200000000000000),(14669671915231827/125000000000000000),25⟩
theorem inputs_valid390 : inputs390.Valid := by decide +kernel
def envelope390 : RatMajorityEnvelope := ⟨195,0,inputs390,(1290514333/1085715000),(713639270444238719/1000000000000000000)⟩
theorem envelope_sound390 : envelope390.Sound := by
  apply rat_majority_inputs_envelopes inputs390 inputs_valid390
  · norm_num [envelope390]
  · intro rho hr0 hr1
    have hh := Batch019.bound780 rho hr0 hr1
    norm_num [Batch019.certificate780,envelope390,inputs390,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound781 rho hr0 hr1
    norm_num [Batch019.certificate781,envelope390,inputs390,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs391 : RatMajorityInputs := ⟨(222713386539865335905350779/100000000000000000000000),(493711873758801/100000000000000),(125168554421373349/125000000000000000),(26009807953707229/200000000000000000),(493711873758801/200000000000000),(84706802405643391/1000000000000000000),26⟩
theorem inputs_valid391 : inputs391.Valid := by decide +kernel
def envelope391 : RatMajorityEnvelope := ⟨195,1,inputs391,1,(135226243654557353/250000000000000000)⟩
theorem envelope_sound391 : envelope391.Sound := by
  apply rat_majority_inputs_envelopes inputs391 inputs_valid391
  · norm_num [envelope391]
  · intro rho hr0 hr1
    have hh := Batch019.bound782 rho hr0 hr1
    norm_num [Batch019.certificate782,envelope391,inputs391,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound783 rho hr0 hr1
    norm_num [Batch019.certificate783,envelope391,inputs391,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs392 : RatMajorityInputs := ⟨(52717542984431854687385959/25000000000000000000000),(214389516472699/50000000000000),(62589015759292061/62500000000000000),(12430706007901283/62500000000000000),(214389516472699/100000000000000),(117197449417308043/1000000000000000000),26⟩
theorem inputs_valid392 : inputs392.Valid := by decide +kernel
def envelope392 : RatMajorityEnvelope := ⟨196,0,inputs392,(2576003929/2166380000),(357026893300646913/500000000000000000)⟩
theorem envelope_sound392 : envelope392.Sound := by
  apply rat_majority_inputs_envelopes inputs392 inputs_valid392
  · norm_num [envelope392]
  · intro rho hr0 hr1
    have hh := Batch019.bound784 rho hr0 hr1
    norm_num [Batch019.certificate784,envelope392,inputs392,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound785 rho hr0 hr1
    norm_num [Batch019.certificate785,envelope392,inputs392,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs393 : RatMajorityInputs := ⟨(52717542984431854687385959/25000000000000000000000),(61699414554299/12500000000000),(62589015759292061/62500000000000000),(130151003064527637/1000000000000000000),(61699414554299/25000000000000),(84756182784596101/1000000000000000000),27⟩
theorem inputs_valid393 : inputs393.Valid := by decide +kernel
def envelope393 : RatMajorityEnvelope := ⟨196,1,inputs393,1,(270475350442071313/500000000000000000)⟩
theorem envelope_sound393 : envelope393.Sound := by
  apply rat_majority_inputs_envelopes inputs393 inputs_valid393
  · norm_num [envelope393]
  · intro rho hr0 hr1
    have hh := Batch019.bound786 rho hr0 hr1
    norm_num [Batch019.certificate786,envelope393,inputs393,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound787 rho hr0 hr1
    norm_num [Batch019.certificate787,envelope393,inputs393,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs394 : RatMajorityInputs := ⟨(100025455324758892218278821/50000000000000000000000),(42815850278929/10000000000000),(1001501369252209983/1000000000000000000),(24959511146109671/125000000000000000),(42815850278929/20000000000000),(14695204607036059/125000000000000000),25⟩
theorem inputs_valid394 : inputs394.Valid := by decide +kernel
def envelope394 : RatMajorityEnvelope := ⟨197,0,inputs394,(642421383/540365000),(356989493420606793/500000000000000000)⟩
theorem envelope_sound394 : envelope394.Sound := by
  apply rat_majority_inputs_envelopes inputs394 inputs_valid394
  · norm_num [envelope394]
  · intro rho hr0 hr1
    have hh := Batch019.bound788 rho hr0 hr1
    norm_num [Batch019.certificate788,envelope394,inputs394,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound789 rho hr0 hr1
    norm_num [Batch019.certificate789,envelope394,inputs394,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs395 : RatMajorityInputs := ⟨(100025455324758892218278821/50000000000000000000000),(246839133923487/50000000000000),(1001501369252209983/1000000000000000000),(130078430664181873/1000000000000000000),(246839133923487/100000000000000),(84721036848177407/1000000000000000000),27⟩
theorem inputs_valid395 : inputs395.Valid := by decide +kernel
def envelope395 : RatMajorityEnvelope := ⟨197,1,inputs395,1,(540978149932814201/1000000000000000000)⟩
theorem envelope_sound395 : envelope395.Sound := by
  apply rat_majority_inputs_envelopes inputs395 inputs_valid395
  · norm_num [envelope395]
  · intro rho hr0 hr1
    have hh := Batch019.bound790 rho hr0 hr1
    norm_num [Batch019.certificate790,envelope395,inputs395,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound791 rho hr0 hr1
    norm_num [Batch019.certificate791,envelope395,inputs395,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs396 : RatMajorityInputs := ⟨(19013976666126467421675133/10000000000000000000000),(8600142174667/2000000000000),(40063189004775533/40000000000000000),(197345773712471269/1000000000000000000),(8600142174667/4000000000000),(14560002196623849/125000000000000000),25⟩
theorem inputs_valid396 : inputs396.Valid := by decide +kernel
def envelope396 : RatMajorityEnvelope := ⟨198,0,inputs396,(20513561/17253200),(356944322375139801/500000000000000000)⟩
theorem envelope_sound396 : envelope396.Sound := by
  apply rat_majority_inputs_envelopes inputs396 inputs_valid396
  · norm_num [envelope396]
  · intro rho hr0 hr1
    have hh := Batch019.bound792 rho hr0 hr1
    norm_num [Batch019.certificate792,envelope396,inputs396,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound793 rho hr0 hr1
    norm_num [Batch019.certificate793,envelope396,inputs396,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs397 : RatMajorityInputs := ⟨(19013976666126467421675133/10000000000000000000000),(49457576650317/10000000000000),(40063189004775533/40000000000000000),(129295514896422577/1000000000000000000),(49457576650317/20000000000000),(42170851764497819/500000000000000000),26⟩
theorem inputs_valid397 : inputs397.Valid := by decide +kernel
def envelope397 : RatMajorityEnvelope := ⟨198,1,inputs397,1,(21637180746436427/40000000000000000)⟩
theorem envelope_sound397 : envelope397.Sound := by
  apply rat_majority_inputs_envelopes inputs397 inputs_valid397
  · norm_num [envelope397]
  · intro rho hr0 hr1
    have hh := Batch019.bound794 rho hr0 hr1
    norm_num [Batch019.certificate794,envelope397,inputs397,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound795 rho hr0 hr1
    norm_num [Batch019.certificate795,envelope397,inputs397,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs398 : RatMajorityInputs := ⟨(36208027995374786164468413/20000000000000000000000),(430479414056467/100000000000000),(125207403668051057/125000000000000000),(196754078128991741/1000000000000000000),(430479414056467/200000000000000),(58102635724567113/500000000000000000),25⟩
theorem inputs_valid398 : inputs398.Valid := by decide +kernel
def envelope398 : RatMajorityEnvelope := ⟨199,0,inputs398,(2559464737/2151970000),(714224263589594869/1000000000000000000)⟩
theorem envelope_sound398 : envelope398.Sound := by
  apply rat_majority_inputs_envelopes inputs398 inputs_valid398
  · norm_num [envelope398]
  · intro rho hr0 hr1
    have hh := Batch019.bound796 rho hr0 hr1
    norm_num [Batch019.certificate796,envelope398,inputs398,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound797 rho hr0 hr1
    norm_num [Batch019.certificate797,envelope398,inputs398,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs399 : RatMajorityInputs := ⟨(36208027995374786164468413/20000000000000000000000),(247220714552929/50000000000000),(125207403668051057/125000000000000000),(16176554438694179/125000000000000000),(247220714552929/100000000000000),(16879674756777221/200000000000000000),26⟩
theorem inputs_valid399 : inputs399.Valid := by decide +kernel
def envelope399 : RatMajorityEnvelope := ⟨199,1,inputs399,1,(540978544489204803/1000000000000000000)⟩
theorem envelope_sound399 : envelope399.Sound := by
  apply rat_majority_inputs_envelopes inputs399 inputs_valid399
  · norm_num [envelope399]
  · intro rho hr0 hr1
    have hh := Batch019.bound798 rho hr0 hr1
    norm_num [Batch019.certificate798,envelope399,inputs399,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch019.bound799 rho hr0 hr1
    norm_num [Batch019.certificate799,envelope399,inputs399,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope380,envelope381,envelope382,envelope383,envelope384,envelope385,envelope386,envelope387,envelope388,envelope389,envelope390,envelope391,envelope392,envelope393,envelope394,envelope395,envelope396,envelope397,envelope398,envelope399]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound380
  · exact envelope_sound381
  · exact envelope_sound382
  · exact envelope_sound383
  · exact envelope_sound384
  · exact envelope_sound385
  · exact envelope_sound386
  · exact envelope_sound387
  · exact envelope_sound388
  · exact envelope_sound389
  · exact envelope_sound390
  · exact envelope_sound391
  · exact envelope_sound392
  · exact envelope_sound393
  · exact envelope_sound394
  · exact envelope_sound395
  · exact envelope_sound396
  · exact envelope_sound397
  · exact envelope_sound398
  · exact envelope_sound399

end Cycle12.MajorityCertificates.Inputs019
