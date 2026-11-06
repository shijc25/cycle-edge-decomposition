import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch020

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs020

def inputs400 : RatMajorityInputs := ⟨(539577965692729161796347/312500000000000000000),(4302947138967/1000000000000),(40069592795729869/40000000000000000),(24623161137364649/125000000000000000),(4302947138967/2000000000000),(29078159169613323/250000000000000000),25⟩
theorem inputs_valid400 : inputs400.Valid := by decide +kernel
def envelope400 : RatMajorityEnvelope := ⟨200,0,inputs400,(106387241/89475000),(2231197120607523/3125000000000000)⟩
theorem envelope_sound400 : envelope400.Sound := by
  apply rat_majority_inputs_envelopes inputs400 inputs_valid400
  · norm_num [envelope400]
  · intro rho hr0 hr1
    have hh := Batch020.bound800 rho hr0 hr1
    norm_num [Batch020.certificate800,envelope400,inputs400,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound801 rho hr0 hr1
    norm_num [Batch020.certificate801,envelope400,inputs400,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs401 : RatMajorityInputs := ⟨(539577965692729161796347/312500000000000000000),(12388047612597/2500000000000),(40069592795729869/40000000000000000),(64237344315756969/500000000000000000),(12388047612597/5000000000000),(10492956418539091/125000000000000000),26⟩
theorem inputs_valid401 : inputs401.Valid := by decide +kernel
def envelope401 : RatMajorityEnvelope := ⟨200,1,inputs401,1,(540914527404130911/1000000000000000000)⟩
theorem envelope_sound401 : envelope401.Sound := by
  apply rat_majority_inputs_envelopes inputs401 inputs_valid401
  · norm_num [envelope401]
  · intro rho hr0 hr1
    have hh := Batch020.bound802 rho hr0 hr1
    norm_num [Batch020.certificate802,envelope401,inputs401,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound803 rho hr0 hr1
    norm_num [Batch020.certificate803,envelope401,inputs401,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs402 : RatMajorityInputs := ⟨(6597629622136798011946049/4000000000000000000000),(17266233699611/4000000000000),(1001821411410478177/1000000000000000000),(48821690353999233/250000000000000000),(17266233699611/8000000000000),(115523741913541689/1000000000000000000),25⟩
theorem inputs_valid402 : inputs402.Valid := by decide +kernel
def envelope402 : RatMajorityEnvelope := ⟨201,0,inputs402,(509679523/428590000),(714029338025499367/1000000000000000000)⟩
theorem envelope_sound402 : envelope402.Sound := by
  apply rat_majority_inputs_envelopes inputs402 inputs_valid402
  · norm_num [envelope402]
  · intro rho hr0 hr1
    have hh := Batch020.bound804 rho hr0 hr1
    norm_num [Batch020.certificate804,envelope402,inputs402,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound805 rho hr0 hr1
    norm_num [Batch020.certificate805,envelope402,inputs402,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs403 : RatMajorityInputs := ⟨(6597629622136798011946049/4000000000000000000000),(2476895370339/500000000000),(1001821411410478177/1000000000000000000),(128598305336813593/1000000000000000000),(2476895370339/1000000000000),(42001810650620697/500000000000000000),26⟩
theorem inputs_valid403 : inputs403.Valid := by decide +kernel
def envelope403 : RatMajorityEnvelope := ⟨201,1,inputs403,1,(540965230213923089/1000000000000000000)⟩
theorem envelope_sound403 : envelope403.Sound := by
  apply rat_majority_inputs_envelopes inputs403 inputs_valid403
  · norm_num [envelope403]
  · intro rho hr0 hr1
    have hh := Batch020.bound806 rho hr0 hr1
    norm_num [Batch020.certificate806,envelope403,inputs403,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound807 rho hr0 hr1
    norm_num [Batch020.certificate807,envelope403,inputs403,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs404 : RatMajorityInputs := ⟨(78901269618571916338496553/50000000000000000000000),(216463792802741/50000000000000),(500951962487318747/500000000000000000),(6053467136287067/31250000000000000),(216463792802741/100000000000000),(114791489854996057/1000000000000000000),25⟩
theorem inputs_valid404 : inputs404.Valid := by decide +kernel
def envelope404 : RatMajorityEnvelope := ⟨202,0,inputs404,(2541858211/2138620000),(178334223447618519/250000000000000000)⟩
theorem envelope_sound404 : envelope404.Sound := by
  apply rat_majority_inputs_envelopes inputs404 inputs_valid404
  · norm_num [envelope404]
  · intro rho hr0 hr1
    have hh := Batch020.bound808 rho hr0 hr1
    norm_num [Batch020.certificate808,envelope404,inputs404,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound809 rho hr0 hr1
    norm_num [Batch020.certificate809,envelope404,inputs404,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs405 : RatMajorityInputs := ⟨(78901269618571916338496553/50000000000000000000000),(49552696780719/10000000000000),(500951962487318747/500000000000000000),(128470308382327213/1000000000000000000),(49552696780719/20000000000000),(20985381553593677/250000000000000000),27⟩
theorem inputs_valid405 : inputs405.Valid := by decide +kernel
def envelope405 : RatMajorityEnvelope := ⟨202,1,inputs405,1,(135247328283856173/250000000000000000)⟩
theorem envelope_sound405 : envelope405.Sound := by
  apply rat_majority_inputs_envelopes inputs405 inputs_valid405
  · norm_num [envelope405]
  · intro rho hr0 hr1
    have hh := Batch020.bound810 rho hr0 hr1
    norm_num [Batch020.certificate810,envelope405,inputs405,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound811 rho hr0 hr1
    norm_num [Batch020.certificate811,envelope405,inputs405,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs406 : RatMajorityInputs := ⟨(472477001673446138080943/312500000000000000000),(337390363543/78125000000),(250496822533032477/250000000000000000),(195033480150275579/1000000000000000000),(337390363543/156250000000),(23081213999143031/200000000000000000),25⟩
theorem inputs_valid406 : inputs406.Valid := by decide +kernel
def envelope406 : RatMajorityEnvelope := ⟨203,0,inputs406,(2538236991/2134400000),(714100394012666137/1000000000000000000)⟩
theorem envelope_sound406 : envelope406.Sound := by
  apply rat_majority_inputs_envelopes inputs406 inputs_valid406
  · norm_num [envelope406]
  · intro rho hr0 hr1
    have hh := Batch020.bound812 rho hr0 hr1
    norm_num [Batch020.certificate812,envelope406,inputs406,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound813 rho hr0 hr1
    norm_num [Batch020.certificate813,envelope406,inputs406,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs407 : RatMajorityInputs := ⟨(472477001673446138080943/312500000000000000000),(1551119658243/312500000000),(250496822533032477/250000000000000000),(127752924749981533/1000000000000000000),(1551119658243/625000000000),(10449167227777057/125000000000000000),27⟩
theorem inputs_valid407 : inputs407.Valid := by decide +kernel
def envelope407 : RatMajorityEnvelope := ⟨203,1,inputs407,1,(540950588196208237/1000000000000000000)⟩
theorem envelope_sound407 : envelope407.Sound := by
  apply rat_majority_inputs_envelopes inputs407 inputs_valid407
  · norm_num [envelope407]
  · intro rho hr0 hr1
    have hh := Batch020.bound814 rho hr0 hr1
    norm_num [Batch020.certificate814,envelope407,inputs407,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound815 rho hr0 hr1
    norm_num [Batch020.certificate815,envelope407,inputs407,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs408 : RatMajorityInputs := ⟨(72530480692788372802256957/50000000000000000000000),(433883228554669/100000000000000),(200414285506902387/200000000000000000),(192533887685291499/1000000000000000000),(433883228554669/200000000000000),(28561074950585471/250000000000000000),25⟩
theorem inputs_valid408 : inputs408.Valid := by decide +kernel
def envelope408 : RatMajorityEnvelope := ⟨204,0,inputs408,(253157291/213029000),(178288592127591351/250000000000000000)⟩
theorem envelope_sound408 : envelope408.Sound := by
  apply rat_majority_inputs_envelopes inputs408 inputs_valid408
  · norm_num [envelope408]
  · intro rho hr0 hr1
    have hh := Batch020.bound816 rho hr0 hr1
    norm_num [Batch020.certificate816,envelope408,inputs408,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound817 rho hr0 hr1
    norm_num [Batch020.certificate817,envelope408,inputs408,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs409 : RatMajorityInputs := ⟨(72530480692788372802256957/50000000000000000000000),(496434156268819/100000000000000),(200414285506902387/200000000000000000),(63843817078529759/500000000000000000),(496434156268819/200000000000000),(83561634528941429/1000000000000000000),26⟩
theorem inputs_valid409 : inputs409.Valid := by decide +kernel
def envelope409 : RatMajorityEnvelope := ⟨204,1,inputs409,1,(13524555306926011/25000000000000000)⟩
theorem envelope_sound409 : envelope409.Sound := by
  apply rat_majority_inputs_envelopes inputs409 inputs_valid409
  · norm_num [envelope409]
  · intro rho hr0 hr1
    have hh := Batch020.bound818 rho hr0 hr1
    norm_num [Batch020.certificate818,envelope409,inputs409,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound819 rho hr0 hr1
    norm_num [Batch020.certificate819,envelope409,inputs409,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs410 : RatMajorityInputs := ⟨(2787278676672489803143747/2000000000000000000000),(43295520026121/10000000000000),(501078123468610191/500000000000000000),(38735370097797813/200000000000000000),(43295520026121/20000000000000),(114775641311787147/1000000000000000000),25⟩
theorem inputs_valid410 : inputs410.Valid := by decide +kernel
def envelope410 : RatMajorityEnvelope := ⟨205,0,inputs410,(2526565631/2126300000),(178299788474999831/250000000000000000)⟩
theorem envelope_sound410 : envelope410.Sound := by
  apply rat_majority_inputs_envelopes inputs410 inputs_valid410
  · norm_num [envelope410]
  · intro rho hr0 hr1
    have hh := Batch020.bound820 rho hr0 hr1
    norm_num [Batch020.certificate820,envelope410,inputs410,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound821 rho hr0 hr1
    norm_num [Batch020.certificate821,envelope410,inputs410,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs411 : RatMajorityInputs := ⟨(2787278676672489803143747/2000000000000000000000),(24872449895271/5000000000000),(501078123468610191/500000000000000000),(126817092383025429/1000000000000000000),(24872449895271/10000000000000),(41569349668648809/500000000000000000),26⟩
theorem inputs_valid411 : inputs411.Valid := by decide +kernel
def envelope411 : RatMajorityEnvelope := ⟨205,1,inputs411,1,(13523201093237193/25000000000000000)⟩
theorem envelope_sound411 : envelope411.Sound := by
  apply rat_majority_inputs_envelopes inputs411 inputs_valid411
  · norm_num [envelope411]
  · intro rho hr0 hr1
    have hh := Batch020.bound822 rho hr0 hr1
    norm_num [Batch020.certificate822,envelope411,inputs411,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound823 rho hr0 hr1
    norm_num [Batch020.certificate823,envelope411,inputs411,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs412 : RatMajorityInputs := ⟨(536244221589524330399109/400000000000000000000),(435752378497077/100000000000000),(200448337490945489/200000000000000000),(38049825912783881/200000000000000000),(435752378497077/200000000000000),(56590787443013097/500000000000000000),25⟩
theorem inputs_valid412 : inputs412.Valid := by decide +kernel
def envelope412 : RatMajorityEnvelope := ⟨206,0,inputs412,(1259774491/1061205000),(71190065542749527/100000000000000000)⟩
theorem envelope_sound412 : envelope412.Sound := by
  apply rat_majority_inputs_envelopes inputs412 inputs_valid412
  · norm_num [envelope412]
  · intro rho hr0 hr1
    have hh := Batch020.bound824 rho hr0 hr1
    norm_num [Batch020.certificate824,envelope412,inputs412,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound825 rho hr0 hr1
    norm_num [Batch020.certificate825,envelope412,inputs412,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs413 : RatMajorityInputs := ⟨(536244221589524330399109/400000000000000000000),(248803019957007/50000000000000),(200448337490945489/200000000000000000),(126682851280074399/1000000000000000000),(248803019957007/100000000000000),(83073443618694123/1000000000000000000),27⟩
theorem inputs_valid413 : inputs413.Valid := by decide +kernel
def envelope413 : RatMajorityEnvelope := ⟨206,1,inputs413,1,(67619121494694227/125000000000000000)⟩
theorem envelope_sound413 : envelope413.Sound := by
  apply rat_majority_inputs_envelopes inputs413 inputs_valid413
  · norm_num [envelope413]
  · intro rho hr0 hr1
    have hh := Batch020.bound826 rho hr0 hr1
    norm_num [Batch020.certificate826,envelope413,inputs413,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound827 rho hr0 hr1
    norm_num [Batch020.certificate827,envelope413,inputs413,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs414 : RatMajorityInputs := ⟨(129118216494108402635283339/100000000000000000000000),(437173951171113/100000000000000),(200465531585209837/200000000000000000),(188526866391891363/1000000000000000000),(437173951171113/200000000000000),(11237994801780241/100000000000000000),25⟩
theorem inputs_valid414 : inputs414.Valid := by decide +kernel
def envelope414 : RatMajorityEnvelope := ⟨207,0,inputs414,(2511683399/2118630000),(710346401013864993/1000000000000000000)⟩
theorem envelope_sound414 : envelope414.Sound := by
  apply rat_majority_inputs_envelopes inputs414 inputs_valid414
  · norm_num [envelope414]
  · intro rho hr0 hr1
    have hh := Batch020.bound828 rho hr0 hr1
    norm_num [Batch020.certificate828,envelope414,inputs414,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound829 rho hr0 hr1
    norm_num [Batch020.certificate829,envelope414,inputs414,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs415 : RatMajorityInputs := ⟨(129118216494108402635283339/100000000000000000000000),(62355832352829/12500000000000),(200465531585209837/200000000000000000),(25125356105431043/200000000000000000),(62355832352829/25000000000000),(20639931540034889/250000000000000000),26⟩
theorem inputs_valid415 : inputs415.Valid := by decide +kernel
def envelope415 : RatMajorityEnvelope := ⟨207,1,inputs415,1,(135219986996993463/250000000000000000)⟩
theorem envelope_sound415 : envelope415.Sound := by
  apply rat_majority_inputs_envelopes inputs415 inputs_valid415
  · norm_num [envelope415]
  · intro rho hr0 hr1
    have hh := Batch020.bound830 rho hr0 hr1
    norm_num [Batch020.certificate830,envelope415,inputs415,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound831 rho hr0 hr1
    norm_num [Batch020.certificate831,envelope415,inputs415,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs416 : RatMajorityInputs := ⟨(15563053743874452434779847/12500000000000000000000),(3422708213393/781250000000),(501207038168743901/500000000000000000),(93702037227379821/500000000000000000),(3422708213393/1562500000000),(55928542092652311/500000000000000000),26⟩
theorem inputs_valid416 : inputs416.Valid := by decide +kernel
def envelope416 : RatMajorityEnvelope := ⟨208,0,inputs416,(1252975767/1057480000),(141939845344312997/200000000000000000)⟩
theorem envelope_sound416 : envelope416.Sound := by
  apply rat_majority_inputs_envelopes inputs416 inputs_valid416
  · norm_num [envelope416]
  · intro rho hr0 hr1
    have hh := Batch020.bound832 rho hr0 hr1
    norm_num [Batch020.certificate832,envelope416,inputs416,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound833 rho hr0 hr1
    norm_num [Batch020.certificate833,envelope416,inputs416,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs417 : RatMajorityInputs := ⟨(15563053743874452434779847/12500000000000000000000),(31186089356571/6250000000000),(501207038168743901/500000000000000000),(62757959409421053/500000000000000000),(31186089356571/12500000000000),(82505761763245417/1000000000000000000),26⟩
theorem inputs_valid417 : inputs417.Valid := by decide +kernel
def envelope417 : RatMajorityEnvelope := ⟨208,1,inputs417,1,(540907924348005823/1000000000000000000)⟩
theorem envelope_sound417 : envelope417.Sound := by
  apply rat_majority_inputs_envelopes inputs417 inputs_valid417
  · norm_num [envelope417]
  · intro rho hr0 hr1
    have hh := Batch020.bound834 rho hr0 hr1
    norm_num [Batch020.certificate834,envelope417,inputs417,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound835 rho hr0 hr1
    norm_num [Batch020.certificate835,envelope417,inputs417,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs418 : RatMajorityInputs := ⟨(3004800598591799754369591/2500000000000000000000),(21953763859887/5000000000000),(62656303758582349/62500000000000000),(186244043963479649/1000000000000000000),(21953763859887/10000000000000),(111316655589534783/1000000000000000000),25⟩
theorem inputs_valid418 : inputs418.Valid := by decide +kernel
def envelope418 : RatMajorityEnvelope := ⟨209,0,inputs418,(1250163589/1055700000),(709037284312705153/1000000000000000000)⟩
theorem envelope_sound418 : envelope418.Sound := by
  apply rat_majority_inputs_envelopes inputs418 inputs_valid418
  · norm_num [envelope418]
  · intro rho hr0 hr1
    have hh := Batch020.bound836 rho hr0 hr1
    norm_num [Batch020.certificate836,envelope418,inputs418,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound837 rho hr0 hr1
    norm_num [Batch020.certificate837,envelope418,inputs418,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs419 : RatMajorityInputs := ⟨(3004800598591799754369591/2500000000000000000000),(999990911583/200000000000),(62656303758582349/62500000000000000),(62327923432380643/500000000000000000),(999990911583/400000000000),(82086863701829319/1000000000000000000),26⟩
theorem inputs_valid419 : inputs419.Valid := by decide +kernel
def envelope419 : RatMajorityEnvelope := ⟨209,1,inputs419,1,(108171308697398573/200000000000000000)⟩
theorem envelope_sound419 : envelope419.Sound := by
  apply rat_majority_inputs_envelopes inputs419 inputs_valid419
  · norm_num [envelope419]
  · intro rho hr0 hr1
    have hh := Batch020.bound838 rho hr0 hr1
    norm_num [Batch020.certificate838,envelope419,inputs419,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch020.bound839 rho hr0 hr1
    norm_num [Batch020.certificate839,envelope419,inputs419,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope400,envelope401,envelope402,envelope403,envelope404,envelope405,envelope406,envelope407,envelope408,envelope409,envelope410,envelope411,envelope412,envelope413,envelope414,envelope415,envelope416,envelope417,envelope418,envelope419]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound400
  · exact envelope_sound401
  · exact envelope_sound402
  · exact envelope_sound403
  · exact envelope_sound404
  · exact envelope_sound405
  · exact envelope_sound406
  · exact envelope_sound407
  · exact envelope_sound408
  · exact envelope_sound409
  · exact envelope_sound410
  · exact envelope_sound411
  · exact envelope_sound412
  · exact envelope_sound413
  · exact envelope_sound414
  · exact envelope_sound415
  · exact envelope_sound416
  · exact envelope_sound417
  · exact envelope_sound418
  · exact envelope_sound419

end Cycle12.MajorityCertificates.Inputs020
