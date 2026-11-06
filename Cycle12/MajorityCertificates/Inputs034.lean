import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch034

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs034

def inputs680 : RatMajorityInputs := ⟨(14692992406617673488839357589/100000000000000000000000),(53689094148249/12500000000000),(500010209110436559/500000000000000000),(395933393209019/2000000000000000),(53689094148249/25000000000000),(116768286408684453/1000000000000000000),25⟩
theorem inputs_valid680 : inputs680.Valid := by decide +kernel
def envelope680 : RatMajorityEnvelope := ⟨340,0,inputs680,(696358567/596752500),(10832900500551719/15625000000000000)⟩
theorem envelope_sound680 : envelope680.Sound := by
  apply rat_majority_inputs_envelopes inputs680 inputs_valid680
  · norm_num [envelope680]
  · intro rho hr0 hr1
    have hh := Batch034.bound1360 rho hr0 hr1
    norm_num [Batch034.certificate1360,envelope680,inputs680,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1361 rho hr0 hr1
    norm_num [Batch034.certificate1361,envelope680,inputs680,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs681 : RatMajorityInputs := ⟨(14692992406617673488839357589/100000000000000000000000),(52760545826043/12500000000000),(500010209110436559/500000000000000000),(207496200478312613/1000000000000000000),(52760545826043/25000000000000),(6059341751922163/50000000000000000),25⟩
theorem inputs_valid681 : inputs681.Valid := by decide +kernel
def envelope681 : RatMajorityEnvelope := ⟨340,1,inputs681,1,(274803796171744919/500000000000000000)⟩
theorem envelope_sound681 : envelope681.Sound := by
  apply rat_majority_inputs_envelopes inputs681 inputs_valid681
  · norm_num [envelope681]
  · intro rho hr0 hr1
    have hh := Batch034.bound1362 rho hr0 hr1
    norm_num [Batch034.certificate1362,envelope681,inputs681,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1363 rho hr0 hr1
    norm_num [Batch034.certificate1363,envelope681,inputs681,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs682 : RatMajorityInputs := ⟨(6821157933270582293781308061/50000000000000000000000),(21564674729793/5000000000000),(500010995388690201/500000000000000000),(97868859513182903/500000000000000000),(21564674729793/10000000000000),(115733230548840899/1000000000000000000),25⟩
theorem inputs_valid682 : inputs682.Valid := by decide +kernel
def envelope682 : RatMajorityEnvelope := ⟨341,0,inputs682,(696778229/596497500),(694152839005740019/1000000000000000000)⟩
theorem envelope_sound682 : envelope682.Sound := by
  apply rat_majority_inputs_envelopes inputs682 inputs_valid682
  · norm_num [envelope682]
  · intro rho hr0 hr1
    have hh := Batch034.bound1364 rho hr0 hr1
    norm_num [Batch034.certificate1364,envelope682,inputs682,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1365 rho hr0 hr1
    norm_num [Batch034.certificate1365,envelope682,inputs682,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs683 : RatMajorityInputs := ⟨(6821157933270582293781308061/50000000000000000000000),(422394434289/100000000000),(500010995388690201/500000000000000000),(103545447894002283/500000000000000000),(422394434289/200000000000),(2419981999962701/20000000000000000),25⟩
theorem inputs_valid683 : inputs683.Valid := by decide +kernel
def envelope683 : RatMajorityEnvelope := ⟨341,1,inputs683,1,(549554575040182087/1000000000000000000)⟩
theorem envelope_sound683 : envelope683.Sound := by
  apply rat_majority_inputs_envelopes inputs683 inputs_valid683
  · norm_num [envelope683]
  · intro rho hr0 hr1
    have hh := Batch034.bound1366 rho hr0 hr1
    norm_num [Batch034.certificate1366,envelope683,inputs683,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1367 rho hr0 hr1
    norm_num [Batch034.certificate1367,envelope683,inputs683,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs684 : RatMajorityInputs := ⟨(6328040049562016348364035631/50000000000000000000000),(214604303075239/50000000000000),(125002963057367313/125000000000000000),(4958738219294427/25000000000000000),(214604303075239/100000000000000),(116945995139161649/1000000000000000000),26⟩
theorem inputs_valid684 : inputs684.Valid := by decide +kernel
def envelope684 : RatMajorityEnvelope := ⟨342,0,inputs684,(697140523/596165000),(695547125636677181/1000000000000000000)⟩
theorem envelope_sound684 : envelope684.Sound := by
  apply rat_majority_inputs_envelopes inputs684 inputs_valid684
  · norm_num [envelope684]
  · intro rho hr0 hr1
    have hh := Batch034.bound1368 rho hr0 hr1
    norm_num [Batch034.certificate1368,envelope684,inputs684,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1369 rho hr0 hr1
    norm_num [Batch034.certificate1369,envelope684,inputs684,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs685 : RatMajorityInputs := ⟨(6328040049562016348364035631/50000000000000000000000),(211348430675441/50000000000000),(125002963057367313/125000000000000000),(206696215427969071/1000000000000000000),(211348430675441/100000000000000),(120816271252359373/1000000000000000000),25⟩
theorem inputs_valid685 : inputs685.Valid := by decide +kernel
def envelope685 : RatMajorityEnvelope := ⟨342,1,inputs685,1,(274751538915069507/500000000000000000)⟩
theorem envelope_sound685 : envelope685.Sound := by
  apply rat_majority_inputs_envelopes inputs685 inputs_valid685
  · norm_num [envelope685]
  · intro rho hr0 hr1
    have hh := Batch034.bound1370 rho hr0 hr1
    norm_num [Batch034.certificate1370,envelope685,inputs685,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1371 rho hr0 hr1
    norm_num [Batch034.certificate1371,envelope685,inputs685,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs686 : RatMajorityInputs := ⟨(683912280873995017816309019/6250000000000000000000),(837037214299/195312500000),(100002741638123177/100000000000000000),(49791038361021803/250000000000000000),(837037214299/390625000000),(117324078849399629/1000000000000000000),25⟩
theorem inputs_valid686 : inputs686.Valid := by decide +kernel
def envelope686 : RatMajorityEnvelope := ⟨343,0,inputs686,(2789507573/2381720000),(697278804276513227/1000000000000000000)⟩
theorem envelope_sound686 : envelope686.Sound := by
  apply rat_majority_inputs_envelopes inputs686 inputs_valid686
  · norm_num [envelope686]
  · intro rho hr0 hr1
    have hh := Batch034.bound1372 rho hr0 hr1
    norm_num [Batch034.certificate1372,envelope686,inputs686,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1373 rho hr0 hr1
    norm_num [Batch034.certificate1373,envelope686,inputs686,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs687 : RatMajorityInputs := ⟨(683912280873995017816309019/6250000000000000000000),(105561725167173/25000000000000),(100002741638123177/100000000000000000),(41456732347912171/200000000000000000),(105561725167173/50000000000000),(121088390103701087/1000000000000000000),25⟩
theorem inputs_valid687 : inputs687.Valid := by decide +kernel
def envelope687 : RatMajorityEnvelope := ⟨343,1,inputs687,1,(137395584635024191/250000000000000000)⟩
theorem envelope_sound687 : envelope687.Sound := by
  apply rat_majority_inputs_envelopes inputs687 inputs_valid687
  · norm_num [envelope687]
  · intro rho hr0 hr1
    have hh := Batch034.bound1374 rho hr0 hr1
    norm_num [Batch034.certificate1374,envelope687,inputs687,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1375 rho hr0 hr1
    norm_num [Batch034.certificate1375,envelope687,inputs687,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs688 : RatMajorityInputs := ⟨(2569669230710144678743062849/25000000000000000000000),(53623436102437/12500000000000),(500014593649192843/500000000000000000),(198628241458651713/1000000000000000000),(53623436102437/25000000000000),(117075360569902411/1000000000000000000),25⟩
theorem inputs_valid688 : inputs688.Valid := by decide +kernel
def envelope688 : RatMajorityEnvelope := ⟨344,0,inputs688,(279190593/238076000),(69854888510316833/100000000000000000)⟩
theorem envelope_sound688 : envelope688.Sound := by
  apply rat_majority_inputs_envelopes inputs688 inputs_valid688
  · norm_num [envelope688]
  · intro rho hr0 hr1
    have hh := Batch034.bound1376 rho hr0 hr1
    norm_num [Batch034.certificate1376,envelope688,inputs688,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1377 rho hr0 hr1
    norm_num [Batch034.certificate1377,envelope688,inputs688,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs689 : RatMajorityInputs := ⟨(2569669230710144678743062849/25000000000000000000000),(26409631822173/6250000000000),(500014593649192843/500000000000000000),(206882434866089577/1000000000000000000),(26409631822173/12500000000000),(60451267987565747/500000000000000000),25⟩
theorem inputs_valid689 : inputs689.Valid := by decide +kernel
def envelope689 : RatMajorityEnvelope := ⟨344,1,inputs689,1,(109905994822169847/200000000000000000)⟩
theorem envelope_sound689 : envelope689.Sound := by
  apply rat_majority_inputs_envelopes inputs689 inputs_valid689
  · norm_num [envelope689]
  · intro rho hr0 hr1
    have hh := Batch034.bound1378 rho hr0 hr1
    norm_num [Batch034.certificate1378,envelope689,inputs689,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1379 rho hr0 hr1
    norm_num [Batch034.certificate1379,envelope689,inputs689,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs690 : RatMajorityInputs := ⟨(9638392563291473330906751063/100000000000000000000000),(429094190043463/100000000000000),(1000031126275549917/1000000000000000000),(198493706240969579/1000000000000000000),(429094190043463/200000000000000),(58506458403551193/500000000000000000),25⟩
theorem inputs_valid690 : inputs690.Valid := by decide +kernel
def envelope690 : RatMajorityEnvelope := ⟨345,0,inputs690,(2792377277/2379490000),(699273815816348041/1000000000000000000)⟩
theorem envelope_sound690 : envelope690.Sound := by
  apply rat_majority_inputs_envelopes inputs690 inputs_valid690
  · norm_num [envelope690]
  · intro rho hr0 hr1
    have hh := Batch034.bound1380 rho hr0 hr1
    norm_num [Batch034.certificate1380,envelope690,inputs690,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1381 rho hr0 hr1
    norm_num [Batch034.certificate1381,envelope690,inputs690,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs691 : RatMajorityInputs := ⟨(9638392563291473330906751063/100000000000000000000000),(52840599405539/12500000000000),(1000031126275549917/1000000000000000000),(206659792200941883/1000000000000000000),(52840599405539/25000000000000),(120799398086490979/1000000000000000000),25⟩
theorem inputs_valid691 : inputs691.Valid := by decide +kernel
def envelope691 : RatMajorityEnvelope := ⟨345,1,inputs691,1,(549501337133208301/1000000000000000000)⟩
theorem envelope_sound691 : envelope691.Sound := by
  apply rat_majority_inputs_envelopes inputs691 inputs_valid691
  · norm_num [envelope691]
  · intro rho hr0 hr1
    have hh := Batch034.bound1382 rho hr0 hr1
    norm_num [Batch034.certificate1382,envelope691,inputs691,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1383 rho hr0 hr1
    norm_num [Batch034.certificate1383,envelope691,inputs691,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs692 : RatMajorityInputs := ⟨(339813542880550599949883271/4000000000000000000000),(85708694450847/20000000000000),(10000353144536239/10000000000000000),(49797226807996441/250000000000000000),(85708694450847/40000000000000),(14666945787443563/125000000000000000),26⟩
theorem inputs_valid692 : inputs692.Valid := by decide +kernel
def envelope692 : RatMajorityEnvelope := ⟨346,0,inputs692,(174587794/148540625),(700989880434015863/1000000000000000000)⟩
theorem envelope_sound692 : envelope692.Sound := by
  apply rat_majority_inputs_envelopes inputs692 inputs_valid692
  · norm_num [envelope692]
  · intro rho hr0 hr1
    have hh := Batch034.bound1384 rho hr0 hr1
    norm_num [Batch034.certificate1384,envelope692,inputs692,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1385 rho hr0 hr1
    norm_num [Batch034.certificate1385,envelope692,inputs692,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs693 : RatMajorityInputs := ⟨(339813542880550599949883271/4000000000000000000000),(1688193008123/400000000000),(10000353144536239/10000000000000000),(207543450632115221/1000000000000000000),(1688193008123/800000000000),(121208720071092403/1000000000000000000),25⟩
theorem inputs_valid693 : inputs693.Valid := by decide +kernel
def envelope693 : RatMajorityEnvelope := ⟨346,1,inputs693,1,(68702501983182957/125000000000000000)⟩
theorem envelope_sound693 : envelope693.Sound := by
  apply rat_majority_inputs_envelopes inputs693 inputs_valid693
  · norm_num [envelope693]
  · intro rho hr0 hr1
    have hh := Batch034.bound1386 rho hr0 hr1
    norm_num [Batch034.certificate1386,envelope693,inputs693,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1387 rho hr0 hr1
    norm_num [Batch034.certificate1387,envelope693,inputs693,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs694 : RatMajorityInputs := ⟨(251573162891937880760087841/3125000000000000000000),(13405669859241/3125000000000),(500018633290663983/500000000000000000),(39727175228950951/200000000000000000),(13405669859241/6250000000000),(117078904098850751/1000000000000000000),25⟩
theorem inputs_valid694 : inputs694.Valid := by decide +kernel
def envelope694 : RatMajorityEnvelope := ⟨347,0,inputs694,(559177747/475152000),(17556648710617503/25000000000000000)⟩
theorem envelope_sound694 : envelope694.Sound := by
  apply rat_majority_inputs_envelopes inputs694 inputs_valid694
  · norm_num [envelope694]
  · intro rho hr0 hr1
    have hh := Batch034.bound1388 rho hr0 hr1
    norm_num [Batch034.certificate1388,envelope694,inputs694,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1389 rho hr0 hr1
    norm_num [Batch034.certificate1389,envelope694,inputs694,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs695 : RatMajorityInputs := ⟨(251573162891937880760087841/3125000000000000000000),(13197793175607/3125000000000),(500018633290663983/500000000000000000),(207175874502154173/1000000000000000000),(13197793175607/6250000000000),(30259615742952543/250000000000000000),27⟩
theorem inputs_valid695 : inputs695.Valid := by decide +kernel
def envelope695 : RatMajorityEnvelope := ⟨347,1,inputs695,1,(549572146266252297/1000000000000000000)⟩
theorem envelope_sound695 : envelope695.Sound := by
  apply rat_majority_inputs_envelopes inputs695 inputs_valid695
  · norm_num [envelope695]
  · intro rho hr0 hr1
    have hh := Batch034.bound1390 rho hr0 hr1
    norm_num [Batch034.certificate1390,envelope695,inputs695,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1391 rho hr0 hr1
    norm_num [Batch034.certificate1391,envelope695,inputs695,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs696 : RatMajorityInputs := ⟨(95136068076235222227541279/1250000000000000000000),(5363658662739/1250000000000),(1000039418435573187/1000000000000000000),(198495593247839269/1000000000000000000),(5363658662739/2500000000000),(58506896333152433/500000000000000000),26⟩
theorem inputs_valid696 : inputs696.Valid := by decide +kernel
def envelope696 : RatMajorityEnvelope := ⟨348,0,inputs696,(699107569/593637500),(140598963348997651/200000000000000000)⟩
theorem envelope_sound696 : envelope696.Sound := by
  apply rat_majority_inputs_envelopes inputs696 inputs_valid696
  · norm_num [envelope696]
  · intro rho hr0 hr1
    have hh := Batch034.bound1392 rho hr0 hr1
    norm_num [Batch034.certificate1392,envelope696,inputs696,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1393 rho hr0 hr1
    norm_num [Batch034.certificate1393,envelope696,inputs696,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs697 : RatMajorityInputs := ⟨(95136068076235222227541279/1250000000000000000000),(42262080997803/10000000000000),(1000039418435573187/1000000000000000000),(103397703293885051/500000000000000000),(42262080997803/20000000000000),(15107777650582011/125000000000000000),26⟩
theorem inputs_valid697 : inputs697.Valid := by decide +kernel
def envelope697 : RatMajorityEnvelope := ⟨348,1,inputs697,1,(549522701778864821/1000000000000000000)⟩
theorem envelope_sound697 : envelope697.Sound := by
  apply rat_majority_inputs_envelopes inputs697 inputs_valid697
  · norm_num [envelope697]
  · intro rho hr0 hr1
    have hh := Batch034.bound1394 rho hr0 hr1
    norm_num [Batch034.certificate1394,envelope697,inputs697,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1395 rho hr0 hr1
    norm_num [Batch034.certificate1395,envelope697,inputs697,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs698 : RatMajorityInputs := ⟨(170217265357218209037545979/2500000000000000000000),(10713444685629/2500000000000),(31251376963915941/31250000000000000),(99598047078509267/500000000000000000),(10713444685629/5000000000000),(29334725377535673/250000000000000000),25⟩
theorem inputs_valid698 : inputs698.Valid := by decide +kernel
def envelope698 : RatMajorityEnvelope := ⟨349,0,inputs698,(1398788803/1185900000),(352363179409208613/500000000000000000)⟩
theorem envelope_sound698 : envelope698.Sound := by
  apply rat_majority_inputs_envelopes inputs698 inputs_valid698
  · norm_num [envelope698]
  · intro rho hr0 hr1
    have hh := Batch034.bound1396 rho hr0 hr1
    norm_num [Batch034.certificate1396,envelope698,inputs698,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1397 rho hr0 hr1
    norm_num [Batch034.certificate1397,envelope698,inputs698,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs699 : RatMajorityInputs := ⟨(170217265357218209037545979/2500000000000000000000),(263901611943/62500000000),(31251376963915941/31250000000000000),(207289310503567367/1000000000000000000),(263901611943/125000000000),(3784093955800609/31250000000000000),26⟩
theorem inputs_valid699 : inputs699.Valid := by decide +kernel
def envelope699 : RatMajorityEnvelope := ⟨349,1,inputs699,1,(549589976314577083/1000000000000000000)⟩
theorem envelope_sound699 : envelope699.Sound := by
  apply rat_majority_inputs_envelopes inputs699 inputs_valid699
  · norm_num [envelope699]
  · intro rho hr0 hr1
    have hh := Batch034.bound1398 rho hr0 hr1
    norm_num [Batch034.certificate1398,envelope699,inputs699,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch034.bound1399 rho hr0 hr1
    norm_num [Batch034.certificate1399,envelope699,inputs699,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope680,envelope681,envelope682,envelope683,envelope684,envelope685,envelope686,envelope687,envelope688,envelope689,envelope690,envelope691,envelope692,envelope693,envelope694,envelope695,envelope696,envelope697,envelope698,envelope699]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound680
  · exact envelope_sound681
  · exact envelope_sound682
  · exact envelope_sound683
  · exact envelope_sound684
  · exact envelope_sound685
  · exact envelope_sound686
  · exact envelope_sound687
  · exact envelope_sound688
  · exact envelope_sound689
  · exact envelope_sound690
  · exact envelope_sound691
  · exact envelope_sound692
  · exact envelope_sound693
  · exact envelope_sound694
  · exact envelope_sound695
  · exact envelope_sound696
  · exact envelope_sound697
  · exact envelope_sound698
  · exact envelope_sound699

end Cycle12.MajorityCertificates.Inputs034
