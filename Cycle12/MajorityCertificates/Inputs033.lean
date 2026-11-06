import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs033

def inputs660 : RatMajorityInputs := ⟨(2104315861043615933069238261/3125000000000000000000),(54147709872771/12500000000000),(1000004455145094413/1000000000000000000),(193397391451343349/1000000000000000000),(54147709872771/25000000000000),(5732287183554481/50000000000000000),25⟩
theorem inputs_valid660 : inputs660.Valid := by decide +kernel
def envelope660 : RatMajorityEnvelope := ⟨330,0,inputs660,(69422209/60162000),(340617102204368261/500000000000000000)⟩
theorem envelope_sound660 : envelope660.Sound := by
  apply rat_majority_inputs_envelopes inputs660 inputs_valid660
  · norm_num [envelope660]
  · intro rho hr0 hr1
    have hh := Batch033.bound1320 rho hr0 hr1
    norm_num [Batch033.certificate1320,envelope660,inputs660,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1321 rho hr0 hr1
    norm_num [Batch033.certificate1321,envelope660,inputs660,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs661 : RatMajorityInputs := ⟨(2104315861043615933069238261/3125000000000000000000),(13207154827131/3125000000000),(1000004455145094413/1000000000000000000),(51696195528123393/250000000000000000),(13207154827131/6250000000000),(120857299499010933/1000000000000000000),25⟩
theorem inputs_valid661 : inputs661.Valid := by decide +kernel
def envelope661 : RatMajorityEnvelope := ⟨330,1,inputs661,1,(68688351960154883/125000000000000000)⟩
theorem envelope_sound661 : envelope661.Sound := by
  apply rat_majority_inputs_envelopes inputs661 inputs_valid661
  · norm_num [envelope661]
  · intro rho hr0 hr1
    have hh := Batch033.bound1322 rho hr0 hr1
    norm_num [Batch033.certificate1322,envelope661,inputs661,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1323 rho hr0 hr1
    norm_num [Batch033.certificate1323,envelope661,inputs661,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs662 : RatMajorityInputs := ⟨(56758177762104718857762485343/100000000000000000000000),(431209834864783/100000000000000),(125000660700460127/125000000000000000),(12240122610978601/62500000000000000),(431209834864783/200000000000000),(57890825865057157/500000000000000000),26⟩
theorem inputs_valid662 : inputs662.Valid := by decide +kernel
def envelope662 : RatMajorityEnvelope := ⟨331,0,inputs662,(1388963351/1202435000),(170640342519457387/250000000000000000)⟩
theorem envelope_sound662 : envelope662.Sound := by
  apply rat_majority_inputs_envelopes inputs662 inputs_valid662
  · norm_num [envelope662]
  · intro rho hr0 hr1
    have hh := Batch033.bound1324 rho hr0 hr1
    norm_num [Batch033.certificate1324,envelope662,inputs662,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1325 rho hr0 hr1
    norm_num [Batch033.certificate1325,envelope662,inputs662,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs663 : RatMajorityInputs := ⟨(56758177762104718857762485343/100000000000000000000000),(105733159165647/25000000000000),(125000660700460127/125000000000000000),(206388954398155987/1000000000000000000),(105733159165647/50000000000000),(120673927701513801/1000000000000000000),25⟩
theorem inputs_valid663 : inputs663.Valid := by decide +kernel
def envelope663 : RatMajorityEnvelope := ⟨331,1,inputs663,1,(549454838526523649/1000000000000000000)⟩
theorem envelope_sound663 : envelope663.Sound := by
  apply rat_majority_inputs_envelopes inputs663 inputs_valid663
  · norm_num [envelope663]
  · intro rho hr0 hr1
    have hh := Batch033.bound1326 rho hr0 hr1
    norm_num [Batch033.certificate1326,envelope663,inputs663,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1327 rho hr0 hr1
    norm_num [Batch033.certificate1327,envelope663,inputs663,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs664 : RatMajorityInputs := ⟨(8359646481507909550633557343/20000000000000000000000),(85159517091643/20000000000000),(500003588688533471/500000000000000000),(202685777543964683/1000000000000000000),(85159517091643/40000000000000),(118957626716852887/1000000000000000000),25⟩
theorem inputs_valid664 : inputs664.Valid := by decide +kernel
def envelope664 : RatMajorityEnvelope := ⟨332,0,inputs664,(2780588529/2401450000),(5357294450111349/7812500000000000)⟩
theorem envelope_sound664 : envelope664.Sound := by
  apply rat_majority_inputs_envelopes inputs664 inputs_valid664
  · norm_num [envelope664]
  · intro rho hr0 hr1
    have hh := Batch033.bound1328 rho hr0 hr1
    norm_num [Batch033.certificate1328,envelope664,inputs664,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1329 rho hr0 hr1
    norm_num [Batch033.certificate1329,envelope664,inputs664,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs665 : RatMajorityInputs := ⟨(8359646481507909550633557343/20000000000000000000000),(84492674482829/20000000000000),(500003588688533471/500000000000000000),(20700087323853907/100000000000000000),(84492674482829/40000000000000),(60478699964934357/500000000000000000),25⟩
theorem inputs_valid665 : inputs665.Valid := by decide +kernel
def envelope665 : RatMajorityEnvelope := ⟨332,1,inputs665,1,(549536528834180869/1000000000000000000)⟩
theorem envelope_sound665 : envelope665.Sound := by
  apply rat_majority_inputs_envelopes inputs665 inputs_valid665
  · norm_num [envelope665]
  · intro rho hr0 hr1
    have hh := Batch033.bound1330 rho hr0 hr1
    norm_num [Batch033.certificate1330,envelope665,inputs665,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1331 rho hr0 hr1
    norm_num [Batch033.certificate1331,envelope665,inputs665,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs666 : RatMajorityInputs := ⟨(572965862125079405752399533/1562500000000000000000),(214788236677043/50000000000000),(500004090583869843/500000000000000000),(39577314067131707/200000000000000000),(214788236677043/100000000000000),(23346217972046969/200000000000000000),25⟩
theorem inputs_valid666 : inputs666.Valid := by decide +kernel
def envelope666 : RatMajorityEnvelope := ⟨333,0,inputs666,(1390506703/1200110000),(27436627541683403/40000000000000000)⟩
theorem envelope_sound666 : envelope666.Sound := by
  apply rat_majority_inputs_envelopes inputs666 inputs_valid666
  · norm_num [envelope666]
  · intro rho hr0 hr1
    have hh := Batch033.bound1332 rho hr0 hr1
    norm_num [Batch033.certificate1332,envelope666,inputs666,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1333 rho hr0 hr1
    norm_num [Batch033.certificate1333,envelope666,inputs666,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs667 : RatMajorityInputs := ⟨(572965862125079405752399533/1562500000000000000000),(211302857533239/50000000000000),(500004090583869843/500000000000000000),(206815099082693547/1000000000000000000),(211302857533239/100000000000000),(15108917946450047/125000000000000000),25⟩
theorem inputs_valid667 : inputs667.Valid := by decide +kernel
def envelope667 : RatMajorityEnvelope := ⟨333,1,inputs667,1,(109902473688077397/200000000000000000)⟩
theorem envelope_sound667 : envelope667.Sound := by
  apply rat_majority_inputs_envelopes inputs667 inputs_valid667
  · norm_num [envelope667]
  · intro rho hr0 hr1
    have hh := Batch033.bound1334 rho hr0 hr1
    norm_num [Batch033.certificate1334,envelope667,inputs667,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1335 rho hr0 hr1
    norm_num [Batch033.certificate1335,envelope667,inputs667,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs668 : RatMajorityInputs := ⟨(16166153143909672953900448413/50000000000000000000000),(107645349748371/25000000000000),(1000009278712206949/1000000000000000000),(39325301899315393/200000000000000000),(107645349748371/50000000000000),(116146030618150017/1000000000000000000),25⟩
theorem inputs_valid668 : inputs668.Valid := by decide +kernel
def envelope668 : RatMajorityEnvelope := ⟨334,0,inputs668,(2780777237/2398710000),(343173790034140309/500000000000000000)⟩
theorem envelope_sound668 : envelope668.Sound := by
  apply rat_majority_inputs_envelopes inputs668 inputs_valid668
  · norm_num [envelope668]
  · intro rho hr0 hr1
    have hh := Batch033.bound1336 rho hr0 hr1
    norm_num [Batch033.certificate1336,envelope668,inputs668,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1337 rho hr0 hr1
    norm_num [Batch033.certificate1337,envelope668,inputs668,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs669 : RatMajorityInputs := ⟨(16166153143909672953900448413/50000000000000000000000),(422634936434127/100000000000000),(1000009278712206949/1000000000000000000),(206776978937186431/1000000000000000000),(422634936434127/200000000000000),(60426842365913371/500000000000000000),25⟩
theorem inputs_valid669 : inputs669.Valid := by decide +kernel
def envelope669 : RatMajorityEnvelope := ⟨334,1,inputs669,1,(274753890792743221/500000000000000000)⟩
theorem envelope_sound669 : envelope669.Sound := by
  apply rat_majority_inputs_envelopes inputs669 inputs_valid669
  · norm_num [envelope669]
  · intro rho hr0 hr1
    have hh := Batch033.bound1338 rho hr0 hr1
    norm_num [Batch033.certificate1338,envelope669,inputs669,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1339 rho hr0 hr1
    norm_num [Batch033.certificate1339,envelope669,inputs669,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs670 : RatMajorityInputs := ⟨(2560976905293177306405760079/10000000000000000000000),(84187001326339/20000000000000),(1000011714386519253/1000000000000000000),(209004363452952831/1000000000000000000),(84187001326339/40000000000000),(121885276507359699/1000000000000000000),26⟩
theorem inputs_valid670 : inputs670.Valid := by decide +kernel
def envelope670 : RatMajorityEnvelope := ⟨335,0,inputs670,(557168173/479090000),(690944806042897451/1000000000000000000)⟩
theorem envelope_sound670 : envelope670.Sound := by
  apply rat_majority_inputs_envelopes inputs670 inputs_valid670
  · norm_num [envelope670]
  · intro rho hr0 hr1
    have hh := Batch033.bound1340 rho hr0 hr1
    norm_num [Batch033.certificate1340,envelope670,inputs670,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1341 rho hr0 hr1
    norm_num [Batch033.certificate1341,envelope670,inputs670,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs671 : RatMajorityInputs := ⟨(2560976905293177306405760079/10000000000000000000000),(84441832076061/20000000000000),(1000011714386519253/1000000000000000000),(207332996872705653/1000000000000000000),(84441832076061/40000000000000),(121111241813522731/1000000000000000000),25⟩
theorem inputs_valid671 : inputs671.Valid := by decide +kernel
def envelope671 : RatMajorityEnvelope := ⟨335,1,inputs671,1,(549582372769416393/1000000000000000000)⟩
theorem envelope_sound671 : envelope671.Sound := by
  apply rat_majority_inputs_envelopes inputs671 inputs_valid671
  · norm_num [envelope671]
  · intro rho hr0 hr1
    have hh := Batch033.bound1342 rho hr0 hr1
    norm_num [Batch033.certificate1342,envelope671,inputs671,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1343 rho hr0 hr1
    norm_num [Batch033.certificate1343,envelope671,inputs671,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs672 : RatMajorityInputs := ⟨(11575880706772937325929465357/50000000000000000000000),(105849815908189/25000000000000),(1000012958107946833/1000000000000000000),(205781973580996613/1000000000000000000),(105849815908189/50000000000000),(60196353672640799/500000000000000000),25⟩
theorem inputs_valid672 : inputs672.Valid := by decide +kernel
def envelope672 : RatMajorityEnvelope := ⟨336,0,inputs672,(696292863/598577500),(69084582690088713/100000000000000000)⟩
theorem envelope_sound672 : envelope672.Sound := by
  apply rat_majority_inputs_envelopes inputs672 inputs_valid672
  · norm_num [envelope672]
  · intro rho hr0 hr1
    have hh := Batch033.bound1344 rho hr0 hr1
    norm_num [Batch033.certificate1344,envelope672,inputs672,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1345 rho hr0 hr1
    norm_num [Batch033.certificate1345,envelope672,inputs672,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs673 : RatMajorityInputs := ⟨(11575880706772937325929465357/50000000000000000000000),(422686636288509/100000000000000),(1000012958107946833/1000000000000000000),(41341909861764729/200000000000000000),(422686636288509/200000000000000),(60411224089901421/500000000000000000),25⟩
theorem inputs_valid673 : inputs673.Valid := by decide +kernel
def envelope673 : RatMajorityEnvelope := ⟨336,1,inputs673,1,(68687548660571411/125000000000000000)⟩
theorem envelope_sound673 : envelope673.Sound := by
  apply rat_majority_inputs_envelopes inputs673 inputs_valid673
  · norm_num [envelope673]
  · intro rho hr0 hr1
    have hh := Batch033.bound1346 rho hr0 hr1
    norm_num [Batch033.certificate1346,envelope673,inputs673,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1347 rho hr0 hr1
    norm_num [Batch033.certificate1347,envelope673,inputs673,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs674 : RatMajorityInputs := ⟨(2620381479457907499765875787/12500000000000000000000),(26115302385347/6250000000000),(1000014311052684239/1000000000000000000),(213104549985774973/1000000000000000000),(26115302385347/12500000000000),(123783130663936507/1000000000000000000),25⟩
theorem inputs_valid674 : inputs674.Valid := by decide +kernel
def envelope674 : RatMajorityEnvelope := ⟨337,0,inputs674,(1395083141/1196440000),(173527602768723659/250000000000000000)⟩
theorem envelope_sound674 : envelope674.Sound := by
  apply rat_majority_inputs_envelopes inputs674 inputs_valid674
  · norm_num [envelope674]
  · intro rho hr0 hr1
    have hh := Batch033.bound1348 rho hr0 hr1
    norm_num [Batch033.certificate1348,envelope674,inputs674,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1349 rho hr0 hr1
    norm_num [Batch033.certificate1349,envelope674,inputs674,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs675 : RatMajorityInputs := ⟨(2620381479457907499765875787/12500000000000000000000),(26397158942861/6250000000000),(1000014311052684239/1000000000000000000),(25892875308481783/125000000000000000),(26397158942861/12500000000000),(60511618201785201/500000000000000000),25⟩
theorem inputs_valid675 : inputs675.Valid := by decide +kernel
def envelope675 : RatMajorityEnvelope := ⟨337,1,inputs675,1,(54955829231321259/100000000000000000)⟩
theorem envelope_sound675 : envelope675.Sound := by
  apply rat_majority_inputs_envelopes inputs675 inputs_valid675
  · norm_num [envelope675]
  · intro rho hr0 hr1
    have hh := Batch033.bound1350 rho hr0 hr1
    norm_num [Batch033.certificate1350,envelope675,inputs675,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1351 rho hr0 hr1
    norm_num [Batch033.certificate1351,envelope675,inputs675,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs676 : RatMajorityInputs := ⟨(190769414222395083727149427/1000000000000000000000),(213565088841823/50000000000000),(250003931495918979/250000000000000000),(100491175837773257/500000000000000000),(213565088841823/100000000000000),(29541912846076683/250000000000000000),25⟩
theorem inputs_valid676 : inputs676.Valid := by decide +kernel
def envelope676 : RatMajorityEnvelope := ⟨338,0,inputs676,(2785750949/2391470000),(345895214216595203/500000000000000000)⟩
theorem envelope_sound676 : envelope676.Sound := by
  apply rat_majority_inputs_envelopes inputs676 inputs_valid676
  · norm_num [envelope676]
  · intro rho hr0 hr1
    have hh := Batch033.bound1352 rho hr0 hr1
    norm_num [Batch033.certificate1352,envelope676,inputs676,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1353 rho hr0 hr1
    norm_num [Batch033.certificate1353,envelope676,inputs676,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs677 : RatMajorityInputs := ⟨(190769414222395083727149427/1000000000000000000000),(26416279735769/6250000000000),(250003931495918979/250000000000000000),(206743666913987679/1000000000000000000),(26416279735769/12500000000000),(120838253101510261/1000000000000000000),25⟩
theorem inputs_valid677 : inputs677.Valid := by decide +kernel
def envelope677 : RatMajorityEnvelope := ⟨338,1,inputs677,1,(109901209391064981/200000000000000000)⟩
theorem envelope_sound677 : envelope677.Sound := by
  apply rat_majority_inputs_envelopes inputs677 inputs_valid677
  · norm_num [envelope677]
  · intro rho hr0 hr1
    have hh := Batch033.bound1354 rho hr0 hr1
    norm_num [Batch033.certificate1354,envelope677,inputs677,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1355 rho hr0 hr1
    norm_num [Batch033.certificate1355,envelope677,inputs677,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs678 : RatMajorityInputs := ⟨(17439844841669468568048452979/100000000000000000000000),(429152120443839/100000000000000),(31250537569314281/31250000000000000),(99210348128710779/500000000000000000),(429152120443839/200000000000000),(58489514344810427/500000000000000000),26⟩
theorem inputs_valid678 : inputs678.Valid := by decide +kernel
def envelope678 : RatMajorityEnvelope := ⟨339,0,inputs678,(92837703/79669000),(345951420466857503/500000000000000000)⟩
theorem envelope_sound678 : envelope678.Sound := by
  apply rat_majority_inputs_envelopes inputs678 inputs_valid678
  · norm_num [envelope678]
  · intro rho hr0 hr1
    have hh := Batch033.bound1356 rho hr0 hr1
    norm_num [Batch033.certificate1356,envelope678,inputs678,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1357 rho hr0 hr1
    norm_num [Batch033.certificate1357,envelope678,inputs678,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs679 : RatMajorityInputs := ⟨(17439844841669468568048452979/100000000000000000000000),(26408548108467/6250000000000),(31250537569314281/31250000000000000),(41381012715913441/200000000000000000),(26408548108467/12500000000000),(24182603665669167/200000000000000000),25⟩
theorem inputs_valid679 : inputs679.Valid := by decide +kernel
def envelope679 : RatMajorityEnvelope := ⟨339,1,inputs679,1,(274764002043578773/500000000000000000)⟩
theorem envelope_sound679 : envelope679.Sound := by
  apply rat_majority_inputs_envelopes inputs679 inputs_valid679
  · norm_num [envelope679]
  · intro rho hr0 hr1
    have hh := Batch033.bound1358 rho hr0 hr1
    norm_num [Batch033.certificate1358,envelope679,inputs679,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch033.bound1359 rho hr0 hr1
    norm_num [Batch033.certificate1359,envelope679,inputs679,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope660,envelope661,envelope662,envelope663,envelope664,envelope665,envelope666,envelope667,envelope668,envelope669,envelope670,envelope671,envelope672,envelope673,envelope674,envelope675,envelope676,envelope677,envelope678,envelope679]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound660
  · exact envelope_sound661
  · exact envelope_sound662
  · exact envelope_sound663
  · exact envelope_sound664
  · exact envelope_sound665
  · exact envelope_sound666
  · exact envelope_sound667
  · exact envelope_sound668
  · exact envelope_sound669
  · exact envelope_sound670
  · exact envelope_sound671
  · exact envelope_sound672
  · exact envelope_sound673
  · exact envelope_sound674
  · exact envelope_sound675
  · exact envelope_sound676
  · exact envelope_sound677
  · exact envelope_sound678
  · exact envelope_sound679

end Cycle12.MajorityCertificates.Inputs033
