import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch036

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs036

def inputs720 : RatMajorityInputs := ⟨(866593063484038642779517179/25000000000000000000000),(42889909607559/10000000000000),(1000086551637646667/1000000000000000000),(198739750308098759/1000000000000000000),(42889909607559/20000000000000),(11712711506768793/100000000000000000),25⟩
theorem inputs_valid720 : inputs720.Valid := by decide +kernel
def envelope720 : RatMajorityEnvelope := ⟨360,0,inputs720,(281296267/235434000),(359221047454486463/500000000000000000)⟩
theorem envelope_sound720 : envelope720.Sound := by
  apply rat_majority_inputs_envelopes inputs720 inputs_valid720
  · norm_num [envelope720]
  · intro rho hr0 hr1
    have hh := Batch036.bound1440 rho hr0 hr1
    norm_num [Batch036.certificate1440,envelope720,inputs720,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1441 rho hr0 hr1
    norm_num [Batch036.certificate1441,envelope720,inputs720,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs721 : RatMajorityInputs := ⟨(866593063484038642779517179/25000000000000000000000),(211383642439857/50000000000000),(1000086551637646667/1000000000000000000),(206604399903116501/1000000000000000000),(211383642439857/100000000000000),(6038686860024217/50000000000000000),25⟩
theorem inputs_valid721 : inputs721.Valid := by decide +kernel
def envelope721 : RatMajorityEnvelope := ⟨360,1,inputs721,1,(549516977321384721/1000000000000000000)⟩
theorem envelope_sound721 : envelope721.Sound := by
  apply rat_majority_inputs_envelopes inputs721 inputs_valid721
  · norm_num [envelope721]
  · intro rho hr0 hr1
    have hh := Batch036.bound1442 rho hr0 hr1
    norm_num [Batch036.certificate1442,envelope721,inputs721,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1443 rho hr0 hr1
    norm_num [Batch036.certificate1443,envelope721,inputs721,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs722 : RatMajorityInputs := ⟨(809991711559892647401443049/25000000000000000000000),(21489805236123/5000000000000),(1000092600208837503/1000000000000000000),(197610599279146897/1000000000000000000),(21489805236123/10000000000000),(23320594235065293/200000000000000000),25⟩
theorem inputs_valid722 : inputs722.Valid := by decide +kernel
def envelope722 : RatMajorityEnvelope := ⟨361,0,inputs722,(234521553/196030000),(359868833976674227/500000000000000000)⟩
theorem envelope_sound722 : envelope722.Sound := by
  apply rat_majority_inputs_envelopes inputs722 inputs_valid722
  · norm_num [envelope722]
  · intro rho hr0 hr1
    have hh := Batch036.bound1444 rho hr0 hr1
    norm_num [Batch036.certificate1444,envelope722,inputs722,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1445 rho hr0 hr1
    norm_num [Batch036.certificate1445,envelope722,inputs722,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs723 : RatMajorityInputs := ⟨(809991711559892647401443049/25000000000000000000000),(26432429047599/6250000000000),(1000092600208837503/1000000000000000000),(206406891362980831/1000000000000000000),(26432429047599/12500000000000),(60341118767273179/500000000000000000),25⟩
theorem inputs_valid723 : inputs723.Valid := by decide +kernel
def envelope723 : RatMajorityEnvelope := ⟨361,1,inputs723,1,(274746695825131817/500000000000000000)⟩
theorem envelope_sound723 : envelope723.Sound := by
  apply rat_majority_inputs_envelopes inputs723 inputs_valid723
  · norm_num [envelope723]
  · intro rho hr0 hr1
    have hh := Batch036.bound1446 rho hr0 hr1
    norm_num [Batch036.certificate1446,envelope723,inputs723,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1447 rho hr0 hr1
    norm_num [Batch036.certificate1447,envelope723,inputs723,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs724 : RatMajorityInputs := ⟨(189808975634396035182126863/6250000000000000000000),(215027689395959/50000000000000),(500049395558434681/500000000000000000),(197285233228397459/1000000000000000000),(215027689395959/100000000000000),(1455648855985563/12500000000000000),26⟩
theorem inputs_valid724 : inputs724.Valid := by decide +kernel
def envelope724 : RatMajorityEnvelope := ⟨362,0,inputs724,(1407962177/1175210000),(360619564912762473/500000000000000000)⟩
theorem envelope_sound724 : envelope724.Sound := by
  apply rat_majority_inputs_envelopes inputs724 inputs_valid724
  · norm_num [envelope724]
  · intro rho hr0 hr1
    have hh := Batch036.bound1448 rho hr0 hr1
    norm_num [Batch036.certificate1448,envelope724,inputs724,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1449 rho hr0 hr1
    norm_num [Batch036.certificate1449,envelope724,inputs724,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs725 : RatMajorityInputs := ⟨(189808975634396035182126863/6250000000000000000000),(105765824357909/25000000000000),(500049395558434681/500000000000000000),(206218842398254509/1000000000000000000),(105765824357909/50000000000000),(120595116707092123/1000000000000000000),25⟩
theorem inputs_valid725 : inputs725.Valid := by decide +kernel
def envelope725 : RatMajorityEnvelope := ⟨362,1,inputs725,1,(274735564181589867/500000000000000000)⟩
theorem envelope_sound725 : envelope725.Sound := by
  apply rat_majority_inputs_envelopes inputs725 inputs_valid725
  · norm_num [envelope725]
  · intro rho hr0 hr1
    have hh := Batch036.bound1450 rho hr0 hr1
    norm_num [Batch036.certificate1450,envelope725,inputs725,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1451 rho hr0 hr1
    norm_num [Batch036.certificate1451,envelope725,inputs725,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs726 : RatMajorityInputs := ⟨(713543665953084697225168551/25000000000000000000000),(107579747290809/25000000000000),(50005255889401657/50000000000000000),(24619360979524737/125000000000000000),(107579747290809/50000000000000),(14537314991738199/125000000000000000),25⟩
theorem inputs_valid726 : inputs726.Valid := by decide +kernel
def envelope726 : RatMajorityEnvelope := ⟨363,0,inputs726,(939212797/782840000),(722743840430748537/1000000000000000000)⟩
theorem envelope_sound726 : envelope726.Sound := by
  apply rat_majority_inputs_envelopes inputs726 inputs_valid726
  · norm_num [envelope726]
  · intro rho hr0 hr1
    have hh := Batch036.bound1452 rho hr0 hr1
    norm_num [Batch036.certificate1452,envelope726,inputs726,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1453 rho hr0 hr1
    norm_num [Batch036.certificate1453,envelope726,inputs726,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs727 : RatMajorityInputs := ⟨(713543665953084697225168551/25000000000000000000000),(52901468013897/12500000000000),(50005255889401657/50000000000000000),(51506429108029753/250000000000000000),(52901468013897/25000000000000),(120505640194208471/1000000000000000000),25⟩
theorem inputs_valid727 : inputs727.Valid := by decide +kernel
def envelope727 : RatMajorityEnvelope := ⟨363,1,inputs727,1,(274724132485973399/500000000000000000)⟩
theorem envelope_sound727 : envelope727.Sound := by
  apply rat_majority_inputs_envelopes inputs727 inputs_valid727
  · norm_num [envelope727]
  · intro rho hr0 hr1
    have hh := Batch036.bound1454 rho hr0 hr1
    norm_num [Batch036.certificate1454,envelope727,inputs727,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1455 rho hr0 hr1
    norm_num [Batch036.certificate1455,envelope727,inputs727,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs728 : RatMajorityInputs := ⟨(1344520462717333861676843211/50000000000000000000000),(215293298438907/50000000000000),(1000111573621220377/1000000000000000000),(98310004774576379/500000000000000000),(215293298438907/100000000000000),(116143012089212389/1000000000000000000),25⟩
theorem inputs_valid728 : inputs728.Valid := by decide +kernel
def envelope728 : RatMajorityEnvelope := ⟨364,0,inputs728,(31326677/26074000),(724251846865722307/1000000000000000000)⟩
theorem envelope_sound728 : envelope728.Sound := by
  apply rat_majority_inputs_envelopes inputs728 inputs_valid728
  · norm_num [envelope728]
  · intro rho hr0 hr1
    have hh := Batch036.bound1456 rho hr0 hr1
    norm_num [Batch036.certificate1456,envelope728,inputs728,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1457 rho hr0 hr1
    norm_num [Batch036.certificate1457,envelope728,inputs728,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs729 : RatMajorityInputs := ⟨(1344520462717333861676843211/50000000000000000000000),(13229773412643/3125000000000),(1000111573621220377/1000000000000000000),(20584241178382861/100000000000000000),(13229773412643/6250000000000),(24084142118247769/200000000000000000),25⟩
theorem inputs_valid729 : inputs729.Valid := by decide +kernel
def envelope729 : RatMajorityEnvelope := ⟨364,1,inputs729,1,(274713382188100971/500000000000000000)⟩
theorem envelope_sound729 : envelope729.Sound := by
  apply rat_majority_inputs_envelopes inputs729 inputs_valid729
  · norm_num [envelope729]
  · intro rho hr0 hr1
    have hh := Batch036.bound1458 rho hr0 hr1
    norm_num [Batch036.certificate1458,envelope729,inputs729,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1459 rho hr0 hr1
    norm_num [Batch036.certificate1459,envelope729,inputs729,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs730 : RatMajorityInputs := ⟨(634833935076509802402335071/25000000000000000000000),(5385776412783/1250000000000),(500059075994526523/500000000000000000),(19627573585896547/100000000000000000),(5385776412783/2500000000000),(115983125867889221/1000000000000000000),25⟩
theorem inputs_valid730 : inputs730.Valid := by decide +kernel
def envelope730 : RatMajorityEnvelope := ⟨365,0,inputs730,(176325627/146552500),(72576186643951849/100000000000000000)⟩
theorem envelope_sound730 : envelope730.Sound := by
  apply rat_majority_inputs_envelopes inputs730 inputs_valid730
  · norm_num [envelope730]
  · intro rho hr0 hr1
    have hh := Batch036.bound1460 rho hr0 hr1
    norm_num [Batch036.certificate1460,envelope730,inputs730,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1461 rho hr0 hr1
    norm_num [Batch036.certificate1461,envelope730,inputs730,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs731 : RatMajorityInputs := ⟨(634833935076509802402335071/25000000000000000000000),(52937719784619/12500000000000),(500059075994526523/500000000000000000),(102824425106067147/500000000000000000),(52937719784619/25000000000000),(60165512556680927/500000000000000000),25⟩
theorem inputs_valid731 : inputs731.Valid := by decide +kernel
def envelope731 : RatMajorityEnvelope := ⟨365,1,inputs731,1,(549403975609073233/1000000000000000000)⟩
theorem envelope_sound731 : envelope731.Sound := by
  apply rat_majority_inputs_envelopes inputs731 inputs_valid731
  · norm_num [envelope731]
  · intro rho hr0 hr1
    have hh := Batch036.bound1462 rho hr0 hr1
    norm_num [Batch036.certificate1462,envelope731,inputs731,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1463 rho hr0 hr1
    norm_num [Batch036.certificate1463,envelope731,inputs731,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs732 : RatMajorityInputs := ⟨(150199323573466306337274153/6250000000000000000000),(107900818277247/25000000000000),(1000124846239075883/1000000000000000000),(195352131926076299/1000000000000000000),(107900818277247/50000000000000),(115554110962753931/1000000000000000000),26⟩
theorem inputs_valid732 : inputs732.Valid := by decide +kernel
def envelope732 : RatMajorityEnvelope := ⟨366,0,inputs732,(470161483/390510000),(363205061244378747/500000000000000000)⟩
theorem envelope_sound732 : envelope732.Sound := by
  apply rat_majority_inputs_envelopes inputs732 inputs_valid732
  · norm_num [envelope732]
  · intro rho hr0 hr1
    have hh := Batch036.bound1464 rho hr0 hr1
    norm_num [Batch036.certificate1464,envelope732,inputs732,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1465 rho hr0 hr1
    norm_num [Batch036.certificate1465,envelope732,inputs732,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs733 : RatMajorityInputs := ⟨(150199323573466306337274153/6250000000000000000000),(52971770088711/12500000000000),(1000124846239075883/1000000000000000000),(205295394941337057/1000000000000000000),(52971770088711/25000000000000),(7510452772156317/62500000000000000),25⟩
theorem inputs_valid733 : inputs733.Valid := by decide +kernel
def envelope733 : RatMajorityEnvelope := ⟨366,1,inputs733,1,(3433501196091067/6250000000000000)⟩
theorem envelope_sound733 : envelope733.Sound := by
  apply rat_majority_inputs_envelopes inputs733 inputs_valid733
  · norm_num [envelope733]
  · intro rho hr0 hr1
    have hh := Batch036.bound1466 rho hr0 hr1
    norm_num [Batch036.certificate1466,envelope733,inputs733,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1467 rho hr0 hr1
    norm_num [Batch036.certificate1467,envelope733,inputs733,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs734 : RatMajorityInputs := ⟨(569752018729724931186800181/25000000000000000000000),(107976454973613/25000000000000),(100013164969501747/100000000000000000),(97488082238626599/500000000000000000),(107976454973613/50000000000000),(23075888097389167/200000000000000000),25⟩
theorem inputs_valid734 : inputs734.Valid := by decide +kernel
def envelope734 : RatMajorityEnvelope := ⟨367,0,inputs734,(235238409/195110000),(727917967635511527/1000000000000000000)⟩
theorem envelope_sound734 : envelope734.Sound := by
  apply rat_majority_inputs_envelopes inputs734 inputs_valid734
  · norm_num [envelope734]
  · intro rho hr0 hr1
    have hh := Batch036.bound1468 rho hr0 hr1
    norm_num [Batch036.certificate1468,envelope734,inputs734,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1469 rho hr0 hr1
    norm_num [Batch036.certificate1469,envelope734,inputs734,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs735 : RatMajorityInputs := ⟨(569752018729724931186800181/25000000000000000000000),(105973339232943/25000000000000),(100013164969501747/100000000000000000),(205140891924505377/1000000000000000000),(105973339232943/50000000000000),(24019129656769323/200000000000000000),25⟩
theorem inputs_valid735 : inputs735.Valid := by decide +kernel
def envelope735 : RatMajorityEnvelope := ⟨367,1,inputs735,1,(109868535228122557/200000000000000000)⟩
theorem envelope_sound735 : envelope735.Sound := by
  apply rat_majority_inputs_envelopes inputs735 inputs_valid735
  · norm_num [envelope735]
  · intro rho hr0 hr1
    have hh := Batch036.bound1470 rho hr0 hr1
    norm_num [Batch036.certificate1470,envelope735,inputs735,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1471 rho hr0 hr1
    norm_num [Batch036.certificate1471,envelope735,inputs735,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs736 : RatMajorityInputs := ⟨(1082714099973713034690426639/50000000000000000000000),(21591162230401/5000000000000),(1000138555658126397/1000000000000000000),(195078718178474657/1000000000000000000),(21591162230401/10000000000000),(7214192985888927/62500000000000000),25⟩
theorem inputs_valid736 : inputs736.Valid := by decide +kernel
def envelope736 : RatMajorityEnvelope := ⟨368,0,inputs736,(1412496907/1169810000),(729549192487147443/1000000000000000000)⟩
theorem envelope_sound736 : envelope736.Sound := by
  apply rat_majority_inputs_envelopes inputs736 inputs_valid736
  · norm_num [envelope736]
  · intro rho hr0 hr1
    have hh := Batch036.bound1472 rho hr0 hr1
    norm_num [Batch036.certificate1472,envelope736,inputs736,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1473 rho hr0 hr1
    norm_num [Batch036.certificate1473,envelope736,inputs736,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs737 : RatMajorityInputs := ⟨(1082714099973713034690426639/50000000000000000000000),(106004321710019/25000000000000),(1000138555658126397/1000000000000000000),(102490178089110963/500000000000000000),(106004321710019/50000000000000),(120021254121983527/1000000000000000000),25⟩
theorem inputs_valid737 : inputs737.Valid := by decide +kernel
def envelope737 : RatMajorityEnvelope := ⟨368,1,inputs737,1,(274662209581518029/500000000000000000)⟩
theorem envelope_sound737 : envelope737.Sound := by
  apply rat_majority_inputs_envelopes inputs737 inputs_valid737
  · norm_num [envelope737]
  · intro rho hr0 hr1
    have hh := Batch036.bound1474 rho hr0 hr1
    norm_num [Batch036.certificate1474,envelope737,inputs737,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1475 rho hr0 hr1
    norm_num [Batch036.certificate1475,envelope737,inputs737,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs738 : RatMajorityInputs := ⟨(515318948705810596527927633/25000000000000000000000),(108238680526863/25000000000000),(500072778704294447/500000000000000000),(193677440857946207/1000000000000000000),(108238680526863/50000000000000),(114775915714136263/1000000000000000000),26⟩
theorem inputs_valid738 : inputs738.Valid := by decide +kernel
def envelope738 : RatMajorityEnvelope := ⟨369,0,inputs738,(23539133/19483000),(91260134781050699/125000000000000000)⟩
theorem envelope_sound738 : envelope738.Sound := by
  apply rat_majority_inputs_envelopes inputs738 inputs_valid738
  · norm_num [envelope738]
  · intro rho hr0 hr1
    have hh := Batch036.bound1476 rho hr0 hr1
    norm_num [Batch036.certificate1476,envelope738,inputs738,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1477 rho hr0 hr1
    norm_num [Batch036.certificate1477,envelope738,inputs738,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs739 : RatMajorityInputs := ⟨(515318948705810596527927633/25000000000000000000000),(106157680450053/25000000000000),(500072778704294447/500000000000000000),(25523409268967917/125000000000000000),(106157680450053/50000000000000),(5982684596634609/50000000000000000),25⟩
theorem inputs_valid739 : inputs739.Valid := by decide +kernel
def envelope739 : RatMajorityEnvelope := ⟨369,1,inputs739,1,(549223101652636269/1000000000000000000)⟩
theorem envelope_sound739 : envelope739.Sound := by
  apply rat_majority_inputs_envelopes inputs739 inputs_valid739
  · norm_num [envelope739]
  · intro rho hr0 hr1
    have hh := Batch036.bound1478 rho hr0 hr1
    norm_num [Batch036.certificate1478,envelope739,inputs739,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch036.bound1479 rho hr0 hr1
    norm_num [Batch036.certificate1479,envelope739,inputs739,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope720,envelope721,envelope722,envelope723,envelope724,envelope725,envelope726,envelope727,envelope728,envelope729,envelope730,envelope731,envelope732,envelope733,envelope734,envelope735,envelope736,envelope737,envelope738,envelope739]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound720
  · exact envelope_sound721
  · exact envelope_sound722
  · exact envelope_sound723
  · exact envelope_sound724
  · exact envelope_sound725
  · exact envelope_sound726
  · exact envelope_sound727
  · exact envelope_sound728
  · exact envelope_sound729
  · exact envelope_sound730
  · exact envelope_sound731
  · exact envelope_sound732
  · exact envelope_sound733
  · exact envelope_sound734
  · exact envelope_sound735
  · exact envelope_sound736
  · exact envelope_sound737
  · exact envelope_sound738
  · exact envelope_sound739

end Cycle12.MajorityCertificates.Inputs036
