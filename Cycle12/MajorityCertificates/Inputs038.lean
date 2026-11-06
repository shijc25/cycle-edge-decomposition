import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch038

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs038

def inputs760 : RatMajorityInputs := ⟨(8261874912002343390922723/625000000000000000000),(13840962371709/3125000000000),(500113493065233043/500000000000000000),(90855163724185037/500000000000000000),(13840962371709/6250000000000),(54601104907584451/500000000000000000),25⟩
theorem inputs_valid760 : inputs760.Valid := by decide +kernel
def envelope760 : RatMajorityEnvelope := ⟨380,0,inputs760,(2821610799/2322080000),(45957414987672143/62500000000000000)⟩
theorem envelope_sound760 : envelope760.Sound := by
  apply rat_majority_inputs_envelopes inputs760 inputs_valid760
  · norm_num [envelope760]
  · intro rho hr0 hr1
    have hh := Batch038.bound1520 rho hr0 hr1
    norm_num [Batch038.certificate1520,envelope760,inputs760,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1521 rho hr0 hr1
    norm_num [Batch038.certificate1521,envelope760,inputs760,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs761 : RatMajorityInputs := ⟨(8261874912002343390922723/625000000000000000000),(669352200823/156250000000),(500113493065233043/500000000000000000),(39877763433468363/200000000000000000),(669352200823/312500000000),(11742833543820643/100000000000000000),25⟩
theorem inputs_valid761 : inputs761.Valid := by decide +kernel
def envelope761 : RatMajorityEnvelope := ⟨380,1,inputs761,1,(548631109017869891/1000000000000000000)⟩
theorem envelope_sound761 : envelope761.Sound := by
  apply rat_majority_inputs_envelopes inputs761 inputs_valid761
  · norm_num [envelope761]
  · intro rho hr0 hr1
    have hh := Batch038.bound1522 rho hr0 hr1
    norm_num [Batch038.certificate1522,envelope761,inputs761,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1523 rho hr0 hr1
    norm_num [Batch038.certificate1523,envelope761,inputs761,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs762 : RatMajorityInputs := ⟨(255786087585600371808981231/20000000000000000000000),(88950010690247/20000000000000),(500117306904859123/500000000000000000),(89784909673668727/500000000000000000),(88950010690247/40000000000000),(108202558453177049/1000000000000000000),25⟩
theorem inputs_valid762 : inputs762.Valid := by decide +kernel
def envelope762 : RatMajorityEnvelope := ⟨381,0,inputs762,(2817707443/2320850000),(734188057070236127/1000000000000000000)⟩
theorem envelope_sound762 : envelope762.Sound := by
  apply rat_majority_inputs_envelopes inputs762 inputs_valid762
  · norm_num [envelope762]
  · intro rho hr0 hr1
    have hh := Batch038.bound1524 rho hr0 hr1
    norm_num [Batch038.certificate1524,envelope762,inputs762,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1525 rho hr0 hr1
    norm_num [Batch038.certificate1525,envelope762,inputs762,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs763 : RatMajorityInputs := ⟨(255786087585600371808981231/20000000000000000000000),(85837673788027/20000000000000),(500117306904859123/500000000000000000),(198375023575224939/1000000000000000000),(85837673788027/40000000000000),(116957829041376487/1000000000000000000),25⟩
theorem inputs_valid763 : inputs763.Valid := by decide +kernel
def envelope763 : RatMajorityEnvelope := ⟨381,1,inputs763,1,(137125767358237751/250000000000000000)⟩
theorem envelope_sound763 : envelope763.Sound := by
  apply rat_majority_inputs_envelopes inputs763 inputs_valid763
  · norm_num [envelope763]
  · intro rho hr0 hr1
    have hh := Batch038.bound1526 rho hr0 hr1
    norm_num [Batch038.certificate1526,envelope763,inputs763,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1527 rho hr0 hr1
    norm_num [Batch038.certificate1527,envelope763,inputs763,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs764 : RatMajorityInputs := ⟨(619313831767007255783601837/50000000000000000000000),(27839020573539/6250000000000),(250060562292602329/250000000000000000),(178790511989142889/1000000000000000000),(27839020573539/12500000000000),(4313535235815491/40000000000000000),25⟩
theorem inputs_valid764 : inputs764.Valid := by decide +kernel
def envelope764 : RatMajorityEnvelope := ⟨382,0,inputs764,(40232299/33138000),(367061265163526433/500000000000000000)⟩
theorem envelope_sound764 : envelope764.Sound := by
  apply rat_majority_inputs_envelopes inputs764 inputs_valid764
  · norm_num [envelope764]
  · intro rho hr0 hr1
    have hh := Batch038.bound1528 rho hr0 hr1
    norm_num [Batch038.certificate1528,envelope764,inputs764,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1529 rho hr0 hr1
    norm_num [Batch038.certificate1529,envelope764,inputs764,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs765 : RatMajorityInputs := ⟨(619313831767007255783601837/50000000000000000000000),(10745791198947/2500000000000),(250060562292602329/250000000000000000),(49391492242883687/250000000000000000),(10745791198947/5000000000000),(116582250782279739/1000000000000000000),25⟩
theorem inputs_valid765 : inputs765.Valid := by decide +kernel
def envelope765 : RatMajorityEnvelope := ⟨382,1,inputs765,1,(109680357882865819/200000000000000000)⟩
theorem envelope_sound765 : envelope765.Sound := by
  apply rat_majority_inputs_envelopes inputs765 inputs_valid765
  · norm_num [envelope765]
  · intro rho hr0 hr1
    have hh := Batch038.bound1530 rho hr0 hr1
    norm_num [Batch038.certificate1530,envelope765,inputs765,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1531 rho hr0 hr1
    norm_num [Batch038.certificate1531,envelope765,inputs765,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs766 : RatMajorityInputs := ⟨(24015568993440045050912513/2000000000000000000000),(4479273423407/1000000000000),(500124943242445549/500000000000000000),(3518456483643727/20000000000000000),(4479273423407/2000000000000),(106497186533918303/1000000000000000000),25⟩
theorem inputs_valid766 : inputs766.Valid := by decide +kernel
def envelope766 : RatMajorityEnvelope := ⟨383,0,inputs766,(351521181/289812500),(22900638659017973/31250000000000000)⟩
theorem envelope_sound766 : envelope766.Sound := by
  apply rat_majority_inputs_envelopes inputs766 inputs_valid766
  · norm_num [envelope766]
  · intro rho hr0 hr1
    have hh := Batch038.bound1532 rho hr0 hr1
    norm_num [Batch038.certificate1532,envelope766,inputs766,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1533 rho hr0 hr1
    norm_num [Batch038.certificate1533,envelope766,inputs766,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs767 : RatMajorityInputs := ⟨(24015568993440045050912513/2000000000000000000000),(430261939183/100000000000),(500124943242445549/500000000000000000),(98513170478746881/500000000000000000),(430261939183/200000000000),(1163316988071343/10000000000000000),25⟩
theorem inputs_valid767 : inputs767.Valid := by decide +kernel
def envelope767 : RatMajorityEnvelope := ⟨383,1,inputs767,1,(109667086049922687/200000000000000000)⟩
theorem envelope_sound767 : envelope767.Sound := by
  apply rat_majority_inputs_envelopes inputs767 inputs_valid767
  · norm_num [envelope767]
  · intro rho hr0 hr1
    have hh := Batch038.bound1534 rho hr0 hr1
    norm_num [Batch038.certificate1534,envelope767,inputs767,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1535 rho hr0 hr1
    norm_num [Batch038.certificate1535,envelope767,inputs767,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs768 : RatMajorityInputs := ⟨(1165195636532746747010571533/100000000000000000000000),(22489257123179/5000000000000),(1000257519061512781/1000000000000000000),(43454970977680189/250000000000000000),(22489257123179/10000000000000),(105512514492606989/1000000000000000000),25⟩
theorem inputs_valid768 : inputs768.Valid := by decide +kernel
def envelope768 : RatMajorityEnvelope := ⟨384,0,inputs768,(2808406063/2317370000),(73170055558265463/100000000000000000)⟩
theorem envelope_sound768 : envelope768.Sound := by
  apply rat_majority_inputs_envelopes inputs768 inputs_valid768
  · norm_num [envelope768]
  · intro rho hr0 hr1
    have hh := Batch038.bound1536 rho hr0 hr1
    norm_num [Batch038.certificate1536,envelope768,inputs768,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1537 rho hr0 hr1
    norm_num [Batch038.certificate1537,envelope768,inputs768,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs769 : RatMajorityInputs := ⟨(1165195636532746747010571533/100000000000000000000000),(215512689639357/50000000000000),(1000257519061512781/1000000000000000000),(24508995588266963/125000000000000000),(215512689639357/100000000000000),(115888483849124111/1000000000000000000),25⟩
theorem inputs_valid769 : inputs769.Valid := by decide +kernel
def envelope769 : RatMajorityEnvelope := ⟨384,1,inputs769,1,(68526980894587001/125000000000000000)⟩
theorem envelope_sound769 : envelope769.Sound := by
  apply rat_majority_inputs_envelopes inputs769 inputs_valid769
  · norm_num [envelope769]
  · intro rho hr0 hr1
    have hh := Batch038.bound1538 rho hr0 hr1
    norm_num [Batch038.certificate1538,envelope769,inputs769,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1539 rho hr0 hr1
    norm_num [Batch038.certificate1539,envelope769,inputs769,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs770 : RatMajorityInputs := ⟨(282928740680088388293645263/25000000000000000000000),(112903155071219/25000000000000),(1000265139080624063/1000000000000000000),(171772326994974683/1000000000000000000),(112903155071219/50000000000000),(104552796925880689/1000000000000000000),25⟩
theorem inputs_valid770 : inputs770.Valid := by decide +kernel
def envelope770 : RatMajorityEnvelope := ⟨385,0,inputs770,(701178153/579070000),(73059390099748883/100000000000000000)⟩
theorem envelope_sound770 : envelope770.Sound := by
  apply rat_majority_inputs_envelopes inputs770 inputs_valid770
  · norm_num [envelope770]
  · intro rho hr0 hr1
    have hh := Batch038.bound1540 rho hr0 hr1
    norm_num [Batch038.certificate1540,envelope770,inputs770,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1541 rho hr0 hr1
    norm_num [Batch038.certificate1541,envelope770,inputs770,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs771 : RatMajorityInputs := ⟨(282928740680088388293645263/25000000000000000000000),(53973619599167/12500000000000),(1000265139080624063/1000000000000000000),(195121315009498331/1000000000000000000),(53973619599167/25000000000000),(57723439091787331/500000000000000000),25⟩
theorem inputs_valid771 : inputs771.Valid := by decide +kernel
def envelope771 : RatMajorityEnvelope := ⟨385,1,inputs771,1,(27404852302362667/50000000000000000)⟩
theorem envelope_sound771 : envelope771.Sound := by
  apply rat_majority_inputs_envelopes inputs771 inputs_valid771
  · norm_num [envelope771]
  · intro rho hr0 hr1
    have hh := Batch038.bound1542 rho hr0 hr1
    norm_num [Batch038.certificate1542,envelope771,inputs771,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1543 rho hr0 hr1
    norm_num [Batch038.certificate1543,envelope771,inputs771,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs772 : RatMajorityInputs := ⟨(275044525657731992154636153/25000000000000000000000),(226746248573769/50000000000000),(200054548193195137/200000000000000000),(42421925388893067/250000000000000000),(226746248573769/100000000000000),(103574669107506219/1000000000000000000),25⟩
theorem inputs_valid772 : inputs772.Valid := by decide +kernel
def envelope772 : RatMajorityEnvelope := ⟨386,0,inputs772,(350130733/289402500),(364740092440520379/500000000000000000)⟩
theorem envelope_sound772 : envelope772.Sound := by
  apply rat_majority_inputs_envelopes inputs772 inputs_valid772
  · norm_num [envelope772]
  · intro rho hr0 hr1
    have hh := Batch038.bound1544 rho hr0 hr1
    norm_num [Batch038.certificate1544,envelope772,inputs772,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1545 rho hr0 hr1
    norm_num [Batch038.certificate1545,envelope772,inputs772,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs773 : RatMajorityInputs := ⟨(275044525657731992154636153/25000000000000000000000),(54065189576607/12500000000000),(200054548193195137/200000000000000000),(19421293725840617/100000000000000000),(54065189576607/25000000000000),(57512396470480311/500000000000000000),25⟩
theorem inputs_valid773 : inputs773.Valid := by decide +kernel
def envelope773 : RatMajorityEnvelope := ⟨386,1,inputs773,1,(68497993615825201/125000000000000000)⟩
theorem envelope_sound773 : envelope773.Sound := by
  apply rat_majority_inputs_envelopes inputs773 inputs_valid773
  · norm_num [envelope773]
  · intro rho hr0 hr1
    have hh := Batch038.bound1546 rho hr0 hr1
    norm_num [Batch038.certificate1546,envelope773,inputs773,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1547 rho hr0 hr1
    norm_num [Batch038.certificate1547,envelope773,inputs773,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs774 : RatMajorityInputs := ⟨(53522536822281658447353849/5000000000000000000000),(11394317668461/2500000000000),(200056063375154177/200000000000000000),(83594185605026253/500000000000000000),(11394317668461/5000000000000),(102400515348192627/1000000000000000000),26⟩
theorem inputs_valid774 : inputs774.Valid := by decide +kernel
def envelope774 : RatMajorityEnvelope := ⟨387,0,inputs774,(73563181/60900000),(36376682326941129/50000000000000000)⟩
theorem envelope_sound774 : envelope774.Sound := by
  apply rat_majority_inputs_envelopes inputs774 inputs_valid774
  · norm_num [envelope774]
  · intro rho hr0 hr1
    have hh := Batch038.bound1548 rho hr0 hr1
    norm_num [Batch038.certificate1548,envelope774,inputs774,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1549 rho hr0 hr1
    norm_num [Batch038.certificate1549,envelope774,inputs774,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs775 : RatMajorityInputs := ⟨(53522536822281658447353849/5000000000000000000000),(21652875859503/5000000000000),(200056063375154177/200000000000000000),(6048454884728279/31250000000000000),(21652875859503/10000000000000),(114716938873071499/1000000000000000000),25⟩
theorem inputs_valid775 : inputs775.Valid := by decide +kernel
def envelope775 : RatMajorityEnvelope := ⟨387,1,inputs775,1,(27395125649864349/50000000000000000)⟩
theorem envelope_sound775 : envelope775.Sound := by
  apply rat_majority_inputs_envelopes inputs775 inputs_valid775
  · norm_num [envelope775]
  · intro rho hr0 hr1
    have hh := Batch038.bound1550 rho hr0 hr1
    norm_num [Batch038.certificate1550,envelope775,inputs775,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1551 rho hr0 hr1
    norm_num [Batch038.certificate1551,envelope775,inputs775,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs776 : RatMajorityInputs := ⟨(42498175374403597999573893/4000000000000000000000),(9159552403387/2000000000000),(1000282427088531617/1000000000000000000),(164801796904340341/1000000000000000000),(9159552403387/4000000000000),(101277794119241103/1000000000000000000),26⟩
theorem inputs_valid776 : inputs776.Valid := by decide +kernel
def envelope776 : RatMajorityEnvelope := ⟨388,0,inputs776,(558545493/462850000),(726254236551053813/1000000000000000000)⟩
theorem envelope_sound776 : envelope776.Sound := by
  apply rat_majority_inputs_envelopes inputs776 inputs_valid776
  · norm_num [envelope776]
  · intro rho hr0 hr1
    have hh := Batch038.bound1552 rho hr0 hr1
    norm_num [Batch038.certificate1552,envelope776,inputs776,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1553 rho hr0 hr1
    norm_num [Batch038.certificate1553,envelope776,inputs776,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs777 : RatMajorityInputs := ⟨(42498175374403597999573893/4000000000000000000000),(8680952543587/2000000000000),(1000282427088531617/1000000000000000000),(192332008960915039/1000000000000000000),(8680952543587/4000000000000),(57075215179410047/500000000000000000),26⟩
theorem inputs_valid777 : inputs777.Valid := by decide +kernel
def envelope777 : RatMajorityEnvelope := ⟨388,1,inputs777,1,(547748093443011979/1000000000000000000)⟩
theorem envelope_sound777 : envelope777.Sound := by
  apply rat_majority_inputs_envelopes inputs777 inputs_valid777
  · norm_num [envelope777]
  · intro rho hr0 hr1
    have hh := Batch038.bound1554 rho hr0 hr1
    norm_num [Batch038.certificate1554,envelope777,inputs777,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1555 rho hr0 hr1
    norm_num [Batch038.certificate1555,envelope777,inputs777,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs778 : RatMajorityInputs := ⟨(32768186798093851689871697/3125000000000000000000),(28698127133233/6250000000000),(1000286164340885199/1000000000000000000),(163523430550716809/1000000000000000000),(28698127133233/12500000000000),(10067576529257717/100000000000000000),26⟩
theorem inputs_valid778 : inputs778.Valid := by decide +kernel
def envelope778 : RatMajorityEnvelope := ⟨389,0,inputs778,(2789931917/2313760000),(181319943311073437/250000000000000000)⟩
theorem envelope_sound778 : envelope778.Sound := by
  apply rat_majority_inputs_envelopes inputs778 inputs_valid778
  · norm_num [envelope778]
  · intro rho hr0 hr1
    have hh := Batch038.bound1556 rho hr0 hr1
    norm_num [Batch038.certificate1556,envelope778,inputs778,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1557 rho hr0 hr1
    norm_num [Batch038.certificate1557,envelope778,inputs778,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs779 : RatMajorityInputs := ⟨(32768186798093851689871697/3125000000000000000000),(27155020344707/6250000000000),(1000286164340885199/1000000000000000000),(191801517478560543/1000000000000000000),(27155020344707/12500000000000),(56951866905840801/500000000000000000),25⟩
theorem inputs_valid779 : inputs779.Valid := by decide +kernel
def envelope779 : RatMajorityEnvelope := ⟨389,1,inputs779,1,(10953644233276521/20000000000000000)⟩
theorem envelope_sound779 : envelope779.Sound := by
  apply rat_majority_inputs_envelopes inputs779 inputs_valid779
  · norm_num [envelope779]
  · intro rho hr0 hr1
    have hh := Batch038.bound1558 rho hr0 hr1
    norm_num [Batch038.certificate1558,envelope779,inputs779,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch038.bound1559 rho hr0 hr1
    norm_num [Batch038.certificate1559,envelope779,inputs779,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope760,envelope761,envelope762,envelope763,envelope764,envelope765,envelope766,envelope767,envelope768,envelope769,envelope770,envelope771,envelope772,envelope773,envelope774,envelope775,envelope776,envelope777,envelope778,envelope779]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound760
  · exact envelope_sound761
  · exact envelope_sound762
  · exact envelope_sound763
  · exact envelope_sound764
  · exact envelope_sound765
  · exact envelope_sound766
  · exact envelope_sound767
  · exact envelope_sound768
  · exact envelope_sound769
  · exact envelope_sound770
  · exact envelope_sound771
  · exact envelope_sound772
  · exact envelope_sound773
  · exact envelope_sound774
  · exact envelope_sound775
  · exact envelope_sound776
  · exact envelope_sound777
  · exact envelope_sound778
  · exact envelope_sound779

end Cycle12.MajorityCertificates.Inputs038
