import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch041

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs041

def inputs820 : RatMajorityInputs := ⟨(202193297112452521495451047/25000000000000000000000),(247517087838879/50000000000000),(8002968313767713/8000000000000000),(128897241927133637/1000000000000000000),(247517087838879/100000000000000),(42074304924912437/500000000000000000),26⟩
theorem inputs_valid820 : inputs820.Valid := by decide +kernel
def envelope820 : RatMajorityEnvelope := ⟨410,0,inputs820,(2686772999/2304620000),(686131379392823949/1000000000000000000)⟩
theorem envelope_sound820 : envelope820.Sound := by
  apply rat_majority_inputs_envelopes inputs820 inputs_valid820
  · norm_num [envelope820]
  · intro rho hr0 hr1
    have hh := Batch041.bound1640 rho hr0 hr1
    norm_num [Batch041.certificate1640,envelope820,inputs820,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1641 rho hr0 hr1
    norm_num [Batch041.certificate1641,envelope820,inputs820,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs821 : RatMajorityInputs := ⟨(202193297112452521495451047/25000000000000000000000),(112372512864789/25000000000000),(8002968313767713/8000000000000000),(87076233426851617/500000000000000000),(112372512864789/50000000000000),(26417077091793939/250000000000000000),26⟩
theorem inputs_valid821 : inputs821.Valid := by decide +kernel
def envelope821 : RatMajorityEnvelope := ⟨410,1,inputs821,1,(545525993874445773/1000000000000000000)⟩
theorem envelope_sound821 : envelope821.Sound := by
  apply rat_majority_inputs_envelopes inputs821 inputs_valid821
  · norm_num [envelope821]
  · intro rho hr0 hr1
    have hh := Batch041.bound1642 rho hr0 hr1
    norm_num [Batch041.certificate1642,envelope821,inputs821,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1643 rho hr0 hr1
    norm_num [Batch041.certificate1643,envelope821,inputs821,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs822 : RatMajorityInputs := ⟨(80175091079507312348023587/10000000000000000000000),(19877617642017/4000000000000),(500187144989929619/500000000000000000),(7953292368697297/62500000000000000),(19877617642017/8000000000000),(20837593029918411/250000000000000000),26⟩
theorem inputs_valid822 : inputs822.Valid := by decide +kernel
def envelope822 : RatMajorityEnvelope := ⟨411,0,inputs822,(53615853/46087000),(170943213506755231/250000000000000000)⟩
theorem envelope_sound822 : envelope822.Sound := by
  apply rat_majority_inputs_envelopes inputs822 inputs_valid822
  · norm_num [envelope822]
  · intro rho hr0 hr1
    have hh := Batch041.bound1644 rho hr0 hr1
    norm_num [Batch041.certificate1644,envelope822,inputs822,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1645 rho hr0 hr1
    norm_num [Batch041.certificate1645,envelope822,inputs822,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs823 : RatMajorityInputs := ⟨(80175091079507312348023587/10000000000000000000000),(90119220921531/20000000000000),(500187144989929619/500000000000000000),(86454345123738811/500000000000000000),(90119220921531/40000000000000),(105085547438001493/1000000000000000000),25⟩
theorem inputs_valid823 : inputs823.Valid := by decide +kernel
def envelope823 : RatMajorityEnvelope := ⟨411,1,inputs823,1,(272688304585618911/500000000000000000)⟩
theorem envelope_sound823 : envelope823.Sound := by
  apply rat_majority_inputs_envelopes inputs823 inputs_valid823
  · norm_num [envelope823]
  · intro rho hr0 hr1
    have hh := Batch041.bound1646 rho hr0 hr1
    norm_num [Batch041.certificate1646,envelope823,inputs823,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1647 rho hr0 hr1
    norm_num [Batch041.certificate1647,envelope823,inputs823,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs824 : RatMajorityInputs := ⟨(99363536320564226776550089/12500000000000000000000),(62301781827603/12500000000000),(1000377512837367319/1000000000000000000),(125993972390752963/1000000000000000000),(62301781827603/25000000000000),(82738415117634131/1000000000000000000),26⟩
theorem inputs_valid824 : inputs824.Valid := by decide +kernel
def envelope824 : RatMajorityEnvelope := ⟨412,0,inputs824,(2676688059/2304080000),(85272858580480353/125000000000000000)⟩
theorem envelope_sound824 : envelope824.Sound := by
  apply rat_majority_inputs_envelopes inputs824 inputs_valid824
  · norm_num [envelope824]
  · intro rho hr0 hr1
    have hh := Batch041.bound1648 rho hr0 hr1
    norm_num [Batch041.certificate1648,envelope824,inputs824,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1649 rho hr0 hr1
    norm_num [Batch041.certificate1649,envelope824,inputs824,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs825 : RatMajorityInputs := ⟨(99363536320564226776550089/12500000000000000000000),(28199897583513/6250000000000),(1000377512837367319/1000000000000000000),(10764665691655389/62500000000000000),(28199897583513/12500000000000),(104769581018925903/1000000000000000000),26⟩
theorem inputs_valid825 : inputs825.Valid := by decide +kernel
def envelope825 : RatMajorityEnvelope := ⟨412,1,inputs825,1,(272648244052371069/500000000000000000)⟩
theorem envelope_sound825 : envelope825.Sound := by
  apply rat_majority_inputs_envelopes inputs825 inputs_valid825
  · norm_num [envelope825]
  · intro rho hr0 hr1
    have hh := Batch041.bound1650 rho hr0 hr1
    norm_num [Batch041.certificate1650,envelope825,inputs825,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1651 rho hr0 hr1
    norm_num [Batch041.certificate1651,envelope825,inputs825,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs826 : RatMajorityInputs := ⟨(197061019224932714326120233/25000000000000000000000),(250139228685111/50000000000000),(200076141093329641/200000000000000000),(124417686441850143/1000000000000000000),(250139228685111/100000000000000),(81970792282084097/1000000000000000000),26⟩
theorem inputs_valid826 : inputs826.Valid := by decide +kernel
def envelope826 : RatMajorityEnvelope := ⟨413,0,inputs826,(2670779983/2303820000),(169963661889119303/250000000000000000)⟩
theorem envelope_sound826 : envelope826.Sound := by
  apply rat_majority_inputs_envelopes inputs826 inputs_valid826
  · norm_num [envelope826]
  · intro rho hr0 hr1
    have hh := Batch041.bound1652 rho hr0 hr1
    norm_num [Batch041.certificate1652,envelope826,inputs826,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1653 rho hr0 hr1
    norm_num [Batch041.certificate1653,envelope826,inputs826,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs827 : RatMajorityInputs := ⟨(197061019224932714326120233/25000000000000000000000),(226157122529541/50000000000000),(200076141093329641/200000000000000000),(10686982834835769/62500000000000000),(226157122529541/100000000000000),(26046663843417089/250000000000000000),26⟩
theorem inputs_valid827 : inputs827.Valid := by decide +kernel
def envelope827 : RatMajorityEnvelope := ⟨413,1,inputs827,1,(545147921424790823/1000000000000000000)⟩
theorem envelope_sound827 : envelope827.Sound := by
  apply rat_majority_inputs_envelopes inputs827 inputs_valid827
  · norm_num [envelope827]
  · intro rho hr0 hr1
    have hh := Batch041.bound1654 rho hr0 hr1
    norm_num [Batch041.certificate1654,envelope827,inputs827,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1655 rho hr0 hr1
    norm_num [Batch041.certificate1655,envelope827,inputs827,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs828 : RatMajorityInputs := ⟨(390876844295027582324739249/50000000000000000000000),(251070238652787/50000000000000),(1000383867158161091/1000000000000000000),(122860754713111963/1000000000000000000),(251070238652787/100000000000000),(20302794391631693/250000000000000000),26⟩
theorem inputs_valid828 : inputs828.Valid := by decide +kernel
def envelope828 : RatMajorityEnvelope := ⟨414,0,inputs828,(666228057/575892500),(169384968675581609/250000000000000000)⟩
theorem envelope_sound828 : envelope828.Sound := by
  apply rat_majority_inputs_envelopes inputs828 inputs_valid828
  · norm_num [envelope828]
  · intro rho hr0 hr1
    have hh := Batch041.bound1656 rho hr0 hr1
    norm_num [Batch041.certificate1656,envelope828,inputs828,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1657 rho hr0 hr1
    norm_num [Batch041.certificate1657,envelope828,inputs828,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs829 : RatMajorityInputs := ⟨(390876844295027582324739249/50000000000000000000000),(90627298113061/20000000000000),(1000383867158161091/1000000000000000000),(85040402775948797/500000000000000000),(90627298113061/40000000000000),(103759199613743709/1000000000000000000),26⟩
theorem inputs_valid829 : inputs829.Valid := by decide +kernel
def envelope829 : RatMajorityEnvelope := ⟨414,1,inputs829,1,(109007939969523513/200000000000000000)⟩
theorem envelope_sound829 : envelope829.Sound := by
  apply rat_majority_inputs_envelopes inputs829 inputs_valid829
  · norm_num [envelope829]
  · intro rho hr0 hr1
    have hh := Batch041.bound1658 rho hr0 hr1
    norm_num [Batch041.certificate1658,envelope829,inputs829,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1659 rho hr0 hr1
    norm_num [Batch041.certificate1659,envelope829,inputs829,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs830 : RatMajorityInputs := ⟨(122480781994337090266814647/20000000000000000000),(10824909951/2500000000),(500000244936478539/500000000000000000),(38725197987909553/200000000000000000),(10824909951/5000000000),(28688000309815179/250000000000000000),26⟩
theorem inputs_valid830 : inputs830.Valid := by decide +kernel
def envelope830 : RatMajorityEnvelope := ⟨415,0,inputs830,(1358871991/1175000000),(341770857457144327/500000000000000000)⟩
theorem envelope_sound830 : envelope830.Sound := by
  apply rat_majority_inputs_envelopes inputs830 inputs_valid830
  · norm_num [envelope830]
  · intro rho hr0 hr1
    have hh := Batch041.bound1660 rho hr0 hr1
    norm_num [Batch041.certificate1660,envelope830,inputs830,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1661 rho hr0 hr1
    norm_num [Batch041.certificate1661,envelope830,inputs830,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs831 : RatMajorityInputs := ⟨(122480781994337090266814647/20000000000000000000),(76165986723/20000000000),(500000244936478539/500000000000000000),(133779413815567209/500000000000000000),(76165986723/40000000000),(37237311271438669/250000000000000000),24⟩
theorem inputs_valid831 : inputs831.Valid := by decide +kernel
def envelope831 : RatMajorityEnvelope := ⟨415,1,inputs831,1,(279109595106483531/500000000000000000)⟩
theorem envelope_sound831 : envelope831.Sound := by
  apply rat_majority_inputs_envelopes inputs831 inputs_valid831
  · norm_num [envelope831]
  · intro rho hr0 hr1
    have hh := Batch041.bound1662 rho hr0 hr1
    norm_num [Batch041.certificate1662,envelope831,inputs831,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1663 rho hr0 hr1
    norm_num [Batch041.certificate1663,envelope831,inputs831,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs832 : RatMajorityInputs := ⟨(122480781994337090266814647/20000000000000000000),(41446716457/10000000000),(500000244936478539/500000000000000000),(217662406431639107/1000000000000000000),(41446716457/20000000000),(125891378044043443/1000000000000000000),25⟩
theorem inputs_valid832 : inputs832.Valid := by decide +kernel
def envelope832 : RatMajorityEnvelope := ⟨415,2,inputs832,1,(550964254222862693/1000000000000000000)⟩
theorem envelope_sound832 : envelope832.Sound := by
  apply rat_majority_inputs_envelopes inputs832 inputs_valid832
  · norm_num [envelope832]
  · intro rho hr0 hr1
    have hh := Batch041.bound1664 rho hr0 hr1
    norm_num [Batch041.certificate1664,envelope832,inputs832,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1665 rho hr0 hr1
    norm_num [Batch041.certificate1665,envelope832,inputs832,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs833 : RatMajorityInputs := ⟨(9871622232566145293387521/2500000000000000000),(41940015673/10000000000),(1000000759753995363/1000000000000000000),(8441303712075763/40000000000000000),(41940015673/20000000000),(3838257902870999/31250000000000000),25⟩
theorem inputs_valid833 : inputs833.Valid := by decide +kernel
def envelope833 : RatMajorityEnvelope := ⟨416,0,inputs833,(2724323161/2350000000),(137575640479015793/200000000000000000)⟩
theorem envelope_sound833 : envelope833.Sound := by
  apply rat_majority_inputs_envelopes inputs833 inputs_valid833
  · norm_num [envelope833]
  · intro rho hr0 hr1
    have hh := Batch041.bound1666 rho hr0 hr1
    norm_num [Batch041.certificate1666,envelope833,inputs833,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1667 rho hr0 hr1
    norm_num [Batch041.certificate1667,envelope833,inputs833,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs834 : RatMajorityInputs := ⟨(9871622232566145293387521/2500000000000000000),(76163356039/20000000000),(1000000759753995363/1000000000000000000),(267579989841205079/1000000000000000000),(76163356039/40000000000),(29791808273556831/200000000000000000),24⟩
theorem inputs_valid834 : inputs834.Valid := by decide +kernel
def envelope834 : RatMajorityEnvelope := ⟨416,1,inputs834,1,(139555644721170947/250000000000000000)⟩
theorem envelope_sound834 : envelope834.Sound := by
  apply rat_majority_inputs_envelopes inputs834 inputs_valid834
  · norm_num [envelope834]
  · intro rho hr0 hr1
    have hh := Batch041.bound1668 rho hr0 hr1
    norm_num [Batch041.certificate1668,envelope834,inputs834,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1669 rho hr0 hr1
    norm_num [Batch041.certificate1669,envelope834,inputs834,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs835 : RatMajorityInputs := ⟨(9871622232566145293387521/2500000000000000000),(1661273327/400000000),(1000000759753995363/1000000000000000000),(43301258598356199/200000000000000000),(1661273327/800000000),(12535674346333187/100000000000000000),25⟩
theorem inputs_valid835 : inputs835.Valid := by decide +kernel
def envelope835 : RatMajorityEnvelope := ⟨416,2,inputs835,1,(27540366045816357/50000000000000000)⟩
theorem envelope_sound835 : envelope835.Sound := by
  apply rat_majority_inputs_envelopes inputs835 inputs_valid835
  · norm_num [envelope835]
  · intro rho hr0 hr1
    have hh := Batch041.bound1670 rho hr0 hr1
    norm_num [Batch041.certificate1670,envelope835,inputs835,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1671 rho hr0 hr1
    norm_num [Batch041.certificate1671,envelope835,inputs835,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs836 : RatMajorityInputs := ⟨(27627360531140696425365931/10000000000000000000),(21611366617/5000000000),(1000001085880980321/1000000000000000000),(194577297693151639/1000000000000000000),(21611366617/10000000000),(23038821972345887/200000000000000000),25⟩
theorem inputs_valid836 : inputs836.Valid := by decide +kernel
def envelope836 : RatMajorityEnvelope := ⟨417,0,inputs836,(543617967/470000000),(683771626459146931/1000000000000000000)⟩
theorem envelope_sound836 : envelope836.Sound := by
  apply rat_majority_inputs_envelopes inputs836 inputs_valid836
  · norm_num [envelope836]
  · intro rho hr0 hr1
    have hh := Batch041.bound1672 rho hr0 hr1
    norm_num [Batch041.certificate1672,envelope836,inputs836,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1673 rho hr0 hr1
    norm_num [Batch041.certificate1673,envelope836,inputs836,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs837 : RatMajorityInputs := ⟨(27627360531140696425365931/10000000000000000000),(76479151389/20000000000),(1000001085880980321/1000000000000000000),(26504904794505323/100000000000000000),(76479151389/40000000000),(147787657108231561/1000000000000000000),24⟩
theorem inputs_valid837 : inputs837.Valid := by decide +kernel
def envelope837 : RatMajorityEnvelope := ⟨417,1,inputs837,1,(139457742685636083/250000000000000000)⟩
theorem envelope_sound837 : envelope837.Sound := by
  apply rat_majority_inputs_envelopes inputs837 inputs_valid837
  · norm_num [envelope837]
  · intro rho hr0 hr1
    have hh := Batch041.bound1674 rho hr0 hr1
    norm_num [Batch041.certificate1674,envelope837,inputs837,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1675 rho hr0 hr1
    norm_num [Batch041.certificate1675,envelope837,inputs837,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs838 : RatMajorityInputs := ⟨(27627360531140696425365931/10000000000000000000),(83486822061/20000000000),(1000001085880980321/1000000000000000000),(106827261958918637/500000000000000000),(83486822061/40000000000),(31009399442119257/250000000000000000),25⟩
theorem inputs_valid838 : inputs838.Valid := by decide +kernel
def envelope838 : RatMajorityEnvelope := ⟨417,2,inputs838,1,(137605523328880797/250000000000000000)⟩
theorem envelope_sound838 : envelope838.Sound := by
  apply rat_majority_inputs_envelopes inputs838 inputs_valid838
  · norm_num [envelope838]
  · intro rho hr0 hr1
    have hh := Batch041.bound1676 rho hr0 hr1
    norm_num [Batch041.certificate1676,envelope838,inputs838,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1677 rho hr0 hr1
    norm_num [Batch041.certificate1677,envelope838,inputs838,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs839 : RatMajorityInputs := ⟨(4090272384602219964958459/2000000000000000000),(10453953333/2500000000),(250000366724161703/250000000000000000),(53171457913677083/250000000000000000),(10453953333/5000000000),(123589379181860381/1000000000000000000),25⟩
theorem inputs_valid839 : inputs839.Valid := by decide +kernel
def envelope839 : RatMajorityEnvelope := ⟨418,0,inputs839,(2724926479/2350000000),(137657358609302933/200000000000000000)⟩
theorem envelope_sound839 : envelope839.Sound := by
  apply rat_majority_inputs_envelopes inputs839 inputs_valid839
  · norm_num [envelope839]
  · intro rho hr0 hr1
    have hh := Batch041.bound1678 rho hr0 hr1
    norm_num [Batch041.certificate1678,envelope839,inputs839,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch041.bound1679 rho hr0 hr1
    norm_num [Batch041.certificate1679,envelope839,inputs839,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope820,envelope821,envelope822,envelope823,envelope824,envelope825,envelope826,envelope827,envelope828,envelope829,envelope830,envelope831,envelope832,envelope833,envelope834,envelope835,envelope836,envelope837,envelope838,envelope839]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound820
  · exact envelope_sound821
  · exact envelope_sound822
  · exact envelope_sound823
  · exact envelope_sound824
  · exact envelope_sound825
  · exact envelope_sound826
  · exact envelope_sound827
  · exact envelope_sound828
  · exact envelope_sound829
  · exact envelope_sound830
  · exact envelope_sound831
  · exact envelope_sound832
  · exact envelope_sound833
  · exact envelope_sound834
  · exact envelope_sound835
  · exact envelope_sound836
  · exact envelope_sound837
  · exact envelope_sound838
  · exact envelope_sound839

end Cycle12.MajorityCertificates.Inputs041
