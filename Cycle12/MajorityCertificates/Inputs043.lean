import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch043

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs043

def inputs860 : RatMajorityInputs := ⟨(10796861869659746441025763/20000000000000000000),(87783438921/20000000000),(1000005557194308863/1000000000000000000),(186432947125666301/1000000000000000000),(87783438921/40000000000),(55702338249519923/500000000000000000),26⟩
theorem inputs_valid860 : inputs860.Valid := by decide +kernel
def envelope860 : RatMajorityEnvelope := ⟨425,0,inputs860,(543034429/470000000),(852291105503603/1250000000000000)⟩
theorem envelope_sound860 : envelope860.Sound := by
  apply rat_majority_inputs_envelopes inputs860 inputs_valid860
  · norm_num [envelope860]
  · intro rho hr0 hr1
    have hh := Batch043.bound1720 rho hr0 hr1
    norm_num [Batch043.certificate1720,envelope860,inputs860,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1721 rho hr0 hr1
    norm_num [Batch043.certificate1721,envelope860,inputs860,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs861 : RatMajorityInputs := ⟨(10796861869659746441025763/20000000000000000000),(84038303517/20000000000),(1000005557194308863/1000000000000000000),(209984811004102459/1000000000000000000),(84038303517/40000000000),(122339221582750593/1000000000000000000),25⟩
theorem inputs_valid861 : inputs861.Valid := by decide +kernel
def envelope861 : RatMajorityEnvelope := ⟨425,1,inputs861,1,(549932231936935263/1000000000000000000)⟩
theorem envelope_sound861 : envelope861.Sound := by
  apply rat_majority_inputs_envelopes inputs861 inputs_valid861
  · norm_num [envelope861]
  · intro rho hr0 hr1
    have hh := Batch043.bound1722 rho hr0 hr1
    norm_num [Batch043.certificate1722,envelope861,inputs861,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1723 rho hr0 hr1
    norm_num [Batch043.certificate1723,envelope861,inputs861,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs862 : RatMajorityInputs := ⟨(10796861869659746441025763/20000000000000000000),(4086676931/1000000000),(1000005557194308863/1000000000000000000),(45135227187846177/200000000000000000),(4086676931/2000000000),(4049854322354109/31250000000000000),25⟩
theorem inputs_valid862 : inputs862.Valid := by decide +kernel
def envelope862 : RatMajorityEnvelope := ⟨425,2,inputs862,1,(552067991192576559/1000000000000000000)⟩
theorem envelope_sound862 : envelope862.Sound := by
  apply rat_majority_inputs_envelopes inputs862 inputs_valid862
  · norm_num [envelope862]
  · intro rho hr0 hr1
    have hh := Batch043.bound1724 rho hr0 hr1
    norm_num [Batch043.certificate1724,envelope862,inputs862,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1725 rho hr0 hr1
    norm_num [Batch043.certificate1725,envelope862,inputs862,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs863 : RatMajorityInputs := ⟨(1896151109422277454845777/4000000000000000000),(10934356783/2500000000),(250001582160172739/250000000000000000),(37657047946674983/200000000000000000),(10934356783/5000000000),(14033430566175301/125000000000000000),26⟩
theorem inputs_valid863 : inputs863.Valid := by decide +kernel
def envelope863 : RatMajorityEnvelope := ⟨426,0,inputs863,(543166431/470000000),(682271832786265391/1000000000000000000)⟩
theorem envelope_sound863 : envelope863.Sound := by
  apply rat_majority_inputs_envelopes inputs863 inputs_valid863
  · norm_num [envelope863]
  · intro rho hr0 hr1
    have hh := Batch043.bound1726 rho hr0 hr1
    norm_num [Batch043.certificate1726,envelope863,inputs863,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1727 rho hr0 hr1
    norm_num [Batch043.certificate1727,envelope863,inputs863,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs864 : RatMajorityInputs := ⟨(1896151109422277454845777/4000000000000000000),(41948688301/10000000000),(250001582160172739/250000000000000000),(42183510625607181/200000000000000000),(41948688301/20000000000),(61385501992584943/500000000000000000),25⟩
theorem inputs_valid864 : inputs864.Valid := by decide +kernel
def envelope864 : RatMajorityEnvelope := ⟨426,1,inputs864,1,(55005708164417749/100000000000000000)⟩
theorem envelope_sound864 : envelope864.Sound := by
  apply rat_majority_inputs_envelopes inputs864 inputs_valid864
  · norm_num [envelope864]
  · intro rho hr0 hr1
    have hh := Batch043.bound1728 rho hr0 hr1
    norm_num [Batch043.certificate1728,envelope864,inputs864,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1729 rho hr0 hr1
    norm_num [Batch043.certificate1729,envelope864,inputs864,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs865 : RatMajorityInputs := ⟨(1896151109422277454845777/4000000000000000000),(8203465117/2000000000),(250001582160172739/250000000000000000),(55893188627421417/250000000000000000),(8203465117/4000000000),(128623431502023877/1000000000000000000),25⟩
theorem inputs_valid865 : inputs865.Valid := by decide +kernel
def envelope865 : RatMajorityEnvelope := ⟨426,2,inputs865,1,(551776907104492493/1000000000000000000)⟩
theorem envelope_sound865 : envelope865.Sound := by
  apply rat_majority_inputs_envelopes inputs865 inputs_valid865
  · norm_num [envelope865]
  · intro rho hr0 hr1
    have hh := Batch043.bound1730 rho hr0 hr1
    norm_num [Batch043.certificate1730,envelope865,inputs865,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1731 rho hr0 hr1
    norm_num [Batch043.certificate1731,envelope865,inputs865,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs866 : RatMajorityInputs := ⟨(4200039081140962844733621/10000000000000000000),(5471713257/1250000000),(500003571415180477/500000000000000000),(23481038830596877/125000000000000000),(5471713257/2500000000),(3501999437994709/31250000000000000),25⟩
theorem inputs_valid866 : inputs866.Valid := by decide +kernel
def envelope866 : RatMajorityEnvelope := ⟨427,0,inputs866,(169729809/146875000),(682168924706227663/1000000000000000000)⟩
theorem envelope_sound866 : envelope866.Sound := by
  apply rat_majority_inputs_envelopes inputs866 inputs_valid866
  · norm_num [envelope866]
  · intro rho hr0 hr1
    have hh := Batch043.bound1732 rho hr0 hr1
    norm_num [Batch043.certificate1732,envelope866,inputs866,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1733 rho hr0 hr1
    norm_num [Batch043.certificate1733,envelope866,inputs866,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs867 : RatMajorityInputs := ⟨(4200039081140962844733621/10000000000000000000),(16826620823/4000000000),(500003571415180477/500000000000000000),(209359296148184169/1000000000000000000),(16826620823/8000000000),(61024809557637111/500000000000000000),25⟩
theorem inputs_valid867 : inputs867.Valid := by decide +kernel
def envelope867 : RatMajorityEnvelope := ⟨427,1,inputs867,1,(549849541365278761/1000000000000000000)⟩
theorem envelope_sound867 : envelope867.Sound := by
  apply rat_majority_inputs_envelopes inputs867 inputs_valid867
  · norm_num [envelope867]
  · intro rho hr0 hr1
    have hh := Batch043.bound1734 rho hr0 hr1
    norm_num [Batch043.certificate1734,envelope867,inputs867,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1735 rho hr0 hr1
    norm_num [Batch043.certificate1735,envelope867,inputs867,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs868 : RatMajorityInputs := ⟨(4200039081140962844733621/10000000000000000000),(1286552009/312500000),(500003571415180477/500000000000000000),(110730461621224243/500000000000000000),(1286552009/625000000),(63823718463966759/500000000000000000),25⟩
theorem inputs_valid868 : inputs868.Valid := by decide +kernel
def envelope868 : RatMajorityEnvelope := ⟨427,2,inputs868,1,(551486281036359801/1000000000000000000)⟩
theorem envelope_sound868 : envelope868.Sound := by
  apply rat_majority_inputs_envelopes inputs868 inputs_valid868
  · norm_num [envelope868]
  · intro rho hr0 hr1
    have hh := Batch043.bound1736 rho hr0 hr1
    norm_num [Batch043.certificate1736,envelope868,inputs868,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1737 rho hr0 hr1
    norm_num [Batch043.certificate1737,envelope868,inputs868,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs869 : RatMajorityInputs := ⟨(1875381561845680492167159/5000000000000000000),(21953387497/5000000000),(100000799842209183/100000000000000000),(46563258771725197/250000000000000000),(21953387497/10000000000),(13915105651770267/125000000000000000),25⟩
theorem inputs_valid869 : inputs869.Valid := by decide +kernel
def envelope869 : RatMajorityEnvelope := ⟨428,0,inputs869,(2715113393/2350000000),(340896844657473063/500000000000000000)⟩
theorem envelope_sound869 : envelope869.Sound := by
  apply rat_majority_inputs_envelopes inputs869 inputs_valid869
  · norm_num [envelope869]
  · intro rho hr0 hr1
    have hh := Batch043.bound1738 rho hr0 hr1
    norm_num [Batch043.certificate1738,envelope869,inputs869,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1739 rho hr0 hr1
    norm_num [Batch043.certificate1739,envelope869,inputs869,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs870 : RatMajorityInputs := ⟨(1875381561845680492167159/5000000000000000000),(42089853177/10000000000),(100000799842209183/100000000000000000),(104526187064036837/500000000000000000),(42089853177/20000000000),(6095375363873753/50000000000000000),25⟩
theorem inputs_valid870 : inputs870.Valid := by decide +kernel
def envelope870 : RatMajorityEnvelope := ⟨428,1,inputs870,1,(549809049353861957/1000000000000000000)⟩
theorem envelope_sound870 : envelope870.Sound := by
  apply rat_majority_inputs_envelopes inputs870 inputs_valid870
  · norm_num [envelope870]
  · intro rho hr0 hr1
    have hh := Batch043.bound1740 rho hr0 hr1
    norm_num [Batch043.certificate1740,envelope870,inputs870,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1741 rho hr0 hr1
    norm_num [Batch043.certificate1741,envelope870,inputs870,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs871 : RatMajorityInputs := ⟨(1875381561845680492167159/5000000000000000000),(41322669827/10000000000),(100000799842209183/100000000000000000),(27419554255453361/125000000000000000),(41322669827/20000000000),(12667462457007931/100000000000000000),25⟩
theorem inputs_valid871 : inputs871.Valid := by decide +kernel
def envelope871 : RatMajorityEnvelope := ⟨428,2,inputs871,1,(55119827850272469/100000000000000000)⟩
theorem envelope_sound871 : envelope871.Sound := by
  apply rat_majority_inputs_envelopes inputs871 inputs_valid871
  · norm_num [envelope871]
  · intro rho hr0 hr1
    have hh := Batch043.bound1742 rho hr0 hr1
    norm_num [Batch043.certificate1742,envelope871,inputs871,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1743 rho hr0 hr1
    norm_num [Batch043.certificate1743,envelope871,inputs871,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs872 : RatMajorityInputs := ⟨(3373054873252669035218977/10000000000000000000),(44141683767/10000000000),(31250277939885501/31250000000000000),(91732472763520571/500000000000000000),(44141683767/20000000000),(110020981733174537/1000000000000000000),25⟩
theorem inputs_valid872 : inputs872.Valid := by decide +kernel
def envelope872 : RatMajorityEnvelope := ⟨429,0,inputs872,(2714132979/2350000000),(681140924723339557/1000000000000000000)⟩
theorem envelope_sound872 : envelope872.Sound := by
  apply rat_majority_inputs_envelopes inputs872 inputs_valid872
  · norm_num [envelope872]
  · intro rho hr0 hr1
    have hh := Batch043.bound1744 rho hr0 hr1
    norm_num [Batch043.certificate1744,envelope872,inputs872,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1745 rho hr0 hr1
    norm_num [Batch043.certificate1745,envelope872,inputs872,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs873 : RatMajorityInputs := ⟨(3373054873252669035218977/10000000000000000000),(78418110351/20000000000),(31250277939885501/31250000000000000),(249923275990174843/1000000000000000000),(78418110351/40000000000),(4399833139690043/31250000000000000),25⟩
theorem inputs_valid873 : inputs873.Valid := by decide +kernel
def envelope873 : RatMajorityEnvelope := ⟨429,1,inputs873,1,(69443456176330337/125000000000000000)⟩
theorem envelope_sound873 : envelope873.Sound := by
  apply rat_majority_inputs_envelopes inputs873 inputs_valid873
  · norm_num [envelope873]
  · intro rho hr0 hr1
    have hh := Batch043.bound1746 rho hr0 hr1
    norm_num [Batch043.certificate1746,envelope873,inputs873,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1747 rho hr0 hr1
    norm_num [Batch043.certificate1747,envelope873,inputs873,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs874 : RatMajorityInputs := ⟨(3373054873252669035218977/10000000000000000000),(82953758777/20000000000),(31250277939885501/31250000000000000),(27156516218823409/125000000000000000),(82953758777/40000000000),(15712707311478823/125000000000000000),25⟩
theorem inputs_valid874 : inputs874.Valid := by decide +kernel
def envelope874 : RatMajorityEnvelope := ⟨429,2,inputs874,1,(550911898954496921/1000000000000000000)⟩
theorem envelope_sound874 : envelope874.Sound := by
  apply rat_majority_inputs_envelopes inputs874 inputs_valid874
  · norm_num [envelope874]
  · intro rho hr0 hr1
    have hh := Batch043.bound1748 rho hr0 hr1
    norm_num [Batch043.certificate1748,envelope874,inputs874,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1749 rho hr0 hr1
    norm_num [Batch043.certificate1749,envelope874,inputs874,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs875 : RatMajorityInputs := ⟨(305238500480117243310693/1000000000000000000),(44168137153/10000000000),(250002457113804721/250000000000000000),(91576605136610009/500000000000000000),(44168137153/20000000000),(13734444569273909/125000000000000000),26⟩
theorem inputs_valid875 : inputs875.Valid := by decide +kernel
def envelope875 : RatMajorityEnvelope := ⟨430,0,inputs875,(2714028587/2350000000),(340535253230200629/500000000000000000)⟩
theorem envelope_sound875 : envelope875.Sound := by
  apply rat_majority_inputs_envelopes inputs875 inputs_valid875
  · norm_num [envelope875]
  · intro rho hr0 hr1
    have hh := Batch043.bound1750 rho hr0 hr1
    norm_num [Batch043.certificate1750,envelope875,inputs875,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1751 rho hr0 hr1
    norm_num [Batch043.certificate1751,envelope875,inputs875,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs876 : RatMajorityInputs := ⟨(305238500480117243310693/1000000000000000000),(16853513189/4000000000),(250002457113804721/250000000000000000),(208474751491741733/1000000000000000000),(16853513189/8000000000),(121640032544539809/1000000000000000000),25⟩
theorem inputs_valid876 : inputs876.Valid := by decide +kernel
def envelope876 : RatMajorityEnvelope := ⟨430,1,inputs876,1,(137433255931191113/250000000000000000)⟩
theorem envelope_sound876 : envelope876.Sound := by
  apply rat_majority_inputs_envelopes inputs876 inputs_valid876
  · norm_num [envelope876]
  · intro rho hr0 hr1
    have hh := Batch043.bound1752 rho hr0 hr1
    norm_num [Batch043.certificate1752,envelope876,inputs876,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1753 rho hr0 hr1
    norm_num [Batch043.certificate1753,envelope876,inputs876,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs877 : RatMajorityInputs := ⟨(305238500480117243310693/1000000000000000000),(83265528201/20000000000),(250002457113804721/250000000000000000),(215141976134527287/1000000000000000000),(83265528201/40000000000),(31181429611066483/250000000000000000),25⟩
theorem inputs_valid877 : inputs877.Valid := by decide +kernel
def envelope877 : RatMajorityEnvelope := ⟨430,2,inputs877,1,(275313157612473413/500000000000000000)⟩
theorem envelope_sound877 : envelope877.Sound := by
  apply rat_majority_inputs_envelopes inputs877 inputs_valid877
  · norm_num [envelope877]
  · intro rho hr0 hr1
    have hh := Batch043.bound1754 rho hr0 hr1
    norm_num [Batch043.certificate1754,envelope877,inputs877,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1755 rho hr0 hr1
    norm_num [Batch043.certificate1755,envelope877,inputs877,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs878 : RatMajorityInputs := ⟨(5555487754772141842871639/20000000000000000000),(88478717629/20000000000),(500005400111264623/500000000000000000),(182316151231160267/1000000000000000000),(88478717629/40000000000),(13685622053285879/125000000000000000),25⟩
theorem inputs_valid878 : inputs878.Valid := by decide +kernel
def envelope878 : RatMajorityEnvelope := ⟨431,0,inputs878,(678435109/587500000),(680877741122903079/1000000000000000000)⟩
theorem envelope_sound878 : envelope878.Sound := by
  apply rat_majority_inputs_envelopes inputs878 inputs_valid878
  · norm_num [envelope878]
  · intro rho hr0 hr1
    have hh := Batch043.bound1756 rho hr0 hr1
    norm_num [Batch043.certificate1756,envelope878,inputs878,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1757 rho hr0 hr1
    norm_num [Batch043.certificate1757,envelope878,inputs878,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs879 : RatMajorityInputs := ⟨(5555487754772141842871639/20000000000000000000),(84308672333/20000000000),(500005400111264623/500000000000000000),(208204959644916009/1000000000000000000),(84308672333/40000000000),(15189386524283021/125000000000000000),25⟩
theorem inputs_valid879 : inputs879.Valid := by decide +kernel
def envelope879 : RatMajorityEnvelope := ⟨431,1,inputs879,1,(549697602364586891/1000000000000000000)⟩
theorem envelope_sound879 : envelope879.Sound := by
  apply rat_majority_inputs_envelopes inputs879 inputs_valid879
  · norm_num [envelope879]
  · intro rho hr0 hr1
    have hh := Batch043.bound1758 rho hr0 hr1
    norm_num [Batch043.certificate1758,envelope879,inputs879,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch043.bound1759 rho hr0 hr1
    norm_num [Batch043.certificate1759,envelope879,inputs879,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope860,envelope861,envelope862,envelope863,envelope864,envelope865,envelope866,envelope867,envelope868,envelope869,envelope870,envelope871,envelope872,envelope873,envelope874,envelope875,envelope876,envelope877,envelope878,envelope879]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound860
  · exact envelope_sound861
  · exact envelope_sound862
  · exact envelope_sound863
  · exact envelope_sound864
  · exact envelope_sound865
  · exact envelope_sound866
  · exact envelope_sound867
  · exact envelope_sound868
  · exact envelope_sound869
  · exact envelope_sound870
  · exact envelope_sound871
  · exact envelope_sound872
  · exact envelope_sound873
  · exact envelope_sound874
  · exact envelope_sound875
  · exact envelope_sound876
  · exact envelope_sound877
  · exact envelope_sound878
  · exact envelope_sound879

end Cycle12.MajorityCertificates.Inputs043
