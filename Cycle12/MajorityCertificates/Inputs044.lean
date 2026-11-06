import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch044

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs044

def inputs880 : RatMajorityInputs := ⟨(5555487754772141842871639/20000000000000000000),(16715889387/4000000000),(500005400111264623/500000000000000000),(53258618627740749/250000000000000000),(16715889387/8000000000),(123750705891607507/1000000000000000000),25⟩
theorem inputs_valid880 : inputs880.Valid := by decide +kernel
def envelope880 : RatMajorityEnvelope := ⟨431,2,inputs880,1,(137585667946818217/250000000000000000)⟩
theorem envelope_sound880 : envelope880.Sound := by
  apply rat_majority_inputs_envelopes inputs880 inputs_valid880
  · norm_num [envelope880]
  · intro rho hr0 hr1
    have hh := Batch044.bound1760 rho hr0 hr1
    norm_num [Batch044.certificate1760,envelope880,inputs880,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1761 rho hr0 hr1
    norm_num [Batch044.certificate1761,envelope880,inputs880,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs881 : RatMajorityInputs := ⟨(5081328670864341388851281/20000000000000000000),(88793011141/20000000000),(500005904021854133/500000000000000000),(36096149210872063/200000000000000000),(88793011141/40000000000),(108628086826534249/1000000000000000000),26⟩
theorem inputs_valid881 : inputs881.Valid := by decide +kernel
def envelope881 : RatMajorityEnvelope := ⟨432,0,inputs881,(42392251/36718750),(42528336719473387/62500000000000000)⟩
theorem envelope_sound881 : envelope881.Sound := by
  apply rat_majority_inputs_envelopes inputs881 inputs_valid881
  · norm_num [envelope881]
  · intro rho hr0 hr1
    have hh := Batch044.bound1762 rho hr0 hr1
    norm_num [Batch044.certificate1762,envelope881,inputs881,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1763 rho hr0 hr1
    norm_num [Batch044.certificate1763,envelope881,inputs881,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs882 : RatMajorityInputs := ⟨(5081328670864341388851281/20000000000000000000),(1686759359/400000000),(500005904021854133/500000000000000000),(208012862709085911/1000000000000000000),(1686759359/800000000),(121426128286381903/1000000000000000000),25⟩
theorem inputs_valid882 : inputs882.Valid := by decide +kernel
def envelope882 : RatMajorityEnvelope := ⟨432,1,inputs882,1,(274836263871131467/500000000000000000)⟩
theorem envelope_sound882 : envelope882.Sound := by
  apply rat_majority_inputs_envelopes inputs882 inputs_valid882
  · norm_num [envelope882]
  · intro rho hr0 hr1
    have hh := Batch044.bound1764 rho hr0 hr1
    norm_num [Batch044.certificate1764,envelope882,inputs882,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1765 rho hr0 hr1
    norm_num [Batch044.certificate1765,envelope882,inputs882,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs883 : RatMajorityInputs := ⟨(5081328670864341388851281/20000000000000000000),(633544819/156250000),(500005904021854133/500000000000000000),(230199355437206327/1000000000000000000),(633544819/312500000),(131684888217372549/1000000000000000000),25⟩
theorem inputs_valid883 : inputs883.Valid := by decide +kernel
def envelope883 : RatMajorityEnvelope := ⟨432,2,inputs883,1,(276351299769452219/500000000000000000)⟩
theorem envelope_sound883 : envelope883.Sound := by
  apply rat_majority_inputs_envelopes inputs883 inputs_valid883
  · norm_num [envelope883]
  · intro rho hr0 hr1
    have hh := Batch044.bound1766 rho hr0 hr1
    norm_num [Batch044.certificate1766,envelope883,inputs883,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1767 rho hr0 hr1
    norm_num [Batch044.certificate1767,envelope883,inputs883,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs884 : RatMajorityInputs := ⟨(2334547251543445434414921/10000000000000000000),(89468777611/20000000000),(200002570117167423/200000000000000000),(2207346803416417/12500000000000000),(89468777611/40000000000),(26702080336274553/250000000000000000),26⟩
theorem inputs_valid884 : inputs884.Valid := by decide +kernel
def envelope884 : RatMajorityEnvelope := ⟨433,0,inputs884,(2711771859/2350000000),(339781175174906391/500000000000000000)⟩
theorem envelope_sound884 : envelope884.Sound := by
  apply rat_majority_inputs_envelopes inputs884 inputs_valid884
  · norm_num [envelope884]
  · intro rho hr0 hr1
    have hh := Batch044.bound1768 rho hr0 hr1
    norm_num [Batch044.certificate1768,envelope884,inputs884,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1769 rho hr0 hr1
    norm_num [Batch044.certificate1769,envelope884,inputs884,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs885 : RatMajorityInputs := ⟨(2334547251543445434414921/10000000000000000000),(42190380161/10000000000),(200002570117167423/200000000000000000),(207732530713075961/1000000000000000000),(42190380161/20000000000),(24259258989183689/200000000000000000),25⟩
theorem inputs_valid885 : inputs885.Valid := by decide +kernel
def envelope885 : RatMajorityEnvelope := ⟨433,1,inputs885,1,(274817890871439709/500000000000000000)⟩
theorem envelope_sound885 : envelope885.Sound := by
  apply rat_majority_inputs_envelopes inputs885 inputs_valid885
  · norm_num [envelope885]
  · intro rho hr0 hr1
    have hh := Batch044.bound1770 rho hr0 hr1
    norm_num [Batch044.certificate1770,envelope885,inputs885,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1771 rho hr0 hr1
    norm_num [Batch044.certificate1771,envelope885,inputs885,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs886 : RatMajorityInputs := ⟨(2334547251543445434414921/10000000000000000000),(41590575091/10000000000),(200002570117167423/200000000000000000),(107855694855234799/500000000000000000),(41590575091/20000000000),(124989098866595967/1000000000000000000),25⟩
theorem inputs_valid886 : inputs886.Valid := by decide +kernel
def envelope886 : RatMajorityEnvelope := ⟨433,2,inputs886,1,(550704562688572901/1000000000000000000)⟩
theorem envelope_sound886 : envelope886.Sound := by
  apply rat_majority_inputs_envelopes inputs886 inputs_valid886
  · norm_num [envelope886]
  · intro rho hr0 hr1
    have hh := Batch044.bound1772 rho hr0 hr1
    norm_num [Batch044.certificate1772,envelope886,inputs886,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1773 rho hr0 hr1
    norm_num [Batch044.certificate1773,envelope886,inputs886,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs887 : RatMajorityInputs := ⟨(2154187124187031934271159/10000000000000000000),(89389999501/20000000000),(1000013926517624653/1000000000000000000),(44259461753304331/250000000000000000),(89389999501/40000000000),(107018882564420999/1000000000000000000),25⟩
theorem inputs_valid887 : inputs887.Valid := by decide +kernel
def envelope887 : RatMajorityEnvelope := ⟨434,0,inputs887,(2711927931/2350000000),(679666595750471377/1000000000000000000)⟩
theorem envelope_sound887 : envelope887.Sound := by
  apply rat_majority_inputs_envelopes inputs887 inputs_valid887
  · norm_num [envelope887]
  · intro rho hr0 hr1
    have hh := Batch044.bound1774 rho hr0 hr1
    norm_num [Batch044.certificate1774,envelope887,inputs887,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1775 rho hr0 hr1
    norm_num [Batch044.certificate1775,envelope887,inputs887,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs888 : RatMajorityInputs := ⟨(2154187124187031934271159/10000000000000000000),(1688373621/400000000),(1000013926517624653/1000000000000000000),(207484376264711549/1000000000000000000),(1688373621/800000000),(24236271668064457/200000000000000000),25⟩
theorem inputs_valid888 : inputs888.Valid := by decide +kernel
def envelope888 : RatMajorityEnvelope := ⟨434,1,inputs888,1,(549603339716925573/1000000000000000000)⟩
theorem envelope_sound888 : envelope888.Sound := by
  apply rat_majority_inputs_envelopes inputs888 inputs_valid888
  · norm_num [envelope888]
  · intro rho hr0 hr1
    have hh := Batch044.bound1776 rho hr0 hr1
    norm_num [Batch044.certificate1776,envelope888,inputs888,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1777 rho hr0 hr1
    norm_num [Batch044.certificate1777,envelope888,inputs888,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs889 : RatMajorityInputs := ⟨(2154187124187031934271159/10000000000000000000),(41748637783/10000000000),(1000013926517624653/1000000000000000000),(106792235568327699/500000000000000000),(41748637783/20000000000),(62002593156308213/500000000000000000),25⟩
theorem inputs_valid889 : inputs889.Valid := by decide +kernel
def envelope889 : RatMajorityEnvelope := ⟨434,2,inputs889,1,(275208965385968709/500000000000000000)⟩
theorem envelope_sound889 : envelope889.Sound := by
  apply rat_majority_inputs_envelopes inputs889 inputs_valid889
  · norm_num [envelope889]
  · intro rho hr0 hr1
    have hh := Batch044.bound1778 rho hr0 hr1
    norm_num [Batch044.certificate1778,envelope889,inputs889,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1779 rho hr0 hr1
    norm_num [Batch044.certificate1779,envelope889,inputs889,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs890 : RatMajorityInputs := ⟨(62357270061875709780081/312500000000000000),(17802790707/4000000000),(125001879313674497/125000000000000000),(89599971326065169/500000000000000000),(17802790707/8000000000),(108029727146623221/1000000000000000000),25⟩
theorem inputs_valid890 : inputs890.Valid := by decide +kernel
def envelope890 : RatMajorityEnvelope := ⟨435,0,inputs890,(678167903/587500000),(10627555971708857/15625000000000000)⟩
theorem envelope_sound890 : envelope890.Sound := by
  apply rat_majority_inputs_envelopes inputs890 inputs_valid890
  · norm_num [envelope890]
  · intro rho hr0 hr1
    have hh := Batch044.bound1780 rho hr0 hr1
    norm_num [Batch044.certificate1780,envelope890,inputs890,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1781 rho hr0 hr1
    norm_num [Batch044.certificate1781,envelope890,inputs890,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs891 : RatMajorityInputs := ⟨(62357270061875709780081/312500000000000000),(84454158389/20000000000),(125001879313674497/125000000000000000),(207252435477490129/1000000000000000000),(84454158389/40000000000),(121073926186693589/1000000000000000000),25⟩
theorem inputs_valid891 : inputs891.Valid := by decide +kernel
def envelope891 : RatMajorityEnvelope := ⟨435,1,inputs891,1,(549573079104923131/1000000000000000000)⟩
theorem envelope_sound891 : envelope891.Sound := by
  apply rat_majority_inputs_envelopes inputs891 inputs_valid891
  · norm_num [envelope891]
  · intro rho hr0 hr1
    have hh := Batch044.bound1782 rho hr0 hr1
    norm_num [Batch044.certificate1782,envelope891,inputs891,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1783 rho hr0 hr1
    norm_num [Batch044.certificate1783,envelope891,inputs891,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs892 : RatMajorityInputs := ⟨(62357270061875709780081/312500000000000000),(84119392053/20000000000),(125001879313674497/125000000000000000),(104724837577186671/500000000000000000),(84119392053/40000000000),(61045732542952929/500000000000000000),25⟩
theorem inputs_valid892 : inputs892.Valid := by decide +kernel
def envelope892 : RatMajorityEnvelope := ⟨435,2,inputs892,1,(274932415826038253/500000000000000000)⟩
theorem envelope_sound892 : envelope892.Sound := by
  apply rat_majority_inputs_envelopes inputs892 inputs_valid892
  · norm_num [envelope892]
  · intro rho hr0 hr1
    have hh := Batch044.bound1784 rho hr0 hr1
    norm_num [Batch044.certificate1784,envelope892,inputs892,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1785 rho hr0 hr1
    norm_num [Batch044.certificate1785,envelope892,inputs892,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs893 : RatMajorityInputs := ⟨(1854940024752227571667679/10000000000000000000),(45041768547/10000000000),(62501010827067679/62500000000000000),(173108808983544069/1000000000000000000),(45041768547/20000000000),(3286854238424113/31250000000000000),25⟩
theorem inputs_valid893 : inputs893.Valid := by decide +kernel
def envelope893 : RatMajorityEnvelope := ⟨436,0,inputs893,(2710612479/2350000000),(678782599826410173/1000000000000000000)⟩
theorem envelope_sound893 : envelope893.Sound := by
  apply rat_majority_inputs_envelopes inputs893 inputs_valid893
  · norm_num [envelope893]
  · intro rho hr0 hr1
    have hh := Batch044.bound1786 rho hr0 hr1
    norm_num [Batch044.certificate1786,envelope893,inputs893,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1787 rho hr0 hr1
    norm_num [Batch044.certificate1787,envelope893,inputs893,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs894 : RatMajorityInputs := ⟨(1854940024752227571667679/10000000000000000000),(42242805559/10000000000),(62501010827067679/62500000000000000),(51761746869200153/250000000000000000),(42242805559/20000000000),(120978760971935421/1000000000000000000),25⟩
theorem inputs_valid894 : inputs894.Valid := by decide +kernel
def envelope894 : RatMajorityEnvelope := ⟨436,1,inputs894,1,(549546355702336977/1000000000000000000)⟩
theorem envelope_sound894 : envelope894.Sound := by
  apply rat_majority_inputs_envelopes inputs894 inputs_valid894
  · norm_num [envelope894]
  · intro rho hr0 hr1
    have hh := Batch044.bound1788 rho hr0 hr1
    norm_num [Batch044.certificate1788,envelope894,inputs894,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1789 rho hr0 hr1
    norm_num [Batch044.certificate1789,envelope894,inputs894,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs895 : RatMajorityInputs := ⟨(1854940024752227571667679/10000000000000000000),(84137560091/20000000000),(62501010827067679/62500000000000000),(6541560402981189/31250000000000000),(84137560091/40000000000),(122036023618213719/1000000000000000000),25⟩
theorem inputs_valid895 : inputs895.Valid := by decide +kernel
def envelope895 : RatMajorityEnvelope := ⟨436,2,inputs895,1,(68731169903724979/125000000000000000)⟩
theorem envelope_sound895 : envelope895.Sound := by
  apply rat_majority_inputs_envelopes inputs895 inputs_valid895
  · norm_num [envelope895]
  · intro rho hr0 hr1
    have hh := Batch044.bound1790 rho hr0 hr1
    norm_num [Batch044.certificate1790,envelope895,inputs895,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1791 rho hr0 hr1
    norm_num [Batch044.certificate1791,envelope895,inputs895,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs896 : RatMajorityInputs := ⟨(3459982469151140727758287/20000000000000000000),(89941740867/20000000000),(1000017341362217191/1000000000000000000),(17390598137952371/100000000000000000),(89941740867/40000000000),(422211392381707/4000000000000000),26⟩
theorem inputs_valid896 : inputs896.Valid := by decide +kernel
def envelope896 : RatMajorityEnvelope := ⟨437,0,inputs896,(542174349/470000000),(678959615663269053/1000000000000000000)⟩
theorem envelope_sound896 : envelope896.Sound := by
  apply rat_majority_inputs_envelopes inputs896 inputs_valid896
  · norm_num [envelope896]
  · intro rho hr0 hr1
    have hh := Batch044.bound1792 rho hr0 hr1
    norm_num [Batch044.certificate1792,envelope896,inputs896,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1793 rho hr0 hr1
    norm_num [Batch044.certificate1793,envelope896,inputs896,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs897 : RatMajorityInputs := ⟨(3459982469151140727758287/20000000000000000000),(660225873/156250000),(1000017341362217191/1000000000000000000),(206894898352637103/1000000000000000000),(660225873/312500000),(120908309471894489/1000000000000000000),25⟩
theorem inputs_valid897 : inputs897.Valid := by decide +kernel
def envelope897 : RatMajorityEnvelope := ⟨437,1,inputs897,1,(137381679258698441/250000000000000000)⟩
theorem envelope_sound897 : envelope897.Sound := by
  apply rat_majority_inputs_envelopes inputs897 inputs_valid897
  · norm_num [envelope897]
  · intro rho hr0 hr1
    have hh := Batch044.bound1794 rho hr0 hr1
    norm_num [Batch044.certificate1794,envelope897,inputs897,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1795 rho hr0 hr1
    norm_num [Batch044.certificate1795,envelope897,inputs897,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs898 : RatMajorityInputs := ⟨(3459982469151140727758287/20000000000000000000),(20713279807/5000000000),(1000017341362217191/1000000000000000000),(27242117165927217/125000000000000000),(20713279807/10000000000),(31504580159865461/250000000000000000),25⟩
theorem inputs_valid898 : inputs898.Valid := by decide +kernel
def envelope898 : RatMajorityEnvelope := ⟨437,2,inputs898,1,(275504242992023193/500000000000000000)⟩
theorem envelope_sound898 : envelope898.Sound := by
  apply rat_majority_inputs_envelopes inputs898 inputs_valid898
  · norm_num [envelope898]
  · intro rho hr0 hr1
    have hh := Batch044.bound1796 rho hr0 hr1
    norm_num [Batch044.certificate1796,envelope898,inputs898,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1797 rho hr0 hr1
    norm_num [Batch044.certificate1797,envelope898,inputs898,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs899 : RatMajorityInputs := ⟨(323671650837331969447831/2000000000000000000),(45226851069/10000000000),(500009268785964179/500000000000000000),(85521257363272131/500000000000000000),(45226851069/20000000000),(20842096530525969/200000000000000000),26⟩
theorem inputs_valid899 : inputs899.Valid := by decide +kernel
def envelope899 : RatMajorityEnvelope := ⟨438,0,inputs899,(2709918839/2350000000),(5299369278903319/7812500000000000)⟩
theorem envelope_sound899 : envelope899.Sound := by
  apply rat_majority_inputs_envelopes inputs899 inputs_valid899
  · norm_num [envelope899]
  · intro rho hr0 hr1
    have hh := Batch044.bound1798 rho hr0 hr1
    norm_num [Batch044.certificate1798,envelope899,inputs899,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch044.bound1799 rho hr0 hr1
    norm_num [Batch044.certificate1799,envelope899,inputs899,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope880,envelope881,envelope882,envelope883,envelope884,envelope885,envelope886,envelope887,envelope888,envelope889,envelope890,envelope891,envelope892,envelope893,envelope894,envelope895,envelope896,envelope897,envelope898,envelope899]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound880
  · exact envelope_sound881
  · exact envelope_sound882
  · exact envelope_sound883
  · exact envelope_sound884
  · exact envelope_sound885
  · exact envelope_sound886
  · exact envelope_sound887
  · exact envelope_sound888
  · exact envelope_sound889
  · exact envelope_sound890
  · exact envelope_sound891
  · exact envelope_sound892
  · exact envelope_sound893
  · exact envelope_sound894
  · exact envelope_sound895
  · exact envelope_sound896
  · exact envelope_sound897
  · exact envelope_sound898
  · exact envelope_sound899

end Cycle12.MajorityCertificates.Inputs044
