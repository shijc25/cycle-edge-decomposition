import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch045

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs045

def inputs900 : RatMajorityInputs := ⟨(323671650837331969447831/2000000000000000000),(42266525801/10000000000),(500009268785964179/500000000000000000),(103368714870108771/500000000000000000),(42266525801/20000000000),(120835363749808811/1000000000000000000),25⟩
theorem inputs_valid900 : inputs900.Valid := by decide +kernel
def envelope900 : RatMajorityEnvelope := ⟨438,1,inputs900,1,(274753193407695321/500000000000000000)⟩
theorem envelope_sound900 : envelope900.Sound := by
  apply rat_majority_inputs_envelopes inputs900 inputs_valid900
  · norm_num [envelope900]
  · intro rho hr0 hr1
    have hh := Batch045.bound1800 rho hr0 hr1
    norm_num [Batch045.certificate1800,envelope900,inputs900,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1801 rho hr0 hr1
    norm_num [Batch045.certificate1801,envelope900,inputs900,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs901 : RatMajorityInputs := ⟨(323671650837331969447831/2000000000000000000),(41588883467/10000000000),(500009268785964179/500000000000000000),(215734247121413273/1000000000000000000),(41588883467/20000000000),(124999671041662347/1000000000000000000),25⟩
theorem inputs_valid901 : inputs901.Valid := by decide +kernel
def envelope901 : RatMajorityEnvelope := ⟨438,2,inputs901,1,(68838747796782151/125000000000000000)⟩
theorem envelope_sound901 : envelope901.Sound := by
  apply rat_majority_inputs_envelopes inputs901 inputs_valid901
  · norm_num [envelope901]
  · intro rho hr0 hr1
    have hh := Batch045.bound1802 rho hr0 hr1
    norm_num [Batch045.certificate1802,envelope901,inputs901,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1803 rho hr0 hr1
    norm_num [Batch045.certificate1803,envelope901,inputs901,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs902 : RatMajorityInputs := ⟨(3036401098250113864601867/20000000000000000000),(5664989759/1250000000),(200003952107789179/200000000000000000),(17001152607522701/100000000000000000),(5664989759/2500000000),(25931670327269939/250000000000000000),26⟩
theorem inputs_valid902 : inputs902.Valid := by decide +kernel
def envelope902 : RatMajorityEnvelope := ⟨439,0,inputs902,(1354789413/1175000000),(339045418981944037/500000000000000000)⟩
theorem envelope_sound902 : envelope902.Sound := by
  apply rat_majority_inputs_envelopes inputs902 inputs_valid902
  · norm_num [envelope902]
  · intro rho hr0 hr1
    have hh := Batch045.bound1804 rho hr0 hr1
    norm_num [Batch045.certificate1804,envelope902,inputs902,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1805 rho hr0 hr1
    norm_num [Batch045.certificate1805,envelope902,inputs902,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs903 : RatMajorityInputs := ⟨(3036401098250113864601867/20000000000000000000),(8456787033/2000000000),(200003952107789179/200000000000000000),(12906904828031421/62500000000000000),(8456787033/4000000000),(120730226174325903/1000000000000000000),26⟩
theorem inputs_valid903 : inputs903.Valid := by decide +kernel
def envelope903 : RatMajorityEnvelope := ⟨439,1,inputs903,1,(109895378694535889/200000000000000000)⟩
theorem envelope_sound903 : envelope903.Sound := by
  apply rat_majority_inputs_envelopes inputs903 inputs_valid903
  · norm_num [envelope903]
  · intro rho hr0 hr1
    have hh := Batch045.bound1806 rho hr0 hr1
    norm_num [Batch045.certificate1806,envelope903,inputs903,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1807 rho hr0 hr1
    norm_num [Batch045.certificate1807,envelope903,inputs903,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs904 : RatMajorityInputs := ⟨(3036401098250113864601867/20000000000000000000),(41752325967/10000000000),(200003952107789179/200000000000000000),(213535050859183543/1000000000000000000),(41752325967/20000000000),(7748895045236871/62500000000000000),25⟩
theorem inputs_valid904 : inputs904.Valid := by decide +kernel
def envelope904 : RatMajorityEnvelope := ⟨439,2,inputs904,1,(275206836437776093/500000000000000000)⟩
theorem envelope_sound904 : envelope904.Sound := by
  apply rat_majority_inputs_envelopes inputs904 inputs_valid904
  · norm_num [envelope904]
  · intro rho hr0 hr1
    have hh := Batch045.bound1808 rho hr0 hr1
    norm_num [Batch045.certificate1808,envelope904,inputs904,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1809 rho hr0 hr1
    norm_num [Batch045.certificate1809,envelope904,inputs904,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs905 : RatMajorityInputs := ⟨(2855973496164786459339777/20000000000000000000),(18196772249/4000000000),(1000021008941608367/1000000000000000000),(84060022283140529/500000000000000000),(18196772249/8000000000),(51419196078209323/500000000000000000),26⟩
theorem inputs_valid905 : inputs905.Valid := by decide +kernel
def envelope905 : RatMajorityEnvelope := ⟨440,0,inputs905,(84654919/73437500),(677672826563199479/1000000000000000000)⟩
theorem envelope_sound905 : envelope905.Sound := by
  apply rat_majority_inputs_envelopes inputs905 inputs_valid905
  · norm_num [envelope905]
  · intro rho hr0 hr1
    have hh := Batch045.bound1810 rho hr0 hr1
    norm_num [Batch045.certificate1810,envelope905,inputs905,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1811 rho hr0 hr1
    norm_num [Batch045.certificate1811,envelope905,inputs905,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs906 : RatMajorityInputs := ⟨(2855973496164786459339777/20000000000000000000),(21147779767/5000000000),(1000021008941608367/1000000000000000000),(206359055176147123/1000000000000000000),(21147779767/10000000000),(120660075927684339/1000000000000000000),25⟩
theorem inputs_valid906 : inputs906.Valid := by decide +kernel
def envelope906 : RatMajorityEnvelope := ⟨440,1,inputs906,1,(549457404790653087/1000000000000000000)⟩
theorem envelope_sound906 : envelope906.Sound := by
  apply rat_majority_inputs_envelopes inputs906 inputs_valid906
  · norm_num [envelope906]
  · intro rho hr0 hr1
    have hh := Batch045.bound1812 rho hr0 hr1
    norm_num [Batch045.certificate1812,envelope906,inputs906,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1813 rho hr0 hr1
    norm_num [Batch045.certificate1813,envelope906,inputs906,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs907 : RatMajorityInputs := ⟨(2855973496164786459339777/20000000000000000000),(10479689217/2500000000),(1000021008941608367/1000000000000000000),(264143506239273/1250000000000000),(10479689217/5000000000),(122954877144536079/1000000000000000000),25⟩
theorem inputs_valid907 : inputs907.Valid := by decide +kernel
def envelope907 : RatMajorityEnvelope := ⟨440,2,inputs907,1,(275058126342356187/500000000000000000)⟩
theorem envelope_sound907 : envelope907.Sound := by
  apply rat_majority_inputs_envelopes inputs907 inputs_valid907
  · norm_num [envelope907]
  · intro rho hr0 hr1
    have hh := Batch045.bound1814 rho hr0 hr1
    norm_num [Batch045.certificate1814,envelope907,inputs907,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1815 rho hr0 hr1
    norm_num [Batch045.certificate1815,envelope907,inputs907,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs908 : RatMajorityInputs := ⟨(2692868426204975266668379/20000000000000000000),(89221068153/20000000000),(250005570364969943/250000000000000000),(178006352852180829/1000000000000000000),(89221068153/40000000000),(4298872376513233/40000000000000000),25⟩
theorem inputs_valid908 : inputs908.Valid := by decide +kernel
def envelope908 : RatMajorityEnvelope := ⟨441,0,inputs908,(2202413/1880000),(10866059021811753/15625000000000000)⟩
theorem envelope_sound908 : envelope908.Sound := by
  apply rat_majority_inputs_envelopes inputs908 inputs_valid908
  · norm_num [envelope908]
  · intro rho hr0 hr1
    have hh := Batch045.bound1816 rho hr0 hr1
    norm_num [Batch045.certificate1816,envelope908,inputs908,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1817 rho hr0 hr1
    norm_num [Batch045.certificate1817,envelope908,inputs908,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs909 : RatMajorityInputs := ⟨(2692868426204975266668379/20000000000000000000),(82268362853/20000000000),(250005570364969943/250000000000000000),(22195133812094817/100000000000000000),(82268362853/40000000000),(31968525688387251/250000000000000000),25⟩
theorem inputs_valid909 : inputs909.Valid := by decide +kernel
def envelope909 : RatMajorityEnvelope := ⟨441,1,inputs909,1,(551559841097079717/1000000000000000000)⟩
theorem envelope_sound909 : envelope909.Sound := by
  apply rat_majority_inputs_envelopes inputs909 inputs_valid909
  · norm_num [envelope909]
  · intro rho hr0 hr1
    have hh := Batch045.bound1818 rho hr0 hr1
    norm_num [Batch045.certificate1818,envelope909,inputs909,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1819 rho hr0 hr1
    norm_num [Batch045.certificate1819,envelope909,inputs909,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs910 : RatMajorityInputs := ⟨(2692868426204975266668379/20000000000000000000),(10520530807/2500000000),(250005570364969943/250000000000000000),(209154151316335767/1000000000000000000),(10520530807/5000000000),(60977316662317773/500000000000000000),26⟩
theorem inputs_valid910 : inputs910.Valid := by decide +kernel
def envelope910 : RatMajorityEnvelope := ⟨441,2,inputs910,1,(109965697289271103/200000000000000000)⟩
theorem envelope_sound910 : envelope910.Sound := by
  apply rat_majority_inputs_envelopes inputs910 inputs_valid910
  · norm_num [envelope910]
  · intro rho hr0 hr1
    have hh := Batch045.bound1820 rho hr0 hr1
    norm_num [Batch045.certificate1820,envelope910,inputs910,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1821 rho hr0 hr1
    norm_num [Batch045.certificate1821,envelope910,inputs910,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs911 : RatMajorityInputs := ⟨(2544923947165609207730943/20000000000000000000),(87354913789/20000000000),(500011788387687321/500000000000000000),(9450469324355427/50000000000000000),(87354913789/40000000000),(112604585002250889/1000000000000000000),27⟩
theorem inputs_valid911 : inputs911.Valid := by decide +kernel
def envelope911 : RatMajorityEnvelope := ⟨442,0,inputs911,(279901581/235000000),(357049934808549923/500000000000000000)⟩
theorem envelope_sound911 : envelope911.Sound := by
  apply rat_majority_inputs_envelopes inputs911 inputs_valid911
  · norm_num [envelope911]
  · intro rho hr0 hr1
    have hh := Batch045.bound1822 rho hr0 hr1
    norm_num [Batch045.certificate1822,envelope911,inputs911,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1823 rho hr0 hr1
    norm_num [Batch045.certificate1823,envelope911,inputs911,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs912 : RatMajorityInputs := ⟨(2544923947165609207730943/20000000000000000000),(82675820611/20000000000),(500011788387687321/500000000000000000),(43829543792727141/200000000000000000),(82675820611/40000000000),(6328906612243299/50000000000000000),25⟩
theorem inputs_valid912 : inputs912.Valid := by decide +kernel
def envelope912 : RatMajorityEnvelope := ⟨442,1,inputs912,1,(4409408863281547/8000000000000000)⟩
theorem envelope_sound912 : envelope912.Sound := by
  apply rat_majority_inputs_envelopes inputs912 inputs_valid912
  · norm_num [envelope912]
  · intro rho hr0 hr1
    have hh := Batch045.bound1824 rho hr0 hr1
    norm_num [Batch045.certificate1824,envelope912,inputs912,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1825 rho hr0 hr1
    norm_num [Batch045.certificate1825,envelope912,inputs912,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs913 : RatMajorityInputs := ⟨(2544923947165609207730943/20000000000000000000),(83918869843/20000000000),(500011788387687321/500000000000000000),(210775075000618999/1000000000000000000),(83918869843/40000000000),(24541010607218119/200000000000000000),25⟩
theorem inputs_valid913 : inputs913.Valid := by decide +kernel
def envelope913 : RatMajorityEnvelope := ⟨442,2,inputs913,1,(275022571868365613/500000000000000000)⟩
theorem envelope_sound913 : envelope913.Sound := by
  apply rat_majority_inputs_envelopes inputs913 inputs_valid913
  · norm_num [envelope913]
  · intro rho hr0 hr1
    have hh := Batch045.bound1826 rho hr0 hr1
    norm_num [Batch045.certificate1826,envelope913,inputs913,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1827 rho hr0 hr1
    norm_num [Batch045.certificate1827,envelope913,inputs913,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs914 : RatMajorityInputs := ⟨(96412299787339360317853/800000000000000000),(87262760419/20000000000),(500012446785696537/500000000000000000),(189567368771151939/1000000000000000000),(87262760419/40000000000),(11286430636449513/100000000000000000),25⟩
theorem inputs_valid914 : inputs914.Valid := by decide +kernel
def envelope914 : RatMajorityEnvelope := ⟨443,0,inputs914,(702582113/587500000),(718497297846570721/1000000000000000000)⟩
theorem envelope_sound914 : envelope914.Sound := by
  apply rat_majority_inputs_envelopes inputs914 inputs_valid914
  · norm_num [envelope914]
  · intro rho hr0 hr1
    have hh := Batch045.bound1828 rho hr0 hr1
    norm_num [Batch045.certificate1828,envelope914,inputs914,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1829 rho hr0 hr1
    norm_num [Batch045.certificate1829,envelope914,inputs914,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs915 : RatMajorityInputs := ⟨(96412299787339360317853/800000000000000000),(82674526701/20000000000),(500012446785696537/500000000000000000),(219156575537169941/1000000000000000000),(82674526701/40000000000),(31645556707217059/250000000000000000),25⟩
theorem inputs_valid915 : inputs915.Valid := by decide +kernel
def envelope915 : RatMajorityEnvelope := ⟨443,1,inputs915,1,(137794463322967939/250000000000000000)⟩
theorem envelope_sound915 : envelope915.Sound := by
  apply rat_majority_inputs_envelopes inputs915 inputs_valid915
  · norm_num [envelope915]
  · intro rho hr0 hr1
    have hh := Batch045.bound1830 rho hr0 hr1
    norm_num [Batch045.certificate1830,envelope915,inputs915,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1831 rho hr0 hr1
    norm_num [Batch045.certificate1831,envelope915,inputs915,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs916 : RatMajorityInputs := ⟨(96412299787339360317853/800000000000000000),(84258387503/20000000000),(500012446785696537/500000000000000000),(208535031775674849/1000000000000000000),(84258387503/40000000000),(60833973698346337/500000000000000000),25⟩
theorem inputs_valid916 : inputs916.Valid := by decide +kernel
def envelope916 : RatMajorityEnvelope := ⟨443,2,inputs916,1,(109949451129340399/200000000000000000)⟩
theorem envelope_sound916 : envelope916.Sound := by
  apply rat_majority_inputs_envelopes inputs916 inputs_valid916
  · norm_num [envelope916]
  · intro rho hr0 hr1
    have hh := Batch045.bound1832 rho hr0 hr1
    norm_num [Batch045.certificate1832,envelope916,inputs916,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1833 rho hr0 hr1
    norm_num [Batch045.certificate1833,envelope916,inputs916,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs917 : RatMajorityInputs := ⟨(1143728649454178581043003/10000000000000000000),(43706582207/10000000000),(250006557633241737/250000000000000000),(188657401154641687/1000000000000000000),(43706582207/20000000000),(56220361079383301/500000000000000000),25⟩
theorem inputs_valid917 : inputs917.Valid := by decide +kernel
def envelope917 : RatMajorityEnvelope := ⟨444,0,inputs917,(2812555759/2350000000),(179816829343774037/250000000000000000)⟩
theorem envelope_sound917 : envelope917.Sound := by
  apply rat_majority_inputs_envelopes inputs917 inputs_valid917
  · norm_num [envelope917]
  · intro rho hr0 hr1
    have hh := Batch045.bound1834 rho hr0 hr1
    norm_num [Batch045.certificate1834,envelope917,inputs917,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1835 rho hr0 hr1
    norm_num [Batch045.certificate1835,envelope917,inputs917,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs918 : RatMajorityInputs := ⟨(1143728649454178581043003/10000000000000000000),(16525877317/4000000000),(250006557633241737/250000000000000000),(109732868212518323/500000000000000000),(16525877317/8000000000),(396016112099013/3125000000000000),25⟩
theorem inputs_valid918 : inputs918.Valid := by decide +kernel
def envelope918 : RatMajorityEnvelope := ⟨444,1,inputs918,1,(551220633014092207/1000000000000000000)⟩
theorem envelope_sound918 : envelope918.Sound := by
  apply rat_majority_inputs_envelopes inputs918 inputs_valid918
  · norm_num [envelope918]
  · intro rho hr0 hr1
    have hh := Batch045.bound1836 rho hr0 hr1
    norm_num [Batch045.certificate1836,envelope918,inputs918,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1837 rho hr0 hr1
    norm_num [Batch045.certificate1837,envelope918,inputs918,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs919 : RatMajorityInputs := ⟨(1143728649454178581043003/10000000000000000000),(4229977863/1000000000),(250006557633241737/250000000000000000),(20630411907240461/100000000000000000),(4229977863/2000000000),(120634624790113233/1000000000000000000),25⟩
theorem inputs_valid919 : inputs919.Valid := by decide +kernel
def envelope919 : RatMajorityEnvelope := ⟨444,2,inputs919,1,(549452312694602683/1000000000000000000)⟩
theorem envelope_sound919 : envelope919.Sound := by
  apply rat_majority_inputs_envelopes inputs919 inputs_valid919
  · norm_num [envelope919]
  · intro rho hr0 hr1
    have hh := Batch045.bound1838 rho hr0 hr1
    norm_num [Batch045.certificate1838,envelope919,inputs919,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch045.bound1839 rho hr0 hr1
    norm_num [Batch045.certificate1839,envelope919,inputs919,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope900,envelope901,envelope902,envelope903,envelope904,envelope905,envelope906,envelope907,envelope908,envelope909,envelope910,envelope911,envelope912,envelope913,envelope914,envelope915,envelope916,envelope917,envelope918,envelope919]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound900
  · exact envelope_sound901
  · exact envelope_sound902
  · exact envelope_sound903
  · exact envelope_sound904
  · exact envelope_sound905
  · exact envelope_sound906
  · exact envelope_sound907
  · exact envelope_sound908
  · exact envelope_sound909
  · exact envelope_sound910
  · exact envelope_sound911
  · exact envelope_sound912
  · exact envelope_sound913
  · exact envelope_sound914
  · exact envelope_sound915
  · exact envelope_sound916
  · exact envelope_sound917
  · exact envelope_sound918
  · exact envelope_sound919

end Cycle12.MajorityCertificates.Inputs045
