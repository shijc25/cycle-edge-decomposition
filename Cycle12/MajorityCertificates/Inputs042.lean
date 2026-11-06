import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs042

def inputs840 : RatMajorityInputs := ⟨(4090272384602219964958459/2000000000000000000),(76108986157/20000000000),(250000366724161703/250000000000000000),(134008828789860951/500000000000000000),(76108986157/40000000000),(14916165117252949/100000000000000000),24⟩
theorem inputs_valid840 : inputs840.Valid := by decide +kernel
def envelope840 : RatMajorityEnvelope := ⟨418,1,inputs840,1,(17446589352770067/31250000000000000)⟩
theorem envelope_sound840 : envelope840.Sound := by
  apply rat_majority_inputs_envelopes inputs840 inputs_valid840
  · norm_num [envelope840]
  · intro rho hr0 hr1
    have hh := Batch042.bound1680 rho hr0 hr1
    norm_num [Batch042.certificate1680,envelope840,inputs840,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1681 rho hr0 hr1
    norm_num [Batch042.certificate1681,envelope840,inputs840,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs841 : RatMajorityInputs := ⟨(4090272384602219964958459/2000000000000000000),(81664388883/20000000000),(250000366724161703/250000000000000000),(226161461561330033/1000000000000000000),(81664388883/40000000000),(64909784583658233/500000000000000000),25⟩
theorem inputs_valid841 : inputs841.Valid := by decide +kernel
def envelope841 : RatMajorityEnvelope := ⟨418,2,inputs841,1,(552133806997158239/1000000000000000000)⟩
theorem envelope_sound841 : envelope841.Sound := by
  apply rat_majority_inputs_envelopes inputs841 inputs_valid841
  · norm_num [envelope841]
  · intro rho hr0 hr1
    have hh := Batch042.bound1682 rho hr0 hr1
    norm_num [Batch042.certificate1682,envelope841,inputs841,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1683 rho hr0 hr1
    norm_num [Batch042.certificate1683,envelope841,inputs841,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs842 : RatMajorityInputs := ⟨(7888748210787074681592789/5000000000000000000),(85876521739/20000000000),(1000001901445170099/1000000000000000000),(198130434325633863/1000000000000000000),(85876521739/40000000000),(23368858976441189/200000000000000000),25⟩
theorem inputs_valid842 : inputs842.Valid := by decide +kernel
def envelope842 : RatMajorityEnvelope := ⟨419,0,inputs842,(679848839/587500000),(342318514221011127/500000000000000000)⟩
theorem envelope_sound842 : envelope842.Sound := by
  apply rat_majority_inputs_envelopes inputs842 inputs_valid842
  · norm_num [envelope842]
  · intro rho hr0 hr1
    have hh := Batch042.bound1684 rho hr0 hr1
    norm_num [Batch042.certificate1684,envelope842,inputs842,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1685 rho hr0 hr1
    norm_num [Batch042.certificate1685,envelope842,inputs842,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs843 : RatMajorityInputs := ⟨(7888748210787074681592789/5000000000000000000),(76306676617/20000000000),(1000001901445170099/1000000000000000000),(266428989904665753/1000000000000000000),(76306676617/40000000000),(37106568499167917/250000000000000000),24⟩
theorem inputs_valid843 : inputs843.Valid := by decide +kernel
def envelope843 : RatMajorityEnvelope := ⟨419,1,inputs843,1,(17438891601940259/31250000000000000)⟩
theorem envelope_sound843 : envelope843.Sound := by
  apply rat_majority_inputs_envelopes inputs843 inputs_valid843
  · norm_num [envelope843]
  · intro rho hr0 hr1
    have hh := Batch042.bound1686 rho hr0 hr1
    norm_num [Batch042.certificate1686,envelope843,inputs843,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1687 rho hr0 hr1
    norm_num [Batch042.certificate1687,envelope843,inputs843,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs844 : RatMajorityInputs := ⟨(7888748210787074681592789/5000000000000000000),(81961533411/20000000000),(1000001901445170099/1000000000000000000),(224082020261476531/1000000000000000000),(81961533411/40000000000),(128858762949504973/1000000000000000000),25⟩
theorem inputs_valid844 : inputs844.Valid := by decide +kernel
def envelope844 : RatMajorityEnvelope := ⟨419,2,inputs844,1,(110369104527465789/200000000000000000)⟩
theorem envelope_sound844 : envelope844.Sound := by
  apply rat_majority_inputs_envelopes inputs844 inputs_valid844
  · norm_num [envelope844]
  · intro rho hr0 hr1
    have hh := Batch042.bound1688 rho hr0 hr1
    norm_num [Batch042.certificate1688,envelope844,inputs844,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1689 rho hr0 hr1
    norm_num [Batch042.certificate1689,envelope844,inputs844,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs845 : RatMajorityInputs := ⟨(25123862869819114345656713/20000000000000000000),(86584085589/20000000000),(1000002388172223313/1000000000000000000),(193719787284474151/1000000000000000000),(86584085589/40000000000),(114795598121062577/1000000000000000000),27⟩
theorem inputs_valid845 : inputs845.Valid := by decide +kernel
def envelope845 : RatMajorityEnvelope := ⟨420,0,inputs845,(11565033/10000000),(34178356456913199/50000000000000000)⟩
theorem envelope_sound845 : envelope845.Sound := by
  apply rat_majority_inputs_envelopes inputs845 inputs_valid845
  · norm_num [envelope845]
  · intro rho hr0 hr1
    have hh := Batch042.bound1690 rho hr0 hr1
    norm_num [Batch042.certificate1690,envelope845,inputs845,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1691 rho hr0 hr1
    norm_num [Batch042.certificate1691,envelope845,inputs845,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs846 : RatMajorityInputs := ⟨(25123862869819114345656713/20000000000000000000),(16722524377/4000000000),(1000002388172223313/1000000000000000000),(212812758614700729/1000000000000000000),(16722524377/8000000000),(61824056427231909/500000000000000000),25⟩
theorem inputs_valid846 : inputs846.Valid := by decide +kernel
def envelope846 : RatMajorityEnvelope := ⟨420,1,inputs846,1,(27515471268724391/50000000000000000)⟩
theorem envelope_sound846 : envelope846.Sound := by
  apply rat_majority_inputs_envelopes inputs846 inputs_valid846
  · norm_num [envelope846]
  · intro rho hr0 hr1
    have hh := Batch042.bound1692 rho hr0 hr1
    norm_num [Batch042.certificate1692,envelope846,inputs846,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1693 rho hr0 hr1
    norm_num [Batch042.certificate1693,envelope846,inputs846,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs847 : RatMajorityInputs := ⟨(25123862869819114345656713/20000000000000000000),(822600909/200000000),(1000002388172223313/1000000000000000000),(222008560396915777/1000000000000000000),(822600909/400000000),(127900549702251073/1000000000000000000),26⟩
theorem inputs_valid847 : inputs847.Valid := by decide +kernel
def envelope847 : RatMajorityEnvelope := ⟨420,2,inputs847,1,(551559649661987641/1000000000000000000)⟩
theorem envelope_sound847 : envelope847.Sound := by
  apply rat_majority_inputs_envelopes inputs847 inputs_valid847
  · norm_num [envelope847]
  · intro rho hr0 hr1
    have hh := Batch042.bound1694 rho hr0 hr1
    norm_num [Batch042.certificate1694,envelope847,inputs847,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1695 rho hr0 hr1
    norm_num [Batch042.certificate1695,envelope847,inputs847,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs848 : RatMajorityInputs := ⟨(10253891940699585536600117/10000000000000000000),(86488448297/20000000000),(200000585145005241/200000000000000000),(9715553318332393/50000000000000000),(86488448297/40000000000),(4602815800158881/40000000000000000),25⟩
theorem inputs_valid848 : inputs848.Valid := by decide +kernel
def envelope848 : RatMajorityEnvelope := ⟨421,0,inputs848,(1358997793/1175000000),(341854647581501871/500000000000000000)⟩
theorem envelope_sound848 : envelope848.Sound := by
  apply rat_majority_inputs_envelopes inputs848 inputs_valid848
  · norm_num [envelope848]
  · intro rho hr0 hr1
    have hh := Batch042.bound1696 rho hr0 hr1
    norm_num [Batch042.certificate1696,envelope848,inputs848,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1697 rho hr0 hr1
    norm_num [Batch042.certificate1697,envelope848,inputs848,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs849 : RatMajorityInputs := ⟨(10253891940699585536600117/10000000000000000000),(3150694679/800000000),(200000585145005241/200000000000000000),(247273735906581237/1000000000000000000),(3150694679/1600000000),(139570675113807337/1000000000000000000),24⟩
theorem inputs_valid849 : inputs849.Valid := by decide +kernel
def envelope849 : RatMajorityEnvelope := ⟨421,1,inputs849,1,(555154270703377929/1000000000000000000)⟩
theorem envelope_sound849 : envelope849.Sound := by
  apply rat_majority_inputs_envelopes inputs849 inputs_valid849
  · norm_num [envelope849]
  · intro rho hr0 hr1
    have hh := Batch042.bound1698 rho hr0 hr1
    norm_num [Batch042.certificate1698,envelope849,inputs849,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1699 rho hr0 hr1
    norm_num [Batch042.certificate1699,envelope849,inputs849,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs850 : RatMajorityInputs := ⟨(10253891940699585536600117/10000000000000000000),(41280467493/10000000000),(200000585145005241/200000000000000000),(109967621524710569/500000000000000000),(41280467493/20000000000),(126942205024558107/1000000000000000000),25⟩
theorem inputs_valid850 : inputs850.Valid := by decide +kernel
def envelope850 : RatMajorityEnvelope := ⟨421,2,inputs850,1,(551275364620053391/1000000000000000000)⟩
theorem envelope_sound850 : envelope850.Sound := by
  apply rat_majority_inputs_envelopes inputs850 inputs_valid850
  · norm_num [envelope850]
  · intro rho hr0 hr1
    have hh := Batch042.bound1700 rho hr0 hr1
    norm_num [Batch042.certificate1700,envelope850,inputs850,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1701 rho hr0 hr1
    norm_num [Batch042.certificate1701,envelope850,inputs850,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs851 : RatMajorityInputs := ⟨(2135083737137769044551673/2500000000000000000),(85305274433/20000000000),(62500219547024099/62500000000000000),(201752690725324007/1000000000000000000),(85305274433/40000000000),(5926247092398483/50000000000000000),25⟩
theorem inputs_valid851 : inputs851.Valid := by decide +kernel
def envelope851 : RatMajorityEnvelope := ⟨422,0,inputs851,(2720757753/2350000000),(68553524238397789/100000000000000000)⟩
theorem envelope_sound851 : envelope851.Sound := by
  apply rat_majority_inputs_envelopes inputs851 inputs_valid851
  · norm_num [envelope851]
  · intro rho hr0 hr1
    have hh := Batch042.bound1702 rho hr0 hr1
    norm_num [Batch042.certificate1702,envelope851,inputs851,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1703 rho hr0 hr1
    norm_num [Batch042.certificate1703,envelope851,inputs851,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs852 : RatMajorityInputs := ⟨(2135083737137769044551673/2500000000000000000),(76898257439/20000000000),(62500219547024099/62500000000000000),(32714929683589501/125000000000000000),(76898257439/40000000000),(18280909183916793/125000000000000000),24⟩
theorem inputs_valid852 : inputs852.Valid := by decide +kernel
def envelope852 : RatMajorityEnvelope := ⟨422,1,inputs852,1,(278660303103874087/500000000000000000)⟩
theorem envelope_sound852 : envelope852.Sound := by
  apply rat_majority_inputs_envelopes inputs852 inputs_valid852
  · norm_num [envelope852]
  · intro rho hr0 hr1
    have hh := Batch042.bound1704 rho hr0 hr1
    norm_num [Batch042.certificate1704,envelope852,inputs852,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1705 rho hr0 hr1
    norm_num [Batch042.certificate1705,envelope852,inputs852,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs853 : RatMajorityInputs := ⟨(2135083737137769044551673/2500000000000000000),(16572837273/4000000000),(62500219547024099/62500000000000000),(54465385768044373/250000000000000000),(16572837273/8000000000),(62991729455976247/500000000000000000),25⟩
theorem inputs_valid853 : inputs853.Valid := by decide +kernel
def envelope853 : RatMajorityEnvelope := ⟨422,2,inputs853,1,(550992584856582553/1000000000000000000)⟩
theorem envelope_sound853 : envelope853.Sound := by
  apply rat_majority_inputs_envelopes inputs853 inputs_valid853
  · norm_num [envelope853]
  · intro rho hr0 hr1
    have hh := Batch042.bound1706 rho hr0 hr1
    norm_num [Batch042.certificate1706,envelope853,inputs853,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1707 rho hr0 hr1
    norm_num [Batch042.certificate1707,envelope853,inputs853,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs854 : RatMajorityInputs := ⟨(3616295304816484921708913/5000000000000000000),(43563197427/10000000000),(1000004147904727867/1000000000000000000),(190395611538703573/1000000000000000000),(43563197427/20000000000),(113249733100528037/1000000000000000000),25⟩
theorem inputs_valid854 : inputs854.Valid := by decide +kernel
def envelope854 : RatMajorityEnvelope := ⟨423,0,inputs854,(543316227/470000000),(170692573998172499/250000000000000000)⟩
theorem envelope_sound854 : envelope854.Sound := by
  apply rat_majority_inputs_envelopes inputs854 inputs_valid854
  · norm_num [envelope854]
  · intro rho hr0 hr1
    have hh := Batch042.bound1708 rho hr0 hr1
    norm_num [Batch042.certificate1708,envelope854,inputs854,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1709 rho hr0 hr1
    norm_num [Batch042.certificate1709,envelope854,inputs854,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs855 : RatMajorityInputs := ⟨(3616295304816484921708913/5000000000000000000),(10403870603/2500000000),(1000004147904727867/1000000000000000000),(215375071521535121/1000000000000000000),(10403870603/5000000000),(199733661713773/1600000000000000),25⟩
theorem inputs_valid855 : inputs855.Valid := by decide +kernel
def envelope855 : RatMajorityEnvelope := ⟨423,1,inputs855,1,(137663875584546849/250000000000000000)⟩
theorem envelope_sound855 : envelope855.Sound := by
  apply rat_majority_inputs_envelopes inputs855 inputs_valid855
  · norm_num [envelope855]
  · intro rho hr0 hr1
    have hh := Batch042.bound1710 rho hr0 hr1
    norm_num [Batch042.certificate1710,envelope855,inputs855,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1711 rho hr0 hr1
    norm_num [Batch042.certificate1711,envelope855,inputs855,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs856 : RatMajorityInputs := ⟨(3616295304816484921708913/5000000000000000000),(83169787791/20000000000),(1000004147904727867/1000000000000000000),(26973520325393019/125000000000000000),(83169787791/40000000000),(125024608285057403/1000000000000000000),25⟩
theorem inputs_valid856 : inputs856.Valid := by decide +kernel
def envelope856 : RatMajorityEnvelope := ⟨423,2,inputs856,1,(137677848875185631/250000000000000000)⟩
theorem envelope_sound856 : envelope856.Sound := by
  apply rat_majority_inputs_envelopes inputs856 inputs_valid856
  · norm_num [envelope856]
  · intro rho hr0 hr1
    have hh := Batch042.bound1712 rho hr0 hr1
    norm_num [Batch042.certificate1712,envelope856,inputs856,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1713 rho hr0 hr1
    norm_num [Batch042.certificate1713,envelope856,inputs856,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs857 : RatMajorityInputs := ⟨(1242283354851108754781377/2000000000000000000),(86663251449/20000000000),(1000004829834124227/1000000000000000000),(38646298499989429/200000000000000000),(86663251449/40000000000),(28642156373738297/250000000000000000),25⟩
theorem inputs_valid857 : inputs857.Valid := by decide +kernel
def envelope857 : RatMajorityEnvelope := ⟨424,0,inputs857,(2717605461/2350000000),(170862690123016829/250000000000000000)⟩
theorem envelope_sound857 : envelope857.Sound := by
  apply rat_majority_inputs_envelopes inputs857 inputs_valid857
  · norm_num [envelope857]
  · intro rho hr0 hr1
    have hh := Batch042.bound1714 rho hr0 hr1
    norm_num [Batch042.certificate1714,envelope857,inputs857,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1715 rho hr0 hr1
    norm_num [Batch042.certificate1715,envelope857,inputs857,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs858 : RatMajorityInputs := ⟨(1242283354851108754781377/2000000000000000000),(81958564609/20000000000),(1000004829834124227/1000000000000000000),(224102718139302241/1000000000000000000),(81958564609/40000000000),(64434163604129757/500000000000000000),25⟩
theorem inputs_valid858 : inputs858.Valid := by decide +kernel
def envelope858 : RatMajorityEnvelope := ⟨424,1,inputs858,1,(275924784763951061/500000000000000000)⟩
theorem envelope_sound858 : envelope858.Sound := by
  apply rat_majority_inputs_envelopes inputs858 inputs_valid858
  · norm_num [envelope858]
  · intro rho hr0 hr1
    have hh := Batch042.bound1716 rho hr0 hr1
    norm_num [Batch042.certificate1716,envelope858,inputs858,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1717 rho hr0 hr1
    norm_num [Batch042.certificate1717,envelope858,inputs858,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs859 : RatMajorityInputs := ⟨(1242283354851108754781377/2000000000000000000),(81435227881/20000000000),(1000004829834124227/1000000000000000000),(227775951569564757/1000000000000000000),(81435227881/40000000000),(16320680407081911/125000000000000000),24⟩
theorem inputs_valid859 : inputs859.Valid := by decide +kernel
def envelope859 : RatMajorityEnvelope := ⟨424,2,inputs859,1,(552360207694683039/1000000000000000000)⟩
theorem envelope_sound859 : envelope859.Sound := by
  apply rat_majority_inputs_envelopes inputs859 inputs_valid859
  · norm_num [envelope859]
  · intro rho hr0 hr1
    have hh := Batch042.bound1718 rho hr0 hr1
    norm_num [Batch042.certificate1718,envelope859,inputs859,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch042.bound1719 rho hr0 hr1
    norm_num [Batch042.certificate1719,envelope859,inputs859,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope840,envelope841,envelope842,envelope843,envelope844,envelope845,envelope846,envelope847,envelope848,envelope849,envelope850,envelope851,envelope852,envelope853,envelope854,envelope855,envelope856,envelope857,envelope858,envelope859]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound840
  · exact envelope_sound841
  · exact envelope_sound842
  · exact envelope_sound843
  · exact envelope_sound844
  · exact envelope_sound845
  · exact envelope_sound846
  · exact envelope_sound847
  · exact envelope_sound848
  · exact envelope_sound849
  · exact envelope_sound850
  · exact envelope_sound851
  · exact envelope_sound852
  · exact envelope_sound853
  · exact envelope_sound854
  · exact envelope_sound855
  · exact envelope_sound856
  · exact envelope_sound857
  · exact envelope_sound858
  · exact envelope_sound859

end Cycle12.MajorityCertificates.Inputs042
