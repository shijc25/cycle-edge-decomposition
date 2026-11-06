import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay092
import Cycle12.CutFailureCertificates.Decay093
import Cycle12.CutFailureCertificates.Decay094

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget037

def certificate740 : RatFailureBudget := ⟨(397359652228848228231/500000000000000000),(564336923977467/1000000000000000000),(1/62500000000000000),[(2,CutFailureCertificates.Decay092.certificate1850),(2,CutFailureCertificates.Decay092.certificate1851),(2,CutFailureCertificates.Decay092.certificate1852)]⟩
theorem numericValid740 : certificate740.NumericValid := by decide +kernel
theorem sound740 : certificate740.Sound := rat_failure_budget_sound certificate740 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1850,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1851,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1852,List.forall_mem_nil _⟩⟩⟩) numericValid740

def certificate741 : RatFailureBudget := ⟨(397359652228848228231/500000000000000000),(1032161788934641/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay092.certificate1853),(2,CutFailureCertificates.Decay092.certificate1854)]⟩
theorem numericValid741 : certificate741.NumericValid := by decide +kernel
theorem sound741 : certificate741.Sound := rat_failure_budget_sound certificate741 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1853,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1854,List.forall_mem_nil _⟩⟩) numericValid741

def certificate742 : RatFailureBudget := ⟨(46774558057064058789/62500000000000000),(295526393884981/500000000000000000),(3/500000000000000000),[(2,CutFailureCertificates.Decay092.certificate1855),(2,CutFailureCertificates.Decay092.certificate1856),(2,CutFailureCertificates.Decay092.certificate1857)]⟩
theorem numericValid742 : certificate742.NumericValid := by decide +kernel
theorem sound742 : certificate742.Sound := rat_failure_budget_sound certificate742 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1855,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1856,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1857,List.forall_mem_nil _⟩⟩⟩) numericValid742

def certificate743 : RatFailureBudget := ⟨(46774558057064058789/62500000000000000),(1104228996509569/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay092.certificate1858),(2,CutFailureCertificates.Decay092.certificate1859)]⟩
theorem numericValid743 : certificate743.NumericValid := by decide +kernel
theorem sound743 : certificate743.Sound := rat_failure_budget_sound certificate743 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1858,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1859,List.forall_mem_nil _⟩⟩) numericValid743

def certificate744 : RatFailureBudget := ⟨(705775029171982801787/1000000000000000000),(309100615642891/500000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay093.certificate1860),(2,CutFailureCertificates.Decay093.certificate1861),(2,CutFailureCertificates.Decay093.certificate1862)]⟩
theorem numericValid744 : certificate744.NumericValid := by decide +kernel
theorem sound744 : certificate744.Sound := rat_failure_budget_sound certificate744 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1860,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1861,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1862,List.forall_mem_nil _⟩⟩⟩) numericValid744

def certificate745 : RatFailureBudget := ⟨(705775029171982801787/1000000000000000000),(1141730920516197/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay093.certificate1863),(2,CutFailureCertificates.Decay093.certificate1864)]⟩
theorem numericValid745 : certificate745.NumericValid := by decide +kernel
theorem sound745 : certificate745.Sound := rat_failure_budget_sound certificate745 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1863,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1864,List.forall_mem_nil _⟩⟩) numericValid745

def certificate746 : RatFailureBudget := ⟨(333242582177592760029/500000000000000000),(129228298206161/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay093.certificate1865),(2,CutFailureCertificates.Decay093.certificate1866),(2,CutFailureCertificates.Decay093.certificate1867)]⟩
theorem numericValid746 : certificate746.NumericValid := by decide +kernel
theorem sound746 : certificate746.Sound := rat_failure_budget_sound certificate746 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1865,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1866,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1867,List.forall_mem_nil _⟩⟩⟩) numericValid746

def certificate747 : RatFailureBudget := ⟨(333242582177592760029/500000000000000000),(298650837396637/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay093.certificate1868),(2,CutFailureCertificates.Decay093.certificate1869)]⟩
theorem numericValid747 : certificate747.NumericValid := by decide +kernel
theorem sound747 : certificate747.Sound := rat_failure_budget_sound certificate747 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1868,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1869,List.forall_mem_nil _⟩⟩) numericValid747

def certificate748 : RatFailureBudget := ⟨(126038043328365260791/200000000000000000),(336900542926599/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay093.certificate1870),(2,CutFailureCertificates.Decay093.certificate1871),(2,CutFailureCertificates.Decay093.certificate1872)]⟩
theorem numericValid748 : certificate748.NumericValid := by decide +kernel
theorem sound748 : certificate748.Sound := rat_failure_budget_sound certificate748 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1870,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1871,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1872,List.forall_mem_nil _⟩⟩⟩) numericValid748

def certificate749 : RatFailureBudget := ⟨(126038043328365260791/200000000000000000),(156537598204101/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay093.certificate1873),(2,CutFailureCertificates.Decay093.certificate1874)]⟩
theorem numericValid749 : certificate749.NumericValid := by decide +kernel
theorem sound749 : certificate749.Sound := rat_failure_budget_sound certificate749 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1873,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1874,List.forall_mem_nil _⟩⟩) numericValid749

def certificate750 : RatFailureBudget := ⟨(298298758095224492837/500000000000000000),(14034720253107/20000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay093.certificate1875),(2,CutFailureCertificates.Decay093.certificate1876),(2,CutFailureCertificates.Decay093.certificate1877)]⟩
theorem numericValid750 : certificate750.NumericValid := by decide +kernel
theorem sound750 : certificate750.Sound := rat_failure_budget_sound certificate750 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1875,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1876,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1877,List.forall_mem_nil _⟩⟩⟩) numericValid750

def certificate751 : RatFailureBudget := ⟨(298298758095224492837/500000000000000000),(52439793237233/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay093.certificate1878),(2,CutFailureCertificates.Decay093.certificate1879)]⟩
theorem numericValid751 : certificate751.NumericValid := by decide +kernel
theorem sound751 : certificate751.Sound := rat_failure_budget_sound certificate751 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1878,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay093.sound1879,List.forall_mem_nil _⟩⟩) numericValid751

def certificate752 : RatFailureBudget := ⟨(282724551084683841297/500000000000000000),(729915299288471/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay094.certificate1880),(2,CutFailureCertificates.Decay094.certificate1881),(2,CutFailureCertificates.Decay094.certificate1882)]⟩
theorem numericValid752 : certificate752.NumericValid := by decide +kernel
theorem sound752 : certificate752.Sound := rat_failure_budget_sound certificate752 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1880,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1881,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1882,List.forall_mem_nil _⟩⟩⟩) numericValid752

def certificate753 : RatFailureBudget := ⟨(282724551084683841297/500000000000000000),(1368540749742463/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay094.certificate1883),(2,CutFailureCertificates.Decay094.certificate1884)]⟩
theorem numericValid753 : certificate753.NumericValid := by decide +kernel
theorem sound753 : certificate753.Sound := rat_failure_budget_sound certificate753 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1883,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1884,List.forall_mem_nil _⟩⟩) numericValid753

def certificate754 : RatFailureBudget := ⟨(134129227617246420223/250000000000000000),(94707633874879/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay094.certificate1885),(2,CutFailureCertificates.Decay094.certificate1886),(2,CutFailureCertificates.Decay094.certificate1887)]⟩
theorem numericValid754 : certificate754.NumericValid := by decide +kernel
theorem sound754 : certificate754.Sound := rat_failure_budget_sound certificate754 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1885,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1886,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1887,List.forall_mem_nil _⟩⟩⟩) numericValid754

def certificate755 : RatFailureBudget := ⟨(134129227617246420223/250000000000000000),(1427625076322579/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay094.certificate1888),(2,CutFailureCertificates.Decay094.certificate1889)]⟩
theorem numericValid755 : certificate755.NumericValid := by decide +kernel
theorem sound755 : certificate755.Sound := rat_failure_budget_sound certificate755 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1888,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1889,List.forall_mem_nil _⟩⟩) numericValid755

def certificate756 : RatFailureBudget := ⟨(101919744219146161073/200000000000000000),(39183151537903/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay094.certificate1890),(2,CutFailureCertificates.Decay094.certificate1891),(2,CutFailureCertificates.Decay094.certificate1892)]⟩
theorem numericValid756 : certificate756.NumericValid := by decide +kernel
theorem sound756 : certificate756.Sound := rat_failure_budget_sound certificate756 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1890,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1891,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1892,List.forall_mem_nil _⟩⟩⟩) numericValid756

def certificate757 : RatFailureBudget := ⟨(101919744219146161073/200000000000000000),(744828963545193/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay094.certificate1893),(2,CutFailureCertificates.Decay094.certificate1894)]⟩
theorem numericValid757 : certificate757.NumericValid := by decide +kernel
theorem sound757 : certificate757.Sound := rat_failure_budget_sound certificate757 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1893,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1894,List.forall_mem_nil _⟩⟩) numericValid757

def certificate758 : RatFailureBudget := ⟨(96902946267737970119/200000000000000000),(814722249363227/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay094.certificate1895),(2,CutFailureCertificates.Decay094.certificate1896),(2,CutFailureCertificates.Decay094.certificate1897)]⟩
theorem numericValid758 : certificate758.NumericValid := by decide +kernel
theorem sound758 : certificate758.Sound := rat_failure_budget_sound certificate758 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1895,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1896,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1897,List.forall_mem_nil _⟩⟩⟩) numericValid758

def certificate759 : RatFailureBudget := ⟨(96902946267737970119/200000000000000000),(775328846074817/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay094.certificate1898),(2,CutFailureCertificates.Decay094.certificate1899)]⟩
theorem numericValid759 : certificate759.NumericValid := by decide +kernel
theorem sound759 : certificate759.Sound := rat_failure_budget_sound certificate759 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1898,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay094.sound1899,List.forall_mem_nil _⟩⟩) numericValid759

end Cycle12.CutFailureCertificates.Budget037
