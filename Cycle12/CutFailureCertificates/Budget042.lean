import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay105
import Cycle12.CutFailureCertificates.Decay106
import Cycle12.CutFailureCertificates.Decay107

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget042

def certificate840 : RatFailureBudget := ⟨(120871515643124418446001/1000000000000000000),(9611430383111/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay105.certificate2102),(2,CutFailureCertificates.Decay105.certificate2103)]⟩
theorem numericValid840 : certificate840.NumericValid := by decide +kernel
theorem sound840 : certificate840.Sound := rat_failure_budget_sound certificate840 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2102,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2103,List.forall_mem_nil _⟩⟩) numericValid840

def certificate841 : RatFailureBudget := ⟨(120871515643124418446001/1000000000000000000),(4472589425169449/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay105.certificate2104),(918,CutFailureCertificates.Decay105.certificate2105),(1,CutFailureCertificates.Decay105.certificate2106)]⟩
theorem numericValid841 : certificate841.NumericValid := by decide +kernel
theorem sound841 : certificate841.Sound := rat_failure_budget_sound certificate841 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2104,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2105,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2106,List.forall_mem_nil _⟩⟩⟩) numericValid841

def certificate842 : RatFailureBudget := ⟨(23032998842882170964523/250000000000000000),(6913844715599/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay105.certificate2107),(2,CutFailureCertificates.Decay105.certificate2108),(2,CutFailureCertificates.Decay105.certificate2109)]⟩
theorem numericValid842 : certificate842.NumericValid := by decide +kernel
theorem sound842 : certificate842.Sound := rat_failure_budget_sound certificate842 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2107,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2108,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2109,List.forall_mem_nil _⟩⟩⟩) numericValid842

def certificate843 : RatFailureBudget := ⟨(23032998842882170964523/250000000000000000),(34715100561/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay105.certificate2110),(2,CutFailureCertificates.Decay105.certificate2111)]⟩
theorem numericValid843 : certificate843.NumericValid := by decide +kernel
theorem sound843 : certificate843.Sound := rat_failure_budget_sound certificate843 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2110,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2111,List.forall_mem_nil _⟩⟩) numericValid843

def certificate844 : RatFailureBudget := ⟨(23032998842882170964523/250000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay105.certificate2112),(918,CutFailureCertificates.Decay105.certificate2113),(1,CutFailureCertificates.Decay105.certificate2114)]⟩
theorem numericValid844 : certificate844.NumericValid := by decide +kernel
theorem sound844 : certificate844.Sound := rat_failure_budget_sound certificate844 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2112,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2113,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2114,List.forall_mem_nil _⟩⟩⟩) numericValid844

def certificate845 : RatFailureBudget := ⟨(72471107720699531725569/1000000000000000000),(9484771398089/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay105.certificate2115),(2,CutFailureCertificates.Decay105.certificate2116),(2,CutFailureCertificates.Decay105.certificate2117)]⟩
theorem numericValid845 : certificate845.NumericValid := by decide +kernel
theorem sound845 : certificate845.Sound := rat_failure_budget_sound certificate845 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2115,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2116,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2117,List.forall_mem_nil _⟩⟩⟩) numericValid845

def certificate846 : RatFailureBudget := ⟨(72471107720699531725569/1000000000000000000),(6828147719547/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay105.certificate2118),(2,CutFailureCertificates.Decay105.certificate2119)]⟩
theorem numericValid846 : certificate846.NumericValid := by decide +kernel
theorem sound846 : certificate846.Sound := rat_failure_budget_sound certificate846 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2118,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2119,List.forall_mem_nil _⟩⟩) numericValid846

def certificate847 : RatFailureBudget := ⟨(72471107720699531725569/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay106.certificate2120),(916,CutFailureCertificates.Decay106.certificate2121),(1,CutFailureCertificates.Decay106.certificate2122)]⟩
theorem numericValid847 : certificate847.NumericValid := by decide +kernel
theorem sound847 : certificate847.Sound := rat_failure_budget_sound certificate847 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2120,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2121,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2122,List.forall_mem_nil _⟩⟩⟩) numericValid847

def certificate848 : RatFailureBudget := ⟨(58438407163718057272441/1000000000000000000),(1020653187273/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay106.certificate2123),(2,CutFailureCertificates.Decay106.certificate2124),(2,CutFailureCertificates.Decay106.certificate2125)]⟩
theorem numericValid848 : certificate848.NumericValid := by decide +kernel
theorem sound848 : certificate848.Sound := rat_failure_budget_sound certificate848 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2123,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2124,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2125,List.forall_mem_nil _⟩⟩⟩) numericValid848

def certificate849 : RatFailureBudget := ⟨(58438407163718057272441/1000000000000000000),(256069457707/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay106.certificate2126),(2,CutFailureCertificates.Decay106.certificate2127)]⟩
theorem numericValid849 : certificate849.NumericValid := by decide +kernel
theorem sound849 : certificate849.Sound := rat_failure_budget_sound certificate849 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2126,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2127,List.forall_mem_nil _⟩⟩) numericValid849

def certificate850 : RatFailureBudget := ⟨(58438407163718057272441/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay106.certificate2128),(916,CutFailureCertificates.Decay106.certificate2129),(1,CutFailureCertificates.Decay106.certificate2130)]⟩
theorem numericValid850 : certificate850.NumericValid := by decide +kernel
theorem sound850 : certificate850.Sound := rat_failure_budget_sound certificate850 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2128,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2129,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2130,List.forall_mem_nil _⟩⟩⟩) numericValid850

def certificate851 : RatFailureBudget := ⟨(9615687695137442862049/200000000000000000),(30873519990299/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay106.certificate2131),(2,CutFailureCertificates.Decay106.certificate2132),(2,CutFailureCertificates.Decay106.certificate2133)]⟩
theorem numericValid851 : certificate851.NumericValid := by decide +kernel
theorem sound851 : certificate851.Sound := rat_failure_budget_sound certificate851 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2131,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2132,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2133,List.forall_mem_nil _⟩⟩⟩) numericValid851

def certificate852 : RatFailureBudget := ⟨(9615687695137442862049/200000000000000000),(4904040158981/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay106.certificate2134),(2,CutFailureCertificates.Decay106.certificate2135)]⟩
theorem numericValid852 : certificate852.NumericValid := by decide +kernel
theorem sound852 : certificate852.Sound := rat_failure_budget_sound certificate852 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2134,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2135,List.forall_mem_nil _⟩⟩) numericValid852

def certificate853 : RatFailureBudget := ⟨(9615687695137442862049/200000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay106.certificate2136),(916,CutFailureCertificates.Decay106.certificate2137),(1,CutFailureCertificates.Decay106.certificate2138)]⟩
theorem numericValid853 : certificate853.NumericValid := by decide +kernel
theorem sound853 : certificate853.Sound := rat_failure_budget_sound certificate853 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2136,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2137,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2138,List.forall_mem_nil _⟩⟩⟩) numericValid853

def certificate854 : RatFailureBudget := ⟨(20108024706910554078163/500000000000000000),(1267058135723/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay106.certificate2139),(2,CutFailureCertificates.Decay107.certificate2140),(2,CutFailureCertificates.Decay107.certificate2141)]⟩
theorem numericValid854 : certificate854.NumericValid := by decide +kernel
theorem sound854 : certificate854.Sound := rat_failure_budget_sound certificate854 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay106.sound2139,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2140,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2141,List.forall_mem_nil _⟩⟩⟩) numericValid854

def certificate855 : RatFailureBudget := ⟨(20108024706910554078163/500000000000000000),(2386679869861/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay107.certificate2142),(2,CutFailureCertificates.Decay107.certificate2143)]⟩
theorem numericValid855 : certificate855.NumericValid := by decide +kernel
theorem sound855 : certificate855.Sound := rat_failure_budget_sound certificate855 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2142,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2143,List.forall_mem_nil _⟩⟩) numericValid855

def certificate856 : RatFailureBudget := ⟨(20108024706910554078163/500000000000000000),(4472588439023809/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay107.certificate2144),(914,CutFailureCertificates.Decay107.certificate2145),(1,CutFailureCertificates.Decay107.certificate2146)]⟩
theorem numericValid856 : certificate856.NumericValid := by decide +kernel
theorem sound856 : certificate856.Sound := rat_failure_budget_sound certificate856 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2144,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2145,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2146,List.forall_mem_nil _⟩⟩⟩) numericValid856

def certificate857 : RatFailureBudget := ⟨(6822131672314993651691/200000000000000000),(424299933139/25000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay107.certificate2147),(2,CutFailureCertificates.Decay107.certificate2148),(2,CutFailureCertificates.Decay107.certificate2149)]⟩
theorem numericValid857 : certificate857.NumericValid := by decide +kernel
theorem sound857 : certificate857.Sound := rat_failure_budget_sound certificate857 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2147,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2148,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2149,List.forall_mem_nil _⟩⟩⟩) numericValid857

def certificate858 : RatFailureBudget := ⟨(6822131672314993651691/200000000000000000),(525093886331/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay107.certificate2150),(2,CutFailureCertificates.Decay107.certificate2151)]⟩
theorem numericValid858 : certificate858.NumericValid := by decide +kernel
theorem sound858 : certificate858.Sound := rat_failure_budget_sound certificate858 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2150,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2151,List.forall_mem_nil _⟩⟩) numericValid858

def certificate859 : RatFailureBudget := ⟨(6822131672314993651691/200000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay107.certificate2152),(922,CutFailureCertificates.Decay107.certificate2153),(1,CutFailureCertificates.Decay107.certificate2154)]⟩
theorem numericValid859 : certificate859.NumericValid := by decide +kernel
theorem sound859 : certificate859.Sound := rat_failure_budget_sound certificate859 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2152,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2153,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2154,List.forall_mem_nil _⟩⟩⟩) numericValid859

end Cycle12.CutFailureCertificates.Budget042
