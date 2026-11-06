import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay102
import Cycle12.CutFailureCertificates.Decay103
import Cycle12.CutFailureCertificates.Decay104
import Cycle12.CutFailureCertificates.Decay105

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget041

def certificate820 : RatFailureBudget := ⟨(198806338180814466443/1000000000000000000),(274313083295999/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay102.certificate2050),(2,CutFailureCertificates.Decay102.certificate2051),(2,CutFailureCertificates.Decay102.certificate2052)]⟩
theorem numericValid820 : certificate820.NumericValid := by decide +kernel
theorem sound820 : certificate820.Sound := rat_failure_budget_sound certificate820 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2050,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2051,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2052,List.forall_mem_nil _⟩⟩⟩) numericValid820

def certificate821 : RatFailureBudget := ⟨(198806338180814466443/1000000000000000000),(1463921096076593/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay102.certificate2053),(2,CutFailureCertificates.Decay102.certificate2054)]⟩
theorem numericValid821 : certificate821.NumericValid := by decide +kernel
theorem sound821 : certificate821.Sound := rat_failure_budget_sound certificate821 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2053,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2054,List.forall_mem_nil _⟩⟩) numericValid821

def certificate822 : RatFailureBudget := ⟨(24400471323788476259/125000000000000000),(1385470429830729/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay102.certificate2055),(2,CutFailureCertificates.Decay102.certificate2056),(2,CutFailureCertificates.Decay102.certificate2057)]⟩
theorem numericValid822 : certificate822.NumericValid := by decide +kernel
theorem sound822 : certificate822.Sound := rat_failure_budget_sound certificate822 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2055,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2056,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2057,List.forall_mem_nil _⟩⟩⟩) numericValid822

def certificate823 : RatFailureBudget := ⟨(24400471323788476259/125000000000000000),(591466382040387/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay102.certificate2058),(2,CutFailureCertificates.Decay102.certificate2059)]⟩
theorem numericValid823 : certificate823.NumericValid := by decide +kernel
theorem sound823 : certificate823.Sound := rat_failure_budget_sound certificate823 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2058,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2059,List.forall_mem_nil _⟩⟩) numericValid823

def certificate824 : RatFailureBudget := ⟨(191686014252223588973/1000000000000000000),(699602187558669/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay103.certificate2060),(2,CutFailureCertificates.Decay103.certificate2061),(2,CutFailureCertificates.Decay103.certificate2062)]⟩
theorem numericValid824 : certificate824.NumericValid := by decide +kernel
theorem sound824 : certificate824.Sound := rat_failure_budget_sound certificate824 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2060,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2061,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2062,List.forall_mem_nil _⟩⟩⟩) numericValid824

def certificate825 : RatFailureBudget := ⟨(191686014252223588973/1000000000000000000),(2993881074271997/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay103.certificate2063),(2,CutFailureCertificates.Decay103.certificate2064)]⟩
theorem numericValid825 : certificate825.NumericValid := by decide +kernel
theorem sound825 : certificate825.Sound := rat_failure_budget_sound certificate825 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2063,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2064,List.forall_mem_nil _⟩⟩) numericValid825

def certificate826 : RatFailureBudget := ⟨(94125250331974770191/500000000000000000),(1413808574566189/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay103.certificate2065),(2,CutFailureCertificates.Decay103.certificate2066),(2,CutFailureCertificates.Decay103.certificate2067)]⟩
theorem numericValid826 : certificate826.NumericValid := by decide +kernel
theorem sound826 : certificate826.Sound := rat_failure_budget_sound certificate826 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2065,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2066,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2067,List.forall_mem_nil _⟩⟩⟩) numericValid826

def certificate827 : RatFailureBudget := ⟨(94125250331974770191/500000000000000000),(3023716355766787/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay103.certificate2068),(2,CutFailureCertificates.Decay103.certificate2069)]⟩
theorem numericValid827 : certificate827.NumericValid := by decide +kernel
theorem sound827 : certificate827.Sound := rat_failure_budget_sound certificate827 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2068,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2069,List.forall_mem_nil _⟩⟩) numericValid827

def certificate828 : RatFailureBudget := ⟨(92447378412680925593/500000000000000000),(357127350786513/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay103.certificate2070),(2,CutFailureCertificates.Decay103.certificate2071),(2,CutFailureCertificates.Decay103.certificate2072)]⟩
theorem numericValid828 : certificate828.NumericValid := by decide +kernel
theorem sound828 : certificate828.Sound := rat_failure_budget_sound certificate828 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2070,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2071,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2072,List.forall_mem_nil _⟩⟩⟩) numericValid828

def certificate829 : RatFailureBudget := ⟨(92447378412680925593/500000000000000000),(1530481704827463/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay103.certificate2073),(2,CutFailureCertificates.Decay103.certificate2074)]⟩
theorem numericValid829 : certificate829.NumericValid := by decide +kernel
theorem sound829 : certificate829.Sound := rat_failure_budget_sound certificate829 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2073,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2074,List.forall_mem_nil _⟩⟩) numericValid829

def certificate830 : RatFailureBudget := ⟨(75016018916683844152359/200000000000000000),(1029582822243/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay103.certificate2075),(2,CutFailureCertificates.Decay103.certificate2076),(2,CutFailureCertificates.Decay103.certificate2077)]⟩
theorem numericValid830 : certificate830.NumericValid := by decide +kernel
theorem sound830 : certificate830.Sound := rat_failure_budget_sound certificate830 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2075,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2076,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2077,List.forall_mem_nil _⟩⟩⟩) numericValid830

def certificate831 : RatFailureBudget := ⟨(75016018916683844152359/200000000000000000),(2200155247/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay103.certificate2078),(2,CutFailureCertificates.Decay103.certificate2079)]⟩
theorem numericValid831 : certificate831.NumericValid := by decide +kernel
theorem sound831 : certificate831.Sound := rat_failure_budget_sound certificate831 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2078,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay103.sound2079,List.forall_mem_nil _⟩⟩) numericValid831

def certificate832 : RatFailureBudget := ⟨(75016018916683844152359/200000000000000000),(4472621967974437/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay104.certificate2080),(912,CutFailureCertificates.Decay104.certificate2081),(1,CutFailureCertificates.Decay104.certificate2082)]⟩
theorem numericValid832 : certificate832.NumericValid := by decide +kernel
theorem sound832 : certificate832.Sound := rat_failure_budget_sound certificate832 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2080,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2081,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2082,List.forall_mem_nil _⟩⟩⟩) numericValid832

def certificate833 : RatFailureBudget := ⟨(47800972580928223399921/200000000000000000),(8076206893041/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay104.certificate2083),(2,CutFailureCertificates.Decay104.certificate2084),(2,CutFailureCertificates.Decay104.certificate2085)]⟩
theorem numericValid833 : certificate833.NumericValid := by decide +kernel
theorem sound833 : certificate833.Sound := rat_failure_budget_sound certificate833 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2083,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2084,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2085,List.forall_mem_nil _⟩⟩⟩) numericValid833

def certificate834 : RatFailureBudget := ⟨(47800972580928223399921/200000000000000000),(698391402767/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay104.certificate2086),(2,CutFailureCertificates.Decay104.certificate2087)]⟩
theorem numericValid834 : certificate834.NumericValid := by decide +kernel
theorem sound834 : certificate834.Sound := rat_failure_budget_sound certificate834 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2086,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2087,List.forall_mem_nil _⟩⟩) numericValid834

def certificate835 : RatFailureBudget := ⟨(47800972580928223399921/200000000000000000),(2320559867244761/500000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay104.certificate2088),(912,CutFailureCertificates.Decay104.certificate2089),(1,CutFailureCertificates.Decay104.certificate2090)]⟩
theorem numericValid835 : certificate835.NumericValid := by decide +kernel
theorem sound835 : certificate835.Sound := rat_failure_budget_sound certificate835 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2088,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2089,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2090,List.forall_mem_nil _⟩⟩⟩) numericValid835

def certificate836 : RatFailureBudget := ⟨(82624014196148766232829/500000000000000000),(115680839549/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay104.certificate2091),(2,CutFailureCertificates.Decay104.certificate2092),(2,CutFailureCertificates.Decay104.certificate2093)]⟩
theorem numericValid836 : certificate836.NumericValid := by decide +kernel
theorem sound836 : certificate836.Sound := rat_failure_budget_sound certificate836 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2091,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2092,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2093,List.forall_mem_nil _⟩⟩⟩) numericValid836

def certificate837 : RatFailureBudget := ⟨(82624014196148766232829/500000000000000000),(6646013965709/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay104.certificate2094),(2,CutFailureCertificates.Decay104.certificate2095)]⟩
theorem numericValid837 : certificate837.NumericValid := by decide +kernel
theorem sound837 : certificate837.Sound := rat_failure_budget_sound certificate837 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2094,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2095,List.forall_mem_nil _⟩⟩) numericValid837

def certificate838 : RatFailureBudget := ⟨(82624014196148766232829/500000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay104.certificate2096),(912,CutFailureCertificates.Decay104.certificate2097),(1,CutFailureCertificates.Decay104.certificate2098)]⟩
theorem numericValid838 : certificate838.NumericValid := by decide +kernel
theorem sound838 : certificate838.Sound := rat_failure_budget_sound certificate838 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2096,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2097,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2098,List.forall_mem_nil _⟩⟩⟩) numericValid838

def certificate839 : RatFailureBudget := ⟨(120871515643124418446001/1000000000000000000),(10273419566273/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay104.certificate2099),(2,CutFailureCertificates.Decay105.certificate2100),(2,CutFailureCertificates.Decay105.certificate2101)]⟩
theorem numericValid839 : certificate839.NumericValid := by decide +kernel
theorem sound839 : certificate839.Sound := rat_failure_budget_sound certificate839 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay104.sound2099,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2100,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay105.sound2101,List.forall_mem_nil _⟩⟩⟩) numericValid839

end Cycle12.CutFailureCertificates.Budget041
