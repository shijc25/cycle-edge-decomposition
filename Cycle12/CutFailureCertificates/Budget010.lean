import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay025
import Cycle12.CutFailureCertificates.Decay026
import Cycle12.CutFailureCertificates.Decay027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget010

def certificate200 : RatFailureBudget := ⟨(14684821021866378471/1000000000000000000),(5028274467672051/200000000000000000),(148344594071633741/1000000000000000000),[(2,CutFailureCertificates.Decay025.certificate500),(2,CutFailureCertificates.Decay025.certificate501),(2,CutFailureCertificates.Decay025.certificate502)]⟩
theorem numericValid200 : certificate200.NumericValid := by decide +kernel
theorem sound200 : certificate200.Sound := rat_failure_budget_sound certificate200 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound500,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound501,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound502,List.forall_mem_nil _⟩⟩⟩) numericValid200

def certificate201 : RatFailureBudget := ⟨(14684821021866378471/1000000000000000000),(366721214646767/15625000000000000),(4674308564354431/1000000000000000000),[(2,CutFailureCertificates.Decay025.certificate503),(2,CutFailureCertificates.Decay025.certificate504)]⟩
theorem numericValid201 : certificate201.NumericValid := by decide +kernel
theorem sound201 : certificate201.Sound := rat_failure_budget_sound certificate201 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound503,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound504,List.forall_mem_nil _⟩⟩) numericValid201

def certificate202 : RatFailureBudget := ⟨(7266453255346924291/500000000000000000),(25218634264699189/1000000000000000000),(27253248162066131/1000000000000000000),[(2,CutFailureCertificates.Decay025.certificate505),(2,CutFailureCertificates.Decay025.certificate506),(2,CutFailureCertificates.Decay025.certificate507)]⟩
theorem numericValid202 : certificate202.NumericValid := by decide +kernel
theorem sound202 : certificate202.Sound := rat_failure_budget_sound certificate202 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound505,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound506,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound507,List.forall_mem_nil _⟩⟩⟩) numericValid202

def certificate203 : RatFailureBudget := ⟨(7266453255346924291/500000000000000000),(23615991734710809/1000000000000000000),(122165865806999/62500000000000000),[(2,CutFailureCertificates.Decay025.certificate508),(2,CutFailureCertificates.Decay025.certificate509)]⟩
theorem numericValid203 : certificate203.NumericValid := by decide +kernel
theorem sound203 : certificate203.Sound := rat_failure_budget_sound certificate203 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound508,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound509,List.forall_mem_nil _⟩⟩) numericValid203

def certificate204 : RatFailureBudget := ⟨(14383096214428220263/1000000000000000000),(5092293921271877/200000000000000000),(13921966600243553/500000000000000000),[(2,CutFailureCertificates.Decay025.certificate510),(2,CutFailureCertificates.Decay025.certificate511),(2,CutFailureCertificates.Decay025.certificate512)]⟩
theorem numericValid204 : certificate204.NumericValid := by decide +kernel
theorem sound204 : certificate204.Sound := rat_failure_budget_sound certificate204 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound510,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound511,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound512,List.forall_mem_nil _⟩⟩⟩) numericValid204

def certificate205 : RatFailureBudget := ⟨(14383096214428220263/1000000000000000000),(23821198007354921/1000000000000000000),(1655971521791943/1000000000000000000),[(2,CutFailureCertificates.Decay025.certificate513),(2,CutFailureCertificates.Decay025.certificate514)]⟩
theorem numericValid205 : certificate205.NumericValid := by decide +kernel
theorem sound205 : certificate205.Sound := rat_failure_budget_sound certificate205 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound513,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound514,List.forall_mem_nil _⟩⟩) numericValid205

def certificate206 : RatFailureBudget := ⟨(7117676167741895767/500000000000000000),(25590551318821967/1000000000000000000),(23742661145788637/1000000000000000000),[(2,CutFailureCertificates.Decay025.certificate515),(2,CutFailureCertificates.Decay025.certificate516),(2,CutFailureCertificates.Decay025.certificate517)]⟩
theorem numericValid206 : certificate206.NumericValid := by decide +kernel
theorem sound206 : certificate206.Sound := rat_failure_budget_sound certificate206 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound515,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound516,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound517,List.forall_mem_nil _⟩⟩⟩) numericValid206

def certificate207 : RatFailureBudget := ⟨(7117676167741895767/500000000000000000),(2998251684220911/125000000000000000),(148168520381253/100000000000000000),[(2,CutFailureCertificates.Decay025.certificate518),(2,CutFailureCertificates.Decay025.certificate519)]⟩
theorem numericValid207 : certificate207.NumericValid := by decide +kernel
theorem sound207 : certificate207.Sound := rat_failure_budget_sound certificate207 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound518,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay025.sound519,List.forall_mem_nil _⟩⟩) numericValid207

def certificate208 : RatFailureBudget := ⟨(1408963791382908709/100000000000000000),(5146805500410207/200000000000000000),(21469436124441403/1000000000000000000),[(2,CutFailureCertificates.Decay026.certificate520),(2,CutFailureCertificates.Decay026.certificate521),(2,CutFailureCertificates.Decay026.certificate522)]⟩
theorem numericValid208 : certificate208.NumericValid := by decide +kernel
theorem sound208 : certificate208.Sound := rat_failure_budget_sound certificate208 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound520,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound521,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound522,List.forall_mem_nil _⟩⟩⟩) numericValid208

def certificate209 : RatFailureBudget := ⟨(1408963791382908709/100000000000000000),(24141456833076291/1000000000000000000),(1265212282780211/1000000000000000000),[(2,CutFailureCertificates.Decay026.certificate523),(2,CutFailureCertificates.Decay026.certificate524)]⟩
theorem numericValid209 : certificate209.NumericValid := by decide +kernel
theorem sound209 : certificate209.Sound := rat_failure_budget_sound certificate209 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound523,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound524,List.forall_mem_nil _⟩⟩) numericValid209

def certificate210 : RatFailureBudget := ⟨(13945916804907706299/1000000000000000000),(12967204058596549/500000000000000000),(20946627575131577/1000000000000000000),[(2,CutFailureCertificates.Decay026.certificate525),(2,CutFailureCertificates.Decay026.certificate526),(2,CutFailureCertificates.Decay026.certificate527)]⟩
theorem numericValid210 : certificate210.NumericValid := by decide +kernel
theorem sound210 : certificate210.Sound := rat_failure_budget_sound certificate210 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound525,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound526,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound527,List.forall_mem_nil _⟩⟩⟩) numericValid210

def certificate211 : RatFailureBudget := ⟨(13945916804907706299/1000000000000000000),(12180050293336571/500000000000000000),(1076509741951227/1000000000000000000),[(2,CutFailureCertificates.Decay026.certificate528),(2,CutFailureCertificates.Decay026.certificate529)]⟩
theorem numericValid211 : certificate211.NumericValid := by decide +kernel
theorem sound211 : certificate211.Sound := rat_failure_budget_sound certificate211 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound528,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound529,List.forall_mem_nil _⟩⟩) numericValid211

def certificate212 : RatFailureBudget := ⟨(13874792665248591837/1000000000000000000),(6503243057320883/250000000000000000),(8712824182076413/500000000000000000),[(2,CutFailureCertificates.Decay026.certificate530),(2,CutFailureCertificates.Decay026.certificate531),(2,CutFailureCertificates.Decay026.certificate532)]⟩
theorem numericValid212 : certificate212.NumericValid := by decide +kernel
theorem sound212 : certificate212.Sound := rat_failure_budget_sound certificate212 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound530,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound531,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound532,List.forall_mem_nil _⟩⟩⟩) numericValid212

def certificate213 : RatFailureBudget := ⟨(13874792665248591837/1000000000000000000),(12192356822380207/500000000000000000),(24341567207479/31250000000000000),[(2,CutFailureCertificates.Decay026.certificate533),(2,CutFailureCertificates.Decay026.certificate534)]⟩
theorem numericValid213 : certificate213.NumericValid := by decide +kernel
theorem sound213 : certificate213.Sound := rat_failure_budget_sound certificate213 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound533,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound534,List.forall_mem_nil _⟩⟩) numericValid213

def certificate214 : RatFailureBudget := ⟨(13804153658233638553/1000000000000000000),(2604106471810297/100000000000000000),(16118535353508493/1000000000000000000),[(2,CutFailureCertificates.Decay026.certificate535),(2,CutFailureCertificates.Decay026.certificate536),(2,CutFailureCertificates.Decay026.certificate537)]⟩
theorem numericValid214 : certificate214.NumericValid := by decide +kernel
theorem sound214 : certificate214.Sound := rat_failure_budget_sound certificate214 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound535,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound536,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound537,List.forall_mem_nil _⟩⟩⟩) numericValid214

def certificate215 : RatFailureBudget := ⟨(13804153658233638553/1000000000000000000),(24461580055877939/1000000000000000000),(174840773717287/250000000000000000),[(2,CutFailureCertificates.Decay026.certificate538),(2,CutFailureCertificates.Decay026.certificate539)]⟩
theorem numericValid215 : certificate215.NumericValid := by decide +kernel
theorem sound215 : certificate215.Sound := rat_failure_budget_sound certificate215 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound538,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay026.sound539,List.forall_mem_nil _⟩⟩) numericValid215

def certificate216 : RatFailureBudget := ⟨(13664313896637635951/1000000000000000000),(2646066731925093/100000000000000000),(10182692485787501/500000000000000000),[(2,CutFailureCertificates.Decay027.certificate540),(2,CutFailureCertificates.Decay027.certificate541),(2,CutFailureCertificates.Decay027.certificate542)]⟩
theorem numericValid216 : certificate216.NumericValid := by decide +kernel
theorem sound216 : certificate216.Sound := rat_failure_budget_sound certificate216 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound540,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound541,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound542,List.forall_mem_nil _⟩⟩⟩) numericValid216

def certificate217 : RatFailureBudget := ⟨(13664313896637635951/1000000000000000000),(12369596294491491/500000000000000000),(3954586167556437/1000000000000000000),[(2,CutFailureCertificates.Decay027.certificate543),(2,CutFailureCertificates.Decay027.certificate544)]⟩
theorem numericValid217 : certificate217.NumericValid := by decide +kernel
theorem sound217 : certificate217.Sound := rat_failure_budget_sound certificate217 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound543,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound544,List.forall_mem_nil _⟩⟩) numericValid217

def certificate218 : RatFailureBudget := ⟨(6763181848071071287/500000000000000000),(26468476551133621/1000000000000000000),(7786797520615079/500000000000000000),[(2,CutFailureCertificates.Decay027.certificate545),(2,CutFailureCertificates.Decay027.certificate546),(2,CutFailureCertificates.Decay027.certificate547)]⟩
theorem numericValid218 : certificate218.NumericValid := by decide +kernel
theorem sound218 : certificate218.Sound := rat_failure_budget_sound certificate218 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound545,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound546,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound547,List.forall_mem_nil _⟩⟩⟩) numericValid218

def certificate219 : RatFailureBudget := ⟨(6763181848071071287/500000000000000000),(1244630110326721/50000000000000000),(1676582104139289/500000000000000000),[(2,CutFailureCertificates.Decay027.certificate548),(2,CutFailureCertificates.Decay027.certificate549)]⟩
theorem numericValid219 : certificate219.NumericValid := by decide +kernel
theorem sound219 : certificate219.Sound := rat_failure_budget_sound certificate219 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound548,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound549,List.forall_mem_nil _⟩⟩) numericValid219

end Cycle12.CutFailureCertificates.Budget010
