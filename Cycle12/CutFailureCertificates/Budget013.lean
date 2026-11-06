import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay032
import Cycle12.CutFailureCertificates.Decay033
import Cycle12.CutFailureCertificates.Decay034

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget013

def certificate260 : RatFailureBudget := ⟨(2832962528370347873/250000000000000000),(30291525989796289/1000000000000000000),(785608428359087/250000000000000000),[(2,CutFailureCertificates.Decay032.certificate650),(2,CutFailureCertificates.Decay032.certificate651),(2,CutFailureCertificates.Decay032.certificate652)]⟩
theorem numericValid260 : certificate260.NumericValid := by decide +kernel
theorem sound260 : certificate260.Sound := rat_failure_budget_sound certificate260 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound650,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound651,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound652,List.forall_mem_nil _⟩⟩⟩) numericValid260

def certificate261 : RatFailureBudget := ⟨(2832962528370347873/250000000000000000),(7130119695795749/250000000000000000),(3084949986151703/1000000000000000000),[(2,CutFailureCertificates.Decay032.certificate653),(2,CutFailureCertificates.Decay032.certificate654)]⟩
theorem numericValid261 : certificate261.NumericValid := by decide +kernel
theorem sound261 : certificate261.Sound := rat_failure_budget_sound certificate261 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound653,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound654,List.forall_mem_nil _⟩⟩) numericValid261

def certificate262 : RatFailureBudget := ⟨(5638939790275060547/500000000000000000),(7576178563321169/250000000000000000),(2833667920958617/1000000000000000000),[(2,CutFailureCertificates.Decay032.certificate655),(2,CutFailureCertificates.Decay032.certificate656),(2,CutFailureCertificates.Decay032.certificate657)]⟩
theorem numericValid262 : certificate262.NumericValid := by decide +kernel
theorem sound262 : certificate262.Sound := rat_failure_budget_sound certificate262 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound655,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound656,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound657,List.forall_mem_nil _⟩⟩⟩) numericValid262

def certificate263 : RatFailureBudget := ⟨(5638939790275060547/500000000000000000),(3578580873886007/125000000000000000),(2710271986752631/1000000000000000000),[(2,CutFailureCertificates.Decay032.certificate658),(2,CutFailureCertificates.Decay032.certificate659)]⟩
theorem numericValid263 : certificate263.NumericValid := by decide +kernel
theorem sound263 : certificate263.Sound := rat_failure_budget_sound certificate263 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound658,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound659,List.forall_mem_nil _⟩⟩) numericValid263

def certificate264 : RatFailureBudget := ⟨(1122424805136893381/100000000000000000),(30616142402348993/1000000000000000000),(1421391607282541/500000000000000000),[(2,CutFailureCertificates.Decay033.certificate660),(2,CutFailureCertificates.Decay033.certificate661),(2,CutFailureCertificates.Decay033.certificate662)]⟩
theorem numericValid264 : certificate264.NumericValid := by decide +kernel
theorem sound264 : certificate264.Sound := rat_failure_budget_sound certificate264 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound660,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound661,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound662,List.forall_mem_nil _⟩⟩⟩) numericValid264

def certificate265 : RatFailureBudget := ⟨(1122424805136893381/100000000000000000),(28803845436301819/1000000000000000000),(1050119442482301/500000000000000000),[(2,CutFailureCertificates.Decay033.certificate663),(2,CutFailureCertificates.Decay033.certificate664)]⟩
theorem numericValid265 : certificate265.NumericValid := by decide +kernel
theorem sound265 : certificate265.Sound := rat_failure_budget_sound certificate265 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound663,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound664,List.forall_mem_nil _⟩⟩) numericValid265

def certificate266 : RatFailureBudget := ⟨(11117990995896675357/1000000000000000000),(30838376212078659/1000000000000000000),(1458218777384333/500000000000000000),[(2,CutFailureCertificates.Decay033.certificate665),(2,CutFailureCertificates.Decay033.certificate666),(2,CutFailureCertificates.Decay033.certificate667)]⟩
theorem numericValid266 : certificate266.NumericValid := by decide +kernel
theorem sound266 : certificate266.Sound := rat_failure_budget_sound certificate266 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound665,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound666,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound667,List.forall_mem_nil _⟩⟩⟩) numericValid266

def certificate267 : RatFailureBudget := ⟨(11117990995896675357/1000000000000000000),(14519725097961717/500000000000000000),(2163141033497481/1000000000000000000),[(2,CutFailureCertificates.Decay033.certificate668),(2,CutFailureCertificates.Decay033.certificate669)]⟩
theorem numericValid267 : certificate267.NumericValid := by decide +kernel
theorem sound267 : certificate267.Sound := rat_failure_budget_sound certificate267 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound668,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound669,List.forall_mem_nil _⟩⟩) numericValid267

def certificate268 : RatFailureBudget := ⟨(11065360034428862023/1000000000000000000),(15494723650197061/500000000000000000),(2636086248443891/1000000000000000000),[(2,CutFailureCertificates.Decay033.certificate670),(2,CutFailureCertificates.Decay033.certificate671),(2,CutFailureCertificates.Decay033.certificate672)]⟩
theorem numericValid268 : certificate268.NumericValid := by decide +kernel
theorem sound268 : certificate268.Sound := rat_failure_budget_sound certificate268 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound670,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound671,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound672,List.forall_mem_nil _⟩⟩⟩) numericValid268

def certificate269 : RatFailureBudget := ⟨(11065360034428862023/1000000000000000000),(1815263702251351/62500000000000000),(1507701889894239/1000000000000000000),[(2,CutFailureCertificates.Decay033.certificate673),(2,CutFailureCertificates.Decay033.certificate674)]⟩
theorem numericValid269 : certificate269.NumericValid := by decide +kernel
theorem sound269 : certificate269.Sound := rat_failure_budget_sound certificate269 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound673,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound674,List.forall_mem_nil _⟩⟩) numericValid269

def certificate270 : RatFailureBudget := ⟨(11013057205697723371/1000000000000000000),(31049070486031229/1000000000000000000),(2416117298791193/1000000000000000000),[(2,CutFailureCertificates.Decay033.certificate675),(2,CutFailureCertificates.Decay033.certificate676),(2,CutFailureCertificates.Decay033.certificate677)]⟩
theorem numericValid270 : certificate270.NumericValid := by decide +kernel
theorem sound270 : certificate270.Sound := rat_failure_budget_sound certificate270 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound675,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound676,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound677,List.forall_mem_nil _⟩⟩⟩) numericValid270

def certificate271 : RatFailureBudget := ⟨(11013057205697723371/1000000000000000000),(14557486479873161/500000000000000000),(4351051851396743/1000000000000000000),[(2,CutFailureCertificates.Decay033.certificate678),(2,CutFailureCertificates.Decay033.certificate679)]⟩
theorem numericValid271 : certificate271.NumericValid := by decide +kernel
theorem sound271 : certificate271.Sound := rat_failure_budget_sound certificate271 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound678,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay033.sound679,List.forall_mem_nil _⟩⟩) numericValid271

def certificate272 : RatFailureBudget := ⟨(2727356343157655291/250000000000000000),(30963835839472083/1000000000000000000),(2170442115709141/1000000000000000000),[(2,CutFailureCertificates.Decay034.certificate680),(2,CutFailureCertificates.Decay034.certificate681),(2,CutFailureCertificates.Decay034.certificate682)]⟩
theorem numericValid272 : certificate272.NumericValid := by decide +kernel
theorem sound272 : certificate272.Sound := rat_failure_budget_sound certificate272 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound680,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound681,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound682,List.forall_mem_nil _⟩⟩⟩) numericValid272

def certificate273 : RatFailureBudget := ⟨(2727356343157655291/250000000000000000),(29371294271169597/1000000000000000000),(4382904484110019/1000000000000000000),[(2,CutFailureCertificates.Decay034.certificate683),(2,CutFailureCertificates.Decay034.certificate684)]⟩
theorem numericValid273 : certificate273.NumericValid := by decide +kernel
theorem sound273 : certificate273.Sound := rat_failure_budget_sound certificate273 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound683,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound684,List.forall_mem_nil _⟩⟩) numericValid273

def certificate274 : RatFailureBudget := ⟨(2171618229430897931/200000000000000000),(980683411100743/31250000000000000),(2104966345237359/1000000000000000000),[(2,CutFailureCertificates.Decay034.certificate685),(2,CutFailureCertificates.Decay034.certificate686),(2,CutFailureCertificates.Decay034.certificate687)]⟩
theorem numericValid274 : certificate274.NumericValid := by decide +kernel
theorem sound274 : certificate274.Sound := rat_failure_budget_sound certificate274 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound685,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound686,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound687,List.forall_mem_nil _⟩⟩⟩) numericValid274

def certificate275 : RatFailureBudget := ⟨(2171618229430897931/200000000000000000),(5881430111439521/200000000000000000),(298985515615569/100000000000000000),[(2,CutFailureCertificates.Decay034.certificate688),(2,CutFailureCertificates.Decay034.certificate689)]⟩
theorem numericValid275 : certificate275.NumericValid := by decide +kernel
theorem sound275 : certificate275.Sound := rat_failure_budget_sound certificate275 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound688,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound689,List.forall_mem_nil _⟩⟩) numericValid275

def certificate276 : RatFailureBudget := ⟨(2701768652877649923/250000000000000000),(485346966500233/15625000000000000),(860383611522823/500000000000000000),[(2,CutFailureCertificates.Decay034.certificate690),(2,CutFailureCertificates.Decay034.certificate691),(2,CutFailureCertificates.Decay034.certificate692)]⟩
theorem numericValid276 : certificate276.NumericValid := by decide +kernel
theorem sound276 : certificate276.Sound := rat_failure_budget_sound certificate276 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound690,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound691,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound692,List.forall_mem_nil _⟩⟩⟩) numericValid276

def certificate277 : RatFailureBudget := ⟨(2701768652877649923/250000000000000000),(2940269084373931/100000000000000000),(317968805841983/125000000000000000),[(2,CutFailureCertificates.Decay034.certificate693),(2,CutFailureCertificates.Decay034.certificate694)]⟩
theorem numericValid277 : certificate277.NumericValid := by decide +kernel
theorem sound277 : certificate277.Sound := rat_failure_budget_sound certificate277 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound693,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound694,List.forall_mem_nil _⟩⟩) numericValid277

def certificate278 : RatFailureBudget := ⟨(2151274643899885449/200000000000000000),(31210276662705533/1000000000000000000),(171967478838647/100000000000000000),[(2,CutFailureCertificates.Decay034.certificate695),(2,CutFailureCertificates.Decay034.certificate696),(2,CutFailureCertificates.Decay034.certificate697)]⟩
theorem numericValid278 : certificate278.NumericValid := by decide +kernel
theorem sound278 : certificate278.Sound := rat_failure_budget_sound certificate278 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound695,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound696,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound697,List.forall_mem_nil _⟩⟩⟩) numericValid278

def certificate279 : RatFailureBudget := ⟨(2151274643899885449/200000000000000000),(29482887897810429/1000000000000000000),(1110421085119533/500000000000000000),[(2,CutFailureCertificates.Decay034.certificate698),(2,CutFailureCertificates.Decay034.certificate699)]⟩
theorem numericValid279 : certificate279.NumericValid := by decide +kernel
theorem sound279 : certificate279.Sound := rat_failure_budget_sound certificate279 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound698,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay034.sound699,List.forall_mem_nil _⟩⟩) numericValid279

end Cycle12.CutFailureCertificates.Budget013
