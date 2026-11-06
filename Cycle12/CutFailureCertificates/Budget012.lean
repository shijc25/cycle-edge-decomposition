import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay030
import Cycle12.CutFailureCertificates.Decay031
import Cycle12.CutFailureCertificates.Decay032

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget012

def certificate240 : RatFailureBudget := ⟨(1212464700727096087/100000000000000000),(28917786350355347/1000000000000000000),(5360025793519239/200000000000000000),[(2,CutFailureCertificates.Decay030.certificate600),(2,CutFailureCertificates.Decay030.certificate601),(2,CutFailureCertificates.Decay030.certificate602)]⟩
theorem numericValid240 : certificate240.NumericValid := by decide +kernel
theorem sound240 : certificate240.Sound := rat_failure_budget_sound certificate240 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound600,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound601,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound602,List.forall_mem_nil _⟩⟩⟩) numericValid240

def certificate241 : RatFailureBudget := ⟨(1212464700727096087/100000000000000000),(26872524020008929/1000000000000000000),(756621078597811/250000000000000000),[(2,CutFailureCertificates.Decay030.certificate603),(2,CutFailureCertificates.Decay030.certificate604)]⟩
theorem numericValid241 : certificate241.NumericValid := by decide +kernel
theorem sound241 : certificate241.Sound := rat_failure_budget_sound certificate241 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound603,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound604,List.forall_mem_nil _⟩⟩) numericValid241

def certificate242 : RatFailureBudget := ⟨(12006982453999286597/1000000000000000000),(3639192115339577/125000000000000000),(5328735134978777/250000000000000000),[(2,CutFailureCertificates.Decay030.certificate605),(2,CutFailureCertificates.Decay030.certificate606),(2,CutFailureCertificates.Decay030.certificate607)]⟩
theorem numericValid242 : certificate242.NumericValid := by decide +kernel
theorem sound242 : certificate242.Sound := rat_failure_budget_sound certificate242 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound605,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound606,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound607,List.forall_mem_nil _⟩⟩⟩) numericValid242

def certificate243 : RatFailureBudget := ⟨(12006982453999286597/1000000000000000000),(27125157044855739/1000000000000000000),(2624984766633769/1000000000000000000),[(2,CutFailureCertificates.Decay030.certificate608),(2,CutFailureCertificates.Decay030.certificate609)]⟩
theorem numericValid243 : certificate243.NumericValid := by decide +kernel
theorem sound243 : certificate243.Sound := rat_failure_budget_sound certificate243 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound608,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound609,List.forall_mem_nil _⟩⟩) numericValid243

def certificate244 : RatFailureBudget := ⟨(11890828153437861019/1000000000000000000),(29396355528534017/1000000000000000000),(5217891222380287/1000000000000000000),[(2,CutFailureCertificates.Decay030.certificate610),(2,CutFailureCertificates.Decay030.certificate611),(2,CutFailureCertificates.Decay030.certificate612)]⟩
theorem numericValid244 : certificate244.NumericValid := by decide +kernel
theorem sound244 : certificate244.Sound := rat_failure_budget_sound certificate244 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound610,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound611,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound612,List.forall_mem_nil _⟩⟩⟩) numericValid244

def certificate245 : RatFailureBudget := ⟨(11890828153437861019/1000000000000000000),(5463802587943103/200000000000000000),(978774180243683/500000000000000000),[(2,CutFailureCertificates.Decay030.certificate613),(2,CutFailureCertificates.Decay030.certificate614)]⟩
theorem numericValid245 : certificate245.NumericValid := by decide +kernel
theorem sound245 : certificate245.Sound := rat_failure_budget_sound certificate245 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound613,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound614,List.forall_mem_nil _⟩⟩) numericValid245

def certificate246 : RatFailureBudget := ⟨(368004969325543779/31250000000000000),(236953733842873/8000000000000000),(5294614988506619/1000000000000000000),[(2,CutFailureCertificates.Decay030.certificate615),(2,CutFailureCertificates.Decay030.certificate616),(2,CutFailureCertificates.Decay030.certificate617)]⟩
theorem numericValid246 : certificate246.NumericValid := by decide +kernel
theorem sound246 : certificate246.Sound := rat_failure_budget_sound certificate246 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound615,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound616,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound617,List.forall_mem_nil _⟩⟩⟩) numericValid246

def certificate247 : RatFailureBudget := ⟨(368004969325543779/31250000000000000),(3444524103930529/125000000000000000),(1678292930650577/1000000000000000000),[(2,CutFailureCertificates.Decay030.certificate618),(2,CutFailureCertificates.Decay030.certificate619)]⟩
theorem numericValid247 : certificate247.NumericValid := by decide +kernel
theorem sound247 : certificate247.Sound := rat_failure_budget_sound certificate247 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound618,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay030.sound619,List.forall_mem_nil _⟩⟩) numericValid247

def certificate248 : RatFailureBudget := ⟨(2343874737817172533/200000000000000000),(29730512413409871/1000000000000000000),(2292893109792671/500000000000000000),[(2,CutFailureCertificates.Decay031.certificate620),(2,CutFailureCertificates.Decay031.certificate621),(2,CutFailureCertificates.Decay031.certificate622)]⟩
theorem numericValid248 : certificate248.NumericValid := by decide +kernel
theorem sound248 : certificate248.Sound := rat_failure_budget_sound certificate248 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound620,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound621,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound622,List.forall_mem_nil _⟩⟩⟩) numericValid248

def certificate249 : RatFailureBudget := ⟨(2343874737817172533/200000000000000000),(689053908214463/25000000000000000),(1214106670677701/250000000000000000),[(2,CutFailureCertificates.Decay031.certificate623),(2,CutFailureCertificates.Decay031.certificate624)]⟩
theorem numericValid249 : certificate249.NumericValid := by decide +kernel
theorem sound249 : certificate249.Sound := rat_failure_budget_sound certificate249 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound623,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound624,List.forall_mem_nil _⟩⟩) numericValid249

def certificate250 : RatFailureBudget := ⟨(2915737618896080953/250000000000000000),(5941564158489577/200000000000000000),(2007019245373791/500000000000000000),[(2,CutFailureCertificates.Decay031.certificate625),(2,CutFailureCertificates.Decay031.certificate626),(2,CutFailureCertificates.Decay031.certificate627)]⟩
theorem numericValid250 : certificate250.NumericValid := by decide +kernel
theorem sound250 : certificate250.Sound := rat_failure_budget_sound certificate250 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound625,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound626,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound627,List.forall_mem_nil _⟩⟩⟩) numericValid250

def certificate251 : RatFailureBudget := ⟨(2915737618896080953/250000000000000000),(13818837706470863/500000000000000000),(174480580796219/40000000000000000),[(2,CutFailureCertificates.Decay031.certificate628),(2,CutFailureCertificates.Decay031.certificate629)]⟩
theorem numericValid251 : certificate251.NumericValid := by decide +kernel
theorem sound251 : certificate251.Sound := rat_failure_budget_sound certificate251 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound628,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound629,List.forall_mem_nil _⟩⟩) numericValid251

def certificate252 : RatFailureBudget := ⟨(2887794613220535943/250000000000000000),(29910303191367569/1000000000000000000),(63132600808757/15625000000000000),[(2,CutFailureCertificates.Decay031.certificate630),(2,CutFailureCertificates.Decay031.certificate631),(2,CutFailureCertificates.Decay031.certificate632)]⟩
theorem numericValid252 : certificate252.NumericValid := by decide +kernel
theorem sound252 : certificate252.Sound := rat_failure_budget_sound certificate252 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound630,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound631,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound632,List.forall_mem_nil _⟩⟩⟩) numericValid252

def certificate253 : RatFailureBudget := ⟨(2887794613220535943/250000000000000000),(6985786770575683/250000000000000000),(149851644167319/31250000000000000),[(2,CutFailureCertificates.Decay031.certificate633),(2,CutFailureCertificates.Decay031.certificate634)]⟩
theorem numericValid253 : certificate253.NumericValid := by decide +kernel
theorem sound253 : certificate253.Sound := rat_failure_budget_sound certificate253 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound633,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound634,List.forall_mem_nil _⟩⟩) numericValid253

def certificate254 : RatFailureBudget := ⟨(11495823748135086563/1000000000000000000),(15076940125023649/500000000000000000),(3868078538729253/1000000000000000000),[(2,CutFailureCertificates.Decay031.certificate635),(2,CutFailureCertificates.Decay031.certificate636),(2,CutFailureCertificates.Decay031.certificate637)]⟩
theorem numericValid254 : certificate254.NumericValid := by decide +kernel
theorem sound254 : certificate254.Sound := rat_failure_budget_sound certificate254 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound635,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound636,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound637,List.forall_mem_nil _⟩⟩⟩) numericValid254

def certificate255 : RatFailureBudget := ⟨(11495823748135086563/1000000000000000000),(13982977839065777/500000000000000000),(3438814525641999/1000000000000000000),[(2,CutFailureCertificates.Decay031.certificate638),(2,CutFailureCertificates.Decay031.certificate639)]⟩
theorem numericValid255 : certificate255.NumericValid := by decide +kernel
theorem sound255 : certificate255.Sound := rat_failure_budget_sound certificate255 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound638,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay031.sound639,List.forall_mem_nil _⟩⟩) numericValid255

def certificate256 : RatFailureBudget := ⟨(2288163873477269037/200000000000000000),(6983974771081411/250000000000000000),(133112281103531/40000000000000000),[(2,CutFailureCertificates.Decay032.certificate640),(2,CutFailureCertificates.Decay032.certificate641),(2,CutFailureCertificates.Decay032.certificate642)]⟩
theorem numericValid256 : certificate256.NumericValid := by decide +kernel
theorem sound256 : certificate256.Sound := rat_failure_budget_sound certificate256 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound640,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound641,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound642,List.forall_mem_nil _⟩⟩⟩) numericValid256

def certificate257 : RatFailureBudget := ⟨(2288163873477269037/200000000000000000),(1122334344014411/40000000000000000),(796146333053739/250000000000000000),[(2,CutFailureCertificates.Decay032.certificate643),(2,CutFailureCertificates.Decay032.certificate644)]⟩
theorem numericValid257 : certificate257.NumericValid := by decide +kernel
theorem sound257 : certificate257.Sound := rat_failure_budget_sound certificate257 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound643,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound644,List.forall_mem_nil _⟩⟩) numericValid257

def certificate258 : RatFailureBudget := ⟨(11386162437257547639/1000000000000000000),(30153810920320901/1000000000000000000),(3062564333015717/1000000000000000000),[(2,CutFailureCertificates.Decay032.certificate645),(2,CutFailureCertificates.Decay032.certificate646),(2,CutFailureCertificates.Decay032.certificate647)]⟩
theorem numericValid258 : certificate258.NumericValid := by decide +kernel
theorem sound258 : certificate258.Sound := rat_failure_budget_sound certificate258 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound645,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound646,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound647,List.forall_mem_nil _⟩⟩⟩) numericValid258

def certificate259 : RatFailureBudget := ⟨(11386162437257547639/1000000000000000000),(14256887691932923/500000000000000000),(2951371167196257/1000000000000000000),[(2,CutFailureCertificates.Decay032.certificate648),(2,CutFailureCertificates.Decay032.certificate649)]⟩
theorem numericValid259 : certificate259.NumericValid := by decide +kernel
theorem sound259 : certificate259.Sound := rat_failure_budget_sound certificate259 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound648,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay032.sound649,List.forall_mem_nil _⟩⟩) numericValid259

end Cycle12.CutFailureCertificates.Budget012
