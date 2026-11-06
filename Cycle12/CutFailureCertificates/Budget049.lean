import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay123
import Cycle12.CutFailureCertificates.Decay124
import Cycle12.CutFailureCertificates.Decay125
import Cycle12.CutFailureCertificates.Decay126

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget049

def certificate980 : RatFailureBudget := ⟨(167661534521558025279/62500000000000000),(7617433699891/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay123.certificate2475),(2,CutFailureCertificates.Decay123.certificate2476),(2,CutFailureCertificates.Decay123.certificate2477)]⟩
theorem numericValid980 : certificate980.NumericValid := by decide +kernel
theorem sound980 : certificate980.Sound := rat_failure_budget_sound certificate980 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2475,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2476,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2477,List.forall_mem_nil _⟩⟩⟩) numericValid980

def certificate981 : RatFailureBudget := ⟨(167661534521558025279/62500000000000000),(66485859987471/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay123.certificate2478),(2,CutFailureCertificates.Decay123.certificate2479)]⟩
theorem numericValid981 : certificate981.NumericValid := by decide +kernel
theorem sound981 : certificate981.Sound := rat_failure_budget_sound certificate981 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2478,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2479,List.forall_mem_nil _⟩⟩) numericValid981

def certificate982 : RatFailureBudget := ⟨(167661534521558025279/62500000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay124.certificate2480),(912,CutFailureCertificates.Decay124.certificate2481),(1,CutFailureCertificates.Decay124.certificate2482)]⟩
theorem numericValid982 : certificate982.NumericValid := by decide +kernel
theorem sound982 : certificate982.Sound := rat_failure_budget_sound certificate982 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2480,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2481,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2482,List.forall_mem_nil _⟩⟩⟩) numericValid982

def certificate983 : RatFailureBudget := ⟨(636998401369663506707/250000000000000000),(158125233900229/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay124.certificate2483),(2,CutFailureCertificates.Decay124.certificate2484),(2,CutFailureCertificates.Decay124.certificate2485)]⟩
theorem numericValid983 : certificate983.NumericValid := by decide +kernel
theorem sound983 : certificate983.Sound := rat_failure_budget_sound certificate983 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2483,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2484,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2485,List.forall_mem_nil _⟩⟩⟩) numericValid983

def certificate984 : RatFailureBudget := ⟨(636998401369663506707/250000000000000000),(348284148665021/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay124.certificate2486),(2,CutFailureCertificates.Decay124.certificate2487)]⟩
theorem numericValid984 : certificate984.NumericValid := by decide +kernel
theorem sound984 : certificate984.Sound := rat_failure_budget_sound certificate984 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2486,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2487,List.forall_mem_nil _⟩⟩) numericValid984

def certificate985 : RatFailureBudget := ⟨(636998401369663506707/250000000000000000),(280276069692237/62500000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay124.certificate2488),(912,CutFailureCertificates.Decay124.certificate2489),(1,CutFailureCertificates.Decay124.certificate2490)]⟩
theorem numericValid985 : certificate985.NumericValid := by decide +kernel
theorem sound985 : certificate985.Sound := rat_failure_budget_sound certificate985 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2488,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2489,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2490,List.forall_mem_nil _⟩⟩⟩) numericValid985

def certificate986 : RatFailureBudget := ⟨(2484189479669223829747/1000000000000000000),(157949977131233/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay124.certificate2491),(2,CutFailureCertificates.Decay124.certificate2492),(2,CutFailureCertificates.Decay124.certificate2493)]⟩
theorem numericValid986 : certificate986.NumericValid := by decide +kernel
theorem sound986 : certificate986.Sound := rat_failure_budget_sound certificate986 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2491,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2492,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2493,List.forall_mem_nil _⟩⟩⟩) numericValid986

def certificate987 : RatFailureBudget := ⟨(2484189479669223829747/1000000000000000000),(177534789677309/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay124.certificate2494),(2,CutFailureCertificates.Decay124.certificate2495)]⟩
theorem numericValid987 : certificate987.NumericValid := by decide +kernel
theorem sound987 : certificate987.Sound := rat_failure_budget_sound certificate987 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2494,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2495,List.forall_mem_nil _⟩⟩) numericValid987

def certificate988 : RatFailureBudget := ⟨(2484189479669223829747/1000000000000000000),(1118147109755953/250000000000000000),(1851093/1000000000000000000),[(2,CutFailureCertificates.Decay124.certificate2496),(914,CutFailureCertificates.Decay124.certificate2497),(1,CutFailureCertificates.Decay124.certificate2498)]⟩
theorem numericValid988 : certificate988.NumericValid := by decide +kernel
theorem sound988 : certificate988.Sound := rat_failure_budget_sound certificate988 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2496,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2497,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2498,List.forall_mem_nil _⟩⟩⟩) numericValid988

def certificate989 : RatFailureBudget := ⟨(2422573656693449252979/1000000000000000000),(160771916484191/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay124.certificate2499),(2,CutFailureCertificates.Decay125.certificate2500),(2,CutFailureCertificates.Decay125.certificate2501)]⟩
theorem numericValid989 : certificate989.NumericValid := by decide +kernel
theorem sound989 : certificate989.Sound := rat_failure_budget_sound certificate989 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay124.sound2499,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2500,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2501,List.forall_mem_nil _⟩⟩⟩) numericValid989

def certificate990 : RatFailureBudget := ⟨(2422573656693449252979/1000000000000000000),(182249298272803/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay125.certificate2502),(2,CutFailureCertificates.Decay125.certificate2503)]⟩
theorem numericValid990 : certificate990.NumericValid := by decide +kernel
theorem sound990 : certificate990.Sound := rat_failure_budget_sound certificate990 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2502,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2503,List.forall_mem_nil _⟩⟩) numericValid990

def certificate991 : RatFailureBudget := ⟨(2422573656693449252979/1000000000000000000),(4472588439023811/1000000000000000000),(15447/1000000000000000000),[(2,CutFailureCertificates.Decay125.certificate2504),(912,CutFailureCertificates.Decay125.certificate2505),(1,CutFailureCertificates.Decay125.certificate2506)]⟩
theorem numericValid991 : certificate991.NumericValid := by decide +kernel
theorem sound991 : certificate991.Sound := rat_failure_budget_sound certificate991 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2504,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2505,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2506,List.forall_mem_nil _⟩⟩⟩) numericValid991

def certificate992 : RatFailureBudget := ⟨(118152444412213092533/50000000000000000),(81813792930503/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay125.certificate2507),(2,CutFailureCertificates.Decay125.certificate2508),(2,CutFailureCertificates.Decay125.certificate2509)]⟩
theorem numericValid992 : certificate992.NumericValid := by decide +kernel
theorem sound992 : certificate992.Sound := rat_failure_budget_sound certificate992 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2507,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2508,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2509,List.forall_mem_nil _⟩⟩⟩) numericValid992

def certificate993 : RatFailureBudget := ⟨(118152444412213092533/50000000000000000),(372710636007331/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay125.certificate2510),(2,CutFailureCertificates.Decay125.certificate2511)]⟩
theorem numericValid993 : certificate993.NumericValid := by decide +kernel
theorem sound993 : certificate993.Sound := rat_failure_budget_sound certificate993 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2510,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2511,List.forall_mem_nil _⟩⟩) numericValid993

def certificate994 : RatFailureBudget := ⟨(118152444412213092533/50000000000000000),(447258843902381/100000000000000000),(27/200000000000000000),[(2,CutFailureCertificates.Decay125.certificate2512),(912,CutFailureCertificates.Decay125.certificate2513),(1,CutFailureCertificates.Decay125.certificate2514)]⟩
theorem numericValid994 : certificate994.NumericValid := by decide +kernel
theorem sound994 : certificate994.Sound := rat_failure_budget_sound certificate994 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2512,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2513,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2514,List.forall_mem_nil _⟩⟩⟩) numericValid994

def certificate995 : RatFailureBudget := ⟨(461104646765771894257/200000000000000000),(166490763811329/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay125.certificate2515),(2,CutFailureCertificates.Decay125.certificate2516),(2,CutFailureCertificates.Decay125.certificate2517)]⟩
theorem numericValid995 : certificate995.NumericValid := by decide +kernel
theorem sound995 : certificate995.Sound := rat_failure_budget_sound certificate995 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2515,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2516,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2517,List.forall_mem_nil _⟩⟩⟩) numericValid995

def certificate996 : RatFailureBudget := ⟨(461104646765771894257/200000000000000000),(47541965172743/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay125.certificate2518),(2,CutFailureCertificates.Decay125.certificate2519)]⟩
theorem numericValid996 : certificate996.NumericValid := by decide +kernel
theorem sound996 : certificate996.Sound := rat_failure_budget_sound certificate996 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2518,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay125.sound2519,List.forall_mem_nil _⟩⟩) numericValid996

def certificate997 : RatFailureBudget := ⟨(461104646765771894257/200000000000000000),(447258843902381/100000000000000000),(3/1000000000000000000),[(2,CutFailureCertificates.Decay126.certificate2520),(912,CutFailureCertificates.Decay126.certificate2521),(1,CutFailureCertificates.Decay126.certificate2522)]⟩
theorem numericValid997 : certificate997.NumericValid := by decide +kernel
theorem sound997 : certificate997.Sound := rat_failure_budget_sound certificate997 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2520,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2521,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2522,List.forall_mem_nil _⟩⟩⟩) numericValid997

def certificate998 : RatFailureBudget := ⟨(2249909717982827983939/1000000000000000000),(42342499172541/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay126.certificate2523),(2,CutFailureCertificates.Decay126.certificate2524),(2,CutFailureCertificates.Decay126.certificate2525)]⟩
theorem numericValid998 : certificate998.NumericValid := by decide +kernel
theorem sound998 : certificate998.Sound := rat_failure_budget_sound certificate998 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2523,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2524,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2525,List.forall_mem_nil _⟩⟩⟩) numericValid998

def certificate999 : RatFailureBudget := ⟨(2249909717982827983939/1000000000000000000),(389437530223959/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay126.certificate2526),(2,CutFailureCertificates.Decay126.certificate2527)]⟩
theorem numericValid999 : certificate999.NumericValid := by decide +kernel
theorem sound999 : certificate999.Sound := rat_failure_budget_sound certificate999 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2526,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2527,List.forall_mem_nil _⟩⟩) numericValid999

end Cycle12.CutFailureCertificates.Budget049
