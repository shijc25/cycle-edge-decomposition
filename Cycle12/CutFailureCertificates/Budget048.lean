import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay121
import Cycle12.CutFailureCertificates.Decay122
import Cycle12.CutFailureCertificates.Decay123

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget048

def certificate960 : RatFailureBudget := ⟨(98467221350285359993/31250000000000000),(71720681717887/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay121.certificate2422),(2,CutFailureCertificates.Decay121.certificate2423)]⟩
theorem numericValid960 : certificate960.NumericValid := by decide +kernel
theorem sound960 : certificate960.Sound := rat_failure_budget_sound certificate960 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2422,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2423,List.forall_mem_nil _⟩⟩) numericValid960

def certificate961 : RatFailureBudget := ⟨(98467221350285359993/31250000000000000),(4472828072356481/1000000000000000000),(3/1000000000000000000),[(2,CutFailureCertificates.Decay121.certificate2424),(916,CutFailureCertificates.Decay121.certificate2425),(1,CutFailureCertificates.Decay121.certificate2426)]⟩
theorem numericValid961 : certificate961.NumericValid := by decide +kernel
theorem sound961 : certificate961.Sound := rat_failure_budget_sound certificate961 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2424,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2425,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2426,List.forall_mem_nil _⟩⟩⟩) numericValid961

def certificate962 : RatFailureBudget := ⟨(3107746678209120739629/1000000000000000000),(133529817133571/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay121.certificate2427),(2,CutFailureCertificates.Decay121.certificate2428),(2,CutFailureCertificates.Decay121.certificate2429)]⟩
theorem numericValid962 : certificate962.NumericValid := by decide +kernel
theorem sound962 : certificate962.Sound := rat_failure_budget_sound certificate962 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2427,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2428,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2429,List.forall_mem_nil _⟩⟩⟩) numericValid962

def certificate963 : RatFailureBudget := ⟨(3107746678209120739629/1000000000000000000),(276765221427569/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay121.certificate2430),(2,CutFailureCertificates.Decay121.certificate2431)]⟩
theorem numericValid963 : certificate963.NumericValid := by decide +kernel
theorem sound963 : certificate963.Sound := rat_failure_budget_sound certificate963 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2430,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2431,List.forall_mem_nil _⟩⟩) numericValid963

def certificate964 : RatFailureBudget := ⟨(3107746678209120739629/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay121.certificate2432),(916,CutFailureCertificates.Decay121.certificate2433),(1,CutFailureCertificates.Decay121.certificate2434)]⟩
theorem numericValid964 : certificate964.NumericValid := by decide +kernel
theorem sound964 : certificate964.Sound := rat_failure_budget_sound certificate964 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2432,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2433,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2434,List.forall_mem_nil _⟩⟩⟩) numericValid964

def certificate965 : RatFailureBudget := ⟨(24522918443256535917/8000000000000000),(33707269966807/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay121.certificate2435),(2,CutFailureCertificates.Decay121.certificate2436),(2,CutFailureCertificates.Decay121.certificate2437)]⟩
theorem numericValid965 : certificate965.NumericValid := by decide +kernel
theorem sound965 : certificate965.Sound := rat_failure_budget_sound certificate965 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2435,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2436,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2437,List.forall_mem_nil _⟩⟩⟩) numericValid965

def certificate966 : RatFailureBudget := ⟨(24522918443256535917/8000000000000000),(294653097469227/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay121.certificate2438),(2,CutFailureCertificates.Decay121.certificate2439)]⟩
theorem numericValid966 : certificate966.NumericValid := by decide +kernel
theorem sound966 : certificate966.Sound := rat_failure_budget_sound certificate966 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2438,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2439,List.forall_mem_nil _⟩⟩) numericValid966

def certificate967 : RatFailureBudget := ⟨(24522918443256535917/8000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay122.certificate2440),(914,CutFailureCertificates.Decay122.certificate2441),(1,CutFailureCertificates.Decay122.certificate2442)]⟩
theorem numericValid967 : certificate967.NumericValid := by decide +kernel
theorem sound967 : certificate967.Sound := rat_failure_budget_sound certificate967 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2440,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2441,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2442,List.forall_mem_nil _⟩⟩⟩) numericValid967

def certificate968 : RatFailureBudget := ⟨(3023785039358298996097/1000000000000000000),(2129492229331/15625000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay122.certificate2443),(2,CutFailureCertificates.Decay122.certificate2444),(2,CutFailureCertificates.Decay122.certificate2445)]⟩
theorem numericValid968 : certificate968.NumericValid := by decide +kernel
theorem sound968 : certificate968.Sound := rat_failure_budget_sound certificate968 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2443,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2444,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2445,List.forall_mem_nil _⟩⟩⟩) numericValid968

def certificate969 : RatFailureBudget := ⟨(3023785039358298996097/1000000000000000000),(298150754798389/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay122.certificate2446),(2,CutFailureCertificates.Decay122.certificate2447)]⟩
theorem numericValid969 : certificate969.NumericValid := by decide +kernel
theorem sound969 : certificate969.Sound := rat_failure_budget_sound certificate969 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2446,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2447,List.forall_mem_nil _⟩⟩) numericValid969

def certificate970 : RatFailureBudget := ⟨(3023785039358298996097/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay122.certificate2448),(914,CutFailureCertificates.Decay122.certificate2449),(1,CutFailureCertificates.Decay122.certificate2450)]⟩
theorem numericValid970 : certificate970.NumericValid := by decide +kernel
theorem sound970 : certificate970.Sound := rat_failure_budget_sound certificate970 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2448,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2449,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2450,List.forall_mem_nil _⟩⟩⟩) numericValid970

def certificate971 : RatFailureBudget := ⟨(3003289735309396365599/1000000000000000000),(136739177966079/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay122.certificate2451),(2,CutFailureCertificates.Decay122.certificate2452),(2,CutFailureCertificates.Decay122.certificate2453)]⟩
theorem numericValid971 : certificate971.NumericValid := by decide +kernel
theorem sound971 : certificate971.Sound := rat_failure_budget_sound certificate971 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2451,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2452,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2453,List.forall_mem_nil _⟩⟩⟩) numericValid971

def certificate972 : RatFailureBudget := ⟨(3003289735309396365599/1000000000000000000),(299940999249373/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay122.certificate2454),(2,CutFailureCertificates.Decay122.certificate2455)]⟩
theorem numericValid972 : certificate972.NumericValid := by decide +kernel
theorem sound972 : certificate972.Sound := rat_failure_budget_sound certificate972 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2454,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2455,List.forall_mem_nil _⟩⟩) numericValid972

def certificate973 : RatFailureBudget := ⟨(3003289735309396365599/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay122.certificate2456),(914,CutFailureCertificates.Decay122.certificate2457),(1,CutFailureCertificates.Decay122.certificate2458)]⟩
theorem numericValid973 : certificate973.NumericValid := by decide +kernel
theorem sound973 : certificate973.Sound := rat_failure_budget_sound certificate973 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2456,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2457,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2458,List.forall_mem_nil _⟩⟩⟩) numericValid973

def certificate974 : RatFailureBudget := ⟨(1491493790476122464187/500000000000000000),(68704406545009/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay122.certificate2459),(2,CutFailureCertificates.Decay123.certificate2460),(2,CutFailureCertificates.Decay123.certificate2461)]⟩
theorem numericValid974 : certificate974.NumericValid := by decide +kernel
theorem sound974 : certificate974.Sound := rat_failure_budget_sound certificate974 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay122.sound2459,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2460,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2461,List.forall_mem_nil _⟩⟩⟩) numericValid974

def certificate975 : RatFailureBudget := ⟨(1491493790476122464187/500000000000000000),(479982913267/1600000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay123.certificate2462),(2,CutFailureCertificates.Decay123.certificate2463)]⟩
theorem numericValid975 : certificate975.NumericValid := by decide +kernel
theorem sound975 : certificate975.Sound := rat_failure_budget_sound certificate975 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2462,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2463,List.forall_mem_nil _⟩⟩) numericValid975

def certificate976 : RatFailureBudget := ⟨(1491493790476122464187/500000000000000000),(4472613092664197/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay123.certificate2464),(914,CutFailureCertificates.Decay123.certificate2465),(1,CutFailureCertificates.Decay123.certificate2466)]⟩
theorem numericValid976 : certificate976.NumericValid := by decide +kernel
theorem sound976 : certificate976.Sound := rat_failure_budget_sound certificate976 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2464,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2465,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2466,List.forall_mem_nil _⟩⟩⟩) numericValid976

def certificate977 : RatFailureBudget := ⟨(1413622755423419206487/500000000000000000),(146523993265823/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay123.certificate2467),(2,CutFailureCertificates.Decay123.certificate2468),(2,CutFailureCertificates.Decay123.certificate2469)]⟩
theorem numericValid977 : certificate977.NumericValid := by decide +kernel
theorem sound977 : certificate977.Sound := rat_failure_budget_sound certificate977 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2467,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2468,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2469,List.forall_mem_nil _⟩⟩⟩) numericValid977

def certificate978 : RatFailureBudget := ⟨(1413622755423419206487/500000000000000000),(317054836742443/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay123.certificate2470),(2,CutFailureCertificates.Decay123.certificate2471)]⟩
theorem numericValid978 : certificate978.NumericValid := by decide +kernel
theorem sound978 : certificate978.Sound := rat_failure_budget_sound certificate978 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2470,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2471,List.forall_mem_nil _⟩⟩) numericValid978

def certificate979 : RatFailureBudget := ⟨(1413622755423419206487/500000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay123.certificate2472),(914,CutFailureCertificates.Decay123.certificate2473),(1,CutFailureCertificates.Decay123.certificate2474)]⟩
theorem numericValid979 : certificate979.NumericValid := by decide +kernel
theorem sound979 : certificate979.Sound := rat_failure_budget_sound certificate979 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2472,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2473,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay123.sound2474,List.forall_mem_nil _⟩⟩⟩) numericValid979

end Cycle12.CutFailureCertificates.Budget048
