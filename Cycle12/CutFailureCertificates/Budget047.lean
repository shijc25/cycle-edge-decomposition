import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay118
import Cycle12.CutFailureCertificates.Decay119
import Cycle12.CutFailureCertificates.Decay120
import Cycle12.CutFailureCertificates.Decay121

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget047

def certificate940 : RatFailureBudget := ⟨(705775029171982801787/200000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay118.certificate2368),(916,CutFailureCertificates.Decay118.certificate2369),(1,CutFailureCertificates.Decay118.certificate2370)]⟩
theorem numericValid940 : certificate940.NumericValid := by decide +kernel
theorem sound940 : certificate940.Sound := rat_failure_budget_sound certificate940 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2368,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2369,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2370,List.forall_mem_nil _⟩⟩⟩) numericValid940

def certificate941 : RatFailureBudget := ⟨(3478271617621589972309/1000000000000000000),(24566689586889/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay118.certificate2371),(2,CutFailureCertificates.Decay118.certificate2372),(2,CutFailureCertificates.Decay118.certificate2373)]⟩
theorem numericValid941 : certificate941.NumericValid := by decide +kernel
theorem sound941 : certificate941.Sound := rat_failure_budget_sound certificate941 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2371,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2372,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2373,List.forall_mem_nil _⟩⟩⟩) numericValid941

def certificate942 : RatFailureBudget := ⟨(3478271617621589972309/1000000000000000000),(258160154021677/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay118.certificate2374),(2,CutFailureCertificates.Decay118.certificate2375)]⟩
theorem numericValid942 : certificate942.NumericValid := by decide +kernel
theorem sound942 : certificate942.Sound := rat_failure_budget_sound certificate942 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2374,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2375,List.forall_mem_nil _⟩⟩) numericValid942

def certificate943 : RatFailureBudget := ⟨(3478271617621589972309/1000000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay118.certificate2376),(914,CutFailureCertificates.Decay118.certificate2377),(1,CutFailureCertificates.Decay118.certificate2378)]⟩
theorem numericValid943 : certificate943.NumericValid := by decide +kernel
theorem sound943 : certificate943.Sound := rat_failure_budget_sound certificate943 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2376,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2377,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2378,List.forall_mem_nil _⟩⟩⟩) numericValid943

def certificate944 : RatFailureBudget := ⟨(857169918378039990671/250000000000000000),(124274241800469/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay118.certificate2379),(2,CutFailureCertificates.Decay119.certificate2380),(2,CutFailureCertificates.Decay119.certificate2381)]⟩
theorem numericValid944 : certificate944.NumericValid := by decide +kernel
theorem sound944 : certificate944.Sound := rat_failure_budget_sound certificate944 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2379,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2380,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2381,List.forall_mem_nil _⟩⟩⟩) numericValid944

def certificate945 : RatFailureBudget := ⟨(857169918378039990671/250000000000000000),(265854406616503/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay119.certificate2382),(2,CutFailureCertificates.Decay119.certificate2383)]⟩
theorem numericValid945 : certificate945.NumericValid := by decide +kernel
theorem sound945 : certificate945.Sound := rat_failure_budget_sound certificate945 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2382,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2383,List.forall_mem_nil _⟩⟩) numericValid945

def certificate946 : RatFailureBudget := ⟨(857169918378039990671/250000000000000000),(559078239069589/125000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay119.certificate2384),(914,CutFailureCertificates.Decay119.certificate2385),(1,CutFailureCertificates.Decay119.certificate2386)]⟩
theorem numericValid946 : certificate946.NumericValid := by decide +kernel
theorem sound946 : certificate946.Sound := rat_failure_budget_sound certificate946 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2384,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2385,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2386,List.forall_mem_nil _⟩⟩⟩) numericValid946

def certificate947 : RatFailureBudget := ⟨(3380072921991454528517/1000000000000000000),(62753153971949/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay119.certificate2387),(2,CutFailureCertificates.Decay119.certificate2388),(2,CutFailureCertificates.Decay119.certificate2389)]⟩
theorem numericValid947 : certificate947.NumericValid := by decide +kernel
theorem sound947 : certificate947.Sound := rat_failure_budget_sound certificate947 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2387,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2388,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2389,List.forall_mem_nil _⟩⟩⟩) numericValid947

def certificate948 : RatFailureBudget := ⟨(3380072921991454528517/1000000000000000000),(16834617848867/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay119.certificate2390),(2,CutFailureCertificates.Decay119.certificate2391)]⟩
theorem numericValid948 : certificate948.NumericValid := by decide +kernel
theorem sound948 : certificate948.Sound := rat_failure_budget_sound certificate948 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2390,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2391,List.forall_mem_nil _⟩⟩) numericValid948

def certificate949 : RatFailureBudget := ⟨(3380072921991454528517/1000000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay119.certificate2392),(914,CutFailureCertificates.Decay119.certificate2393),(1,CutFailureCertificates.Decay119.certificate2394)]⟩
theorem numericValid949 : certificate949.NumericValid := by decide +kernel
theorem sound949 : certificate949.Sound := rat_failure_budget_sound certificate949 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2392,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2393,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2394,List.forall_mem_nil _⟩⟩⟩) numericValid949

def certificate950 : RatFailureBudget := ⟨(3356130979488257458691/1000000000000000000),(31486744047483/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay119.certificate2395),(2,CutFailureCertificates.Decay119.certificate2396),(2,CutFailureCertificates.Decay119.certificate2397)]⟩
theorem numericValid950 : certificate950.NumericValid := by decide +kernel
theorem sound950 : certificate950.Sound := rat_failure_budget_sound certificate950 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2395,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2396,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2397,List.forall_mem_nil _⟩⟩⟩) numericValid950

def certificate951 : RatFailureBudget := ⟨(3356130979488257458691/1000000000000000000),(271051430171067/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay119.certificate2398),(2,CutFailureCertificates.Decay119.certificate2399)]⟩
theorem numericValid951 : certificate951.NumericValid := by decide +kernel
theorem sound951 : certificate951.Sound := rat_failure_budget_sound certificate951 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2398,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay119.sound2399,List.forall_mem_nil _⟩⟩) numericValid951

def certificate952 : RatFailureBudget := ⟨(3356130979488257458691/1000000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay120.certificate2400),(914,CutFailureCertificates.Decay120.certificate2401),(1,CutFailureCertificates.Decay120.certificate2402)]⟩
theorem numericValid952 : certificate952.NumericValid := by decide +kernel
theorem sound952 : certificate952.Sound := rat_failure_budget_sound certificate952 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2400,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2401,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2402,List.forall_mem_nil _⟩⟩⟩) numericValid952

def certificate953 : RatFailureBudget := ⟨(3332425821775927600291/1000000000000000000),(126648454139871/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay120.certificate2403),(2,CutFailureCertificates.Decay120.certificate2404),(2,CutFailureCertificates.Decay120.certificate2405)]⟩
theorem numericValid953 : certificate953.NumericValid := by decide +kernel
theorem sound953 : certificate953.Sound := rat_failure_budget_sound certificate953 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2403,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2404,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2405,List.forall_mem_nil _⟩⟩⟩) numericValid953

def certificate954 : RatFailureBudget := ⟨(3332425821775927600291/1000000000000000000),(136386732449907/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay120.certificate2406),(2,CutFailureCertificates.Decay120.certificate2407)]⟩
theorem numericValid954 : certificate954.NumericValid := by decide +kernel
theorem sound954 : certificate954.Sound := rat_failure_budget_sound certificate954 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2406,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2407,List.forall_mem_nil _⟩⟩) numericValid954

def certificate955 : RatFailureBudget := ⟨(3332425821775927600291/1000000000000000000),(4472642677031043/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay120.certificate2408),(914,CutFailureCertificates.Decay120.certificate2409),(1,CutFailureCertificates.Decay120.certificate2410)]⟩
theorem numericValid955 : certificate955.NumericValid := by decide +kernel
theorem sound955 : certificate955.Sound := rat_failure_budget_sound certificate955 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2408,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2409,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2410,List.forall_mem_nil _⟩⟩⟩) numericValid955

def certificate956 : RatFailureBudget := ⟨(404989058429119377839/125000000000000000),(127322738155019/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay120.certificate2411),(2,CutFailureCertificates.Decay120.certificate2412),(2,CutFailureCertificates.Decay120.certificate2413)]⟩
theorem numericValid956 : certificate956.NumericValid := by decide +kernel
theorem sound956 : certificate956.Sound := rat_failure_budget_sound certificate956 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2411,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2412,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2413,List.forall_mem_nil _⟩⟩⟩) numericValid956

def certificate957 : RatFailureBudget := ⟨(404989058429119377839/125000000000000000),(70054505648147/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay120.certificate2414),(2,CutFailureCertificates.Decay120.certificate2415)]⟩
theorem numericValid957 : certificate957.NumericValid := by decide +kernel
theorem sound957 : certificate957.Sound := rat_failure_budget_sound certificate957 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2414,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2415,List.forall_mem_nil _⟩⟩) numericValid957

def certificate958 : RatFailureBudget := ⟨(404989058429119377839/125000000000000000),(447258843902381/100000000000000000),(231/1000000000000000000),[(2,CutFailureCertificates.Decay120.certificate2416),(916,CutFailureCertificates.Decay120.certificate2417),(1,CutFailureCertificates.Decay120.certificate2418)]⟩
theorem numericValid958 : certificate958.NumericValid := by decide +kernel
theorem sound958 : certificate958.Sound := rat_failure_budget_sound certificate958 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2416,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2417,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2418,List.forall_mem_nil _⟩⟩⟩) numericValid958

def certificate959 : RatFailureBudget := ⟨(98467221350285359993/31250000000000000),(132504547579301/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay120.certificate2419),(2,CutFailureCertificates.Decay121.certificate2420),(2,CutFailureCertificates.Decay121.certificate2421)]⟩
theorem numericValid959 : certificate959.NumericValid := by decide +kernel
theorem sound959 : certificate959.Sound := rat_failure_budget_sound certificate959 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay120.sound2419,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2420,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay121.sound2421,List.forall_mem_nil _⟩⟩⟩) numericValid959

end Cycle12.CutFailureCertificates.Budget047
