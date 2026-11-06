import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay126
import Cycle12.CutFailureCertificates.Decay127
import Cycle12.CutFailureCertificates.Decay128
import Cycle12.CutFailureCertificates.Decay129

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget050

def certificate1000 : RatFailureBudget := ⟨(2249909717982827983939/1000000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay126.certificate2528),(910,CutFailureCertificates.Decay126.certificate2529),(1,CutFailureCertificates.Decay126.certificate2530)]⟩
theorem numericValid1000 : certificate1000.NumericValid := by decide +kernel
theorem sound1000 : certificate1000.Sound := rat_failure_budget_sound certificate1000 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2528,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2529,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2530,List.forall_mem_nil _⟩⟩⟩) numericValid1000

def certificate1001 : RatFailureBudget := ⟨(549031503247572455771/250000000000000000),(172233501524381/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay126.certificate2531),(2,CutFailureCertificates.Decay126.certificate2532),(2,CutFailureCertificates.Decay126.certificate2533)]⟩
theorem numericValid1001 : certificate1001.NumericValid := by decide +kernel
theorem sound1001 : certificate1001.Sound := rat_failure_budget_sound certificate1001 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2531,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2532,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2533,List.forall_mem_nil _⟩⟩⟩) numericValid1001

def certificate1002 : RatFailureBudget := ⟨(549031503247572455771/250000000000000000),(79582775362553/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay126.certificate2534),(2,CutFailureCertificates.Decay126.certificate2535)]⟩
theorem numericValid1002 : certificate1002.NumericValid := by decide +kernel
theorem sound1002 : certificate1002.Sound := rat_failure_budget_sound certificate1002 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2534,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2535,List.forall_mem_nil _⟩⟩) numericValid1002

def certificate1003 : RatFailureBudget := ⟨(549031503247572455771/250000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay126.certificate2536),(910,CutFailureCertificates.Decay126.certificate2537),(1,CutFailureCertificates.Decay126.certificate2538)]⟩
theorem numericValid1003 : certificate1003.NumericValid := by decide +kernel
theorem sound1003 : certificate1003.Sound := rat_failure_budget_sound certificate1003 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2536,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2537,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2538,List.forall_mem_nil _⟩⟩⟩) numericValid1003

def certificate1004 : RatFailureBudget := ⟨(2093740221358285443809/1000000000000000000),(179403549420059/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay126.certificate2539),(2,CutFailureCertificates.Decay127.certificate2540),(2,CutFailureCertificates.Decay127.certificate2541)]⟩
theorem numericValid1004 : certificate1004.NumericValid := by decide +kernel
theorem sound1004 : certificate1004.Sound := rat_failure_budget_sound certificate1004 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay126.sound2539,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2540,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2541,List.forall_mem_nil _⟩⟩⟩) numericValid1004

def certificate1005 : RatFailureBudget := ⟨(2093740221358285443809/1000000000000000000),(415683727652471/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay127.certificate2542),(2,CutFailureCertificates.Decay127.certificate2543)]⟩
theorem numericValid1005 : certificate1005.NumericValid := by decide +kernel
theorem sound1005 : certificate1005.Sound := rat_failure_budget_sound certificate1005 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2542,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2543,List.forall_mem_nil _⟩⟩) numericValid1005

def certificate1006 : RatFailureBudget := ⟨(2093740221358285443809/1000000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay127.certificate2544),(910,CutFailureCertificates.Decay127.certificate2545),(1,CutFailureCertificates.Decay127.certificate2546)]⟩
theorem numericValid1006 : certificate1006.NumericValid := by decide +kernel
theorem sound1006 : certificate1006.Sound := rat_failure_budget_sound certificate1006 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2544,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2545,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2546,List.forall_mem_nil _⟩⟩⟩) numericValid1006

def certificate1007 : RatFailureBudget := ⟨(499447386208932962817/250000000000000000),(92621757673993/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay127.certificate2547),(2,CutFailureCertificates.Decay127.certificate2548),(2,CutFailureCertificates.Decay127.certificate2549)]⟩
theorem numericValid1007 : certificate1007.NumericValid := by decide +kernel
theorem sound1007 : certificate1007.Sound := rat_failure_budget_sound certificate1007 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2547,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2548,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2549,List.forall_mem_nil _⟩⟩⟩) numericValid1007

def certificate1008 : RatFailureBudget := ⟨(499447386208932962817/250000000000000000),(433360438559531/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay127.certificate2550),(2,CutFailureCertificates.Decay127.certificate2551)]⟩
theorem numericValid1008 : certificate1008.NumericValid := by decide +kernel
theorem sound1008 : certificate1008.Sound := rat_failure_budget_sound certificate1008 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2550,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2551,List.forall_mem_nil _⟩⟩) numericValid1008

def certificate1009 : RatFailureBudget := ⟨(499447386208932962817/250000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay127.certificate2552),(908,CutFailureCertificates.Decay127.certificate2553),(1,CutFailureCertificates.Decay127.certificate2554)]⟩
theorem numericValid1009 : certificate1009.NumericValid := by decide +kernel
theorem sound1009 : certificate1009.Sound := rat_failure_budget_sound certificate1009 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2552,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2553,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2554,List.forall_mem_nil _⟩⟩⟩) numericValid1009

def certificate1010 : RatFailureBudget := ⟨(38155106028494393599/20000000000000000),(95561121607587/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay127.certificate2555),(2,CutFailureCertificates.Decay127.certificate2556),(2,CutFailureCertificates.Decay127.certificate2557)]⟩
theorem numericValid1010 : certificate1010.NumericValid := by decide +kernel
theorem sound1010 : certificate1010.Sound := rat_failure_budget_sound certificate1010 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2555,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2556,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2557,List.forall_mem_nil _⟩⟩⟩) numericValid1010

def certificate1011 : RatFailureBudget := ⟨(38155106028494393599/20000000000000000),(28204788668019/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay127.certificate2558),(2,CutFailureCertificates.Decay127.certificate2559)]⟩
theorem numericValid1011 : certificate1011.NumericValid := by decide +kernel
theorem sound1011 : certificate1011.Sound := rat_failure_budget_sound certificate1011 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2558,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay127.sound2559,List.forall_mem_nil _⟩⟩) numericValid1011

def certificate1012 : RatFailureBudget := ⟨(38155106028494393599/20000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay128.certificate2560),(908,CutFailureCertificates.Decay128.certificate2561),(1,CutFailureCertificates.Decay128.certificate2562)]⟩
theorem numericValid1012 : certificate1012.NumericValid := by decide +kernel
theorem sound1012 : certificate1012.Sound := rat_failure_budget_sound certificate1012 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2560,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2561,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2562,List.forall_mem_nil _⟩⟩⟩) numericValid1012

def certificate1013 : RatFailureBudget := ⟨(455792420776076303701/250000000000000000),(367525809166807/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay128.certificate2563),(2,CutFailureCertificates.Decay128.certificate2564),(2,CutFailureCertificates.Decay128.certificate2565)]⟩
theorem numericValid1013 : certificate1013.NumericValid := by decide +kernel
theorem sound1013 : certificate1013.Sound := rat_failure_budget_sound certificate1013 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2563,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2564,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2565,List.forall_mem_nil _⟩⟩⟩) numericValid1013

def certificate1014 : RatFailureBudget := ⟨(455792420776076303701/250000000000000000),(554816252781031/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay128.certificate2566),(2,CutFailureCertificates.Decay128.certificate2567)]⟩
theorem numericValid1014 : certificate1014.NumericValid := by decide +kernel
theorem sound1014 : certificate1014.Sound := rat_failure_budget_sound certificate1014 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2566,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2567,List.forall_mem_nil _⟩⟩) numericValid1014

def certificate1015 : RatFailureBudget := ⟨(455792420776076303701/250000000000000000),(4475020268216611/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay128.certificate2568),(906,CutFailureCertificates.Decay128.certificate2569),(1,CutFailureCertificates.Decay128.certificate2570)]⟩
theorem numericValid1015 : certificate1015.NumericValid := by decide +kernel
theorem sound1015 : certificate1015.Sound := rat_failure_budget_sound certificate1015 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2568,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2569,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2570,List.forall_mem_nil _⟩⟩⟩) numericValid1015

def certificate1016 : RatFailureBudget := ⟨(435902475717329878669/250000000000000000),(101436726393161/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay128.certificate2571),(2,CutFailureCertificates.Decay128.certificate2572),(2,CutFailureCertificates.Decay128.certificate2573)]⟩
theorem numericValid1016 : certificate1016.NumericValid := by decide +kernel
theorem sound1016 : certificate1016.Sound := rat_failure_budget_sound certificate1016 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2571,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2572,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2573,List.forall_mem_nil _⟩⟩⟩) numericValid1016

def certificate1017 : RatFailureBudget := ⟨(435902475717329878669/250000000000000000),(244225175087513/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay128.certificate2574),(2,CutFailureCertificates.Decay128.certificate2575)]⟩
theorem numericValid1017 : certificate1017.NumericValid := by decide +kernel
theorem sound1017 : certificate1017.Sound := rat_failure_budget_sound certificate1017 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2574,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2575,List.forall_mem_nil _⟩⟩) numericValid1017

def certificate1018 : RatFailureBudget := ⟨(435902475717329878669/250000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay128.certificate2576),(906,CutFailureCertificates.Decay128.certificate2577),(1,CutFailureCertificates.Decay128.certificate2578)]⟩
theorem numericValid1018 : certificate1018.NumericValid := by decide +kernel
theorem sound1018 : certificate1018.Sound := rat_failure_budget_sound certificate1018 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2576,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2577,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2578,List.forall_mem_nil _⟩⟩⟩) numericValid1018

def certificate1019 : RatFailureBudget := ⟨(1668693111133782522381/1000000000000000000),(521984893677/2500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay128.certificate2579),(2,CutFailureCertificates.Decay129.certificate2580),(2,CutFailureCertificates.Decay129.certificate2581)]⟩
theorem numericValid1019 : certificate1019.NumericValid := by decide +kernel
theorem sound1019 : certificate1019.Sound := rat_failure_budget_sound certificate1019 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay128.sound2579,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2580,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2581,List.forall_mem_nil _⟩⟩⟩) numericValid1019

end Cycle12.CutFailureCertificates.Budget050
