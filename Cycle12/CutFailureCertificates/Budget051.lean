import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay129
import Cycle12.CutFailureCertificates.Decay130
import Cycle12.CutFailureCertificates.Decay131

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget051

def certificate1020 : RatFailureBudget := ⟨(1668693111133782522381/1000000000000000000),(101510255466029/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay129.certificate2582),(2,CutFailureCertificates.Decay129.certificate2583)]⟩
theorem numericValid1020 : certificate1020.NumericValid := by decide +kernel
theorem sound1020 : certificate1020.Sound := rat_failure_budget_sound certificate1020 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2582,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2583,List.forall_mem_nil _⟩⟩) numericValid1020

def certificate1021 : RatFailureBudget := ⟨(1668693111133782522381/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay129.certificate2584),(904,CutFailureCertificates.Decay129.certificate2585),(1,CutFailureCertificates.Decay129.certificate2586)]⟩
theorem numericValid1021 : certificate1021.NumericValid := by decide +kernel
theorem sound1021 : certificate1021.Sound := rat_failure_budget_sound certificate1021 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2584,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2585,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2586,List.forall_mem_nil _⟩⟩⟩) numericValid1021

def certificate1022 : RatFailureBudget := ⟨(799035984091420394923/500000000000000000),(107346057372917/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay129.certificate2587),(2,CutFailureCertificates.Decay129.certificate2588),(2,CutFailureCertificates.Decay129.certificate2589)]⟩
theorem numericValid1022 : certificate1022.NumericValid := by decide +kernel
theorem sound1022 : certificate1022.Sound := rat_failure_budget_sound certificate1022 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2587,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2588,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2589,List.forall_mem_nil _⟩⟩⟩) numericValid1022

def certificate1023 : RatFailureBudget := ⟨(799035984091420394923/500000000000000000),(6588139801749/12500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay129.certificate2590),(2,CutFailureCertificates.Decay129.certificate2591)]⟩
theorem numericValid1023 : certificate1023.NumericValid := by decide +kernel
theorem sound1023 : certificate1023.Sound := rat_failure_budget_sound certificate1023 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2590,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2591,List.forall_mem_nil _⟩⟩) numericValid1023

def certificate1024 : RatFailureBudget := ⟨(799035984091420394923/500000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay129.certificate2592),(902,CutFailureCertificates.Decay129.certificate2593),(1,CutFailureCertificates.Decay129.certificate2594)]⟩
theorem numericValid1024 : certificate1024.NumericValid := by decide +kernel
theorem sound1024 : certificate1024.Sound := rat_failure_budget_sound certificate1024 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2592,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2593,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2594,List.forall_mem_nil _⟩⟩⟩) numericValid1024

def certificate1025 : RatFailureBudget := ⟨(1495537868925159927/976562500000000),(11032039667019/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay129.certificate2595),(2,CutFailureCertificates.Decay129.certificate2596),(2,CutFailureCertificates.Decay129.certificate2597)]⟩
theorem numericValid1025 : certificate1025.NumericValid := by decide +kernel
theorem sound1025 : certificate1025.Sound := rat_failure_budget_sound certificate1025 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2595,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2596,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2597,List.forall_mem_nil _⟩⟩⟩) numericValid1025

def certificate1026 : RatFailureBudget := ⟨(1495537868925159927/976562500000000),(68350914721877/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay129.certificate2598),(2,CutFailureCertificates.Decay129.certificate2599)]⟩
theorem numericValid1026 : certificate1026.NumericValid := by decide +kernel
theorem sound1026 : certificate1026.Sound := rat_failure_budget_sound certificate1026 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2598,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay129.sound2599,List.forall_mem_nil _⟩⟩) numericValid1026

def certificate1027 : RatFailureBudget := ⟨(1495537868925159927/976562500000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay130.certificate2600),(902,CutFailureCertificates.Decay130.certificate2601),(1,CutFailureCertificates.Decay130.certificate2602)]⟩
theorem numericValid1027 : certificate1027.NumericValid := by decide +kernel
theorem sound1027 : certificate1027.Sound := rat_failure_budget_sound certificate1027 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2600,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2601,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2602,List.forall_mem_nil _⟩⟩⟩) numericValid1027

def certificate1028 : RatFailureBudget := ⟨(367120525546659461781/250000000000000000),(942125216409/3906250000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay130.certificate2603),(2,CutFailureCertificates.Decay130.certificate2604),(2,CutFailureCertificates.Decay130.certificate2605)]⟩
theorem numericValid1028 : certificate1028.NumericValid := by decide +kernel
theorem sound1028 : certificate1028.Sound := rat_failure_budget_sound certificate1028 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2603,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2604,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2605,List.forall_mem_nil _⟩⟩⟩) numericValid1028

def certificate1029 : RatFailureBudget := ⟨(367120525546659461781/250000000000000000),(71234220270337/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay130.certificate2606),(2,CutFailureCertificates.Decay130.certificate2607)]⟩
theorem numericValid1029 : certificate1029.NumericValid := by decide +kernel
theorem sound1029 : certificate1029.Sound := rat_failure_budget_sound certificate1029 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2606,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2607,List.forall_mem_nil _⟩⟩) numericValid1029

def certificate1030 : RatFailureBudget := ⟨(367120525546659461781/250000000000000000),(4473397077790059/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay130.certificate2608),(900,CutFailureCertificates.Decay130.certificate2609),(1,CutFailureCertificates.Decay130.certificate2610)]⟩
theorem numericValid1030 : certificate1030.NumericValid := by decide +kernel
theorem sound1030 : certificate1030.Sound := rat_failure_budget_sound certificate1030 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2608,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2609,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2610,List.forall_mem_nil _⟩⟩⟩) numericValid1030

def certificate1031 : RatFailureBudget := ⟨(704481895691454354547/500000000000000000),(907534732887/3906250000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay130.certificate2611),(2,CutFailureCertificates.Decay130.certificate2612),(2,CutFailureCertificates.Decay130.certificate2613)]⟩
theorem numericValid1031 : certificate1031.NumericValid := by decide +kernel
theorem sound1031 : certificate1031.Sound := rat_failure_budget_sound certificate1031 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2611,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2612,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2613,List.forall_mem_nil _⟩⟩⟩) numericValid1031

def certificate1032 : RatFailureBudget := ⟨(704481895691454354547/500000000000000000),(588008671869457/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay130.certificate2614),(2,CutFailureCertificates.Decay130.certificate2615)]⟩
theorem numericValid1032 : certificate1032.NumericValid := by decide +kernel
theorem sound1032 : certificate1032.Sound := rat_failure_budget_sound certificate1032 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2614,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2615,List.forall_mem_nil _⟩⟩) numericValid1032

def certificate1033 : RatFailureBudget := ⟨(704481895691454354547/500000000000000000),(4472590411315087/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay130.certificate2616),(900,CutFailureCertificates.Decay130.certificate2617),(1,CutFailureCertificates.Decay130.certificate2618)]⟩
theorem numericValid1033 : certificate1033.NumericValid := by decide +kernel
theorem sound1033 : certificate1033.Sound := rat_failure_budget_sound certificate1033 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2616,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2617,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2618,List.forall_mem_nil _⟩⟩⟩) numericValid1033

def certificate1034 : RatFailureBudget := ⟨(54105454784568570297/40000000000000000),(47630171990641/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay130.certificate2619),(2,CutFailureCertificates.Decay131.certificate2620),(2,CutFailureCertificates.Decay131.certificate2621)]⟩
theorem numericValid1034 : certificate1034.NumericValid := by decide +kernel
theorem sound1034 : certificate1034.Sound := rat_failure_budget_sound certificate1034 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay130.sound2619,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2620,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2621,List.forall_mem_nil _⟩⟩⟩) numericValid1034

def certificate1035 : RatFailureBudget := ⟨(54105454784568570297/40000000000000000),(608664244525549/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay131.certificate2622),(2,CutFailureCertificates.Decay131.certificate2623)]⟩
theorem numericValid1035 : certificate1035.NumericValid := by decide +kernel
theorem sound1035 : certificate1035.Sound := rat_failure_budget_sound certificate1035 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2622,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2623,List.forall_mem_nil _⟩⟩) numericValid1035

def certificate1036 : RatFailureBudget := ⟨(54105454784568570297/40000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay131.certificate2624),(898,CutFailureCertificates.Decay131.certificate2625),(1,CutFailureCertificates.Decay131.certificate2626)]⟩
theorem numericValid1036 : certificate1036.NumericValid := by decide +kernel
theorem sound1036 : certificate1036.Sound := rat_failure_budget_sound certificate1036 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2624,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2625,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2626,List.forall_mem_nil _⟩⟩⟩) numericValid1036

def certificate1037 : RatFailureBudget := ⟨(40602522845498831137/31250000000000000),(121963064493177/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay131.certificate2627),(2,CutFailureCertificates.Decay131.certificate2628),(2,CutFailureCertificates.Decay131.certificate2629)]⟩
theorem numericValid1037 : certificate1037.NumericValid := by decide +kernel
theorem sound1037 : certificate1037.Sound := rat_failure_budget_sound certificate1037 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2627,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2628,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2629,List.forall_mem_nil _⟩⟩⟩) numericValid1037

def certificate1038 : RatFailureBudget := ⟨(40602522845498831137/31250000000000000),(630052554900869/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay131.certificate2630),(2,CutFailureCertificates.Decay131.certificate2631)]⟩
theorem numericValid1038 : certificate1038.NumericValid := by decide +kernel
theorem sound1038 : certificate1038.Sound := rat_failure_budget_sound certificate1038 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2630,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2631,List.forall_mem_nil _⟩⟩) numericValid1038

def certificate1039 : RatFailureBudget := ⟨(40602522845498831137/31250000000000000),(4472588439023809/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay131.certificate2632),(898,CutFailureCertificates.Decay131.certificate2633),(1,CutFailureCertificates.Decay131.certificate2634)]⟩
theorem numericValid1039 : certificate1039.NumericValid := by decide +kernel
theorem sound1039 : certificate1039.Sound := rat_failure_budget_sound certificate1039 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2632,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2633,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2634,List.forall_mem_nil _⟩⟩⟩) numericValid1039

end Cycle12.CutFailureCertificates.Budget051
