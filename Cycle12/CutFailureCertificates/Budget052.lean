import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay131
import Cycle12.CutFailureCertificates.Decay132
import Cycle12.CutFailureCertificates.Decay133
import Cycle12.CutFailureCertificates.Decay134

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget052

def certificate1040 : RatFailureBudget := ⟨(9989568828393191787/8000000000000000),(31212214861383/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay131.certificate2635),(2,CutFailureCertificates.Decay131.certificate2636),(2,CutFailureCertificates.Decay131.certificate2637)]⟩
theorem numericValid1040 : certificate1040.NumericValid := by decide +kernel
theorem sound1040 : certificate1040.Sound := rat_failure_budget_sound certificate1040 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2635,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2636,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2637,List.forall_mem_nil _⟩⟩⟩) numericValid1040

def certificate1041 : RatFailureBudget := ⟨(9989568828393191787/8000000000000000),(20361797746337/31250000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay131.certificate2638),(2,CutFailureCertificates.Decay131.certificate2639)]⟩
theorem numericValid1041 : certificate1041.NumericValid := by decide +kernel
theorem sound1041 : certificate1041.Sound := rat_failure_budget_sound certificate1041 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2638,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay131.sound2639,List.forall_mem_nil _⟩⟩) numericValid1041

def certificate1042 : RatFailureBudget := ⟨(9989568828393191787/8000000000000000),(1118149082047217/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay132.certificate2640),(896,CutFailureCertificates.Decay132.certificate2641),(1,CutFailureCertificates.Decay132.certificate2642)]⟩
theorem numericValid1042 : certificate1042.NumericValid := by decide +kernel
theorem sound1042 : certificate1042.Sound := rat_failure_budget_sound certificate1042 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2640,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2641,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2642,List.forall_mem_nil _⟩⟩⟩) numericValid1042

def certificate1043 : RatFailureBudget := ⟨(1200698245399928659727/1000000000000000000),(249615196275019/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay132.certificate2643),(2,CutFailureCertificates.Decay132.certificate2644),(2,CutFailureCertificates.Decay132.certificate2645)]⟩
theorem numericValid1043 : certificate1043.NumericValid := by decide +kernel
theorem sound1043 : certificate1043.Sound := rat_failure_budget_sound certificate1043 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2643,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2644,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2645,List.forall_mem_nil _⟩⟩⟩) numericValid1043

def certificate1044 : RatFailureBudget := ⟨(1200698245399928659727/1000000000000000000),(727974437435781/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay132.certificate2646),(2,CutFailureCertificates.Decay132.certificate2647)]⟩
theorem numericValid1044 : certificate1044.NumericValid := by decide +kernel
theorem sound1044 : certificate1044.Sound := rat_failure_budget_sound certificate1044 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2646,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2647,List.forall_mem_nil _⟩⟩) numericValid1044

def certificate1045 : RatFailureBudget := ⟨(1200698245399928659727/1000000000000000000),(2237392783324173/500000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay132.certificate2648),(896,CutFailureCertificates.Decay132.certificate2649),(1,CutFailureCertificates.Decay132.certificate2650)]⟩
theorem numericValid1045 : certificate1045.NumericValid := by decide +kernel
theorem sound1045 : certificate1045.Sound := rat_failure_budget_sound certificate1045 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2648,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2649,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2650,List.forall_mem_nil _⟩⟩⟩) numericValid1045

def certificate1046 : RatFailureBudget := ⟨(1155117845288214377213/1000000000000000000),(132709053526793/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay132.certificate2651),(2,CutFailureCertificates.Decay132.certificate2652),(2,CutFailureCertificates.Decay132.certificate2653)]⟩
theorem numericValid1046 : certificate1046.NumericValid := by decide +kernel
theorem sound1046 : certificate1046.Sound := rat_failure_budget_sound certificate1046 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2651,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2652,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2653,List.forall_mem_nil _⟩⟩⟩) numericValid1046

def certificate1047 : RatFailureBudget := ⟨(1155117845288214377213/1000000000000000000),(645381508174461/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay132.certificate2654),(2,CutFailureCertificates.Decay132.certificate2655)]⟩
theorem numericValid1047 : certificate1047.NumericValid := by decide +kernel
theorem sound1047 : certificate1047.Sound := rat_failure_budget_sound certificate1047 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2654,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2655,List.forall_mem_nil _⟩⟩) numericValid1047

def certificate1048 : RatFailureBudget := ⟨(1155117845288214377213/1000000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay132.certificate2656),(894,CutFailureCertificates.Decay132.certificate2657),(1,CutFailureCertificates.Decay132.certificate2658)]⟩
theorem numericValid1048 : certificate1048.NumericValid := by decide +kernel
theorem sound1048 : certificate1048.Sound := rat_failure_budget_sound certificate1048 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2656,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2657,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2658,List.forall_mem_nil _⟩⟩⟩) numericValid1048

def certificate1049 : RatFailureBudget := ⟨(555899549794833767863/500000000000000000),(271515995396759/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay132.certificate2659),(2,CutFailureCertificates.Decay133.certificate2660),(2,CutFailureCertificates.Decay133.certificate2661)]⟩
theorem numericValid1049 : certificate1049.NumericValid := by decide +kernel
theorem sound1049 : certificate1049.Sound := rat_failure_budget_sound certificate1049 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay132.sound2659,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2660,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2661,List.forall_mem_nil _⟩⟩⟩) numericValid1049

def certificate1050 : RatFailureBudget := ⟨(555899549794833767863/500000000000000000),(179404889715899/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay133.certificate2662),(2,CutFailureCertificates.Decay133.certificate2663)]⟩
theorem numericValid1050 : certificate1050.NumericValid := by decide +kernel
theorem sound1050 : certificate1050.Sound := rat_failure_budget_sound certificate1050 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2662,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2663,List.forall_mem_nil _⟩⟩) numericValid1050

def certificate1051 : RatFailureBudget := ⟨(555899549794833767863/500000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay133.certificate2664),(892,CutFailureCertificates.Decay133.certificate2665),(1,CutFailureCertificates.Decay133.certificate2666)]⟩
theorem numericValid1051 : certificate1051.NumericValid := by decide +kernel
theorem sound1051 : certificate1051.Sound := rat_failure_budget_sound certificate1051 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2664,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2665,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2666,List.forall_mem_nil _⟩⟩⟩) numericValid1051

def certificate1052 : RatFailureBudget := ⟨(26764961125307303143/25000000000000000),(277080124548891/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay133.certificate2667),(2,CutFailureCertificates.Decay133.certificate2668),(2,CutFailureCertificates.Decay133.certificate2669)]⟩
theorem numericValid1052 : certificate1052.NumericValid := by decide +kernel
theorem sound1052 : certificate1052.Sound := rat_failure_budget_sound certificate1052 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2667,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2668,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2669,List.forall_mem_nil _⟩⟩⟩) numericValid1052

def certificate1053 : RatFailureBudget := ⟨(26764961125307303143/25000000000000000),(399166208000637/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay133.certificate2670),(2,CutFailureCertificates.Decay133.certificate2671)]⟩
theorem numericValid1053 : certificate1053.NumericValid := by decide +kernel
theorem sound1053 : certificate1053.Sound := rat_failure_budget_sound certificate1053 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2670,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2671,List.forall_mem_nil _⟩⟩) numericValid1053

def certificate1054 : RatFailureBudget := ⟨(26764961125307303143/25000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay133.certificate2672),(892,CutFailureCertificates.Decay133.certificate2673),(1,CutFailureCertificates.Decay133.certificate2674)]⟩
theorem numericValid1054 : certificate1054.NumericValid := by decide +kernel
theorem sound1054 : certificate1054.Sound := rat_failure_budget_sound certificate1054 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2672,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2673,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2674,List.forall_mem_nil _⟩⟩⟩) numericValid1054

def certificate1055 : RatFailureBudget := ⟨(1031383427495183753137/1000000000000000000),(263687729781261/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay133.certificate2675),(2,CutFailureCertificates.Decay133.certificate2676),(2,CutFailureCertificates.Decay133.certificate2677)]⟩
theorem numericValid1055 : certificate1055.NumericValid := by decide +kernel
theorem sound1055 : certificate1055.Sound := rat_failure_budget_sound certificate1055 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2675,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2676,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2677,List.forall_mem_nil _⟩⟩⟩) numericValid1055

def certificate1056 : RatFailureBudget := ⟨(1031383427495183753137/1000000000000000000),(151247576645089/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay133.certificate2678),(2,CutFailureCertificates.Decay133.certificate2679)]⟩
theorem numericValid1056 : certificate1056.NumericValid := by decide +kernel
theorem sound1056 : certificate1056.Sound := rat_failure_budget_sound certificate1056 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2678,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay133.sound2679,List.forall_mem_nil _⟩⟩) numericValid1056

def certificate1057 : RatFailureBudget := ⟨(1031383427495183753137/1000000000000000000),(4472645635467631/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay134.certificate2680),(890,CutFailureCertificates.Decay134.certificate2681),(1,CutFailureCertificates.Decay134.certificate2682)]⟩
theorem numericValid1057 : certificate1057.NumericValid := by decide +kernel
theorem sound1057 : certificate1057.Sound := rat_failure_budget_sound certificate1057 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2680,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2681,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2682,List.forall_mem_nil _⟩⟩⟩) numericValid1057

def certificate1058 : RatFailureBudget := ⟨(198806338180814466443/200000000000000000),(264544627853239/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay134.certificate2683),(2,CutFailureCertificates.Decay134.certificate2684),(2,CutFailureCertificates.Decay134.certificate2685)]⟩
theorem numericValid1058 : certificate1058.NumericValid := by decide +kernel
theorem sound1058 : certificate1058.Sound := rat_failure_budget_sound certificate1058 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2683,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2684,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2685,List.forall_mem_nil _⟩⟩⟩) numericValid1058

def certificate1059 : RatFailureBudget := ⟨(198806338180814466443/200000000000000000),(394190300226827/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay134.certificate2686),(2,CutFailureCertificates.Decay134.certificate2687)]⟩
theorem numericValid1059 : certificate1059.NumericValid := by decide +kernel
theorem sound1059 : certificate1059.Sound := rat_failure_budget_sound certificate1059 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2686,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2687,List.forall_mem_nil _⟩⟩) numericValid1059

end Cycle12.CutFailureCertificates.Budget052
