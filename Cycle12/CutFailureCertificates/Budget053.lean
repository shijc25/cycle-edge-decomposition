import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay134
import Cycle12.CutFailureCertificates.Decay135

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget053

def certificate1060 : RatFailureBudget := ⟨(198806338180814466443/200000000000000000),(4472589425169451/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay134.certificate2688),(890,CutFailureCertificates.Decay134.certificate2689),(1,CutFailureCertificates.Decay134.certificate2690)]⟩
theorem numericValid1060 : certificate1060.NumericValid := by decide +kernel
theorem sound1060 : certificate1060.Sound := rat_failure_budget_sound certificate1060 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2688,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2689,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2690,List.forall_mem_nil _⟩⟩⟩) numericValid1060

def certificate1061 : RatFailureBudget := ⟨(958430071261117944869/1000000000000000000),(406662702868701/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay134.certificate2691),(2,CutFailureCertificates.Decay134.certificate2692),(2,CutFailureCertificates.Decay134.certificate2693)]⟩
theorem numericValid1061 : certificate1061.NumericValid := by decide +kernel
theorem sound1061 : certificate1061.Sound := rat_failure_budget_sound certificate1061 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2691,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2692,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2693,List.forall_mem_nil _⟩⟩⟩) numericValid1061

def certificate1062 : RatFailureBudget := ⟨(958430071261117944869/1000000000000000000),(343649530882249/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay134.certificate2694),(2,CutFailureCertificates.Decay134.certificate2695)]⟩
theorem numericValid1062 : certificate1062.NumericValid := by decide +kernel
theorem sound1062 : certificate1062.Sound := rat_failure_budget_sound certificate1062 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2694,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2695,List.forall_mem_nil _⟩⟩) numericValid1062

def certificate1063 : RatFailureBudget := ⟨(958430071261117944869/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay134.certificate2696),(888,CutFailureCertificates.Decay134.certificate2697),(1,CutFailureCertificates.Decay134.certificate2698)]⟩
theorem numericValid1063 : certificate1063.NumericValid := by decide +kernel
theorem sound1063 : certificate1063.Sound := rat_failure_budget_sound certificate1063 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2696,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2697,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2698,List.forall_mem_nil _⟩⟩⟩) numericValid1063

def certificate1064 : RatFailureBudget := ⟨(231118446031702313983/250000000000000000),(75010997971603/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay134.certificate2699),(2,CutFailureCertificates.Decay135.certificate2700),(2,CutFailureCertificates.Decay135.certificate2701)]⟩
theorem numericValid1064 : certificate1064.NumericValid := by decide +kernel
theorem sound1064 : certificate1064.Sound := rat_failure_budget_sound certificate1064 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay134.sound2699,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay135.sound2700,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay135.sound2701,List.forall_mem_nil _⟩⟩⟩) numericValid1064

def certificate1065 : RatFailureBudget := ⟨(231118446031702313983/250000000000000000),(297157597752733/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay135.certificate2702),(2,CutFailureCertificates.Decay135.certificate2703)]⟩
theorem numericValid1065 : certificate1065.NumericValid := by decide +kernel
theorem sound1065 : certificate1065.Sound := rat_failure_budget_sound certificate1065 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay135.sound2702,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay135.sound2703,List.forall_mem_nil _⟩⟩) numericValid1065

def certificate1066 : RatFailureBudget := ⟨(231118446031702313983/250000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay135.certificate2704),(888,CutFailureCertificates.Decay135.certificate2705),(1,CutFailureCertificates.Decay135.certificate2706)]⟩
theorem numericValid1066 : certificate1066.NumericValid := by decide +kernel
theorem sound1066 : certificate1066.Sound := rat_failure_budget_sound certificate1066 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay135.sound2704,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay135.sound2705,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay135.sound2706,List.forall_mem_nil _⟩⟩⟩) numericValid1066

end Cycle12.CutFailureCertificates.Budget053
