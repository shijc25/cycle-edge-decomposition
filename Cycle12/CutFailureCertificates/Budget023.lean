import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay057
import Cycle12.CutFailureCertificates.Decay058
import Cycle12.CutFailureCertificates.Decay059

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget023

def certificate460 : RatFailureBudget := ⟨(4532740045392556597/200000000000000000),(7323036226997731/500000000000000000),(81/500000000000000000),[(2,CutFailureCertificates.Decay057.certificate1150),(2,CutFailureCertificates.Decay057.certificate1151),(2,CutFailureCertificates.Decay057.certificate1152)]⟩
theorem numericValid460 : certificate460.NumericValid := by decide +kernel
theorem sound460 : certificate460.Sound := rat_failure_budget_sound certificate460 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1150,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1151,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1152,List.forall_mem_nil _⟩⟩⟩) numericValid460

def certificate461 : RatFailureBudget := ⟨(4532740045392556597/200000000000000000),(13935602627917063/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay057.certificate1153),(2,CutFailureCertificates.Decay057.certificate1154)]⟩
theorem numericValid461 : certificate461.NumericValid := by decide +kernel
theorem sound461 : certificate461.Sound := rat_failure_budget_sound certificate461 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1153,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1154,List.forall_mem_nil _⟩⟩) numericValid461

def certificate462 : RatFailureBudget := ⟨(11117990995896675357/500000000000000000),(7348641899360223/500000000000000000),(41/500000000000000000),[(2,CutFailureCertificates.Decay057.certificate1155),(2,CutFailureCertificates.Decay057.certificate1156),(2,CutFailureCertificates.Decay057.certificate1157)]⟩
theorem numericValid462 : certificate462.NumericValid := by decide +kernel
theorem sound462 : certificate462.Sound := rat_failure_budget_sound certificate462 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1155,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1156,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1157,List.forall_mem_nil _⟩⟩⟩) numericValid462

def certificate463 : RatFailureBudget := ⟨(11117990995896675357/500000000000000000),(7040323030625189/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay057.certificate1158),(2,CutFailureCertificates.Decay057.certificate1159)]⟩
theorem numericValid463 : certificate463.NumericValid := by decide +kernel
theorem sound463 : certificate463.Sound := rat_failure_budget_sound certificate463 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1158,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1159,List.forall_mem_nil _⟩⟩) numericValid463

def certificate464 : RatFailureBudget := ⟨(2727356343157655291/125000000000000000),(16309140789832939/1000000000000000000),(17/250000000000000000),[(2,CutFailureCertificates.Decay058.certificate1160),(2,CutFailureCertificates.Decay058.certificate1161),(2,CutFailureCertificates.Decay058.certificate1162)]⟩
theorem numericValid464 : certificate464.NumericValid := by decide +kernel
theorem sound464 : certificate464.Sound := rat_failure_budget_sound certificate464 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1160,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1161,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1162,List.forall_mem_nil _⟩⟩⟩) numericValid464

def certificate465 : RatFailureBudget := ⟨(2727356343157655291/125000000000000000),(713277109053861/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay058.certificate1163),(2,CutFailureCertificates.Decay058.certificate1164)]⟩
theorem numericValid465 : certificate465.NumericValid := by decide +kernel
theorem sound465 : certificate465.Sound := rat_failure_budget_sound certificate465 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1163,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1164,List.forall_mem_nil _⟩⟩) numericValid465

def certificate466 : RatFailureBudget := ⟨(10705984450122921257/500000000000000000),(485185681711607/31250000000000000),(1/31250000000000000),[(2,CutFailureCertificates.Decay058.certificate1165),(2,CutFailureCertificates.Decay058.certificate1166),(2,CutFailureCertificates.Decay058.certificate1167)]⟩
theorem numericValid466 : certificate466.NumericValid := by decide +kernel
theorem sound466 : certificate466.Sound := rat_failure_budget_sound certificate466 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1165,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1166,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1167,List.forall_mem_nil _⟩⟩⟩) numericValid466

def certificate467 : RatFailureBudget := ⟨(10705984450122921257/500000000000000000),(7241962923704079/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay058.certificate1168),(2,CutFailureCertificates.Decay058.certificate1169)]⟩
theorem numericValid467 : certificate467.NumericValid := by decide +kernel
theorem sound467 : certificate467.Sound := rat_failure_budget_sound certificate467 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1168,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1169,List.forall_mem_nil _⟩⟩) numericValid467

def certificate468 : RatFailureBudget := ⟨(21015012089040713673/1000000000000000000),(48073322153863/3125000000000000),(1/62500000000000000),[(2,CutFailureCertificates.Decay058.certificate1170),(2,CutFailureCertificates.Decay058.certificate1171),(2,CutFailureCertificates.Decay058.certificate1172)]⟩
theorem numericValid468 : certificate468.NumericValid := by decide +kernel
theorem sound468 : certificate468.Sound := rat_failure_budget_sound certificate468 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1170,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1171,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1172,List.forall_mem_nil _⟩⟩⟩) numericValid468

def certificate469 : RatFailureBudget := ⟨(21015012089040713673/1000000000000000000),(1826704287079117/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay058.certificate1173),(2,CutFailureCertificates.Decay058.certificate1174)]⟩
theorem numericValid469 : certificate469.NumericValid := by decide +kernel
theorem sound469 : certificate469.Sound := rat_failure_budget_sound certificate469 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1173,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1174,List.forall_mem_nil _⟩⟩) numericValid469

def certificate470 : RatFailureBudget := ⟨(10313834274951837531/500000000000000000),(16848060607207701/1000000000000000000),(3/200000000000000000),[(2,CutFailureCertificates.Decay058.certificate1175),(2,CutFailureCertificates.Decay058.certificate1176),(2,CutFailureCertificates.Decay058.certificate1177)]⟩
theorem numericValid470 : certificate470.NumericValid := by decide +kernel
theorem sound470 : certificate470.Sound := rat_failure_budget_sound certificate470 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1175,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1176,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1177,List.forall_mem_nil _⟩⟩⟩) numericValid470

def certificate471 : RatFailureBudget := ⟨(10313834274951837531/500000000000000000),(14827134495426159/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay058.certificate1178),(2,CutFailureCertificates.Decay058.certificate1179)]⟩
theorem numericValid471 : certificate471.NumericValid := by decide +kernel
theorem sound471 : certificate471.Sound := rat_failure_budget_sound certificate471 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1178,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay058.sound1179,List.forall_mem_nil _⟩⟩) numericValid471

def certificate472 : RatFailureBudget := ⟨(161997108371813717/8000000000000000),(4002389389264167/250000000000000000),(7/1000000000000000000),[(2,CutFailureCertificates.Decay059.certificate1180),(2,CutFailureCertificates.Decay059.certificate1181),(2,CutFailureCertificates.Decay059.certificate1182)]⟩
theorem numericValid472 : certificate472.NumericValid := by decide +kernel
theorem sound472 : certificate472.Sound := rat_failure_budget_sound certificate472 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1180,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1181,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1182,List.forall_mem_nil _⟩⟩⟩) numericValid472

def certificate473 : RatFailureBudget := ⟨(161997108371813717/8000000000000000),(14957017401448101/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay059.certificate1183),(2,CutFailureCertificates.Decay059.certificate1184)]⟩
theorem numericValid473 : certificate473.NumericValid := by decide +kernel
theorem sound473 : certificate473.Sound := rat_failure_budget_sound certificate473 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1183,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1184,List.forall_mem_nil _⟩⟩) numericValid473

def certificate474 : RatFailureBudget := ⟨(4970158454520361661/250000000000000000),(15986739051325607/1000000000000000000),(3/1000000000000000000),[(2,CutFailureCertificates.Decay059.certificate1185),(2,CutFailureCertificates.Decay059.certificate1186),(2,CutFailureCertificates.Decay059.certificate1187)]⟩
theorem numericValid474 : certificate474.NumericValid := by decide +kernel
theorem sound474 : certificate474.Sound := rat_failure_budget_sound certificate474 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1185,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1186,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1187,List.forall_mem_nil _⟩⟩⟩) numericValid474

def certificate475 : RatFailureBudget := ⟨(4970158454520361661/250000000000000000),(15180224815020867/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay059.certificate1188),(2,CutFailureCertificates.Decay059.certificate1189)]⟩
theorem numericValid475 : certificate475.NumericValid := by decide +kernel
theorem sound475 : certificate475.Sound := rat_failure_budget_sound certificate475 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1188,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1189,List.forall_mem_nil _⟩⟩) numericValid475

def certificate476 : RatFailureBudget := ⟨(19520377059030781007/1000000000000000000),(8087075389915401/500000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay059.certificate1190),(2,CutFailureCertificates.Decay059.certificate1191),(2,CutFailureCertificates.Decay059.certificate1192)]⟩
theorem numericValid476 : certificate476.NumericValid := by decide +kernel
theorem sound476 : certificate476.Sound := rat_failure_budget_sound certificate476 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1190,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1191,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1192,List.forall_mem_nil _⟩⟩⟩) numericValid476

def certificate477 : RatFailureBudget := ⟨(19520377059030781007/1000000000000000000),(1537045683664699/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay059.certificate1193),(2,CutFailureCertificates.Decay059.certificate1194)]⟩
theorem numericValid477 : certificate477.NumericValid := by decide +kernel
theorem sound477 : certificate477.Sound := rat_failure_budget_sound certificate477 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1193,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1194,List.forall_mem_nil _⟩⟩) numericValid477

def certificate478 : RatFailureBudget := ⟨(19168601425222358897/1000000000000000000),(4132038717277449/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay059.certificate1195),(2,CutFailureCertificates.Decay059.certificate1196),(2,CutFailureCertificates.Decay059.certificate1197)]⟩
theorem numericValid478 : certificate478.NumericValid := by decide +kernel
theorem sound478 : certificate478.Sound := rat_failure_budget_sound certificate478 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1195,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1196,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1197,List.forall_mem_nil _⟩⟩⟩) numericValid478

def certificate479 : RatFailureBudget := ⟨(19168601425222358897/1000000000000000000),(969894227704459/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay059.certificate1198),(2,CutFailureCertificates.Decay059.certificate1199)]⟩
theorem numericValid479 : certificate479.NumericValid := by decide +kernel
theorem sound479 : certificate479.Sound := rat_failure_budget_sound certificate479 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1198,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay059.sound1199,List.forall_mem_nil _⟩⟩) numericValid479

end Cycle12.CutFailureCertificates.Budget023
