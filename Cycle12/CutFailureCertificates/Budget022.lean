import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay055
import Cycle12.CutFailureCertificates.Decay056
import Cycle12.CutFailureCertificates.Decay057

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget022

def certificate440 : RatFailureBudget := ⟨(14684821021866378471/500000000000000000),(3017605471208453/250000000000000000),(32881/500000000000000000),[(2,CutFailureCertificates.Decay055.certificate1100),(2,CutFailureCertificates.Decay055.certificate1101),(2,CutFailureCertificates.Decay055.certificate1102)]⟩
theorem numericValid440 : certificate440.NumericValid := by decide +kernel
theorem sound440 : certificate440.Sound := rat_failure_budget_sound certificate440 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1100,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1101,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1102,List.forall_mem_nil _⟩⟩⟩) numericValid440

def certificate441 : RatFailureBudget := ⟨(14684821021866378471/500000000000000000),(1462585984046059/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay055.certificate1103),(2,CutFailureCertificates.Decay055.certificate1104)]⟩
theorem numericValid441 : certificate441.NumericValid := by decide +kernel
theorem sound441 : certificate441.Sound := rat_failure_budget_sound certificate441 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1103,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1104,List.forall_mem_nil _⟩⟩) numericValid441

def certificate442 : RatFailureBudget := ⟨(28179275827658174181/1000000000000000000),(12523546265937113/1000000000000000000),(105321/1000000000000000000),[(2,CutFailureCertificates.Decay055.certificate1105),(2,CutFailureCertificates.Decay055.certificate1106),(2,CutFailureCertificates.Decay055.certificate1107)]⟩
theorem numericValid442 : certificate442.NumericValid := by decide +kernel
theorem sound442 : certificate442.Sound := rat_failure_budget_sound certificate442 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1105,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1106,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1107,List.forall_mem_nil _⟩⟩⟩) numericValid442

def certificate443 : RatFailureBudget := ⟨(28179275827658174181/1000000000000000000),(2412938394989539/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay055.certificate1108),(2,CutFailureCertificates.Decay055.certificate1109)]⟩
theorem numericValid443 : certificate443.NumericValid := by decide +kernel
theorem sound443 : certificate443.Sound := rat_failure_budget_sound certificate443 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1108,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1109,List.forall_mem_nil _⟩⟩) numericValid443

def certificate444 : RatFailureBudget := ⟨(6763181848071071287/250000000000000000),(12950018349728781/1000000000000000000),(7331/200000000000000000),[(2,CutFailureCertificates.Decay055.certificate1110),(2,CutFailureCertificates.Decay055.certificate1111),(2,CutFailureCertificates.Decay055.certificate1112)]⟩
theorem numericValid444 : certificate444.NumericValid := by decide +kernel
theorem sound444 : certificate444.Sound := rat_failure_budget_sound certificate444 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1110,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1111,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1112,List.forall_mem_nil _⟩⟩⟩) numericValid444

def certificate445 : RatFailureBudget := ⟨(6763181848071071287/250000000000000000),(48714747550933/3906250000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay055.certificate1113),(2,CutFailureCertificates.Decay055.certificate1114)]⟩
theorem numericValid445 : certificate445.NumericValid := by decide +kernel
theorem sound445 : certificate445.Sound := rat_failure_budget_sound certificate445 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1113,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1114,List.forall_mem_nil _⟩⟩) numericValid445

def certificate446 : RatFailureBudget := ⟨(25985614621119251927/1000000000000000000),(13247534217787941/1000000000000000000),(7673/500000000000000000),[(2,CutFailureCertificates.Decay055.certificate1115),(2,CutFailureCertificates.Decay055.certificate1116),(2,CutFailureCertificates.Decay055.certificate1117)]⟩
theorem numericValid446 : certificate446.NumericValid := by decide +kernel
theorem sound446 : certificate446.Sound := rat_failure_budget_sound certificate446 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1115,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1116,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1117,List.forall_mem_nil _⟩⟩⟩) numericValid446

def certificate447 : RatFailureBudget := ⟨(25985614621119251927/1000000000000000000),(6396974536468721/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay055.certificate1118),(2,CutFailureCertificates.Decay055.certificate1119)]⟩
theorem numericValid447 : certificate447.NumericValid := by decide +kernel
theorem sound447 : certificate447.Sound := rat_failure_budget_sound certificate447 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1118,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay055.sound1119,List.forall_mem_nil _⟩⟩) numericValid447

def certificate448 : RatFailureBudget := ⟨(1273653923783853421/50000000000000000),(2662373946507043/200000000000000000),(1403/500000000000000000),[(2,CutFailureCertificates.Decay056.certificate1120),(2,CutFailureCertificates.Decay056.certificate1121),(2,CutFailureCertificates.Decay056.certificate1122)]⟩
theorem numericValid448 : certificate448.NumericValid := by decide +kernel
theorem sound448 : certificate448.Sound := rat_failure_budget_sound certificate448 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1120,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1121,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1122,List.forall_mem_nil _⟩⟩⟩) numericValid448

def certificate449 : RatFailureBudget := ⟨(1273653923783853421/50000000000000000),(12874456576474963/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay056.certificate1123),(2,CutFailureCertificates.Decay056.certificate1124)]⟩
theorem numericValid449 : certificate449.NumericValid := by decide +kernel
theorem sound449 : certificate449.Sound := rat_failure_budget_sound certificate449 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1123,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1124,List.forall_mem_nil _⟩⟩) numericValid449

def certificate450 : RatFailureBudget := ⟨(24973922070982979467/1000000000000000000),(13482449675101619/1000000000000000000),(701/500000000000000000),[(2,CutFailureCertificates.Decay056.certificate1125),(2,CutFailureCertificates.Decay056.certificate1126),(2,CutFailureCertificates.Decay056.certificate1127)]⟩
theorem numericValid450 : certificate450.NumericValid := by decide +kernel
theorem sound450 : certificate450.Sound := rat_failure_budget_sound certificate450 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1125,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1126,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1127,List.forall_mem_nil _⟩⟩⟩) numericValid450

def certificate451 : RatFailureBudget := ⟨(24973922070982979467/1000000000000000000),(13067264950856999/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay056.certificate1128),(2,CutFailureCertificates.Decay056.certificate1129)]⟩
theorem numericValid451 : certificate451.NumericValid := by decide +kernel
theorem sound451 : certificate451.Sound := rat_failure_budget_sound certificate451 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1128,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1129,List.forall_mem_nil _⟩⟩) numericValid451

def certificate452 : RatFailureBudget := ⟨(1530480928390214573/62500000000000000),(2783143564131401/200000000000000000),(281/250000000000000000),[(2,CutFailureCertificates.Decay056.certificate1130),(2,CutFailureCertificates.Decay056.certificate1131),(2,CutFailureCertificates.Decay056.certificate1132)]⟩
theorem numericValid452 : certificate452.NumericValid := by decide +kernel
theorem sound452 : certificate452.Sound := rat_failure_budget_sound certificate452 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1130,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1131,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1132,List.forall_mem_nil _⟩⟩⟩) numericValid452

def certificate453 : RatFailureBudget := ⟨(1530480928390214573/62500000000000000),(2641091449217617/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay056.certificate1133),(2,CutFailureCertificates.Decay056.certificate1134)]⟩
theorem numericValid453 : certificate453.NumericValid := by decide +kernel
theorem sound453 : certificate453.Sound := rat_failure_budget_sound certificate453 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1133,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1134,List.forall_mem_nil _⟩⟩) numericValid453

def certificate454 : RatFailureBudget := ⟨(12006982453999286597/500000000000000000),(3525152834114483/250000000000000000),(69/125000000000000000),[(2,CutFailureCertificates.Decay056.certificate1135),(2,CutFailureCertificates.Decay056.certificate1136),(2,CutFailureCertificates.Decay056.certificate1137)]⟩
theorem numericValid454 : certificate454.NumericValid := by decide +kernel
theorem sound454 : certificate454.Sound := rat_failure_budget_sound certificate454 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1135,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1136,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1137,List.forall_mem_nil _⟩⟩⟩) numericValid454

def certificate455 : RatFailureBudget := ⟨(12006982453999286597/500000000000000000),(536224461106749/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay056.certificate1138),(2,CutFailureCertificates.Decay056.certificate1139)]⟩
theorem numericValid455 : certificate455.NumericValid := by decide +kernel
theorem sound455 : certificate455.Sound := rat_failure_budget_sound certificate455 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1138,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay056.sound1139,List.forall_mem_nil _⟩⟩) numericValid455

def certificate456 : RatFailureBudget := ⟨(368004969325543779/15625000000000000),(7130128197654349/500000000000000000),(11/25000000000000000),[(2,CutFailureCertificates.Decay057.certificate1140),(2,CutFailureCertificates.Decay057.certificate1141),(2,CutFailureCertificates.Decay057.certificate1142)]⟩
theorem numericValid456 : certificate456.NumericValid := by decide +kernel
theorem sound456 : certificate456.Sound := rat_failure_budget_sound certificate456 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1140,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1141,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1142,List.forall_mem_nil _⟩⟩⟩) numericValid456

def certificate457 : RatFailureBudget := ⟨(368004969325543779/15625000000000000),(13598835910865769/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay057.certificate1143),(2,CutFailureCertificates.Decay057.certificate1144)]⟩
theorem numericValid457 : certificate457.NumericValid := by decide +kernel
theorem sound457 : certificate457.Sound := rat_failure_budget_sound certificate457 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1143,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1144,List.forall_mem_nil _⟩⟩) numericValid457

def certificate458 : RatFailureBudget := ⟨(2887794613220535943/125000000000000000),(14474409276913873/1000000000000000000),(101/500000000000000000),[(2,CutFailureCertificates.Decay057.certificate1145),(2,CutFailureCertificates.Decay057.certificate1146),(2,CutFailureCertificates.Decay057.certificate1147)]⟩
theorem numericValid458 : certificate458.NumericValid := by decide +kernel
theorem sound458 : certificate458.Sound := rat_failure_budget_sound certificate458 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1145,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1146,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1147,List.forall_mem_nil _⟩⟩⟩) numericValid458

def certificate459 : RatFailureBudget := ⟨(2887794613220535943/125000000000000000),(6863486027391837/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay057.certificate1148),(2,CutFailureCertificates.Decay057.certificate1149)]⟩
theorem numericValid459 : certificate459.NumericValid := by decide +kernel
theorem sound459 : certificate459.Sound := rat_failure_budget_sound certificate459 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1148,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay057.sound1149,List.forall_mem_nil _⟩⟩) numericValid459

end Cycle12.CutFailureCertificates.Budget022
