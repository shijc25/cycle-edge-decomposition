import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay072
import Cycle12.CutFailureCertificates.Decay073
import Cycle12.CutFailureCertificates.Decay074

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget029

def certificate580 : RatFailureBudget := ⟨(3050098791719196227/31250000000000000),(196455750007741/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay072.certificate1450),(2,CutFailureCertificates.Decay072.certificate1451),(2,CutFailureCertificates.Decay072.certificate1452)]⟩
theorem numericValid580 : certificate580.NumericValid := by decide +kernel
theorem sound580 : certificate580.Sound := rat_failure_budget_sound certificate580 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1450,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1451,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1452,List.forall_mem_nil _⟩⟩⟩) numericValid580

def certificate581 : RatFailureBudget := ⟨(3050098791719196227/31250000000000000),(4738800492912883/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay072.certificate1453),(2,CutFailureCertificates.Decay072.certificate1454)]⟩
theorem numericValid581 : certificate581.NumericValid := by decide +kernel
theorem sound581 : certificate581.Sound := rat_failure_budget_sound certificate581 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1453,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1454,List.forall_mem_nil _⟩⟩) numericValid581

def certificate582 : RatFailureBudget := ⟨(95387765071235983997/1000000000000000000),(3851668811880989/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay072.certificate1455),(2,CutFailureCertificates.Decay072.certificate1456),(2,CutFailureCertificates.Decay072.certificate1457)]⟩
theorem numericValid582 : certificate582.NumericValid := by decide +kernel
theorem sound582 : certificate582.Sound := rat_failure_budget_sound certificate582 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1455,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1456,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1457,List.forall_mem_nil _⟩⟩⟩) numericValid582

def certificate583 : RatFailureBudget := ⟨(95387765071235983997/1000000000000000000),(2415642440374297/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay072.certificate1458),(2,CutFailureCertificates.Decay072.certificate1459)]⟩
theorem numericValid583 : certificate583.NumericValid := by decide +kernel
theorem sound583 : certificate583.Sound := rat_failure_budget_sound certificate583 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1458,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1459,List.forall_mem_nil _⟩⟩) numericValid583

def certificate584 : RatFailureBudget := ⟨(46620220761607238501/500000000000000000),(3901245938444373/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay073.certificate1460),(2,CutFailureCertificates.Decay073.certificate1461),(2,CutFailureCertificates.Decay073.certificate1462)]⟩
theorem numericValid584 : certificate584.NumericValid := by decide +kernel
theorem sound584 : certificate584.Sound := rat_failure_budget_sound certificate584 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1460,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1461,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1462,List.forall_mem_nil _⟩⟩⟩) numericValid584

def certificate585 : RatFailureBudget := ⟨(46620220761607238501/500000000000000000),(2446781089198177/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay073.certificate1463),(2,CutFailureCertificates.Decay073.certificate1464)]⟩
theorem numericValid585 : certificate585.NumericValid := by decide +kernel
theorem sound585 : certificate585.Sound := rat_failure_budget_sound certificate585 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1463,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1464,List.forall_mem_nil _⟩⟩) numericValid585

def certificate586 : RatFailureBudget := ⟨(4557924207760763037/50000000000000000),(201358379775689/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay073.certificate1465),(2,CutFailureCertificates.Decay073.certificate1466),(2,CutFailureCertificates.Decay073.certificate1467)]⟩
theorem numericValid586 : certificate586.NumericValid := by decide +kernel
theorem sound586 : certificate586.Sound := rat_failure_budget_sound certificate586 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1465,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1466,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1467,List.forall_mem_nil _⟩⟩⟩) numericValid586

def certificate587 : RatFailureBudget := ⟨(4557924207760763037/50000000000000000),(4987101870237313/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay073.certificate1468),(2,CutFailureCertificates.Decay073.certificate1469)]⟩
theorem numericValid587 : certificate587.NumericValid := by decide +kernel
theorem sound587 : certificate587.Sound := rat_failure_budget_sound certificate587 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1468,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1469,List.forall_mem_nil _⟩⟩) numericValid587

def certificate588 : RatFailureBudget := ⟨(89139318625963389647/1000000000000000000),(4022125455515617/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay073.certificate1470),(2,CutFailureCertificates.Decay073.certificate1471),(2,CutFailureCertificates.Decay073.certificate1472)]⟩
theorem numericValid588 : certificate588.NumericValid := by decide +kernel
theorem sound588 : certificate588.Sound := rat_failure_budget_sound certificate588 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1470,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1471,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1472,List.forall_mem_nil _⟩⟩⟩) numericValid588

def certificate589 : RatFailureBudget := ⟨(89139318625963389647/1000000000000000000),(5052285659264379/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay073.certificate1473),(2,CutFailureCertificates.Decay073.certificate1474)]⟩
theorem numericValid589 : certificate589.NumericValid := by decide +kernel
theorem sound589 : certificate589.Sound := rat_failure_budget_sound certificate589 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1473,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1474,List.forall_mem_nil _⟩⟩) numericValid589

def certificate590 : RatFailureBudget := ⟨(87180495143465975733/1000000000000000000),(4083545879261849/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay073.certificate1475),(2,CutFailureCertificates.Decay073.certificate1476),(2,CutFailureCertificates.Decay073.certificate1477)]⟩
theorem numericValid590 : certificate590.NumericValid := by decide +kernel
theorem sound590 : certificate590.Sound := rat_failure_budget_sound certificate590 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1475,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1476,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1477,List.forall_mem_nil _⟩⟩⟩) numericValid590

def certificate591 : RatFailureBudget := ⟨(87180495143465975733/1000000000000000000),(5146977173470157/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay073.certificate1478),(2,CutFailureCertificates.Decay073.certificate1479)]⟩
theorem numericValid591 : certificate591.NumericValid := by decide +kernel
theorem sound591 : certificate591.Sound := rat_failure_budget_sound certificate591 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1478,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay073.sound1479,List.forall_mem_nil _⟩⟩) numericValid591

def certificate592 : RatFailureBudget := ⟨(83434655556689126119/1000000000000000000),(530285490221711/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay074.certificate1480),(2,CutFailureCertificates.Decay074.certificate1481),(2,CutFailureCertificates.Decay074.certificate1482)]⟩
theorem numericValid592 : certificate592.NumericValid := by decide +kernel
theorem sound592 : certificate592.Sound := rat_failure_budget_sound certificate592 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1480,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1481,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1482,List.forall_mem_nil _⟩⟩⟩) numericValid592

def certificate593 : RatFailureBudget := ⟨(83434655556689126119/1000000000000000000),(5351272468260523/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay074.certificate1483),(2,CutFailureCertificates.Decay074.certificate1484)]⟩
theorem numericValid593 : certificate593.NumericValid := by decide +kernel
theorem sound593 : certificate593.Sound := rat_failure_budget_sound certificate593 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1483,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1484,List.forall_mem_nil _⟩⟩) numericValid593

def certificate594 : RatFailureBudget := ⟨(163286601437693719/2000000000000000),(4419418883029493/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay074.certificate1485),(2,CutFailureCertificates.Decay074.certificate1486),(2,CutFailureCertificates.Decay074.certificate1487)]⟩
theorem numericValid594 : certificate594.NumericValid := by decide +kernel
theorem sound594 : certificate594.Sound := rat_failure_budget_sound certificate594 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1485,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1486,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1487,List.forall_mem_nil _⟩⟩⟩) numericValid594

def certificate595 : RatFailureBudget := ⟨(163286601437693719/2000000000000000),(5406076440314317/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay074.certificate1488),(2,CutFailureCertificates.Decay074.certificate1489)]⟩
theorem numericValid595 : certificate595.NumericValid := by decide +kernel
theorem sound595 : certificate595.Sound := rat_failure_budget_sound certificate595 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1488,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1489,List.forall_mem_nil _⟩⟩) numericValid595

def certificate596 : RatFailureBudget := ⟨(19975899602285509873/250000000000000000),(433027611187279/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay074.certificate1490),(2,CutFailureCertificates.Decay074.certificate1491),(2,CutFailureCertificates.Decay074.certificate1492)]⟩
theorem numericValid596 : certificate596.NumericValid := by decide +kernel
theorem sound596 : certificate596.Sound := rat_failure_budget_sound certificate596 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1490,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1491,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1492,List.forall_mem_nil _⟩⟩⟩) numericValid596

def certificate597 : RatFailureBudget := ⟨(19975899602285509873/250000000000000000),(2736380559074773/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay074.certificate1493),(2,CutFailureCertificates.Decay074.certificate1494)]⟩
theorem numericValid597 : certificate597.NumericValid := by decide +kernel
theorem sound597 : certificate597.Sound := rat_failure_budget_sound certificate597 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1493,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1494,List.forall_mem_nil _⟩⟩) numericValid597

def certificate598 : RatFailureBudget := ⟨(38285769444484094131/500000000000000000),(2246931109441537/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay074.certificate1495),(2,CutFailureCertificates.Decay074.certificate1496),(2,CutFailureCertificates.Decay074.certificate1497)]⟩
theorem numericValid598 : certificate598.NumericValid := by decide +kernel
theorem sound598 : certificate598.Sound := rat_failure_budget_sound certificate598 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1495,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1496,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1497,List.forall_mem_nil _⟩⟩⟩) numericValid598

def certificate599 : RatFailureBudget := ⟨(38285769444484094131/500000000000000000),(567917166004207/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay074.certificate1498),(2,CutFailureCertificates.Decay074.certificate1499)]⟩
theorem numericValid599 : certificate599.NumericValid := by decide +kernel
theorem sound599 : certificate599.Sound := rat_failure_budget_sound certificate599 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1498,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay074.sound1499,List.forall_mem_nil _⟩⟩) numericValid599

end Cycle12.CutFailureCertificates.Budget029
