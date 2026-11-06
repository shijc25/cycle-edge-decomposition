import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay070
import Cycle12.CutFailureCertificates.Decay071
import Cycle12.CutFailureCertificates.Decay072

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget028

def certificate560 : RatFailureBudget := ⟨(39386888540114143997/250000000000000000),(2703891699845947/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay070.certificate1400),(2,CutFailureCertificates.Decay070.certificate1401),(2,CutFailureCertificates.Decay070.certificate1402)]⟩
theorem numericValid560 : certificate560.NumericValid := by decide +kernel
theorem sound560 : certificate560.Sound := rat_failure_budget_sound certificate560 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1400,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1401,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1402,List.forall_mem_nil _⟩⟩⟩) numericValid560

def certificate561 : RatFailureBudget := ⟨(39386888540114143997/250000000000000000),(832490067788311/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay070.certificate1403),(2,CutFailureCertificates.Decay070.certificate1404)]⟩
theorem numericValid561 : certificate561.NumericValid := by decide +kernel
theorem sound561 : certificate561.Sound := rat_failure_budget_sound certificate561 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1403,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1404,List.forall_mem_nil _⟩⟩) numericValid561

def certificate562 : RatFailureBudget := ⟨(74574689523806123209/500000000000000000),(2817524148763533/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay070.certificate1405),(2,CutFailureCertificates.Decay070.certificate1406),(2,CutFailureCertificates.Decay070.certificate1407)]⟩
theorem numericValid562 : certificate562.NumericValid := by decide +kernel
theorem sound562 : certificate562.Sound := rat_failure_budget_sound certificate562 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1405,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1406,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1407,List.forall_mem_nil _⟩⟩⟩) numericValid562

def certificate563 : RatFailureBudget := ⟨(74574689523806123209/500000000000000000),(346479720352069/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay070.certificate1408),(2,CutFailureCertificates.Decay070.certificate1409)]⟩
theorem numericValid563 : certificate563.NumericValid := by decide +kernel
theorem sound563 : certificate563.Sound := rat_failure_budget_sound certificate563 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1408,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1409,List.forall_mem_nil _⟩⟩) numericValid563

def certificate564 : RatFailureBudget := ⟨(17670284442792740081/125000000000000000),(293251815046197/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay070.certificate1410),(2,CutFailureCertificates.Decay070.certificate1411),(2,CutFailureCertificates.Decay070.certificate1412)]⟩
theorem numericValid564 : certificate564.NumericValid := by decide +kernel
theorem sound564 : certificate564.Sound := rat_failure_budget_sound certificate564 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1410,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1411,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1412,List.forall_mem_nil _⟩⟩⟩) numericValid564

def certificate565 : RatFailureBudget := ⟨(17670284442792740081/125000000000000000),(1797029892535081/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay070.certificate1413),(2,CutFailureCertificates.Decay070.certificate1414)]⟩
theorem numericValid565 : certificate565.NumericValid := by decide +kernel
theorem sound565 : certificate565.Sound := rat_failure_budget_sound certificate565 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1413,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1414,List.forall_mem_nil _⟩⟩) numericValid565

def certificate566 : RatFailureBudget := ⟨(134129227617246420223/1000000000000000000),(3038987611053887/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay070.certificate1415),(2,CutFailureCertificates.Decay070.certificate1416),(2,CutFailureCertificates.Decay070.certificate1417)]⟩
theorem numericValid566 : certificate566.NumericValid := by decide +kernel
theorem sound566 : certificate566.Sound := rat_failure_budget_sound certificate566 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1415,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1416,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1417,List.forall_mem_nil _⟩⟩⟩) numericValid566

def certificate567 : RatFailureBudget := ⟨(134129227617246420223/1000000000000000000),(1879997332910947/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay070.certificate1418),(2,CutFailureCertificates.Decay070.certificate1419)]⟩
theorem numericValid567 : certificate567.NumericValid := by decide +kernel
theorem sound567 : certificate567.Sound := rat_failure_budget_sound certificate567 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1418,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay070.sound1419,List.forall_mem_nil _⟩⟩) numericValid567

def certificate568 : RatFailureBudget := ⟨(127399680273932701341/1000000000000000000),(313259524050137/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay071.certificate1420),(2,CutFailureCertificates.Decay071.certificate1421),(2,CutFailureCertificates.Decay071.certificate1422)]⟩
theorem numericValid568 : certificate568.NumericValid := by decide +kernel
theorem sound568 : certificate568.Sound := rat_failure_budget_sound certificate568 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1420,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1421,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1422,List.forall_mem_nil _⟩⟩⟩) numericValid568

def certificate569 : RatFailureBudget := ⟨(127399680273932701341/1000000000000000000),(1951470005311251/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay071.certificate1423),(2,CutFailureCertificates.Decay071.certificate1424)]⟩
theorem numericValid569 : certificate569.NumericValid := by decide +kernel
theorem sound569 : certificate569.Sound := rat_failure_budget_sound certificate569 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1423,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1424,List.forall_mem_nil _⟩⟩) numericValid569

def certificate570 : RatFailureBudget := ⟨(15141085354334057831/125000000000000000),(410225862094709/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay071.certificate1425),(2,CutFailureCertificates.Decay071.certificate1426),(2,CutFailureCertificates.Decay071.certificate1427)]⟩
theorem numericValid570 : certificate570.NumericValid := by decide +kernel
theorem sound570 : certificate570.Sound := rat_failure_budget_sound certificate570 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1425,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1426,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1427,List.forall_mem_nil _⟩⟩⟩) numericValid570

def certificate571 : RatFailureBudget := ⟨(15141085354334057831/125000000000000000),(506269200242281/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay071.certificate1428),(2,CutFailureCertificates.Decay071.certificate1429)]⟩
theorem numericValid571 : certificate571.NumericValid := by decide +kernel
theorem sound571 : certificate571.Sound := rat_failure_budget_sound certificate571 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1428,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1429,List.forall_mem_nil _⟩⟩) numericValid571

def certificate572 : RatFailureBudget := ⟨(28819040422860743391/250000000000000000),(1699024265108473/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay071.certificate1430),(2,CutFailureCertificates.Decay071.certificate1431),(2,CutFailureCertificates.Decay071.certificate1432)]⟩
theorem numericValid572 : certificate572.NumericValid := by decide +kernel
theorem sound572 : certificate572.Sound := rat_failure_budget_sound certificate572 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1430,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1431,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1432,List.forall_mem_nil _⟩⟩⟩) numericValid572

def certificate573 : RatFailureBudget := ⟨(28819040422860743391/250000000000000000),(2112495677877237/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay071.certificate1433),(2,CutFailureCertificates.Decay071.certificate1434)]⟩
theorem numericValid573 : certificate573.NumericValid := by decide +kernel
theorem sound573 : certificate573.Sound := rat_failure_budget_sound certificate573 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1433,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1434,List.forall_mem_nil _⟩⟩) numericValid573

def certificate574 : RatFailureBudget := ⟨(54903150324757245577/500000000000000000),(702176345722279/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay071.certificate1435),(2,CutFailureCertificates.Decay071.certificate1436),(2,CutFailureCertificates.Decay071.certificate1437)]⟩
theorem numericValid574 : certificate574.NumericValid := by decide +kernel
theorem sound574 : certificate574.Sound := rat_failure_budget_sound certificate574 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1435,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1436,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1437,List.forall_mem_nil _⟩⟩⟩) numericValid574

def certificate575 : RatFailureBudget := ⟨(54903150324757245577/500000000000000000),(4376740157836899/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay071.certificate1438),(2,CutFailureCertificates.Decay071.certificate1439)]⟩
theorem numericValid575 : certificate575.NumericValid := by decide +kernel
theorem sound575 : certificate575.Sound := rat_failure_budget_sound certificate575 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1438,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay071.sound1439,List.forall_mem_nil _⟩⟩) numericValid575

def certificate576 : RatFailureBudget := ⟨(10468701106791427219/100000000000000000),(3629694126624757/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay072.certificate1440),(2,CutFailureCertificates.Decay072.certificate1441),(2,CutFailureCertificates.Decay072.certificate1442)]⟩
theorem numericValid576 : certificate576.NumericValid := by decide +kernel
theorem sound576 : certificate576.Sound := rat_failure_budget_sound certificate576 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1440,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1441,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1442,List.forall_mem_nil _⟩⟩⟩) numericValid576

def certificate577 : RatFailureBudget := ⟨(10468701106791427219/100000000000000000),(4529762801573033/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay072.certificate1443),(2,CutFailureCertificates.Decay072.certificate1444)]⟩
theorem numericValid577 : certificate577.NumericValid := by decide +kernel
theorem sound577 : certificate577.Sound := rat_failure_budget_sound certificate577 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1443,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1444,List.forall_mem_nil _⟩⟩) numericValid577

def certificate578 : RatFailureBudget := ⟨(99889477241786592563/1000000000000000000),(3751288391673199/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay072.certificate1445),(2,CutFailureCertificates.Decay072.certificate1446),(2,CutFailureCertificates.Decay072.certificate1447)]⟩
theorem numericValid578 : certificate578.NumericValid := by decide +kernel
theorem sound578 : certificate578.Sound := rat_failure_budget_sound certificate578 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1445,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1446,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1447,List.forall_mem_nil _⟩⟩⟩) numericValid578

def certificate579 : RatFailureBudget := ⟨(99889477241786592563/1000000000000000000),(2342570468938613/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay072.certificate1448),(2,CutFailureCertificates.Decay072.certificate1449)]⟩
theorem numericValid579 : certificate579.NumericValid := by decide +kernel
theorem sound579 : certificate579.Sound := rat_failure_budget_sound certificate579 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1448,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay072.sound1449,List.forall_mem_nil _⟩⟩) numericValid579

end Cycle12.CutFailureCertificates.Budget028
