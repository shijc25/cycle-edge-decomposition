import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay082
import Cycle12.CutFailureCertificates.Decay083
import Cycle12.CutFailureCertificates.Decay084

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget033

def certificate660 : RatFailureBudget := ⟨(9854593963871327203363/250000000000000000),(3995174146393/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay082.certificate1650),(2,CutFailureCertificates.Decay082.certificate1651),(2,CutFailureCertificates.Decay082.certificate1652)]⟩
theorem numericValid660 : certificate660.NumericValid := by decide +kernel
theorem sound660 : certificate660.Sound := rat_failure_budget_sound certificate660 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1650,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1651,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1652,List.forall_mem_nil _⟩⟩⟩) numericValid660

def certificate661 : RatFailureBudget := ⟨(9854593963871327203363/250000000000000000),(13228713763867/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay082.certificate1653),(2,CutFailureCertificates.Decay082.certificate1654)]⟩
theorem numericValid661 : certificate661.NumericValid := by decide +kernel
theorem sound661 : certificate661.Sound := rat_failure_budget_sound certificate661 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1653,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1654,List.forall_mem_nil _⟩⟩) numericValid661

def certificate662 : RatFailureBudget := ⟨(33049605678459506493131/1000000000000000000),(19973188566971/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay082.certificate1655),(2,CutFailureCertificates.Decay082.certificate1656),(2,CutFailureCertificates.Decay082.certificate1657)]⟩
theorem numericValid662 : certificate662.NumericValid := by decide +kernel
theorem sound662 : certificate662.Sound := rat_failure_budget_sound certificate662 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1655,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1656,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1657,List.forall_mem_nil _⟩⟩⟩) numericValid662

def certificate663 : RatFailureBudget := ⟨(33049605678459506493131/1000000000000000000),(31376818328883/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay082.certificate1658),(2,CutFailureCertificates.Decay082.certificate1659)]⟩
theorem numericValid663 : certificate663.NumericValid := by decide +kernel
theorem sound663 : certificate663.Sound := rat_failure_budget_sound certificate663 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1658,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1659,List.forall_mem_nil _⟩⟩) numericValid663

def certificate664 : RatFailureBudget := ⟨(60435757821562209223/2500000000000000),(2542932299459/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay083.certificate1660),(2,CutFailureCertificates.Decay083.certificate1661),(2,CutFailureCertificates.Decay083.certificate1662)]⟩
theorem numericValid664 : certificate664.NumericValid := by decide +kernel
theorem sound664 : certificate664.Sound := rat_failure_budget_sound certificate664 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1660,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1661,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1662,List.forall_mem_nil _⟩⟩⟩) numericValid664

def certificate665 : RatFailureBudget := ⟨(60435757821562209223/2500000000000000),(4278209632077/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay083.certificate1663),(2,CutFailureCertificates.Decay083.certificate1664)]⟩
theorem numericValid665 : certificate665.NumericValid := by decide +kernel
theorem sound665 : certificate665.Sound := rat_failure_budget_sound certificate665 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1663,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1664,List.forall_mem_nil _⟩⟩) numericValid665

def certificate666 : RatFailureBudget := ⟨(21011839773932265847217/1000000000000000000),(6302803889913/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay083.certificate1665),(2,CutFailureCertificates.Decay083.certificate1666),(2,CutFailureCertificates.Decay083.certificate1667)]⟩
theorem numericValid666 : certificate666.NumericValid := by decide +kernel
theorem sound666 : certificate666.Sound := rat_failure_budget_sound certificate666 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1665,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1666,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1667,List.forall_mem_nil _⟩⟩⟩) numericValid666

def certificate667 : RatFailureBudget := ⟨(21011839773932265847217/1000000000000000000),(10367235635839/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay083.certificate1668),(2,CutFailureCertificates.Decay083.certificate1669)]⟩
theorem numericValid667 : certificate667.NumericValid := by decide +kernel
theorem sound667 : certificate667.Sound := rat_failure_budget_sound certificate667 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1668,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1669,List.forall_mem_nil _⟩⟩) numericValid667

def certificate668 : RatFailureBudget := ⟨(9213199537152868385809/500000000000000000),(33217821116081/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay083.certificate1670),(2,CutFailureCertificates.Decay083.certificate1671),(2,CutFailureCertificates.Decay083.certificate1672)]⟩
theorem numericValid668 : certificate668.NumericValid := by decide +kernel
theorem sound668 : certificate668.Sound := rat_failure_budget_sound certificate668 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1670,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1671,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1672,List.forall_mem_nil _⟩⟩⟩) numericValid668

def certificate669 : RatFailureBudget := ⟨(9213199537152868385809/500000000000000000),(27797451580943/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay083.certificate1673),(2,CutFailureCertificates.Decay083.certificate1674)]⟩
theorem numericValid669 : certificate669.NumericValid := by decide +kernel
theorem sound669 : certificate669.Sound := rat_failure_budget_sound certificate669 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1673,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1674,List.forall_mem_nil _⟩⟩) numericValid669

def certificate670 : RatFailureBudget := ⟨(14494221544139906345113/1000000000000000000),(75123019335427/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay083.certificate1675),(2,CutFailureCertificates.Decay083.certificate1676),(2,CutFailureCertificates.Decay083.certificate1677)]⟩
theorem numericValid670 : certificate670.NumericValid := by decide +kernel
theorem sound670 : certificate670.Sound := rat_failure_budget_sound certificate670 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1675,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1676,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1677,List.forall_mem_nil _⟩⟩⟩) numericValid670

def certificate671 : RatFailureBudget := ⟨(14494221544139906345113/1000000000000000000),(5448768689969/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay083.certificate1678),(2,CutFailureCertificates.Decay083.certificate1679)]⟩
theorem numericValid671 : certificate671.NumericValid := by decide +kernel
theorem sound671 : certificate671.Sound := rat_failure_budget_sound certificate671 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1678,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay083.sound1679,List.forall_mem_nil _⟩⟩) numericValid671

def certificate672 : RatFailureBudget := ⟨(12979510417461775966967/1000000000000000000),(76594057944589/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay084.certificate1680),(2,CutFailureCertificates.Decay084.certificate1681),(2,CutFailureCertificates.Decay084.certificate1682)]⟩
theorem numericValid672 : certificate672.NumericValid := by decide +kernel
theorem sound672 : certificate672.Sound := rat_failure_budget_sound certificate672 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1680,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1681,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1682,List.forall_mem_nil _⟩⟩⟩) numericValid672

def certificate673 : RatFailureBudget := ⟨(12979510417461775966967/1000000000000000000),(78136079053103/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay084.certificate1683),(2,CutFailureCertificates.Decay084.certificate1684)]⟩
theorem numericValid673 : certificate673.NumericValid := by decide +kernel
theorem sound673 : certificate673.Sound := rat_failure_budget_sound certificate673 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1683,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1684,List.forall_mem_nil _⟩⟩) numericValid673

def certificate674 : RatFailureBudget := ⟨(1460960179092951431811/125000000000000000),(1738865707291/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay084.certificate1685),(2,CutFailureCertificates.Decay084.certificate1686),(2,CutFailureCertificates.Decay084.certificate1687)]⟩
theorem numericValid674 : certificate674.NumericValid := by decide +kernel
theorem sound674 : certificate674.Sound := rat_failure_budget_sound certificate674 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1685,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1686,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1687,List.forall_mem_nil _⟩⟩⟩) numericValid674

def certificate675 : RatFailureBudget := ⟨(1460960179092951431811/125000000000000000),(86552531057207/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay084.certificate1688),(2,CutFailureCertificates.Decay084.certificate1689)]⟩
theorem numericValid675 : certificate675.NumericValid := by decide +kernel
theorem sound675 : certificate675.Sound := rat_failure_budget_sound certificate675 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1688,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1689,List.forall_mem_nil _⟩⟩) numericValid675

def certificate676 : RatFailureBudget := ⟨(10577178583233964451179/1000000000000000000),(2999441743469/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay084.certificate1690),(2,CutFailureCertificates.Decay084.certificate1691),(2,CutFailureCertificates.Decay084.certificate1692)]⟩
theorem numericValid676 : certificate676.NumericValid := by decide +kernel
theorem sound676 : certificate676.Sound := rat_failure_budget_sound certificate676 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1690,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1691,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1692,List.forall_mem_nil _⟩⟩⟩) numericValid676

def certificate677 : RatFailureBudget := ⟨(10577178583233964451179/1000000000000000000),(95108547617701/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay084.certificate1693),(2,CutFailureCertificates.Decay084.certificate1694)]⟩
theorem numericValid677 : certificate677.NumericValid := by decide +kernel
theorem sound677 : certificate677.Sound := rat_failure_budget_sound certificate677 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1693,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1694,List.forall_mem_nil _⟩⟩) numericValid677

def certificate678 : RatFailureBudget := ⟨(9615687695137442862049/1000000000000000000),(6276285912787/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay084.certificate1695),(2,CutFailureCertificates.Decay084.certificate1696),(2,CutFailureCertificates.Decay084.certificate1697)]⟩
theorem numericValid678 : certificate678.NumericValid := by decide +kernel
theorem sound678 : certificate678.Sound := rat_failure_budget_sound certificate678 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1695,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1696,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1697,List.forall_mem_nil _⟩⟩⟩) numericValid678

def certificate679 : RatFailureBudget := ⟨(9615687695137442862049/1000000000000000000),(20878043291471/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay084.certificate1698),(2,CutFailureCertificates.Decay084.certificate1699)]⟩
theorem numericValid679 : certificate679.NumericValid := by decide +kernel
theorem sound679 : certificate679.Sound := rat_failure_budget_sound certificate679 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1698,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay084.sound1699,List.forall_mem_nil _⟩⟩) numericValid679

end Cycle12.CutFailureCertificates.Budget033
