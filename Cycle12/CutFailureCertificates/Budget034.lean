import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay085
import Cycle12.CutFailureCertificates.Decay086
import Cycle12.CutFailureCertificates.Decay087

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget034

def certificate680 : RatFailureBudget := ⟨(1608641976552844326253/200000000000000000),(43012812925443/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay085.certificate1700),(2,CutFailureCertificates.Decay085.certificate1701),(2,CutFailureCertificates.Decay085.certificate1702)]⟩
theorem numericValid680 : certificate680.NumericValid := by decide +kernel
theorem sound680 : certificate680.Sound := rat_failure_budget_sound certificate680 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1700,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1701,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1702,List.forall_mem_nil _⟩⟩⟩) numericValid680

def certificate681 : RatFailureBudget := ⟨(1608641976552844326253/200000000000000000),(62204838468787/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay085.certificate1703),(2,CutFailureCertificates.Decay085.certificate1704)]⟩
theorem numericValid681 : certificate681.NumericValid := by decide +kernel
theorem sound681 : certificate681.Sound := rat_failure_budget_sound certificate681 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1703,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1704,List.forall_mem_nil _⟩⟩) numericValid681

def certificate682 : RatFailureBudget := ⟨(7395724679333802015673/1000000000000000000),(15662938275561/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay085.certificate1705),(2,CutFailureCertificates.Decay085.certificate1706),(2,CutFailureCertificates.Decay085.certificate1707)]⟩
theorem numericValid682 : certificate682.NumericValid := by decide +kernel
theorem sound682 : certificate682.Sound := rat_failure_budget_sound certificate682 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1705,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1706,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1707,List.forall_mem_nil _⟩⟩⟩) numericValid682

def certificate683 : RatFailureBudget := ⟨(7395724679333802015673/1000000000000000000),(5372294737013/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay085.certificate1708),(2,CutFailureCertificates.Decay085.certificate1709)]⟩
theorem numericValid683 : certificate683.NumericValid := by decide +kernel
theorem sound683 : certificate683.Sound := rat_failure_budget_sound certificate683 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1708,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1709,List.forall_mem_nil _⟩⟩) numericValid683

def certificate684 : RatFailureBudget := ⟨(6822131672314993651691/1000000000000000000),(87327817068959/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay085.certificate1710),(2,CutFailureCertificates.Decay085.certificate1711),(2,CutFailureCertificates.Decay085.certificate1712)]⟩
theorem numericValid684 : certificate684.NumericValid := by decide +kernel
theorem sound684 : certificate684.Sound := rat_failure_budget_sound certificate684 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1710,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1711,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1712,List.forall_mem_nil _⟩⟩⟩) numericValid684

def certificate685 : RatFailureBudget := ⟨(6822131672314993651691/1000000000000000000),(72364666222349/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay085.certificate1713),(2,CutFailureCertificates.Decay085.certificate1714)]⟩
theorem numericValid685 : certificate685.NumericValid := by decide +kernel
theorem sound685 : certificate685.Sound := rat_failure_budget_sound certificate685 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1713,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1714,List.forall_mem_nil _⟩⟩) numericValid685

def certificate686 : RatFailureBudget := ⟨(5855369243723004773617/1000000000000000000),(100016485218771/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay085.certificate1715),(2,CutFailureCertificates.Decay085.certificate1716),(2,CutFailureCertificates.Decay085.certificate1717)]⟩
theorem numericValid686 : certificate686.NumericValid := by decide +kernel
theorem sound686 : certificate686.Sound := rat_failure_budget_sound certificate686 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1715,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1716,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1717,List.forall_mem_nil _⟩⟩⟩) numericValid686

def certificate687 : RatFailureBudget := ⟨(5855369243723004773617/1000000000000000000),(84034877983469/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay085.certificate1718),(2,CutFailureCertificates.Decay085.certificate1719)]⟩
theorem numericValid687 : certificate687.NumericValid := by decide +kernel
theorem sound687 : certificate687.Sound := rat_failure_budget_sound certificate687 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1718,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay085.sound1719,List.forall_mem_nil _⟩⟩) numericValid687

def certificate688 : RatFailureBudget := ⟨(5445927406376945481761/1000000000000000000),(10630598462149/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay086.certificate1720),(2,CutFailureCertificates.Decay086.certificate1721),(2,CutFailureCertificates.Decay086.certificate1722)]⟩
theorem numericValid688 : certificate688.NumericValid := by decide +kernel
theorem sound688 : certificate688.Sound := rat_failure_budget_sound certificate688 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1720,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1721,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1722,List.forall_mem_nil _⟩⟩⟩) numericValid688

def certificate689 : RatFailureBudget := ⟨(5445927406376945481761/1000000000000000000),(179505406958439/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay086.certificate1723),(2,CutFailureCertificates.Decay086.certificate1724)]⟩
theorem numericValid689 : certificate689.NumericValid := by decide +kernel
theorem sound689 : certificate689.Sound := rat_failure_budget_sound certificate689 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1723,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1724,List.forall_mem_nil _⟩⟩) numericValid689

def certificate690 : RatFailureBudget := ⟨(1015429912494664572893/200000000000000000),(56651878282429/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay086.certificate1725),(2,CutFailureCertificates.Decay086.certificate1726),(2,CutFailureCertificates.Decay086.certificate1727)]⟩
theorem numericValid690 : certificate690.NumericValid := by decide +kernel
theorem sound690 : certificate690.Sound := rat_failure_budget_sound certificate690 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1725,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1726,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1727,List.forall_mem_nil _⟩⟩⟩) numericValid690

def certificate691 : RatFailureBudget := ⟨(1015429912494664572893/200000000000000000),(86742835173099/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay086.certificate1728),(2,CutFailureCertificates.Decay086.certificate1729)]⟩
theorem numericValid691 : certificate691.NumericValid := by decide +kernel
theorem sound691 : certificate691.Sound := rat_failure_budget_sound certificate691 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1728,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1729,List.forall_mem_nil _⟩⟩) numericValid691

def certificate692 : RatFailureBudget := ⟨(555204668868246689109/125000000000000000),(25750915833231/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay086.certificate1730),(2,CutFailureCertificates.Decay086.certificate1731),(2,CutFailureCertificates.Decay086.certificate1732)]⟩
theorem numericValid692 : certificate692.NumericValid := by decide +kernel
theorem sound692 : certificate692.Sound := rat_failure_budget_sound certificate692 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1730,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1731,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1732,List.forall_mem_nil _⟩⟩⟩) numericValid692

def certificate693 : RatFailureBudget := ⟨(555204668868246689109/125000000000000000),(54990869688743/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay086.certificate1733),(2,CutFailureCertificates.Decay086.certificate1734)]⟩
theorem numericValid693 : certificate693.NumericValid := by decide +kernel
theorem sound693 : certificate693.Sound := rat_failure_budget_sound certificate693 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1733,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1734,List.forall_mem_nil _⟩⟩) numericValid693

def certificate694 : RatFailureBudget := ⟨(166671408624338517627/40000000000000000),(67806577549123/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay086.certificate1735),(2,CutFailureCertificates.Decay086.certificate1736),(2,CutFailureCertificates.Decay086.certificate1737)]⟩
theorem numericValid694 : certificate694.NumericValid := by decide +kernel
theorem sound694 : certificate694.Sound := rat_failure_budget_sound certificate694 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1735,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1736,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1737,List.forall_mem_nil _⟩⟩⟩) numericValid694

def certificate695 : RatFailureBudget := ⟨(166671408624338517627/40000000000000000),(115713678464979/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay086.certificate1738),(2,CutFailureCertificates.Decay086.certificate1739)]⟩
theorem numericValid695 : certificate695.NumericValid := by decide +kernel
theorem sound695 : certificate695.Sound := rat_failure_budget_sound certificate695 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1738,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay086.sound1739,List.forall_mem_nil _⟩⟩) numericValid695

def certificate696 : RatFailureBudget := ⟨(1958051853593993522639/500000000000000000),(71722141094213/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay087.certificate1740),(2,CutFailureCertificates.Decay087.certificate1741),(2,CutFailureCertificates.Decay087.certificate1742)]⟩
theorem numericValid696 : certificate696.NumericValid := by decide +kernel
theorem sound696 : certificate696.Sound := rat_failure_budget_sound certificate696 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1740,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1741,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1742,List.forall_mem_nil _⟩⟩⟩) numericValid696

def certificate697 : RatFailureBudget := ⟨(1958051853593993522639/500000000000000000),(122498304426679/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay087.certificate1743),(2,CutFailureCertificates.Decay087.certificate1744)]⟩
theorem numericValid697 : certificate697.NumericValid := by decide +kernel
theorem sound697 : certificate697.Sound := rat_failure_budget_sound certificate697 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1743,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1744,List.forall_mem_nil _⟩⟩) numericValid697

def certificate698 : RatFailureBudget := ⟨(173833819108730224839/50000000000000000),(32130244065043/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay087.certificate1745),(2,CutFailureCertificates.Decay087.certificate1746),(2,CutFailureCertificates.Decay087.certificate1747)]⟩
theorem numericValid698 : certificate698.NumericValid := by decide +kernel
theorem sound698 : certificate698.Sound := rat_failure_budget_sound certificate698 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1745,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1746,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1747,List.forall_mem_nil _⟩⟩⟩) numericValid698

def certificate699 : RatFailureBudget := ⟨(173833819108730224839/50000000000000000),(68758785376101/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay087.certificate1748),(2,CutFailureCertificates.Decay087.certificate1749)]⟩
theorem numericValid699 : certificate699.NumericValid := by decide +kernel
theorem sound699 : certificate699.Sound := rat_failure_budget_sound certificate699 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1748,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1749,List.forall_mem_nil _⟩⟩) numericValid699

end Cycle12.CutFailureCertificates.Budget034
