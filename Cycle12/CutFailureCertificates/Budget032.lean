import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay080
import Cycle12.CutFailureCertificates.Decay081
import Cycle12.CutFailureCertificates.Decay082

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget032

def certificate640 : RatFailureBudget := ⟨(52537530222601784183/1000000000000000000),(5733286828967683/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay080.certificate1600),(2,CutFailureCertificates.Decay080.certificate1601),(2,CutFailureCertificates.Decay080.certificate1602)]⟩
theorem numericValid640 : certificate640.NumericValid := by decide +kernel
theorem sound640 : certificate640.Sound := rat_failure_budget_sound certificate640 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1600,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1601,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1602,List.forall_mem_nil _⟩⟩⟩) numericValid640

def certificate641 : RatFailureBudget := ⟨(52537530222601784183/1000000000000000000),(7226746863148043/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay080.certificate1603),(2,CutFailureCertificates.Decay080.certificate1604)]⟩
theorem numericValid641 : certificate641.NumericValid := by decide +kernel
theorem sound641 : certificate641.Sound := rat_failure_budget_sound certificate641 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1603,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1604,List.forall_mem_nil _⟩⟩) numericValid641

def certificate642 : RatFailureBudget := ⟨(6446146421844898457/125000000000000000),(578526084388997/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay080.certificate1605),(2,CutFailureCertificates.Decay080.certificate1606),(2,CutFailureCertificates.Decay080.certificate1607)]⟩
theorem numericValid642 : certificate642.NumericValid := by decide +kernel
theorem sound642 : certificate642.Sound := rat_failure_budget_sound certificate642 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1605,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1606,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1607,List.forall_mem_nil _⟩⟩⟩) numericValid642

def certificate643 : RatFailureBudget := ⟨(6446146421844898457/125000000000000000),(72947159827011/10000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay080.certificate1608),(2,CutFailureCertificates.Decay080.certificate1609)]⟩
theorem numericValid643 : certificate643.NumericValid := by decide +kernel
theorem sound643 : certificate643.Sound := rat_failure_budget_sound certificate643 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1608,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1609,List.forall_mem_nil _⟩⟩) numericValid643

def certificate644 : RatFailureBudget := ⟨(12656024091547946641/250000000000000000),(732219809875579/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay080.certificate1610),(2,CutFailureCertificates.Decay080.certificate1611),(2,CutFailureCertificates.Decay080.certificate1612)]⟩
theorem numericValid644 : certificate644.NumericValid := by decide +kernel
theorem sound644 : certificate644.Sound := rat_failure_budget_sound certificate644 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1610,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1611,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1612,List.forall_mem_nil _⟩⟩⟩) numericValid644

def certificate645 : RatFailureBudget := ⟨(12656024091547946641/250000000000000000),(3702765384977131/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay080.certificate1613),(2,CutFailureCertificates.Decay080.certificate1614)]⟩
theorem numericValid645 : certificate645.NumericValid := by decide +kernel
theorem sound645 : certificate645.Sound := rat_failure_budget_sound certificate645 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1613,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1614,List.forall_mem_nil _⟩⟩) numericValid645

def certificate646 : RatFailureBudget := ⟨(4970158454520361661/100000000000000000),(6002190818529993/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay080.certificate1615),(2,CutFailureCertificates.Decay080.certificate1616),(2,CutFailureCertificates.Decay080.certificate1617)]⟩
theorem numericValid646 : certificate646.NumericValid := by decide +kernel
theorem sound646 : certificate646.Sound := rat_failure_budget_sound certificate646 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1615,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1616,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1617,List.forall_mem_nil _⟩⟩⟩) numericValid646

def certificate647 : RatFailureBudget := ⟨(4970158454520361661/100000000000000000),(7477572871938423/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay080.certificate1618),(2,CutFailureCertificates.Decay080.certificate1619)]⟩
theorem numericValid647 : certificate647.NumericValid := by decide +kernel
theorem sound647 : certificate647.Sound := rat_failure_budget_sound certificate647 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1618,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay080.sound1619,List.forall_mem_nil _⟩⟩) numericValid647

def certificate648 : RatFailureBudget := ⟨(24400471323788476259/500000000000000000),(6014316591884149/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay081.certificate1620),(2,CutFailureCertificates.Decay081.certificate1621),(2,CutFailureCertificates.Decay081.certificate1622)]⟩
theorem numericValid648 : certificate648.NumericValid := by decide +kernel
theorem sound648 : certificate648.Sound := rat_failure_budget_sound certificate648 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1620,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1621,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1622,List.forall_mem_nil _⟩⟩⟩) numericValid648

def certificate649 : RatFailureBudget := ⟨(24400471323788476259/500000000000000000),(471988309385079/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay081.certificate1623),(2,CutFailureCertificates.Decay081.certificate1624)]⟩
theorem numericValid649 : certificate649.NumericValid := by decide +kernel
theorem sound649 : certificate649.Sound := rat_failure_budget_sound certificate649 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1623,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1624,List.forall_mem_nil _⟩⟩) numericValid649

def certificate650 : RatFailureBudget := ⟨(47921503563055897243/1000000000000000000),(1520254889792993/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay081.certificate1625),(2,CutFailureCertificates.Decay081.certificate1626),(2,CutFailureCertificates.Decay081.certificate1627)]⟩
theorem numericValid650 : certificate650.NumericValid := by decide +kernel
theorem sound650 : certificate650.Sound := rat_failure_budget_sound certificate650 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1625,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1626,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1627,List.forall_mem_nil _⟩⟩⟩) numericValid650

def certificate651 : RatFailureBudget := ⟨(47921503563055897243/1000000000000000000),(1532862829540439/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay081.certificate1628),(2,CutFailureCertificates.Decay081.certificate1629)]⟩
theorem numericValid651 : certificate651.NumericValid := by decide +kernel
theorem sound651 : certificate651.Sound := rat_failure_budget_sound certificate651 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1628,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1629,List.forall_mem_nil _⟩⟩) numericValid651

def certificate652 : RatFailureBudget := ⟨(9412525033197477019/200000000000000000),(1236895843778783/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay081.certificate1630),(2,CutFailureCertificates.Decay081.certificate1631),(2,CutFailureCertificates.Decay081.certificate1632)]⟩
theorem numericValid652 : certificate652.NumericValid := by decide +kernel
theorem sound652 : certificate652.Sound := rat_failure_budget_sound certificate652 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1630,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1631,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1632,List.forall_mem_nil _⟩⟩⟩) numericValid652

def certificate653 : RatFailureBudget := ⟨(9412525033197477019/200000000000000000),(7733275645921067/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay081.certificate1633),(2,CutFailureCertificates.Decay081.certificate1634)]⟩
theorem numericValid653 : certificate653.NumericValid := by decide +kernel
theorem sound653 : certificate653.Sound := rat_failure_budget_sound certificate653 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1633,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1634,List.forall_mem_nil _⟩⟩) numericValid653

def certificate654 : RatFailureBudget := ⟨(11555922301585115699/250000000000000000),(1274358562951069/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay081.certificate1635),(2,CutFailureCertificates.Decay081.certificate1636),(2,CutFailureCertificates.Decay081.certificate1637)]⟩
theorem numericValid654 : certificate654.NumericValid := by decide +kernel
theorem sound654 : certificate654.Sound := rat_failure_budget_sound certificate654 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1635,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1636,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1637,List.forall_mem_nil _⟩⟩⟩) numericValid654

def certificate655 : RatFailureBudget := ⟨(11555922301585115699/250000000000000000),(156168878800477/20000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay081.certificate1638),(2,CutFailureCertificates.Decay081.certificate1639)]⟩
theorem numericValid655 : certificate655.NumericValid := by decide +kernel
theorem sound655 : certificate655.Sound := rat_failure_budget_sound certificate655 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1638,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay081.sound1639,List.forall_mem_nil _⟩⟩) numericValid655

def certificate656 : RatFailureBudget := ⟨(75016018916683844152359/1000000000000000000),(1177551726763/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay082.certificate1640),(2,CutFailureCertificates.Decay082.certificate1641),(2,CutFailureCertificates.Decay082.certificate1642)]⟩
theorem numericValid656 : certificate656.NumericValid := by decide +kernel
theorem sound656 : certificate656.Sound := rat_failure_budget_sound certificate656 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1640,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1641,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1642,List.forall_mem_nil _⟩⟩⟩) numericValid656

def certificate657 : RatFailureBudget := ⟨(75016018916683844152359/1000000000000000000),(804739895363/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay082.certificate1643),(2,CutFailureCertificates.Decay082.certificate1644)]⟩
theorem numericValid657 : certificate657.NumericValid := by decide +kernel
theorem sound657 : certificate657.Sound := rat_failure_budget_sound certificate657 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1643,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1644,List.forall_mem_nil _⟩⟩) numericValid657

def certificate658 : RatFailureBudget := ⟨(47800972580928223399921/1000000000000000000),(3366021975547/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay082.certificate1645),(2,CutFailureCertificates.Decay082.certificate1646),(2,CutFailureCertificates.Decay082.certificate1647)]⟩
theorem numericValid658 : certificate658.NumericValid := by decide +kernel
theorem sound658 : certificate658.Sound := rat_failure_budget_sound certificate658 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1645,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1646,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1647,List.forall_mem_nil _⟩⟩⟩) numericValid658

def certificate659 : RatFailureBudget := ⟨(47800972580928223399921/1000000000000000000),(10950517242461/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay082.certificate1648),(2,CutFailureCertificates.Decay082.certificate1649)]⟩
theorem numericValid659 : certificate659.NumericValid := by decide +kernel
theorem sound659 : certificate659.Sound := rat_failure_budget_sound certificate659 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1648,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay082.sound1649,List.forall_mem_nil _⟩⟩) numericValid659

end Cycle12.CutFailureCertificates.Budget032
