import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay077
import Cycle12.CutFailureCertificates.Decay078
import Cycle12.CutFailureCertificates.Decay079

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget031

def certificate620 : RatFailureBudget := ⟨(30017456134998216493/500000000000000000),(1044751746481913/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay077.certificate1550),(2,CutFailureCertificates.Decay077.certificate1551),(2,CutFailureCertificates.Decay077.certificate1552)]⟩
theorem numericValid620 : certificate620.NumericValid := by decide +kernel
theorem sound620 : certificate620.Sound := rat_failure_budget_sound certificate620 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1550,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1551,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1552,List.forall_mem_nil _⟩⟩⟩) numericValid620

def certificate621 : RatFailureBudget := ⟨(30017456134998216493/500000000000000000),(6655148741295103/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay077.certificate1553),(2,CutFailureCertificates.Decay077.certificate1554)]⟩
theorem numericValid621 : certificate621.NumericValid := by decide +kernel
theorem sound621 : certificate621.Sound := rat_failure_budget_sound certificate621 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1553,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1554,List.forall_mem_nil _⟩⟩) numericValid621

def certificate622 : RatFailureBudget := ⟨(368004969325543779/6250000000000000),(1326801599828629/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay077.certificate1555),(2,CutFailureCertificates.Decay077.certificate1556),(2,CutFailureCertificates.Decay077.certificate1557)]⟩
theorem numericValid622 : certificate622.NumericValid := by decide +kernel
theorem sound622 : certificate622.Sound := rat_failure_budget_sound certificate622 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1555,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1556,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1557,List.forall_mem_nil _⟩⟩⟩) numericValid622

def certificate623 : RatFailureBudget := ⟨(368004969325543779/6250000000000000),(336367052483551/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay077.certificate1558),(2,CutFailureCertificates.Decay077.certificate1559)]⟩
theorem numericValid623 : certificate623.NumericValid := by decide +kernel
theorem sound623 : certificate623.Sound := rat_failure_budget_sound certificate623 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1558,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay077.sound1559,List.forall_mem_nil _⟩⟩) numericValid623

def certificate624 : RatFailureBudget := ⟨(2887794613220535943/50000000000000000),(5376421350593989/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay078.certificate1560),(2,CutFailureCertificates.Decay078.certificate1561),(2,CutFailureCertificates.Decay078.certificate1562)]⟩
theorem numericValid624 : certificate624.NumericValid := by decide +kernel
theorem sound624 : certificate624.Sound := rat_failure_budget_sound certificate624 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1560,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1561,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1562,List.forall_mem_nil _⟩⟩⟩) numericValid624

def certificate625 : RatFailureBudget := ⟨(2887794613220535943/50000000000000000),(6797621304198009/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay078.certificate1563),(2,CutFailureCertificates.Decay078.certificate1564)]⟩
theorem numericValid625 : certificate625.NumericValid := by decide +kernel
theorem sound625 : certificate625.Sound := rat_failure_budget_sound certificate625 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1563,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1564,List.forall_mem_nil _⟩⟩) numericValid625

def certificate626 : RatFailureBudget := ⟨(7150512104616465741/125000000000000000),(5369262860107523/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay078.certificate1565),(2,CutFailureCertificates.Decay078.certificate1566),(2,CutFailureCertificates.Decay078.certificate1567)]⟩
theorem numericValid626 : certificate626.NumericValid := by decide +kernel
theorem sound626 : certificate626.Sound := rat_failure_budget_sound certificate626 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1565,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1566,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1567,List.forall_mem_nil _⟩⟩⟩) numericValid626

def certificate627 : RatFailureBudget := ⟨(7150512104616465741/125000000000000000),(6841975502091379/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay078.certificate1568),(2,CutFailureCertificates.Decay078.certificate1569)]⟩
theorem numericValid627 : certificate627.NumericValid := by decide +kernel
theorem sound627 : certificate627.Sound := rat_failure_budget_sound certificate627 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1568,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1569,List.forall_mem_nil _⟩⟩) numericValid627

def certificate628 : RatFailureBudget := ⟨(56659250567406957463/1000000000000000000),(5403563111921433/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay078.certificate1570),(2,CutFailureCertificates.Decay078.certificate1571),(2,CutFailureCertificates.Decay078.certificate1572)]⟩
theorem numericValid628 : certificate628.NumericValid := by decide +kernel
theorem sound628 : certificate628.Sound := rat_failure_budget_sound certificate628 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1570,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1571,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1572,List.forall_mem_nil _⟩⟩⟩) numericValid628

def certificate629 : RatFailureBudget := ⟨(56659250567406957463/1000000000000000000),(6861570040585511/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay078.certificate1573),(2,CutFailureCertificates.Decay078.certificate1574)]⟩
theorem numericValid629 : certificate629.NumericValid := by decide +kernel
theorem sound629 : certificate629.Sound := rat_failure_budget_sound certificate629 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1573,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1574,List.forall_mem_nil _⟩⟩) numericValid629

def certificate630 : RatFailureBudget := ⟨(56121240256844669053/1000000000000000000),(2726890136294657/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay078.certificate1575),(2,CutFailureCertificates.Decay078.certificate1576),(2,CutFailureCertificates.Decay078.certificate1577)]⟩
theorem numericValid630 : certificate630.NumericValid := by decide +kernel
theorem sound630 : certificate630.Sound := rat_failure_budget_sound certificate630 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1575,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1576,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1577,List.forall_mem_nil _⟩⟩⟩) numericValid630

def certificate631 : RatFailureBudget := ⟨(56121240256844669053/1000000000000000000),(6912461306653271/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay078.certificate1578),(2,CutFailureCertificates.Decay078.certificate1579)]⟩
theorem numericValid631 : certificate631.NumericValid := by decide +kernel
theorem sound631 : certificate631.Sound := rat_failure_budget_sound certificate631 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1578,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay078.sound1579,List.forall_mem_nil _⟩⟩) numericValid631

def certificate632 : RatFailureBudget := ⟨(27794977489741688393/500000000000000000),(5490111323521921/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay079.certificate1580),(2,CutFailureCertificates.Decay079.certificate1581),(2,CutFailureCertificates.Decay079.certificate1582)]⟩
theorem numericValid632 : certificate632.NumericValid := by decide +kernel
theorem sound632 : certificate632.Sound := rat_failure_budget_sound certificate632 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1580,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1581,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1582,List.forall_mem_nil _⟩⟩⟩) numericValid632

def certificate633 : RatFailureBudget := ⟨(27794977489741688393/500000000000000000),(55755373872471/8000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay079.certificate1583),(2,CutFailureCertificates.Decay079.certificate1584)]⟩
theorem numericValid633 : certificate633.NumericValid := by decide +kernel
theorem sound633 : certificate633.Sound := rat_failure_budget_sound certificate633 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1583,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1584,List.forall_mem_nil _⟩⟩) numericValid633

def certificate634 : RatFailureBudget := ⟨(55065286028488616857/1000000000000000000),(5525091473577199/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay079.certificate1585),(2,CutFailureCertificates.Decay079.certificate1586),(2,CutFailureCertificates.Decay079.certificate1587)]⟩
theorem numericValid634 : certificate634.NumericValid := by decide +kernel
theorem sound634 : certificate634.Sound := rat_failure_budget_sound certificate634 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1585,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1586,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1587,List.forall_mem_nil _⟩⟩⟩) numericValid634

def certificate635 : RatFailureBudget := ⟨(55065286028488616857/1000000000000000000),(3492868003309109/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay079.certificate1588),(2,CutFailureCertificates.Decay079.certificate1589)]⟩
theorem numericValid635 : certificate635.NumericValid := by decide +kernel
theorem sound635 : certificate635.Sound := rat_failure_budget_sound certificate635 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1588,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1589,List.forall_mem_nil _⟩⟩) numericValid635

def certificate636 : RatFailureBudget := ⟨(54547126863153105821/1000000000000000000),(5543877701066383/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay079.certificate1590),(2,CutFailureCertificates.Decay079.certificate1591),(2,CutFailureCertificates.Decay079.certificate1592)]⟩
theorem numericValid636 : certificate636.NumericValid := by decide +kernel
theorem sound636 : certificate636.Sound := rat_failure_budget_sound certificate636 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1590,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1591,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1592,List.forall_mem_nil _⟩⟩⟩) numericValid636

def certificate637 : RatFailureBudget := ⟨(54547126863153105821/1000000000000000000),(7036846794986257/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay079.certificate1593),(2,CutFailureCertificates.Decay079.certificate1594)]⟩
theorem numericValid637 : certificate637.NumericValid := by decide +kernel
theorem sound637 : certificate637.Sound := rat_failure_budget_sound certificate637 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1593,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1594,List.forall_mem_nil _⟩⟩) numericValid637

def certificate638 : RatFailureBudget := ⟨(26764961125307303143/500000000000000000),(1486964436485471/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay079.certificate1595),(2,CutFailureCertificates.Decay079.certificate1596),(2,CutFailureCertificates.Decay079.certificate1597)]⟩
theorem numericValid638 : certificate638.NumericValid := by decide +kernel
theorem sound638 : certificate638.Sound := rat_failure_budget_sound certificate638 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1595,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1596,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1597,List.forall_mem_nil _⟩⟩⟩) numericValid638

def certificate639 : RatFailureBudget := ⟨(26764961125307303143/500000000000000000),(3576220153859997/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay079.certificate1598),(2,CutFailureCertificates.Decay079.certificate1599)]⟩
theorem numericValid639 : certificate639.NumericValid := by decide +kernel
theorem sound639 : certificate639.Sound := rat_failure_budget_sound certificate639 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1598,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay079.sound1599,List.forall_mem_nil _⟩⟩) numericValid639

end Cycle12.CutFailureCertificates.Budget031
