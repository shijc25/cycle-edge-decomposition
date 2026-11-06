import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay087
import Cycle12.CutFailureCertificates.Decay088
import Cycle12.CutFailureCertificates.Decay089

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget035

def certificate700 : RatFailureBudget := ⟨(1552807143739511827403/500000000000000000),(88856288188663/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay087.certificate1750),(2,CutFailureCertificates.Decay087.certificate1751),(2,CutFailureCertificates.Decay087.certificate1752)]⟩
theorem numericValid700 : certificate700.NumericValid := by decide +kernel
theorem sound700 : certificate700.Sound := rat_failure_budget_sound certificate700 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1750,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1751,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1752,List.forall_mem_nil _⟩⟩⟩) numericValid700

def certificate701 : RatFailureBudget := ⟨(1552807143739511827403/500000000000000000),(76343013102401/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay087.certificate1753),(2,CutFailureCertificates.Decay087.certificate1754)]⟩
theorem numericValid701 : certificate701.NumericValid := by decide +kernel
theorem sound701 : certificate701.Sound := rat_failure_budget_sound certificate701 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1753,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1754,List.forall_mem_nil _⟩⟩) numericValid701

def certificate702 : RatFailureBudget := ⟨(1470698876854605526097/500000000000000000),(185364740715821/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay087.certificate1755),(2,CutFailureCertificates.Decay087.certificate1756),(2,CutFailureCertificates.Decay087.certificate1757)]⟩
theorem numericValid702 : certificate702.NumericValid := by decide +kernel
theorem sound702 : certificate702.Sound := rat_failure_budget_sound certificate702 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1755,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1756,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1757,List.forall_mem_nil _⟩⟩⟩) numericValid702

def certificate703 : RatFailureBudget := ⟨(1470698876854605526097/500000000000000000),(320017295161393/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay087.certificate1758),(2,CutFailureCertificates.Decay087.certificate1759)]⟩
theorem numericValid703 : certificate703.NumericValid := by decide +kernel
theorem sound703 : certificate703.Sound := rat_failure_budget_sound certificate703 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1758,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay087.sound1759,List.forall_mem_nil _⟩⟩) numericValid703

def certificate704 : RatFailureBudget := ⟨(2789512166984465611873/1000000000000000000),(48579594412121/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay088.certificate1760),(2,CutFailureCertificates.Decay088.certificate1761),(2,CutFailureCertificates.Decay088.certificate1762)]⟩
theorem numericValid704 : certificate704.NumericValid := by decide +kernel
theorem sound704 : certificate704.Sound := rat_failure_budget_sound certificate704 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1760,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1761,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1762,List.forall_mem_nil _⟩⟩⟩) numericValid704

def certificate705 : RatFailureBudget := ⟨(2789512166984465611873/1000000000000000000),(84158587321201/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay088.certificate1763),(2,CutFailureCertificates.Decay088.certificate1764)]⟩
theorem numericValid705 : certificate705.NumericValid := by decide +kernel
theorem sound705 : certificate705.Sound := rat_failure_budget_sound certificate705 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1763,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1764,List.forall_mem_nil _⟩⟩) numericValid705

def certificate706 : RatFailureBudget := ⟨(125904482924188692167/50000000000000000),(53345441254391/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay088.certificate1765),(2,CutFailureCertificates.Decay088.certificate1766),(2,CutFailureCertificates.Decay088.certificate1767)]⟩
theorem numericValid706 : certificate706.NumericValid := by decide +kernel
theorem sound706 : certificate706.Sound := rat_failure_budget_sound certificate706 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1765,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1766,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1767,List.forall_mem_nil _⟩⟩⟩) numericValid706

def certificate707 : RatFailureBudget := ⟨(125904482924188692167/50000000000000000),(370419341827881/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay088.certificate1768),(2,CutFailureCertificates.Decay088.certificate1769)]⟩
theorem numericValid707 : certificate707.NumericValid := by decide +kernel
theorem sound707 : certificate707.Sound := rat_failure_budget_sound certificate707 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1768,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1769,List.forall_mem_nil _⟩⟩) numericValid707

def certificate708 : RatFailureBudget := ⟨(1141678552781577970311/500000000000000000),(58322161078741/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay088.certificate1770),(2,CutFailureCertificates.Decay088.certificate1771),(2,CutFailureCertificates.Decay088.certificate1772)]⟩
theorem numericValid708 : certificate708.NumericValid := by decide +kernel
theorem sound708 : certificate708.Sound := rat_failure_budget_sound certificate708 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1770,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1771,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1772,List.forall_mem_nil _⟩⟩⟩) numericValid708

def certificate709 : RatFailureBudget := ⟨(1141678552781577970311/500000000000000000),(406405393300349/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay088.certificate1773),(2,CutFailureCertificates.Decay088.certificate1774)]⟩
theorem numericValid709 : certificate709.NumericValid := by decide +kernel
theorem sound709 : certificate709.Sound := rat_failure_budget_sound certificate709 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1773,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1774,List.forall_mem_nil _⟩⟩) numericValid709

def certificate710 : RatFailureBudget := ⟨(2177731345554534727063/1000000000000000000),(12081685705001/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay088.certificate1775),(2,CutFailureCertificates.Decay088.certificate1776),(2,CutFailureCertificates.Decay088.certificate1777)]⟩
theorem numericValid710 : certificate710.NumericValid := by decide +kernel
theorem sound710 : certificate710.Sound := rat_failure_budget_sound certificate710 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1775,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1776,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1777,List.forall_mem_nil _⟩⟩⟩) numericValid710

def certificate711 : RatFailureBudget := ⟨(2177731345554534727063/1000000000000000000),(422813313714339/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay088.certificate1778),(2,CutFailureCertificates.Decay088.certificate1779)]⟩
theorem numericValid711 : certificate711.NumericValid := by decide +kernel
theorem sound711 : certificate711.Sound := rat_failure_budget_sound certificate711 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1778,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay088.sound1779,List.forall_mem_nil _⟩⟩) numericValid711

def certificate712 : RatFailureBudget := ⟨(2079029921420965684411/1000000000000000000),(62895053658621/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay089.certificate1780),(2,CutFailureCertificates.Decay089.certificate1781),(2,CutFailureCertificates.Decay089.certificate1782)]⟩
theorem numericValid712 : certificate712.NumericValid := by decide +kernel
theorem sound712 : certificate712.Sound := rat_failure_budget_sound certificate712 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1780,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1781,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1782,List.forall_mem_nil _⟩⟩⟩) numericValid712

def certificate713 : RatFailureBudget := ⟨(2079029921420965684411/1000000000000000000),(1376606941423/3125000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay089.certificate1783),(2,CutFailureCertificates.Decay089.certificate1784)]⟩
theorem numericValid713 : certificate713.NumericValid := by decide +kernel
theorem sound713 : certificate713.Sound := rat_failure_budget_sound certificate713 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1783,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1784,List.forall_mem_nil _⟩⟩) numericValid713

def certificate714 : RatFailureBudget := ⟨(1986665189665141222489/1000000000000000000),(130851003573427/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay089.certificate1785),(2,CutFailureCertificates.Decay089.certificate1786),(2,CutFailureCertificates.Decay089.certificate1787)]⟩
theorem numericValid714 : certificate714.NumericValid := by decide +kernel
theorem sound714 : certificate714.Sound := rat_failure_budget_sound certificate714 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1785,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1786,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1787,List.forall_mem_nil _⟩⟩⟩) numericValid714

def certificate715 : RatFailureBudget := ⟨(1986665189665141222489/1000000000000000000),(92025523631917/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay089.certificate1788),(2,CutFailureCertificates.Decay089.certificate1789)]⟩
theorem numericValid715 : certificate715.NumericValid := by decide +kernel
theorem sound715 : certificate715.Sound := rat_failure_budget_sound certificate715 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1788,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1789,List.forall_mem_nil _⟩⟩) numericValid715

def certificate716 : RatFailureBudget := ⟨(950055181403008516371/500000000000000000),(271977473087317/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay089.certificate1790),(2,CutFailureCertificates.Decay089.certificate1791),(2,CutFailureCertificates.Decay089.certificate1792)]⟩
theorem numericValid716 : certificate716.NumericValid := by decide +kernel
theorem sound716 : certificate716.Sound := rat_failure_budget_sound certificate716 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1790,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1791,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1792,List.forall_mem_nil _⟩⟩⟩) numericValid716

def certificate717 : RatFailureBudget := ⟨(950055181403008516371/500000000000000000),(47809234986011/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay089.certificate1793),(2,CutFailureCertificates.Decay089.certificate1794)]⟩
theorem numericValid717 : certificate717.NumericValid := by decide +kernel
theorem sound717 : certificate717.Sound := rat_failure_budget_sound certificate717 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1793,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1794,List.forall_mem_nil _⟩⟩) numericValid717

def certificate718 : RatFailureBudget := ⟨(435646048538307062267/250000000000000000),(1475097735959/5000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay089.certificate1795),(2,CutFailureCertificates.Decay089.certificate1796),(2,CutFailureCertificates.Decay089.certificate1797)]⟩
theorem numericValid718 : certificate718.NumericValid := by decide +kernel
theorem sound718 : certificate718.Sound := rat_failure_budget_sound certificate718 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1795,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1796,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1797,List.forall_mem_nil _⟩⟩⟩) numericValid718

def certificate719 : RatFailureBudget := ⟨(435646048538307062267/250000000000000000),(519299603495117/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay089.certificate1798),(2,CutFailureCertificates.Decay089.certificate1799)]⟩
theorem numericValid719 : certificate719.NumericValid := by decide +kernel
theorem sound719 : certificate719.Sound := rat_failure_budget_sound certificate719 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1798,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay089.sound1799,List.forall_mem_nil _⟩⟩) numericValid719

end Cycle12.CutFailureCertificates.Budget035
