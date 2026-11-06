import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay095
import Cycle12.CutFailureCertificates.Decay096
import Cycle12.CutFailureCertificates.Decay097

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget038

def certificate760 : RatFailureBudget := ⟨(461104646765771894257/1000000000000000000),(421399128233001/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay095.certificate1900),(2,CutFailureCertificates.Decay095.certificate1901),(2,CutFailureCertificates.Decay095.certificate1902)]⟩
theorem numericValid760 : certificate760.NumericValid := by decide +kernel
theorem sound760 : certificate760.Sound := rat_failure_budget_sound certificate760 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1900,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1901,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1902,List.forall_mem_nil _⟩⟩⟩) numericValid760

def certificate761 : RatFailureBudget := ⟨(461104646765771894257/1000000000000000000),(322384408215687/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay095.certificate1903),(2,CutFailureCertificates.Decay095.certificate1904)]⟩
theorem numericValid761 : certificate761.NumericValid := by decide +kernel
theorem sound761 : certificate761.Sound := rat_failure_budget_sound certificate761 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1903,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1904,List.forall_mem_nil _⟩⟩) numericValid761

def certificate762 : RatFailureBudget := ⟨(54903150324757245577/125000000000000000),(217715623327287/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay095.certificate1905),(2,CutFailureCertificates.Decay095.certificate1906),(2,CutFailureCertificates.Decay095.certificate1907)]⟩
theorem numericValid762 : certificate762.NumericValid := by decide +kernel
theorem sound762 : certificate762.Sound := rat_failure_budget_sound certificate762 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1905,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1906,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1907,List.forall_mem_nil _⟩⟩⟩) numericValid762

def certificate763 : RatFailureBudget := ⟨(54903150324757245577/125000000000000000),(20901893941399/12500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay095.certificate1908),(2,CutFailureCertificates.Decay095.certificate1909)]⟩
theorem numericValid763 : certificate763.NumericValid := by decide +kernel
theorem sound763 : certificate763.Sound := rat_failure_budget_sound certificate763 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1908,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1909,List.forall_mem_nil _⟩⟩) numericValid763

def certificate764 : RatFailureBudget := ⟨(418748044271657088761/1000000000000000000),(44745102500929/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay095.certificate1910),(2,CutFailureCertificates.Decay095.certificate1911),(2,CutFailureCertificates.Decay095.certificate1912)]⟩
theorem numericValid764 : certificate764.NumericValid := by decide +kernel
theorem sound764 : certificate764.Sound := rat_failure_budget_sound certificate764 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1910,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1911,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1912,List.forall_mem_nil _⟩⟩⟩) numericValid764

def certificate765 : RatFailureBudget := ⟨(418748044271657088761/1000000000000000000),(1732961402011981/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay095.certificate1913),(2,CutFailureCertificates.Decay095.certificate1914)]⟩
theorem numericValid765 : certificate765.NumericValid := by decide +kernel
theorem sound765 : certificate765.Sound := rat_failure_budget_sound certificate765 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1913,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1914,List.forall_mem_nil _⟩⟩) numericValid765

def certificate766 : RatFailureBudget := ⟨(399557908967146370253/1000000000000000000),(92650945856007/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay095.certificate1915),(2,CutFailureCertificates.Decay095.certificate1916),(2,CutFailureCertificates.Decay095.certificate1917)]⟩
theorem numericValid766 : certificate766.NumericValid := by decide +kernel
theorem sound766 : certificate766.Sound := rat_failure_budget_sound certificate766 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1915,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1916,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1917,List.forall_mem_nil _⟩⟩⟩) numericValid766

def certificate767 : RatFailureBudget := ⟨(399557908967146370253/1000000000000000000),(360011419807081/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay095.certificate1918),(2,CutFailureCertificates.Decay095.certificate1919)]⟩
theorem numericValid767 : certificate767.NumericValid := by decide +kernel
theorem sound767 : certificate767.Sound := rat_failure_budget_sound certificate767 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1918,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay095.sound1919,List.forall_mem_nil _⟩⟩) numericValid767

def certificate768 : RatFailureBudget := ⟨(38155106028494393599/100000000000000000),(95476981437393/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay096.certificate1920),(2,CutFailureCertificates.Decay096.certificate1921),(2,CutFailureCertificates.Decay096.certificate1922)]⟩
theorem numericValid768 : certificate768.NumericValid := by decide +kernel
theorem sound768 : certificate768.Sound := rat_failure_budget_sound certificate768 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1920,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1921,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1922,List.forall_mem_nil _⟩⟩⟩) numericValid768

def certificate769 : RatFailureBudget := ⟨(38155106028494393599/100000000000000000),(465609621423997/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay096.certificate1923),(2,CutFailureCertificates.Decay096.certificate1924)]⟩
theorem numericValid769 : certificate769.NumericValid := by decide +kernel
theorem sound769 : certificate769.Sound := rat_failure_budget_sound certificate769 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1923,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1924,List.forall_mem_nil _⟩⟩) numericValid769

def certificate770 : RatFailureBudget := ⟨(4557924207760763037/12500000000000000),(122771009892537/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay096.certificate1925),(2,CutFailureCertificates.Decay096.certificate1926),(2,CutFailureCertificates.Decay096.certificate1927)]⟩
theorem numericValid770 : certificate770.NumericValid := by decide +kernel
theorem sound770 : certificate770.Sound := rat_failure_budget_sound certificate770 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1925,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1926,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1927,List.forall_mem_nil _⟩⟩⟩) numericValid770

def certificate771 : RatFailureBudget := ⟨(4557924207760763037/12500000000000000),(962732812443283/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay096.certificate1928),(2,CutFailureCertificates.Decay096.certificate1929)]⟩
theorem numericValid771 : certificate771.NumericValid := by decide +kernel
theorem sound771 : certificate771.Sound := rat_failure_budget_sound certificate771 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1928,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1929,List.forall_mem_nil _⟩⟩) numericValid771

def certificate772 : RatFailureBudget := ⟨(69744396114772780587/200000000000000000),(1010656769415599/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay096.certificate1930),(2,CutFailureCertificates.Decay096.certificate1931),(2,CutFailureCertificates.Decay096.certificate1932)]⟩
theorem numericValid772 : certificate772.NumericValid := by decide +kernel
theorem sound772 : certificate772.Sound := rat_failure_budget_sound certificate772 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1930,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1931,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1932,List.forall_mem_nil _⟩⟩⟩) numericValid772

def certificate773 : RatFailureBudget := ⟨(69744396114772780587/200000000000000000),(497420578846787/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay096.certificate1933),(2,CutFailureCertificates.Decay096.certificate1934)]⟩
theorem numericValid773 : certificate773.NumericValid := by decide +kernel
theorem sound773 : certificate773.Sound := rat_failure_budget_sound certificate773 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1933,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1934,List.forall_mem_nil _⟩⟩) numericValid773

def certificate774 : RatFailureBudget := ⟨(83434655556689126119/250000000000000000),(518669924226239/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay096.certificate1935),(2,CutFailureCertificates.Decay096.certificate1936),(2,CutFailureCertificates.Decay096.certificate1937)]⟩
theorem numericValid774 : certificate774.NumericValid := by decide +kernel
theorem sound774 : certificate774.Sound := rat_failure_budget_sound certificate774 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1935,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1936,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1937,List.forall_mem_nil _⟩⟩⟩) numericValid774

def certificate775 : RatFailureBudget := ⟨(83434655556689126119/250000000000000000),(1030149516493893/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay096.certificate1938),(2,CutFailureCertificates.Decay096.certificate1939)]⟩
theorem numericValid775 : certificate775.NumericValid := by decide +kernel
theorem sound775 : certificate775.Sound := rat_failure_budget_sound certificate775 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1938,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay096.sound1939,List.forall_mem_nil _⟩⟩) numericValid775

def certificate776 : RatFailureBudget := ⟨(326573202875387438003/1000000000000000000),(260322057549307/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay097.certificate1940),(2,CutFailureCertificates.Decay097.certificate1941),(2,CutFailureCertificates.Decay097.certificate1942)]⟩
theorem numericValid776 : certificate776.NumericValid := by decide +kernel
theorem sound776 : certificate776.Sound := rat_failure_budget_sound certificate776 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1940,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1941,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1942,List.forall_mem_nil _⟩⟩⟩) numericValid776

def certificate777 : RatFailureBudget := ⟨(326573202875387438003/1000000000000000000),(416815701925271/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay097.certificate1943),(2,CutFailureCertificates.Decay097.certificate1944)]⟩
theorem numericValid777 : certificate777.NumericValid := by decide +kernel
theorem sound777 : certificate777.Sound := rat_failure_budget_sound certificate777 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1943,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1944,List.forall_mem_nil _⟩⟩) numericValid777

def certificate778 : RatFailureBudget := ⟨(319614393636568157969/1000000000000000000),(1055854475436769/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay097.certificate1945),(2,CutFailureCertificates.Decay097.certificate1946),(2,CutFailureCertificates.Decay097.certificate1947)]⟩
theorem numericValid778 : certificate778.NumericValid := by decide +kernel
theorem sound778 : certificate778.Sound := rat_failure_budget_sound certificate778 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1945,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1946,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1947,List.forall_mem_nil _⟩⟩⟩) numericValid778

def certificate779 : RatFailureBudget := ⟨(319614393636568157969/1000000000000000000),(423340235437081/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay097.certificate1948),(2,CutFailureCertificates.Decay097.certificate1949)]⟩
theorem numericValid779 : certificate779.NumericValid := by decide +kernel
theorem sound779 : certificate779.Sound := rat_failure_budget_sound certificate779 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1948,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay097.sound1949,List.forall_mem_nil _⟩⟩) numericValid779

end Cycle12.CutFailureCertificates.Budget038
