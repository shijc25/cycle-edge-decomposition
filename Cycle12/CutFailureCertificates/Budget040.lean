import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay100
import Cycle12.CutFailureCertificates.Decay101
import Cycle12.CutFailureCertificates.Decay102

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget040

def certificate800 : RatFailureBudget := ⟨(244876948542434331681/1000000000000000000),(613390657350913/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay100.certificate2000),(2,CutFailureCertificates.Decay100.certificate2001),(2,CutFailureCertificates.Decay100.certificate2002)]⟩
theorem numericValid800 : certificate800.NumericValid := by decide +kernel
theorem sound800 : certificate800.Sound := rat_failure_budget_sound certificate800 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2000,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2001,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2002,List.forall_mem_nil _⟩⟩⟩) numericValid800

def certificate801 : RatFailureBudget := ⟨(244876948542434331681/1000000000000000000),(255251207916713/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay100.certificate2003),(2,CutFailureCertificates.Decay100.certificate2004)]⟩
theorem numericValid801 : certificate801.NumericValid := by decide +kernel
theorem sound801 : certificate801.Sound := rat_failure_budget_sound certificate801 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2003,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2004,List.forall_mem_nil _⟩⟩) numericValid801

def certificate802 : RatFailureBudget := ⟨(48027929815997146389/200000000000000000),(247922355618977/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay100.certificate2005),(2,CutFailureCertificates.Decay100.certificate2006),(2,CutFailureCertificates.Decay100.certificate2007)]⟩
theorem numericValid802 : certificate802.NumericValid := by decide +kernel
theorem sound802 : certificate802.Sound := rat_failure_budget_sound certificate802 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2005,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2006,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2007,List.forall_mem_nil _⟩⟩⟩) numericValid802

def certificate803 : RatFailureBudget := ⟨(48027929815997146389/200000000000000000),(258773048786209/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay100.certificate2008),(2,CutFailureCertificates.Decay100.certificate2009)]⟩
theorem numericValid803 : certificate803.NumericValid := by decide +kernel
theorem sound803 : certificate803.Sound := rat_failure_budget_sound certificate803 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2008,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2009,List.forall_mem_nil _⟩⟩) numericValid803

def certificate804 : RatFailureBudget := ⟨(117761590184174009281/500000000000000000),(1250362852372561/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay100.certificate2010),(2,CutFailureCertificates.Decay100.certificate2011),(2,CutFailureCertificates.Decay100.certificate2012)]⟩
theorem numericValid804 : certificate804.NumericValid := by decide +kernel
theorem sound804 : certificate804.Sound := rat_failure_budget_sound certificate804 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2010,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2011,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2012,List.forall_mem_nil _⟩⟩⟩) numericValid804

def certificate805 : RatFailureBudget := ⟨(117761590184174009281/500000000000000000),(654051383473447/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay100.certificate2013),(2,CutFailureCertificates.Decay100.certificate2014)]⟩
theorem numericValid805 : certificate805.NumericValid := by decide +kernel
theorem sound805 : certificate805.Sound := rat_failure_budget_sound certificate805 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2013,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2014,List.forall_mem_nil _⟩⟩) numericValid805

def certificate806 : RatFailureBudget := ⟨(115511784528821437721/500000000000000000),(316454364911641/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay100.certificate2015),(2,CutFailureCertificates.Decay100.certificate2016),(2,CutFailureCertificates.Decay100.certificate2017)]⟩
theorem numericValid806 : certificate806.NumericValid := by decide +kernel
theorem sound806 : certificate806.Sound := rat_failure_budget_sound certificate806 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2015,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2016,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2017,List.forall_mem_nil _⟩⟩⟩) numericValid806

def certificate807 : RatFailureBudget := ⟨(115511784528821437721/500000000000000000),(1325808174422199/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay100.certificate2018),(2,CutFailureCertificates.Decay100.certificate2019)]⟩
theorem numericValid807 : certificate807.NumericValid := by decide +kernel
theorem sound807 : certificate807.Sound := rat_failure_budget_sound certificate807 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2018,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay100.sound2019,List.forall_mem_nil _⟩⟩) numericValid807

def certificate808 : RatFailureBudget := ⟨(44471963983586701429/200000000000000000),(1301905121148313/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay101.certificate2020),(2,CutFailureCertificates.Decay101.certificate2021),(2,CutFailureCertificates.Decay101.certificate2022)]⟩
theorem numericValid808 : certificate808.NumericValid := by decide +kernel
theorem sound808 : certificate808.Sound := rat_failure_budget_sound certificate808 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2020,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2021,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2022,List.forall_mem_nil _⟩⟩⟩) numericValid808

def certificate809 : RatFailureBudget := ⟨(44471963983586701429/200000000000000000),(2733641689880967/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay101.certificate2023),(2,CutFailureCertificates.Decay101.certificate2024)]⟩
theorem numericValid809 : certificate809.NumericValid := by decide +kernel
theorem sound809 : certificate809.Sound := rat_failure_budget_sound certificate809 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2023,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2024,List.forall_mem_nil _⟩⟩) numericValid809

def certificate810 : RatFailureBudget := ⟨(54547126863153105821/250000000000000000),(1303026524955953/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay101.certificate2025),(2,CutFailureCertificates.Decay101.certificate2026),(2,CutFailureCertificates.Decay101.certificate2027)]⟩
theorem numericValid810 : certificate810.NumericValid := by decide +kernel
theorem sound810 : certificate810.Sound := rat_failure_budget_sound certificate810 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2025,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2026,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2027,List.forall_mem_nil _⟩⟩⟩) numericValid810

def certificate811 : RatFailureBudget := ⟨(54547126863153105821/250000000000000000),(344021006510519/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay101.certificate2028),(2,CutFailureCertificates.Decay101.certificate2029)]⟩
theorem numericValid811 : certificate811.NumericValid := by decide +kernel
theorem sound811 : certificate811.Sound := rat_failure_budget_sound certificate811 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2028,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2029,List.forall_mem_nil _⟩⟩) numericValid811

def certificate812 : RatFailureBudget := ⟨(26764961125307303143/125000000000000000),(658062068302939/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay101.certificate2030),(2,CutFailureCertificates.Decay101.certificate2031),(2,CutFailureCertificates.Decay101.certificate2032)]⟩
theorem numericValid812 : certificate812.NumericValid := by decide +kernel
theorem sound812 : certificate812.Sound := rat_failure_budget_sound certificate812 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2030,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2031,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2032,List.forall_mem_nil _⟩⟩⟩) numericValid812

def certificate813 : RatFailureBudget := ⟨(26764961125307303143/125000000000000000),(2788204056555609/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay101.certificate2033),(2,CutFailureCertificates.Decay101.certificate2034)]⟩
theorem numericValid813 : certificate813.NumericValid := by decide +kernel
theorem sound813 : certificate813.Sound := rat_failure_budget_sound certificate813 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2033,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2034,List.forall_mem_nil _⟩⟩) numericValid813

def certificate814 : RatFailureBudget := ⟨(52537530222601784183/250000000000000000),(664999745471141/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay101.certificate2035),(2,CutFailureCertificates.Decay101.certificate2036),(2,CutFailureCertificates.Decay101.certificate2037)]⟩
theorem numericValid814 : certificate814.NumericValid := by decide +kernel
theorem sound814 : certificate814.Sound := rat_failure_budget_sound certificate814 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2035,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2036,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2037,List.forall_mem_nil _⟩⟩⟩) numericValid814

def certificate815 : RatFailureBudget := ⟨(52537530222601784183/250000000000000000),(706188113260397/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay101.certificate2038),(2,CutFailureCertificates.Decay101.certificate2039)]⟩
theorem numericValid815 : certificate815.NumericValid := by decide +kernel
theorem sound815 : certificate815.Sound := rat_failure_budget_sound certificate815 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2038,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay101.sound2039,List.forall_mem_nil _⟩⟩) numericValid815

def certificate816 : RatFailureBudget := ⟨(206276685499036750627/1000000000000000000),(167892119511463/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay102.certificate2040),(2,CutFailureCertificates.Decay102.certificate2041),(2,CutFailureCertificates.Decay102.certificate2042)]⟩
theorem numericValid816 : certificate816.NumericValid := by decide +kernel
theorem sound816 : certificate816.Sound := rat_failure_budget_sound certificate816 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2040,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2041,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2042,List.forall_mem_nil _⟩⟩⟩) numericValid816

def certificate817 : RatFailureBudget := ⟨(206276685499036750627/1000000000000000000),(2853650365823821/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay102.certificate2043),(2,CutFailureCertificates.Decay102.certificate2044)]⟩
theorem numericValid817 : certificate817.NumericValid := by decide +kernel
theorem sound817 : certificate817.Sound := rat_failure_budget_sound certificate817 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2043,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2044,List.forall_mem_nil _⟩⟩) numericValid817

def certificate818 : RatFailureBudget := ⟨(101248192732383573129/500000000000000000),(680160128145933/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay102.certificate2045),(2,CutFailureCertificates.Decay102.certificate2046),(2,CutFailureCertificates.Decay102.certificate2047)]⟩
theorem numericValid818 : certificate818.NumericValid := by decide +kernel
theorem sound818 : certificate818.Sound := rat_failure_budget_sound certificate818 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2045,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2046,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2047,List.forall_mem_nil _⟩⟩⟩) numericValid818

def certificate819 : RatFailureBudget := ⟨(101248192732383573129/500000000000000000),(2890443226439313/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay102.certificate2048),(2,CutFailureCertificates.Decay102.certificate2049)]⟩
theorem numericValid819 : certificate819.NumericValid := by decide +kernel
theorem sound819 : certificate819.Sound := rat_failure_budget_sound certificate819 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2048,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay102.sound2049,List.forall_mem_nil _⟩⟩) numericValid819

end Cycle12.CutFailureCertificates.Budget040
