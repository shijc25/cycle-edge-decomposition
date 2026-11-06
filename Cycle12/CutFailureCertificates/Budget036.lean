import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay090
import Cycle12.CutFailureCertificates.Decay091
import Cycle12.CutFailureCertificates.Decay092

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget036

def certificate720 : RatFailureBudget := ⟨(1603197552115051441481/1000000000000000000),(314991251537871/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay090.certificate1800),(2,CutFailureCertificates.Decay090.certificate1801),(2,CutFailureCertificates.Decay090.certificate1802)]⟩
theorem numericValid720 : certificate720.NumericValid := by decide +kernel
theorem sound720 : certificate720.Sound := rat_failure_budget_sound certificate720 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1800,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1801,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1802,List.forall_mem_nil _⟩⟩⟩) numericValid720

def certificate721 : RatFailureBudget := ⟨(1603197552115051441481/1000000000000000000),(559688846661289/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay090.certificate1803),(2,CutFailureCertificates.Decay090.certificate1804)]⟩
theorem numericValid721 : certificate721.NumericValid := by decide +kernel
theorem sound721 : certificate721.Sound := rat_failure_budget_sound certificate721 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1803,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1804,List.forall_mem_nil _⟩⟩) numericValid721

def certificate722 : RatFailureBudget := ⟨(369822667834612896403/250000000000000000),(339250573016779/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay090.certificate1805),(2,CutFailureCertificates.Decay090.certificate1806),(2,CutFailureCertificates.Decay090.certificate1807)]⟩
theorem numericValid722 : certificate722.NumericValid := by decide +kernel
theorem sound722 : certificate722.Sound := rat_failure_budget_sound certificate722 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1805,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1806,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1807,List.forall_mem_nil _⟩⟩⟩) numericValid722

def certificate723 : RatFailureBudget := ⟨(369822667834612896403/250000000000000000),(300697354703197/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay090.certificate1808),(2,CutFailureCertificates.Decay090.certificate1809)]⟩
theorem numericValid723 : certificate723.NumericValid := by decide +kernel
theorem sound723 : certificate723.Sound := rat_failure_budget_sound certificate723 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1808,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1809,List.forall_mem_nil _⟩⟩) numericValid723

def certificate724 : RatFailureBudget := ⟨(1368672502240183129861/1000000000000000000),(362246091251111/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay090.certificate1810),(2,CutFailureCertificates.Decay090.certificate1811),(2,CutFailureCertificates.Decay090.certificate1812)]⟩
theorem numericValid724 : certificate724.NumericValid := by decide +kernel
theorem sound724 : certificate724.Sound := rat_failure_budget_sound certificate724 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1810,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1811,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1812,List.forall_mem_nil _⟩⟩⟩) numericValid724

def certificate725 : RatFailureBudget := ⟨(1368672502240183129861/1000000000000000000),(644543605889797/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay090.certificate1813),(2,CutFailureCertificates.Decay090.certificate1814)]⟩
theorem numericValid725 : certificate725.NumericValid := by decide +kernel
theorem sound725 : certificate725.Sound := rat_failure_budget_sound certificate725 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1813,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1814,List.forall_mem_nil _⟩⟩) numericValid725

def certificate726 : RatFailureBudget := ⟨(634762562001393096337/500000000000000000),(48225832907147/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay090.certificate1815),(2,CutFailureCertificates.Decay090.certificate1816),(2,CutFailureCertificates.Decay090.certificate1817)]⟩
theorem numericValid726 : certificate726.NumericValid := by decide +kernel
theorem sound726 : certificate726.Sound := rat_failure_budget_sound certificate726 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1815,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1816,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1817,List.forall_mem_nil _⟩⟩⟩) numericValid726

def certificate727 : RatFailureBudget := ⟨(634762562001393096337/500000000000000000),(688860653409523/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay090.certificate1818),(2,CutFailureCertificates.Decay090.certificate1819)]⟩
theorem numericValid727 : certificate727.NumericValid := by decide +kernel
theorem sound727 : certificate727.Sound := rat_failure_budget_sound certificate727 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1818,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay090.sound1819,List.forall_mem_nil _⟩⟩) numericValid727

def certificate728 : RatFailureBudget := ⟨(1180330131266070829961/1000000000000000000),(51239502282337/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay091.certificate1820),(2,CutFailureCertificates.Decay091.certificate1821),(2,CutFailureCertificates.Decay091.certificate1822)]⟩
theorem numericValid728 : certificate728.NumericValid := by decide +kernel
theorem sound728 : certificate728.Sound := rat_failure_budget_sound certificate728 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1820,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1821,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1822,List.forall_mem_nil _⟩⟩⟩) numericValid728

def certificate729 : RatFailureBudget := ⟨(1180330131266070829961/1000000000000000000),(367247004149677/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay091.certificate1823),(2,CutFailureCertificates.Decay091.certificate1824)]⟩
theorem numericValid729 : certificate729.NumericValid := by decide +kernel
theorem sound729 : certificate729.Sound := rat_failure_budget_sound certificate729 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1823,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1824,List.forall_mem_nil _⟩⟩) numericValid729

def certificate730 : RatFailureBudget := ⟨(274952852136900303297/250000000000000000),(86918855257317/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay091.certificate1825),(2,CutFailureCertificates.Decay091.certificate1826),(2,CutFailureCertificates.Decay091.certificate1827)]⟩
theorem numericValid730 : certificate730.NumericValid := by decide +kernel
theorem sound730 : certificate730.Sound := rat_failure_budget_sound certificate730 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1825,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1826,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1827,List.forall_mem_nil _⟩⟩⟩) numericValid730

def certificate731 : RatFailureBudget := ⟨(274952852136900303297/250000000000000000),(780955907503663/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay091.certificate1828),(2,CutFailureCertificates.Decay091.certificate1829)]⟩
theorem numericValid731 : certificate731.NumericValid := by decide +kernel
theorem sound731 : certificate731.Sound := rat_failure_budget_sound certificate731 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1828,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1829,List.forall_mem_nil _⟩⟩) numericValid731

def certificate732 : RatFailureBudget := ⟨(513445127041050074639/500000000000000000),(459353225836477/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay091.certificate1830),(2,CutFailureCertificates.Decay091.certificate1831),(2,CutFailureCertificates.Decay091.certificate1832)]⟩
theorem numericValid732 : certificate732.NumericValid := by decide +kernel
theorem sound732 : certificate732.Sound := rat_failure_budget_sound certificate732 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1830,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1831,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1832,List.forall_mem_nil _⟩⟩⟩) numericValid732

def certificate733 : RatFailureBudget := ⟨(513445127041050074639/500000000000000000),(415124925570053/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay091.certificate1833),(2,CutFailureCertificates.Decay091.certificate1834)]⟩
theorem numericValid733 : certificate733.NumericValid := by decide +kernel
theorem sound733 : certificate733.Sound := rat_failure_budget_sound certificate733 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1833,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1834,List.forall_mem_nil _⟩⟩) numericValid733

def certificate734 : RatFailureBudget := ⟨(960649900360527327901/1000000000000000000),(485302583876189/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay091.certificate1835),(2,CutFailureCertificates.Decay091.certificate1836),(2,CutFailureCertificates.Decay091.certificate1837)]⟩
theorem numericValid734 : certificate734.NumericValid := by decide +kernel
theorem sound734 : certificate734.Sound := rat_failure_budget_sound certificate734 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1835,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1836,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1837,List.forall_mem_nil _⟩⟩⟩) numericValid734

def certificate735 : RatFailureBudget := ⟨(960649900360527327901/1000000000000000000),(446701332876323/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay091.certificate1838),(2,CutFailureCertificates.Decay091.certificate1839)]⟩
theorem numericValid735 : certificate735.NumericValid := by decide +kernel
theorem sound735 : certificate735.Sound := rat_failure_budget_sound certificate735 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1838,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay091.sound1839,List.forall_mem_nil _⟩⟩) numericValid735

def certificate736 : RatFailureBudget := ⟨(900307249488733784293/1000000000000000000),(127401175158899/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay092.certificate1840),(2,CutFailureCertificates.Decay092.certificate1841),(2,CutFailureCertificates.Decay092.certificate1842)]⟩
theorem numericValid736 : certificate736.NumericValid := by decide +kernel
theorem sound736 : certificate736.Sound := rat_failure_budget_sound certificate736 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1840,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1841,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1842,List.forall_mem_nil _⟩⟩⟩) numericValid736

def certificate737 : RatFailureBudget := ⟨(900307249488733784293/1000000000000000000),(185991460354843/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay092.certificate1843),(2,CutFailureCertificates.Decay092.certificate1844)]⟩
theorem numericValid737 : certificate737.NumericValid := by decide +kernel
theorem sound737 : certificate737.Sound := rat_failure_budget_sound certificate737 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1843,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1844,List.forall_mem_nil _⟩⟩) numericValid737

def certificate738 : RatFailureBudget := ⟨(845190195104070023853/1000000000000000000),(53737251577351/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay092.certificate1845),(2,CutFailureCertificates.Decay092.certificate1846),(2,CutFailureCertificates.Decay092.certificate1847)]⟩
theorem numericValid738 : certificate738.NumericValid := by decide +kernel
theorem sound738 : certificate738.Sound := rat_failure_budget_sound certificate738 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1845,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1846,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1847,List.forall_mem_nil _⟩⟩⟩) numericValid738

def certificate739 : RatFailureBudget := ⟨(845190195104070023853/1000000000000000000),(994165515730693/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay092.certificate1848),(2,CutFailureCertificates.Decay092.certificate1849)]⟩
theorem numericValid739 : certificate739.NumericValid := by decide +kernel
theorem sound739 : certificate739.Sound := rat_failure_budget_sound certificate739 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1848,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay092.sound1849,List.forall_mem_nil _⟩⟩) numericValid739

end Cycle12.CutFailureCertificates.Budget036
