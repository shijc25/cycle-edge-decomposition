import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch015
import Cycle12.MergedCutCells.Batch151
import Cycle12.MergedCutCells.Batch152
import Cycle12.MergedCutCells.Batch153
import Cycle12.MergedCutCells.Batch154
import Cycle12.MergedCutCells.Batch155
import Cycle12.PopulationCertificates.Batch015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch039

def certificate468 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate312,PopulationCertificates.Batch015.certificate312,[MergedCutCells.Batch151.certificate1814,MergedCutCells.Batch151.certificate1815,MergedCutCells.Batch151.certificate1816,MergedCutCells.Batch151.certificate1817,MergedCutCells.Batch151.certificate1818,MergedCutCells.Batch151.certificate1819,MergedCutCells.Batch151.certificate1820],(906041704285818243/1000000000000000000),(some 64),(1/2),(1155427043536526169/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (192171865387128081/125000000000000000))⟩
theorem numericValid468 : certificate468.NumericValid := by decide +kernel
theorem cellsSound468 : ∀ c∈certificate468.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1814,MergedCutCells.Batch151.certificate1815,MergedCutCells.Batch151.certificate1816,MergedCutCells.Batch151.certificate1817,MergedCutCells.Batch151.certificate1818,MergedCutCells.Batch151.certificate1819,MergedCutCells.Batch151.certificate1820], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1814,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1815,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1817,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1818,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1819,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1820,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric468 : ∀ c∈certificate468.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1814,MergedCutCells.Batch151.certificate1815,MergedCutCells.Batch151.certificate1816,MergedCutCells.Batch151.certificate1817,MergedCutCells.Batch151.certificate1818,MergedCutCells.Batch151.certificate1819,MergedCutCells.Batch151.certificate1820], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1814,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1815,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1817,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1818,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1819,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1820,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid468 : ∀ c∈certificate468.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1814,MergedCutCells.Batch151.certificate1815,MergedCutCells.Batch151.certificate1816,MergedCutCells.Batch151.certificate1817,MergedCutCells.Batch151.certificate1818,MergedCutCells.Batch151.certificate1819,MergedCutCells.Batch151.certificate1820], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid157,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid157,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid157,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid157,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid157,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid157,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid157,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches468 : ∀ c∈certificate468.cells, c.population=certificate468.population := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1814,MergedCutCells.Batch151.certificate1815,MergedCutCells.Batch151.certificate1816,MergedCutCells.Batch151.certificate1817,MergedCutCells.Batch151.certificate1818,MergedCutCells.Batch151.certificate1819,MergedCutCells.Batch151.certificate1820], c.population=PopulationCertificates.Batch015.certificate312
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers468 {x : ℝ} (hx : certificate468.interval.Contains x) : ∃ c∈certificate468.cells, c.region.interval.Contains x := rat_cut_group_covers certificate468 numericValid468 hx

def certificate469 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate312,PopulationCertificates.Batch015.certificate312,[MergedCutCells.Batch151.certificate1821],64,none,(1/2),(2591477551509959107/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid469 : certificate469.NumericValid := by decide +kernel
theorem cellsSound469 : ∀ c∈certificate469.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1821], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1821,List.forall_mem_nil _⟩
theorem cellsNumeric469 : ∀ c∈certificate469.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1821], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1821,List.forall_mem_nil _⟩
theorem cellsEntropyValid469 : ∀ c∈certificate469.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1821], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches469 : ∀ c∈certificate469.cells, c.population=certificate469.population := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1821], c.population=PopulationCertificates.Batch015.certificate312
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers469 {x : ℝ} (hx : certificate469.interval.Contains x) : ∃ c∈certificate469.cells, c.region.interval.Contains x := rat_cut_group_covers certificate469 numericValid469 hx

def certificate470 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate313,PopulationCertificates.Batch015.certificate313,[MergedCutCells.Batch151.certificate1822,MergedCutCells.Batch151.certificate1823,MergedCutCells.Batch152.certificate1824,MergedCutCells.Batch152.certificate1825],(735732253344838369/250000000000000000),none,(1/2),(1164752920235663619/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid470 : certificate470.NumericValid := by decide +kernel
theorem cellsSound470 : ∀ c∈certificate470.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1822,MergedCutCells.Batch151.certificate1823,MergedCutCells.Batch152.certificate1824,MergedCutCells.Batch152.certificate1825], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1822,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1824,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1825,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric470 : ∀ c∈certificate470.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1822,MergedCutCells.Batch151.certificate1823,MergedCutCells.Batch152.certificate1824,MergedCutCells.Batch152.certificate1825], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1822,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1824,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1825,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid470 : ∀ c∈certificate470.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1822,MergedCutCells.Batch151.certificate1823,MergedCutCells.Batch152.certificate1824,MergedCutCells.Batch152.certificate1825], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches470 : ∀ c∈certificate470.cells, c.population=certificate470.population := by
  change ∀ c∈[MergedCutCells.Batch151.certificate1822,MergedCutCells.Batch151.certificate1823,MergedCutCells.Batch152.certificate1824,MergedCutCells.Batch152.certificate1825], c.population=PopulationCertificates.Batch015.certificate313
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers470 {x : ℝ} (hx : certificate470.interval.Contains x) : ∃ c∈certificate470.cells, c.region.interval.Contains x := rat_cut_group_covers certificate470 numericValid470 hx

def certificate471 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate314,PopulationCertificates.Batch015.certificate314,[MergedCutCells.Batch152.certificate1826,MergedCutCells.Batch152.certificate1827,MergedCutCells.Batch152.certificate1828,MergedCutCells.Batch152.certificate1829,MergedCutCells.Batch152.certificate1830,MergedCutCells.Batch152.certificate1831,MergedCutCells.Batch152.certificate1832],(899074762492129467/1000000000000000000),(some 64),(1/2),(586363792287486989/500000000000000000),(some (69314718055994531/100000000000000000)),(some (307626267129823841/200000000000000000))⟩
theorem numericValid471 : certificate471.NumericValid := by decide +kernel
theorem cellsSound471 : ∀ c∈certificate471.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1826,MergedCutCells.Batch152.certificate1827,MergedCutCells.Batch152.certificate1828,MergedCutCells.Batch152.certificate1829,MergedCutCells.Batch152.certificate1830,MergedCutCells.Batch152.certificate1831,MergedCutCells.Batch152.certificate1832], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1826,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1827,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1828,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1829,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1830,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1831,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1832,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric471 : ∀ c∈certificate471.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1826,MergedCutCells.Batch152.certificate1827,MergedCutCells.Batch152.certificate1828,MergedCutCells.Batch152.certificate1829,MergedCutCells.Batch152.certificate1830,MergedCutCells.Batch152.certificate1831,MergedCutCells.Batch152.certificate1832], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1826,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1827,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1828,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1829,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1830,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1831,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1832,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid471 : ∀ c∈certificate471.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1826,MergedCutCells.Batch152.certificate1827,MergedCutCells.Batch152.certificate1828,MergedCutCells.Batch152.certificate1829,MergedCutCells.Batch152.certificate1830,MergedCutCells.Batch152.certificate1831,MergedCutCells.Batch152.certificate1832], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid158,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid158,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid158,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid158,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid158,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid158,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid158,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches471 : ∀ c∈certificate471.cells, c.population=certificate471.population := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1826,MergedCutCells.Batch152.certificate1827,MergedCutCells.Batch152.certificate1828,MergedCutCells.Batch152.certificate1829,MergedCutCells.Batch152.certificate1830,MergedCutCells.Batch152.certificate1831,MergedCutCells.Batch152.certificate1832], c.population=PopulationCertificates.Batch015.certificate314
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers471 {x : ℝ} (hx : certificate471.interval.Contains x) : ∃ c∈certificate471.cells, c.region.interval.Contains x := rat_cut_group_covers certificate471 numericValid471 hx

def certificate472 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate314,PopulationCertificates.Batch015.certificate314,[MergedCutCells.Batch152.certificate1833],64,none,(1/2),(2629011537122135511/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid472 : certificate472.NumericValid := by decide +kernel
theorem cellsSound472 : ∀ c∈certificate472.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1833], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1833,List.forall_mem_nil _⟩
theorem cellsNumeric472 : ∀ c∈certificate472.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1833], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1833,List.forall_mem_nil _⟩
theorem cellsEntropyValid472 : ∀ c∈certificate472.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1833], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches472 : ∀ c∈certificate472.cells, c.population=certificate472.population := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1833], c.population=PopulationCertificates.Batch015.certificate314
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers472 {x : ℝ} (hx : certificate472.interval.Contains x) : ∃ c∈certificate472.cells, c.region.interval.Contains x := rat_cut_group_covers certificate472 numericValid472 hx

def certificate473 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate315,PopulationCertificates.Batch015.certificate315,[MergedCutCells.Batch152.certificate1834,MergedCutCells.Batch152.certificate1835,MergedCutCells.Batch153.certificate1836,MergedCutCells.Batch153.certificate1837],(2928543907930585127/1000000000000000000),none,(1/2),(1182437601544814451/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid473 : certificate473.NumericValid := by decide +kernel
theorem cellsSound473 : ∀ c∈certificate473.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1834,MergedCutCells.Batch152.certificate1835,MergedCutCells.Batch153.certificate1836,MergedCutCells.Batch153.certificate1837], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1834,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.sound1835,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1836,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1837,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric473 : ∀ c∈certificate473.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1834,MergedCutCells.Batch152.certificate1835,MergedCutCells.Batch153.certificate1836,MergedCutCells.Batch153.certificate1837], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1834,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch152.numericValid1835,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1836,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1837,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid473 : ∀ c∈certificate473.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1834,MergedCutCells.Batch152.certificate1835,MergedCutCells.Batch153.certificate1836,MergedCutCells.Batch153.certificate1837], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches473 : ∀ c∈certificate473.cells, c.population=certificate473.population := by
  change ∀ c∈[MergedCutCells.Batch152.certificate1834,MergedCutCells.Batch152.certificate1835,MergedCutCells.Batch153.certificate1836,MergedCutCells.Batch153.certificate1837], c.population=PopulationCertificates.Batch015.certificate315
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers473 {x : ℝ} (hx : certificate473.interval.Contains x) : ∃ c∈certificate473.cells, c.region.interval.Contains x := rat_cut_group_covers certificate473 numericValid473 hx

def certificate474 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate316,PopulationCertificates.Batch015.certificate316,[MergedCutCells.Batch153.certificate1838,MergedCutCells.Batch153.certificate1839,MergedCutCells.Batch153.certificate1840,MergedCutCells.Batch153.certificate1841,MergedCutCells.Batch153.certificate1842,MergedCutCells.Batch153.certificate1843,MergedCutCells.Batch153.certificate1844],(114441921121736843/125000000000000000),(some 64),(1/2),(1179251240709671881/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1539654601127763517/1000000000000000000))⟩
theorem numericValid474 : certificate474.NumericValid := by decide +kernel
theorem cellsSound474 : ∀ c∈certificate474.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1838,MergedCutCells.Batch153.certificate1839,MergedCutCells.Batch153.certificate1840,MergedCutCells.Batch153.certificate1841,MergedCutCells.Batch153.certificate1842,MergedCutCells.Batch153.certificate1843,MergedCutCells.Batch153.certificate1844], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1838,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1839,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1840,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1841,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1842,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1843,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1844,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric474 : ∀ c∈certificate474.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1838,MergedCutCells.Batch153.certificate1839,MergedCutCells.Batch153.certificate1840,MergedCutCells.Batch153.certificate1841,MergedCutCells.Batch153.certificate1842,MergedCutCells.Batch153.certificate1843,MergedCutCells.Batch153.certificate1844], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1838,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1839,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1840,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1841,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1842,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1843,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1844,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid474 : ∀ c∈certificate474.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1838,MergedCutCells.Batch153.certificate1839,MergedCutCells.Batch153.certificate1840,MergedCutCells.Batch153.certificate1841,MergedCutCells.Batch153.certificate1842,MergedCutCells.Batch153.certificate1843,MergedCutCells.Batch153.certificate1844], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid159,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid159,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid159,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid159,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid159,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid159,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid159,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches474 : ∀ c∈certificate474.cells, c.population=certificate474.population := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1838,MergedCutCells.Batch153.certificate1839,MergedCutCells.Batch153.certificate1840,MergedCutCells.Batch153.certificate1841,MergedCutCells.Batch153.certificate1842,MergedCutCells.Batch153.certificate1843,MergedCutCells.Batch153.certificate1844], c.population=PopulationCertificates.Batch015.certificate316
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers474 {x : ℝ} (hx : certificate474.interval.Contains x) : ∃ c∈certificate474.cells, c.region.interval.Contains x := rat_cut_group_covers certificate474 numericValid474 hx

def certificate475 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate316,PopulationCertificates.Batch015.certificate316,[MergedCutCells.Batch153.certificate1845],64,none,(1/2),(2625117964787826933/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid475 : certificate475.NumericValid := by decide +kernel
theorem cellsSound475 : ∀ c∈certificate475.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1845], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1845,List.forall_mem_nil _⟩
theorem cellsNumeric475 : ∀ c∈certificate475.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1845], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1845,List.forall_mem_nil _⟩
theorem cellsEntropyValid475 : ∀ c∈certificate475.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1845], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches475 : ∀ c∈certificate475.cells, c.population=certificate475.population := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1845], c.population=PopulationCertificates.Batch015.certificate316
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers475 {x : ℝ} (hx : certificate475.interval.Contains x) : ∃ c∈certificate475.cells, c.region.interval.Contains x := rat_cut_group_covers certificate475 numericValid475 hx

def certificate476 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate317,PopulationCertificates.Batch015.certificate317,[MergedCutCells.Batch153.certificate1846,MergedCutCells.Batch153.certificate1847,MergedCutCells.Batch154.certificate1848,MergedCutCells.Batch154.certificate1849],(728641403070763167/250000000000000000),none,(1/2),(1200931530801486741/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid476 : certificate476.NumericValid := by decide +kernel
theorem cellsSound476 : ∀ c∈certificate476.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1846,MergedCutCells.Batch153.certificate1847,MergedCutCells.Batch154.certificate1848,MergedCutCells.Batch154.certificate1849], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1846,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.sound1847,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1848,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1849,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric476 : ∀ c∈certificate476.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1846,MergedCutCells.Batch153.certificate1847,MergedCutCells.Batch154.certificate1848,MergedCutCells.Batch154.certificate1849], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1846,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch153.numericValid1847,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1848,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1849,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid476 : ∀ c∈certificate476.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1846,MergedCutCells.Batch153.certificate1847,MergedCutCells.Batch154.certificate1848,MergedCutCells.Batch154.certificate1849], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches476 : ∀ c∈certificate476.cells, c.population=certificate476.population := by
  change ∀ c∈[MergedCutCells.Batch153.certificate1846,MergedCutCells.Batch153.certificate1847,MergedCutCells.Batch154.certificate1848,MergedCutCells.Batch154.certificate1849], c.population=PopulationCertificates.Batch015.certificate317
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers476 {x : ℝ} (hx : certificate476.interval.Contains x) : ∃ c∈certificate476.cells, c.region.interval.Contains x := rat_cut_group_covers certificate476 numericValid476 hx

def certificate477 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate318,PopulationCertificates.Batch015.certificate318,[MergedCutCells.Batch154.certificate1850,MergedCutCells.Batch154.certificate1851,MergedCutCells.Batch154.certificate1852,MergedCutCells.Batch154.certificate1853,MergedCutCells.Batch154.certificate1854,MergedCutCells.Batch154.certificate1855],(915535368188158949/1000000000000000000),(some 64),(1/2),(1189331838083293011/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (192615164033101883/125000000000000000))⟩
theorem numericValid477 : certificate477.NumericValid := by decide +kernel
theorem cellsSound477 : ∀ c∈certificate477.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1850,MergedCutCells.Batch154.certificate1851,MergedCutCells.Batch154.certificate1852,MergedCutCells.Batch154.certificate1853,MergedCutCells.Batch154.certificate1854,MergedCutCells.Batch154.certificate1855], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1850,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1852,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1853,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1854,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1855,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric477 : ∀ c∈certificate477.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1850,MergedCutCells.Batch154.certificate1851,MergedCutCells.Batch154.certificate1852,MergedCutCells.Batch154.certificate1853,MergedCutCells.Batch154.certificate1854,MergedCutCells.Batch154.certificate1855], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1850,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1852,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1853,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1854,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1855,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid477 : ∀ c∈certificate477.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1850,MergedCutCells.Batch154.certificate1851,MergedCutCells.Batch154.certificate1852,MergedCutCells.Batch154.certificate1853,MergedCutCells.Batch154.certificate1854,MergedCutCells.Batch154.certificate1855], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid160,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid160,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid160,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid160,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid160,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid160,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches477 : ∀ c∈certificate477.cells, c.population=certificate477.population := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1850,MergedCutCells.Batch154.certificate1851,MergedCutCells.Batch154.certificate1852,MergedCutCells.Batch154.certificate1853,MergedCutCells.Batch154.certificate1854,MergedCutCells.Batch154.certificate1855], c.population=PopulationCertificates.Batch015.certificate318
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers477 {x : ℝ} (hx : certificate477.interval.Contains x) : ∃ c∈certificate477.cells, c.region.interval.Contains x := rat_cut_group_covers certificate477 numericValid477 hx

def certificate478 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate318,PopulationCertificates.Batch015.certificate318,[MergedCutCells.Batch154.certificate1856],64,none,(1/2),(21193509248706503/8000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid478 : certificate478.NumericValid := by decide +kernel
theorem cellsSound478 : ∀ c∈certificate478.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1856], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1856,List.forall_mem_nil _⟩
theorem cellsNumeric478 : ∀ c∈certificate478.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1856], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1856,List.forall_mem_nil _⟩
theorem cellsEntropyValid478 : ∀ c∈certificate478.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1856], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches478 : ∀ c∈certificate478.cells, c.population=certificate478.population := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1856], c.population=PopulationCertificates.Batch015.certificate318
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers478 {x : ℝ} (hx : certificate478.interval.Contains x) : ∃ c∈certificate478.cells, c.region.interval.Contains x := rat_cut_group_covers certificate478 numericValid478 hx

def certificate479 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate319,PopulationCertificates.Batch015.certificate319,[MergedCutCells.Batch154.certificate1857,MergedCutCells.Batch154.certificate1858,MergedCutCells.Batch154.certificate1859,MergedCutCells.Batch155.certificate1860],(2900358258425279053/1000000000000000000),none,(1/2),(1218977638576792697/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid479 : certificate479.NumericValid := by decide +kernel
theorem cellsSound479 : ∀ c∈certificate479.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1857,MergedCutCells.Batch154.certificate1858,MergedCutCells.Batch154.certificate1859,MergedCutCells.Batch155.certificate1860], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1857,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.sound1859,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1860,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric479 : ∀ c∈certificate479.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1857,MergedCutCells.Batch154.certificate1858,MergedCutCells.Batch154.certificate1859,MergedCutCells.Batch155.certificate1860], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1857,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch154.numericValid1859,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1860,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid479 : ∀ c∈certificate479.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1857,MergedCutCells.Batch154.certificate1858,MergedCutCells.Batch154.certificate1859,MergedCutCells.Batch155.certificate1860], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches479 : ∀ c∈certificate479.cells, c.population=certificate479.population := by
  change ∀ c∈[MergedCutCells.Batch154.certificate1857,MergedCutCells.Batch154.certificate1858,MergedCutCells.Batch154.certificate1859,MergedCutCells.Batch155.certificate1860], c.population=PopulationCertificates.Batch015.certificate319
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers479 {x : ℝ} (hx : certificate479.interval.Contains x) : ∃ c∈certificate479.cells, c.region.interval.Contains x := rat_cut_group_covers certificate479 numericValid479 hx

end Cycle12.MergedCutGroups.Batch039
