import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch014
import Cycle12.GeometryCertificates.Batch015
import Cycle12.MergedCutCells.Batch143
import Cycle12.MergedCutCells.Batch144
import Cycle12.MergedCutCells.Batch145
import Cycle12.MergedCutCells.Batch146
import Cycle12.MergedCutCells.Batch147
import Cycle12.PopulationCertificates.Batch014
import Cycle12.PopulationCertificates.Batch015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch037

def certificate444 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate296,PopulationCertificates.Batch014.certificate296,[MergedCutCells.Batch143.certificate1722,MergedCutCells.Batch143.certificate1723,MergedCutCells.Batch143.certificate1724,MergedCutCells.Batch143.certificate1725,MergedCutCells.Batch143.certificate1726,MergedCutCells.Batch143.certificate1727,MergedCutCells.Batch144.certificate1728],(174283948877337523/200000000000000000),(some 64),(1/2),(539243533989187247/500000000000000000),(some (69314718055994531/100000000000000000)),(some (190905742316433601/125000000000000000))⟩
theorem numericValid444 : certificate444.NumericValid := by decide +kernel
theorem cellsSound444 : ∀ c∈certificate444.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1722,MergedCutCells.Batch143.certificate1723,MergedCutCells.Batch143.certificate1724,MergedCutCells.Batch143.certificate1725,MergedCutCells.Batch143.certificate1726,MergedCutCells.Batch143.certificate1727,MergedCutCells.Batch144.certificate1728], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1722,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1723,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1724,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1725,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1726,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1727,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1728,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric444 : ∀ c∈certificate444.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1722,MergedCutCells.Batch143.certificate1723,MergedCutCells.Batch143.certificate1724,MergedCutCells.Batch143.certificate1725,MergedCutCells.Batch143.certificate1726,MergedCutCells.Batch143.certificate1727,MergedCutCells.Batch144.certificate1728], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1722,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1723,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1724,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1725,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1726,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1727,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1728,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid444 : ∀ c∈certificate444.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1722,MergedCutCells.Batch143.certificate1723,MergedCutCells.Batch143.certificate1724,MergedCutCells.Batch143.certificate1725,MergedCutCells.Batch143.certificate1726,MergedCutCells.Batch143.certificate1727,MergedCutCells.Batch144.certificate1728], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid149,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid149,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid149,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid149,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid149,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid149,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid149,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches444 : ∀ c∈certificate444.cells, c.population=certificate444.population := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1722,MergedCutCells.Batch143.certificate1723,MergedCutCells.Batch143.certificate1724,MergedCutCells.Batch143.certificate1725,MergedCutCells.Batch143.certificate1726,MergedCutCells.Batch143.certificate1727,MergedCutCells.Batch144.certificate1728], c.population=PopulationCertificates.Batch014.certificate296
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers444 {x : ℝ} (hx : certificate444.interval.Contains x) : ∃ c∈certificate444.cells, c.region.interval.Contains x := rat_cut_group_covers certificate444 numericValid444 hx

def certificate445 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate296,PopulationCertificates.Batch014.certificate296,[MergedCutCells.Batch144.certificate1729],64,none,(1/2),(616746869825112139/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid445 : certificate445.NumericValid := by decide +kernel
theorem cellsSound445 : ∀ c∈certificate445.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1729], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1729,List.forall_mem_nil _⟩
theorem cellsNumeric445 : ∀ c∈certificate445.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1729], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1729,List.forall_mem_nil _⟩
theorem cellsEntropyValid445 : ∀ c∈certificate445.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1729], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches445 : ∀ c∈certificate445.cells, c.population=certificate445.population := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1729], c.population=PopulationCertificates.Batch014.certificate296
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers445 {x : ℝ} (hx : certificate445.interval.Contains x) : ∃ c∈certificate445.cells, c.region.interval.Contains x := rat_cut_group_covers certificate445 numericValid445 hx

def certificate446 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate297,PopulationCertificates.Batch014.certificate297,[MergedCutCells.Batch144.certificate1730,MergedCutCells.Batch144.certificate1731,MergedCutCells.Batch144.certificate1732,MergedCutCells.Batch144.certificate1733],(765253149633769287/250000000000000000),none,(1/2),(1024934168965343399/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid446 : certificate446.NumericValid := by decide +kernel
theorem cellsSound446 : ∀ c∈certificate446.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1730,MergedCutCells.Batch144.certificate1731,MergedCutCells.Batch144.certificate1732,MergedCutCells.Batch144.certificate1733], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1730,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1732,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1733,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric446 : ∀ c∈certificate446.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1730,MergedCutCells.Batch144.certificate1731,MergedCutCells.Batch144.certificate1732,MergedCutCells.Batch144.certificate1733], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1730,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1732,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1733,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid446 : ∀ c∈certificate446.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1730,MergedCutCells.Batch144.certificate1731,MergedCutCells.Batch144.certificate1732,MergedCutCells.Batch144.certificate1733], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches446 : ∀ c∈certificate446.cells, c.population=certificate446.population := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1730,MergedCutCells.Batch144.certificate1731,MergedCutCells.Batch144.certificate1732,MergedCutCells.Batch144.certificate1733], c.population=PopulationCertificates.Batch014.certificate297
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers446 {x : ℝ} (hx : certificate446.interval.Contains x) : ∃ c∈certificate446.cells, c.region.interval.Contains x := rat_cut_group_covers certificate446 numericValid446 hx

def certificate447 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate298,PopulationCertificates.Batch014.certificate298,[MergedCutCells.Batch144.certificate1734,MergedCutCells.Batch144.certificate1735,MergedCutCells.Batch144.certificate1736,MergedCutCells.Batch144.certificate1737,MergedCutCells.Batch144.certificate1738,MergedCutCells.Batch144.certificate1739,MergedCutCells.Batch145.certificate1740],(915535368722335319/1000000000000000000),(some 64),(1/2),(544014136170279141/500000000000000000),(some (69314718055994531/100000000000000000)),(some (19129156220045401/12500000000000000))⟩
theorem numericValid447 : certificate447.NumericValid := by decide +kernel
theorem cellsSound447 : ∀ c∈certificate447.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1734,MergedCutCells.Batch144.certificate1735,MergedCutCells.Batch144.certificate1736,MergedCutCells.Batch144.certificate1737,MergedCutCells.Batch144.certificate1738,MergedCutCells.Batch144.certificate1739,MergedCutCells.Batch145.certificate1740], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1734,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1735,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1736,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1737,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.sound1739,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1740,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric447 : ∀ c∈certificate447.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1734,MergedCutCells.Batch144.certificate1735,MergedCutCells.Batch144.certificate1736,MergedCutCells.Batch144.certificate1737,MergedCutCells.Batch144.certificate1738,MergedCutCells.Batch144.certificate1739,MergedCutCells.Batch145.certificate1740], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1734,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1735,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1736,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1737,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch144.numericValid1739,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1740,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid447 : ∀ c∈certificate447.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1734,MergedCutCells.Batch144.certificate1735,MergedCutCells.Batch144.certificate1736,MergedCutCells.Batch144.certificate1737,MergedCutCells.Batch144.certificate1738,MergedCutCells.Batch144.certificate1739,MergedCutCells.Batch145.certificate1740], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid150,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid150,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid150,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid150,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid150,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid150,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid150,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches447 : ∀ c∈certificate447.cells, c.population=certificate447.population := by
  change ∀ c∈[MergedCutCells.Batch144.certificate1734,MergedCutCells.Batch144.certificate1735,MergedCutCells.Batch144.certificate1736,MergedCutCells.Batch144.certificate1737,MergedCutCells.Batch144.certificate1738,MergedCutCells.Batch144.certificate1739,MergedCutCells.Batch145.certificate1740], c.population=PopulationCertificates.Batch014.certificate298
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers447 {x : ℝ} (hx : certificate447.interval.Contains x) : ∃ c∈certificate447.cells, c.region.interval.Contains x := rat_cut_group_covers certificate447 numericValid447 hx

def certificate448 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate298,PopulationCertificates.Batch014.certificate298,[MergedCutCells.Batch145.certificate1741],64,none,(1/2),(2421902795151567777/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid448 : certificate448.NumericValid := by decide +kernel
theorem cellsSound448 : ∀ c∈certificate448.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1741], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1741,List.forall_mem_nil _⟩
theorem cellsNumeric448 : ∀ c∈certificate448.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1741], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1741,List.forall_mem_nil _⟩
theorem cellsEntropyValid448 : ∀ c∈certificate448.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1741], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches448 : ∀ c∈certificate448.cells, c.population=certificate448.population := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1741], c.population=PopulationCertificates.Batch014.certificate298
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers448 {x : ℝ} (hx : certificate448.interval.Contains x) : ∃ c∈certificate448.cells, c.region.interval.Contains x := rat_cut_group_covers certificate448 numericValid448 hx

def certificate449 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate299,PopulationCertificates.Batch014.certificate299,[MergedCutCells.Batch145.certificate1742,MergedCutCells.Batch145.certificate1743,MergedCutCells.Batch145.certificate1744,MergedCutCells.Batch145.certificate1745],(3045886991227541599/1000000000000000000),none,(1/2),(52101198827942543/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid449 : certificate449.NumericValid := by decide +kernel
theorem cellsSound449 : ∀ c∈certificate449.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1742,MergedCutCells.Batch145.certificate1743,MergedCutCells.Batch145.certificate1744,MergedCutCells.Batch145.certificate1745], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1743,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1744,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1745,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric449 : ∀ c∈certificate449.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1742,MergedCutCells.Batch145.certificate1743,MergedCutCells.Batch145.certificate1744,MergedCutCells.Batch145.certificate1745], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1743,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1744,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1745,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid449 : ∀ c∈certificate449.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1742,MergedCutCells.Batch145.certificate1743,MergedCutCells.Batch145.certificate1744,MergedCutCells.Batch145.certificate1745], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches449 : ∀ c∈certificate449.cells, c.population=certificate449.population := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1742,MergedCutCells.Batch145.certificate1743,MergedCutCells.Batch145.certificate1744,MergedCutCells.Batch145.certificate1745], c.population=PopulationCertificates.Batch014.certificate299
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers449 {x : ℝ} (hx : certificate449.interval.Contains x) : ∃ c∈certificate449.cells, c.region.interval.Contains x := rat_cut_group_covers certificate449 numericValid449 hx

def certificate450 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate300,PopulationCertificates.Batch015.certificate300,[MergedCutCells.Batch145.certificate1746,MergedCutCells.Batch145.certificate1747,MergedCutCells.Batch145.certificate1748,MergedCutCells.Batch145.certificate1749,MergedCutCells.Batch145.certificate1750,MergedCutCells.Batch145.certificate1751,MergedCutCells.Batch146.certificate1752],(910895753783112337/1000000000000000000),(some 64),(1/2),(1098070833079128453/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (306235756722131313/200000000000000000))⟩
theorem numericValid450 : certificate450.NumericValid := by decide +kernel
theorem cellsSound450 : ∀ c∈certificate450.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1746,MergedCutCells.Batch145.certificate1747,MergedCutCells.Batch145.certificate1748,MergedCutCells.Batch145.certificate1749,MergedCutCells.Batch145.certificate1750,MergedCutCells.Batch145.certificate1751,MergedCutCells.Batch146.certificate1752], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1746,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1747,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1748,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1750,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.sound1751,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1752,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric450 : ∀ c∈certificate450.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1746,MergedCutCells.Batch145.certificate1747,MergedCutCells.Batch145.certificate1748,MergedCutCells.Batch145.certificate1749,MergedCutCells.Batch145.certificate1750,MergedCutCells.Batch145.certificate1751,MergedCutCells.Batch146.certificate1752], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1746,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1747,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1748,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1750,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch145.numericValid1751,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1752,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid450 : ∀ c∈certificate450.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1746,MergedCutCells.Batch145.certificate1747,MergedCutCells.Batch145.certificate1748,MergedCutCells.Batch145.certificate1749,MergedCutCells.Batch145.certificate1750,MergedCutCells.Batch145.certificate1751,MergedCutCells.Batch146.certificate1752], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid151,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid151,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid151,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid151,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid151,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid151,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid151,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches450 : ∀ c∈certificate450.cells, c.population=certificate450.population := by
  change ∀ c∈[MergedCutCells.Batch145.certificate1746,MergedCutCells.Batch145.certificate1747,MergedCutCells.Batch145.certificate1748,MergedCutCells.Batch145.certificate1749,MergedCutCells.Batch145.certificate1750,MergedCutCells.Batch145.certificate1751,MergedCutCells.Batch146.certificate1752], c.population=PopulationCertificates.Batch015.certificate300
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers450 {x : ℝ} (hx : certificate450.interval.Contains x) : ∃ c∈certificate450.cells, c.region.interval.Contains x := rat_cut_group_covers certificate450 numericValid450 hx

def certificate451 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate300,PopulationCertificates.Batch015.certificate300,[MergedCutCells.Batch146.certificate1753],64,none,(1/2),(2450615615158089941/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid451 : certificate451.NumericValid := by decide +kernel
theorem cellsSound451 : ∀ c∈certificate451.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1753], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1753,List.forall_mem_nil _⟩
theorem cellsNumeric451 : ∀ c∈certificate451.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1753], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1753,List.forall_mem_nil _⟩
theorem cellsEntropyValid451 : ∀ c∈certificate451.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1753], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches451 : ∀ c∈certificate451.cells, c.population=certificate451.population := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1753], c.population=PopulationCertificates.Batch015.certificate300
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers451 {x : ℝ} (hx : certificate451.interval.Contains x) : ∃ c∈certificate451.cells, c.region.interval.Contains x := rat_cut_group_covers certificate451 numericValid451 hx

def certificate452 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate301,PopulationCertificates.Batch015.certificate301,[MergedCutCells.Batch146.certificate1754,MergedCutCells.Batch146.certificate1755,MergedCutCells.Batch146.certificate1756,MergedCutCells.Batch146.certificate1757],(3030851824129145953/1000000000000000000),none,(1/2),(1059186614773040237/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid452 : certificate452.NumericValid := by decide +kernel
theorem cellsSound452 : ∀ c∈certificate452.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1754,MergedCutCells.Batch146.certificate1755,MergedCutCells.Batch146.certificate1756,MergedCutCells.Batch146.certificate1757], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1755,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1757,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric452 : ∀ c∈certificate452.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1754,MergedCutCells.Batch146.certificate1755,MergedCutCells.Batch146.certificate1756,MergedCutCells.Batch146.certificate1757], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1755,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1757,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid452 : ∀ c∈certificate452.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1754,MergedCutCells.Batch146.certificate1755,MergedCutCells.Batch146.certificate1756,MergedCutCells.Batch146.certificate1757], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches452 : ∀ c∈certificate452.cells, c.population=certificate452.population := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1754,MergedCutCells.Batch146.certificate1755,MergedCutCells.Batch146.certificate1756,MergedCutCells.Batch146.certificate1757], c.population=PopulationCertificates.Batch015.certificate301
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers452 {x : ℝ} (hx : certificate452.interval.Contains x) : ∃ c∈certificate452.cells, c.region.interval.Contains x := rat_cut_group_covers certificate452 numericValid452 hx

def certificate453 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate302,PopulationCertificates.Batch015.certificate302,[MergedCutCells.Batch146.certificate1758,MergedCutCells.Batch146.certificate1759,MergedCutCells.Batch146.certificate1760,MergedCutCells.Batch146.certificate1761,MergedCutCells.Batch146.certificate1762,MergedCutCells.Batch146.certificate1763,MergedCutCells.Batch147.certificate1764],(231608503966701341/250000000000000000),(some 64),(1/2),(552652392148067631/500000000000000000),(some (69314718055994531/100000000000000000)),(some (766738387936947807/500000000000000000))⟩
theorem numericValid453 : certificate453.NumericValid := by decide +kernel
theorem cellsSound453 : ∀ c∈certificate453.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1758,MergedCutCells.Batch146.certificate1759,MergedCutCells.Batch146.certificate1760,MergedCutCells.Batch146.certificate1761,MergedCutCells.Batch146.certificate1762,MergedCutCells.Batch146.certificate1763,MergedCutCells.Batch147.certificate1764], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1759,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1760,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1761,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1762,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.sound1763,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1764,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric453 : ∀ c∈certificate453.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1758,MergedCutCells.Batch146.certificate1759,MergedCutCells.Batch146.certificate1760,MergedCutCells.Batch146.certificate1761,MergedCutCells.Batch146.certificate1762,MergedCutCells.Batch146.certificate1763,MergedCutCells.Batch147.certificate1764], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1759,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1760,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1761,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1762,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch146.numericValid1763,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1764,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid453 : ∀ c∈certificate453.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1758,MergedCutCells.Batch146.certificate1759,MergedCutCells.Batch146.certificate1760,MergedCutCells.Batch146.certificate1761,MergedCutCells.Batch146.certificate1762,MergedCutCells.Batch146.certificate1763,MergedCutCells.Batch147.certificate1764], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid152,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid152,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid152,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid152,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid152,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid152,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid152,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches453 : ∀ c∈certificate453.cells, c.population=certificate453.population := by
  change ∀ c∈[MergedCutCells.Batch146.certificate1758,MergedCutCells.Batch146.certificate1759,MergedCutCells.Batch146.certificate1760,MergedCutCells.Batch146.certificate1761,MergedCutCells.Batch146.certificate1762,MergedCutCells.Batch146.certificate1763,MergedCutCells.Batch147.certificate1764], c.population=PopulationCertificates.Batch015.certificate302
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers453 {x : ℝ} (hx : certificate453.interval.Contains x) : ∃ c∈certificate453.cells, c.region.interval.Contains x := rat_cut_group_covers certificate453 numericValid453 hx

def certificate454 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate302,PopulationCertificates.Batch015.certificate302,[MergedCutCells.Batch147.certificate1765],64,none,(1/2),(2445450594575056961/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid454 : certificate454.NumericValid := by decide +kernel
theorem cellsSound454 : ∀ c∈certificate454.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1765], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1765,List.forall_mem_nil _⟩
theorem cellsNumeric454 : ∀ c∈certificate454.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1765], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1765,List.forall_mem_nil _⟩
theorem cellsEntropyValid454 : ∀ c∈certificate454.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1765], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches454 : ∀ c∈certificate454.cells, c.population=certificate454.population := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1765], c.population=PopulationCertificates.Batch015.certificate302
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers454 {x : ℝ} (hx : certificate454.interval.Contains x) : ∃ c∈certificate454.cells, c.region.interval.Contains x := rat_cut_group_covers certificate454 numericValid454 hx

def certificate455 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate303,PopulationCertificates.Batch015.certificate303,[MergedCutCells.Batch147.certificate1766,MergedCutCells.Batch147.certificate1767,MergedCutCells.Batch147.certificate1768,MergedCutCells.Batch147.certificate1769],(3015913911892523449/1000000000000000000),none,(1/2),(269114388689289247/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid455 : certificate455.NumericValid := by decide +kernel
theorem cellsSound455 : ∀ c∈certificate455.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1766,MergedCutCells.Batch147.certificate1767,MergedCutCells.Batch147.certificate1768,MergedCutCells.Batch147.certificate1769], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1766,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1767,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1768,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1769,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric455 : ∀ c∈certificate455.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1766,MergedCutCells.Batch147.certificate1767,MergedCutCells.Batch147.certificate1768,MergedCutCells.Batch147.certificate1769], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1766,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1767,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1768,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1769,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid455 : ∀ c∈certificate455.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1766,MergedCutCells.Batch147.certificate1767,MergedCutCells.Batch147.certificate1768,MergedCutCells.Batch147.certificate1769], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches455 : ∀ c∈certificate455.cells, c.population=certificate455.population := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1766,MergedCutCells.Batch147.certificate1767,MergedCutCells.Batch147.certificate1768,MergedCutCells.Batch147.certificate1769], c.population=PopulationCertificates.Batch015.certificate303
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers455 {x : ℝ} (hx : certificate455.interval.Contains x) : ∃ c∈certificate455.cells, c.region.interval.Contains x := rat_cut_group_covers certificate455 numericValid455 hx

end Cycle12.MergedCutGroups.Batch037
