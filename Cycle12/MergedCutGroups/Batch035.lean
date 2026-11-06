import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch014
import Cycle12.MergedCutCells.Batch135
import Cycle12.MergedCutCells.Batch136
import Cycle12.MergedCutCells.Batch137
import Cycle12.MergedCutCells.Batch138
import Cycle12.MergedCutCells.Batch139
import Cycle12.PopulationCertificates.Batch014

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch035

def certificate420 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate280,PopulationCertificates.Batch014.certificate280,[MergedCutCells.Batch135.certificate1625,MergedCutCells.Batch135.certificate1626,MergedCutCells.Batch135.certificate1627,MergedCutCells.Batch135.certificate1628,MergedCutCells.Batch135.certificate1629,MergedCutCells.Batch135.certificate1630,MergedCutCells.Batch135.certificate1631],(907207652425697259/1000000000000000000),(some 64),(1/2),(199911679744668353/200000000000000000),(some (69314718055994531/100000000000000000)),(some (1520428494926176737/1000000000000000000))⟩
theorem numericValid420 : certificate420.NumericValid := by decide +kernel
theorem cellsSound420 : ∀ c∈certificate420.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1625,MergedCutCells.Batch135.certificate1626,MergedCutCells.Batch135.certificate1627,MergedCutCells.Batch135.certificate1628,MergedCutCells.Batch135.certificate1629,MergedCutCells.Batch135.certificate1630,MergedCutCells.Batch135.certificate1631], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1626,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1628,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1630,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1631,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric420 : ∀ c∈certificate420.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1625,MergedCutCells.Batch135.certificate1626,MergedCutCells.Batch135.certificate1627,MergedCutCells.Batch135.certificate1628,MergedCutCells.Batch135.certificate1629,MergedCutCells.Batch135.certificate1630,MergedCutCells.Batch135.certificate1631], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1626,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1628,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1630,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1631,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid420 : ∀ c∈certificate420.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1625,MergedCutCells.Batch135.certificate1626,MergedCutCells.Batch135.certificate1627,MergedCutCells.Batch135.certificate1628,MergedCutCells.Batch135.certificate1629,MergedCutCells.Batch135.certificate1630,MergedCutCells.Batch135.certificate1631], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid141,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid141,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid141,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid141,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid141,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid141,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid141,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches420 : ∀ c∈certificate420.cells, c.population=certificate420.population := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1625,MergedCutCells.Batch135.certificate1626,MergedCutCells.Batch135.certificate1627,MergedCutCells.Batch135.certificate1628,MergedCutCells.Batch135.certificate1629,MergedCutCells.Batch135.certificate1630,MergedCutCells.Batch135.certificate1631], c.population=PopulationCertificates.Batch014.certificate280
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers420 {x : ℝ} (hx : certificate420.interval.Contains x) : ∃ c∈certificate420.cells, c.region.interval.Contains x := rat_cut_group_covers certificate420 numericValid420 hx

def certificate421 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate280,PopulationCertificates.Batch014.certificate280,[MergedCutCells.Batch136.certificate1632],64,none,(1/2),(449124975402026671/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid421 : certificate421.NumericValid := by decide +kernel
theorem cellsSound421 : ∀ c∈certificate421.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1632], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1632,List.forall_mem_nil _⟩
theorem cellsNumeric421 : ∀ c∈certificate421.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1632], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1632,List.forall_mem_nil _⟩
theorem cellsEntropyValid421 : ∀ c∈certificate421.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1632], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches421 : ∀ c∈certificate421.cells, c.population=certificate421.population := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1632], c.population=PopulationCertificates.Batch014.certificate280
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers421 {x : ℝ} (hx : certificate421.interval.Contains x) : ∃ c∈certificate421.cells, c.region.interval.Contains x := rat_cut_group_covers certificate421 numericValid421 hx

def certificate422 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate281,PopulationCertificates.Batch014.certificate281,[MergedCutCells.Batch136.certificate1633,MergedCutCells.Batch136.certificate1634,MergedCutCells.Batch136.certificate1635,MergedCutCells.Batch136.certificate1636],(1593576889508627693/500000000000000000),none,(1/2),(199231602458671479/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid422 : certificate422.NumericValid := by decide +kernel
theorem cellsSound422 : ∀ c∈certificate422.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1633,MergedCutCells.Batch136.certificate1634,MergedCutCells.Batch136.certificate1635,MergedCutCells.Batch136.certificate1636], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1634,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1635,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1636,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric422 : ∀ c∈certificate422.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1633,MergedCutCells.Batch136.certificate1634,MergedCutCells.Batch136.certificate1635,MergedCutCells.Batch136.certificate1636], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1634,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1635,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1636,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid422 : ∀ c∈certificate422.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1633,MergedCutCells.Batch136.certificate1634,MergedCutCells.Batch136.certificate1635,MergedCutCells.Batch136.certificate1636], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches422 : ∀ c∈certificate422.cells, c.population=certificate422.population := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1633,MergedCutCells.Batch136.certificate1634,MergedCutCells.Batch136.certificate1635,MergedCutCells.Batch136.certificate1636], c.population=PopulationCertificates.Batch014.certificate281
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers422 {x : ℝ} (hx : certificate422.interval.Contains x) : ∃ c∈certificate422.cells, c.region.interval.Contains x := rat_cut_group_covers certificate422 numericValid422 hx

def certificate423 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate282,PopulationCertificates.Batch014.certificate282,[MergedCutCells.Batch136.certificate1637,MergedCutCells.Batch136.certificate1638,MergedCutCells.Batch136.certificate1639,MergedCutCells.Batch136.certificate1640,MergedCutCells.Batch136.certificate1641,MergedCutCells.Batch136.certificate1642],(449931551304117903/500000000000000000),(some 64),(1/2),(251786207254166573/250000000000000000),(some (69314718055994531/100000000000000000)),(some (190116561613340163/125000000000000000))⟩
theorem numericValid423 : certificate423.NumericValid := by decide +kernel
theorem cellsSound423 : ∀ c∈certificate423.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1637,MergedCutCells.Batch136.certificate1638,MergedCutCells.Batch136.certificate1639,MergedCutCells.Batch136.certificate1640,MergedCutCells.Batch136.certificate1641,MergedCutCells.Batch136.certificate1642], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1637,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1638,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1639,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1640,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1641,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1642,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric423 : ∀ c∈certificate423.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1637,MergedCutCells.Batch136.certificate1638,MergedCutCells.Batch136.certificate1639,MergedCutCells.Batch136.certificate1640,MergedCutCells.Batch136.certificate1641,MergedCutCells.Batch136.certificate1642], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1637,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1638,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1639,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1640,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1641,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1642,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid423 : ∀ c∈certificate423.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1637,MergedCutCells.Batch136.certificate1638,MergedCutCells.Batch136.certificate1639,MergedCutCells.Batch136.certificate1640,MergedCutCells.Batch136.certificate1641,MergedCutCells.Batch136.certificate1642], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid142,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid142,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid142,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid142,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid142,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid142,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches423 : ∀ c∈certificate423.cells, c.population=certificate423.population := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1637,MergedCutCells.Batch136.certificate1638,MergedCutCells.Batch136.certificate1639,MergedCutCells.Batch136.certificate1640,MergedCutCells.Batch136.certificate1641,MergedCutCells.Batch136.certificate1642], c.population=PopulationCertificates.Batch014.certificate282
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers423 {x : ℝ} (hx : certificate423.interval.Contains x) : ∃ c∈certificate423.cells, c.region.interval.Contains x := rat_cut_group_covers certificate423 numericValid423 hx

def certificate424 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate282,PopulationCertificates.Batch014.certificate282,[MergedCutCells.Batch136.certificate1643],64,none,(1/2),(284718302103265231/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid424 : certificate424.NumericValid := by decide +kernel
theorem cellsSound424 : ∀ c∈certificate424.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1643], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.sound1643,List.forall_mem_nil _⟩
theorem cellsNumeric424 : ∀ c∈certificate424.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1643], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch136.numericValid1643,List.forall_mem_nil _⟩
theorem cellsEntropyValid424 : ∀ c∈certificate424.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1643], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches424 : ∀ c∈certificate424.cells, c.population=certificate424.population := by
  change ∀ c∈[MergedCutCells.Batch136.certificate1643], c.population=PopulationCertificates.Batch014.certificate282
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers424 {x : ℝ} (hx : certificate424.interval.Contains x) : ∃ c∈certificate424.cells, c.region.interval.Contains x := rat_cut_group_covers certificate424 numericValid424 hx

def certificate425 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate283,PopulationCertificates.Batch014.certificate283,[MergedCutCells.Batch137.certificate1644,MergedCutCells.Batch137.certificate1645,MergedCutCells.Batch137.certificate1646,MergedCutCells.Batch137.certificate1647],(792269118560323921/250000000000000000),none,(1/2),(1009079507015680717/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid425 : certificate425.NumericValid := by decide +kernel
theorem cellsSound425 : ∀ c∈certificate425.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1644,MergedCutCells.Batch137.certificate1645,MergedCutCells.Batch137.certificate1646,MergedCutCells.Batch137.certificate1647], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1644,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1645,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1646,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1647,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric425 : ∀ c∈certificate425.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1644,MergedCutCells.Batch137.certificate1645,MergedCutCells.Batch137.certificate1646,MergedCutCells.Batch137.certificate1647], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1644,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1645,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1646,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1647,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid425 : ∀ c∈certificate425.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1644,MergedCutCells.Batch137.certificate1645,MergedCutCells.Batch137.certificate1646,MergedCutCells.Batch137.certificate1647], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches425 : ∀ c∈certificate425.cells, c.population=certificate425.population := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1644,MergedCutCells.Batch137.certificate1645,MergedCutCells.Batch137.certificate1646,MergedCutCells.Batch137.certificate1647], c.population=PopulationCertificates.Batch014.certificate283
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers425 {x : ℝ} (hx : certificate425.interval.Contains x) : ∃ c∈certificate425.cells, c.region.interval.Contains x := rat_cut_group_covers certificate425 numericValid425 hx

def certificate426 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate284,PopulationCertificates.Batch014.certificate284,[MergedCutCells.Batch137.certificate1648,MergedCutCells.Batch137.certificate1649,MergedCutCells.Batch137.certificate1650,MergedCutCells.Batch137.certificate1651,MergedCutCells.Batch137.certificate1652,MergedCutCells.Batch137.certificate1653,MergedCutCells.Batch137.certificate1654],(893205237956365063/1000000000000000000),(some 64),(1/2),(1018228941626830853/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (190402791005615047/125000000000000000))⟩
theorem numericValid426 : certificate426.NumericValid := by decide +kernel
theorem cellsSound426 : ∀ c∈certificate426.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1648,MergedCutCells.Batch137.certificate1649,MergedCutCells.Batch137.certificate1650,MergedCutCells.Batch137.certificate1651,MergedCutCells.Batch137.certificate1652,MergedCutCells.Batch137.certificate1653,MergedCutCells.Batch137.certificate1654], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1648,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1650,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1651,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1652,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1653,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1654,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric426 : ∀ c∈certificate426.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1648,MergedCutCells.Batch137.certificate1649,MergedCutCells.Batch137.certificate1650,MergedCutCells.Batch137.certificate1651,MergedCutCells.Batch137.certificate1652,MergedCutCells.Batch137.certificate1653,MergedCutCells.Batch137.certificate1654], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1648,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1650,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1651,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1652,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1653,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1654,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid426 : ∀ c∈certificate426.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1648,MergedCutCells.Batch137.certificate1649,MergedCutCells.Batch137.certificate1650,MergedCutCells.Batch137.certificate1651,MergedCutCells.Batch137.certificate1652,MergedCutCells.Batch137.certificate1653,MergedCutCells.Batch137.certificate1654], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid143,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid143,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid143,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid143,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid143,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid143,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid143,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches426 : ∀ c∈certificate426.cells, c.population=certificate426.population := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1648,MergedCutCells.Batch137.certificate1649,MergedCutCells.Batch137.certificate1650,MergedCutCells.Batch137.certificate1651,MergedCutCells.Batch137.certificate1652,MergedCutCells.Batch137.certificate1653,MergedCutCells.Batch137.certificate1654], c.population=PopulationCertificates.Batch014.certificate284
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers426 {x : ℝ} (hx : certificate426.interval.Contains x) : ∃ c∈certificate426.cells, c.region.interval.Contains x := rat_cut_group_covers certificate426 numericValid426 hx

def certificate427 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate284,PopulationCertificates.Batch014.certificate284,[MergedCutCells.Batch137.certificate1655],64,none,(1/2),(46183643624672677/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid427 : certificate427.NumericValid := by decide +kernel
theorem cellsSound427 : ∀ c∈certificate427.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1655], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.sound1655,List.forall_mem_nil _⟩
theorem cellsNumeric427 : ∀ c∈certificate427.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1655], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch137.numericValid1655,List.forall_mem_nil _⟩
theorem cellsEntropyValid427 : ∀ c∈certificate427.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1655], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches427 : ∀ c∈certificate427.cells, c.population=certificate427.population := by
  change ∀ c∈[MergedCutCells.Batch137.certificate1655], c.population=PopulationCertificates.Batch014.certificate284
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers427 {x : ℝ} (hx : certificate427.interval.Contains x) : ∃ c∈certificate427.cells, c.region.interval.Contains x := rat_cut_group_covers certificate427 numericValid427 hx

def certificate428 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate285,PopulationCertificates.Batch014.certificate285,[MergedCutCells.Batch138.certificate1656,MergedCutCells.Batch138.certificate1657,MergedCutCells.Batch138.certificate1658,MergedCutCells.Batch138.certificate1659],(3151127548206655857/1000000000000000000),none,(1/2),(1021926216017334597/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid428 : certificate428.NumericValid := by decide +kernel
theorem cellsSound428 : ∀ c∈certificate428.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch138.certificate1656,MergedCutCells.Batch138.certificate1657,MergedCutCells.Batch138.certificate1658,MergedCutCells.Batch138.certificate1659], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1656,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1657,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1658,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1659,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric428 : ∀ c∈certificate428.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch138.certificate1656,MergedCutCells.Batch138.certificate1657,MergedCutCells.Batch138.certificate1658,MergedCutCells.Batch138.certificate1659], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1656,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1657,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1658,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1659,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid428 : ∀ c∈certificate428.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch138.certificate1656,MergedCutCells.Batch138.certificate1657,MergedCutCells.Batch138.certificate1658,MergedCutCells.Batch138.certificate1659], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches428 : ∀ c∈certificate428.cells, c.population=certificate428.population := by
  change ∀ c∈[MergedCutCells.Batch138.certificate1656,MergedCutCells.Batch138.certificate1657,MergedCutCells.Batch138.certificate1658,MergedCutCells.Batch138.certificate1659], c.population=PopulationCertificates.Batch014.certificate285
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers428 {x : ℝ} (hx : certificate428.interval.Contains x) : ∃ c∈certificate428.cells, c.region.interval.Contains x := rat_cut_group_covers certificate428 numericValid428 hx

def certificate429 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate286,PopulationCertificates.Batch014.certificate286,[MergedCutCells.Batch138.certificate1660,MergedCutCells.Batch138.certificate1661,MergedCutCells.Batch138.certificate1662,MergedCutCells.Batch138.certificate1663,MergedCutCells.Batch138.certificate1664,MergedCutCells.Batch138.certificate1665,MergedCutCells.Batch138.certificate1666,MergedCutCells.Batch138.certificate1667,MergedCutCells.Batch139.certificate1668],(850130078969395973/1000000000000000000),(some 64),(1/2),(1031581914212435391/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (761164431576169199/500000000000000000))⟩
theorem numericValid429 : certificate429.NumericValid := by decide +kernel
theorem cellsSound429 : ∀ c∈certificate429.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch138.certificate1660,MergedCutCells.Batch138.certificate1661,MergedCutCells.Batch138.certificate1662,MergedCutCells.Batch138.certificate1663,MergedCutCells.Batch138.certificate1664,MergedCutCells.Batch138.certificate1665,MergedCutCells.Batch138.certificate1666,MergedCutCells.Batch138.certificate1667,MergedCutCells.Batch139.certificate1668], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1660,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1662,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1663,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1664,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1665,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1666,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.sound1667,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1668,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric429 : ∀ c∈certificate429.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch138.certificate1660,MergedCutCells.Batch138.certificate1661,MergedCutCells.Batch138.certificate1662,MergedCutCells.Batch138.certificate1663,MergedCutCells.Batch138.certificate1664,MergedCutCells.Batch138.certificate1665,MergedCutCells.Batch138.certificate1666,MergedCutCells.Batch138.certificate1667,MergedCutCells.Batch139.certificate1668], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1660,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1662,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1663,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1664,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1665,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1666,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch138.numericValid1667,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1668,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid429 : ∀ c∈certificate429.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch138.certificate1660,MergedCutCells.Batch138.certificate1661,MergedCutCells.Batch138.certificate1662,MergedCutCells.Batch138.certificate1663,MergedCutCells.Batch138.certificate1664,MergedCutCells.Batch138.certificate1665,MergedCutCells.Batch138.certificate1666,MergedCutCells.Batch138.certificate1667,MergedCutCells.Batch139.certificate1668], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid144,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches429 : ∀ c∈certificate429.cells, c.population=certificate429.population := by
  change ∀ c∈[MergedCutCells.Batch138.certificate1660,MergedCutCells.Batch138.certificate1661,MergedCutCells.Batch138.certificate1662,MergedCutCells.Batch138.certificate1663,MergedCutCells.Batch138.certificate1664,MergedCutCells.Batch138.certificate1665,MergedCutCells.Batch138.certificate1666,MergedCutCells.Batch138.certificate1667,MergedCutCells.Batch139.certificate1668], c.population=PopulationCertificates.Batch014.certificate286
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers429 {x : ℝ} (hx : certificate429.interval.Contains x) : ∃ c∈certificate429.cells, c.region.interval.Contains x := rat_cut_group_covers certificate429 numericValid429 hx

def certificate430 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate286,PopulationCertificates.Batch014.certificate286,[MergedCutCells.Batch139.certificate1669],64,none,(1/2),(1192616702391611257/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid430 : certificate430.NumericValid := by decide +kernel
theorem cellsSound430 : ∀ c∈certificate430.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1669], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1669,List.forall_mem_nil _⟩
theorem cellsNumeric430 : ∀ c∈certificate430.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1669], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1669,List.forall_mem_nil _⟩
theorem cellsEntropyValid430 : ∀ c∈certificate430.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1669], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches430 : ∀ c∈certificate430.cells, c.population=certificate430.population := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1669], c.population=PopulationCertificates.Batch014.certificate286
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers430 {x : ℝ} (hx : certificate430.interval.Contains x) : ∃ c∈certificate430.cells, c.region.interval.Contains x := rat_cut_group_covers certificate430 numericValid430 hx

def certificate431 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate287,PopulationCertificates.Batch014.certificate287,[MergedCutCells.Batch139.certificate1670,MergedCutCells.Batch139.certificate1671,MergedCutCells.Batch139.certificate1672,MergedCutCells.Batch139.certificate1673],(3142771338119082191/1000000000000000000),none,(1/2),(1051295453502993537/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid431 : certificate431.NumericValid := by decide +kernel
theorem cellsSound431 : ∀ c∈certificate431.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1670,MergedCutCells.Batch139.certificate1671,MergedCutCells.Batch139.certificate1672,MergedCutCells.Batch139.certificate1673], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1671,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1672,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1673,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric431 : ∀ c∈certificate431.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1670,MergedCutCells.Batch139.certificate1671,MergedCutCells.Batch139.certificate1672,MergedCutCells.Batch139.certificate1673], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1671,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1672,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1673,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid431 : ∀ c∈certificate431.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1670,MergedCutCells.Batch139.certificate1671,MergedCutCells.Batch139.certificate1672,MergedCutCells.Batch139.certificate1673], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches431 : ∀ c∈certificate431.cells, c.population=certificate431.population := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1670,MergedCutCells.Batch139.certificate1671,MergedCutCells.Batch139.certificate1672,MergedCutCells.Batch139.certificate1673], c.population=PopulationCertificates.Batch014.certificate287
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers431 {x : ℝ} (hx : certificate431.interval.Contains x) : ∃ c∈certificate431.cells, c.region.interval.Contains x := rat_cut_group_covers certificate431 numericValid431 hx

end Cycle12.MergedCutGroups.Batch035
