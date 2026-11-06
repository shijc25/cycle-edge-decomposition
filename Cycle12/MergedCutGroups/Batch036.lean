import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch014
import Cycle12.MergedCutCells.Batch139
import Cycle12.MergedCutCells.Batch140
import Cycle12.MergedCutCells.Batch141
import Cycle12.MergedCutCells.Batch142
import Cycle12.MergedCutCells.Batch143
import Cycle12.PopulationCertificates.Batch014

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch036

def certificate432 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate288,PopulationCertificates.Batch014.certificate288,[MergedCutCells.Batch139.certificate1674,MergedCutCells.Batch139.certificate1675,MergedCutCells.Batch139.certificate1676,MergedCutCells.Batch139.certificate1677,MergedCutCells.Batch139.certificate1678,MergedCutCells.Batch139.certificate1679,MergedCutCells.Batch140.certificate1680],(435473893095902789/500000000000000000),(some 64),(1/2),(519993937580056361/500000000000000000),(some (69314718055994531/100000000000000000)),(some (380671406489042703/250000000000000000))⟩
theorem numericValid432 : certificate432.NumericValid := by decide +kernel
theorem cellsSound432 : ∀ c∈certificate432.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1674,MergedCutCells.Batch139.certificate1675,MergedCutCells.Batch139.certificate1676,MergedCutCells.Batch139.certificate1677,MergedCutCells.Batch139.certificate1678,MergedCutCells.Batch139.certificate1679,MergedCutCells.Batch140.certificate1680], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1675,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1676,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1677,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1678,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.sound1679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1680,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric432 : ∀ c∈certificate432.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1674,MergedCutCells.Batch139.certificate1675,MergedCutCells.Batch139.certificate1676,MergedCutCells.Batch139.certificate1677,MergedCutCells.Batch139.certificate1678,MergedCutCells.Batch139.certificate1679,MergedCutCells.Batch140.certificate1680], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1675,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1676,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1677,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1678,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch139.numericValid1679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1680,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid432 : ∀ c∈certificate432.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1674,MergedCutCells.Batch139.certificate1675,MergedCutCells.Batch139.certificate1676,MergedCutCells.Batch139.certificate1677,MergedCutCells.Batch139.certificate1678,MergedCutCells.Batch139.certificate1679,MergedCutCells.Batch140.certificate1680], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid145,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid145,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid145,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid145,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid145,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid145,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid145,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches432 : ∀ c∈certificate432.cells, c.population=certificate432.population := by
  change ∀ c∈[MergedCutCells.Batch139.certificate1674,MergedCutCells.Batch139.certificate1675,MergedCutCells.Batch139.certificate1676,MergedCutCells.Batch139.certificate1677,MergedCutCells.Batch139.certificate1678,MergedCutCells.Batch139.certificate1679,MergedCutCells.Batch140.certificate1680], c.population=PopulationCertificates.Batch014.certificate288
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers432 {x : ℝ} (hx : certificate432.interval.Contains x) : ∃ c∈certificate432.cells, c.region.interval.Contains x := rat_cut_group_covers certificate432 numericValid432 hx

def certificate433 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate288,PopulationCertificates.Batch014.certificate288,[MergedCutCells.Batch140.certificate1681],64,none,(1/2),(148849539015326373/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid433 : certificate433.NumericValid := by decide +kernel
theorem cellsSound433 : ∀ c∈certificate433.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1681], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1681,List.forall_mem_nil _⟩
theorem cellsNumeric433 : ∀ c∈certificate433.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1681], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1681,List.forall_mem_nil _⟩
theorem cellsEntropyValid433 : ∀ c∈certificate433.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1681], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches433 : ∀ c∈certificate433.cells, c.population=certificate433.population := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1681], c.population=PopulationCertificates.Batch014.certificate288
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers433 {x : ℝ} (hx : certificate433.interval.Contains x) : ∃ c∈certificate433.cells, c.region.interval.Contains x := rat_cut_group_covers certificate433 numericValid433 hx

def certificate434 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate289,PopulationCertificates.Batch014.certificate289,[MergedCutCells.Batch140.certificate1682,MergedCutCells.Batch140.certificate1683,MergedCutCells.Batch140.certificate1684,MergedCutCells.Batch140.certificate1685],(195443867312375697/62500000000000000),none,(1/2),(267016383808916463/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid434 : certificate434.NumericValid := by decide +kernel
theorem cellsSound434 : ∀ c∈certificate434.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1682,MergedCutCells.Batch140.certificate1683,MergedCutCells.Batch140.certificate1684,MergedCutCells.Batch140.certificate1685], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1683,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1684,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1685,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric434 : ∀ c∈certificate434.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1682,MergedCutCells.Batch140.certificate1683,MergedCutCells.Batch140.certificate1684,MergedCutCells.Batch140.certificate1685], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1683,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1684,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1685,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid434 : ∀ c∈certificate434.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1682,MergedCutCells.Batch140.certificate1683,MergedCutCells.Batch140.certificate1684,MergedCutCells.Batch140.certificate1685], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches434 : ∀ c∈certificate434.cells, c.population=certificate434.population := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1682,MergedCutCells.Batch140.certificate1683,MergedCutCells.Batch140.certificate1684,MergedCutCells.Batch140.certificate1685], c.population=PopulationCertificates.Batch014.certificate289
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers434 {x : ℝ} (hx : certificate434.interval.Contains x) : ∃ c∈certificate434.cells, c.region.interval.Contains x := rat_cut_group_covers certificate434 numericValid434 hx

def certificate435 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate290,PopulationCertificates.Batch014.certificate290,[MergedCutCells.Batch140.certificate1686,MergedCutCells.Batch140.certificate1687,MergedCutCells.Batch140.certificate1688,MergedCutCells.Batch140.certificate1689,MergedCutCells.Batch140.certificate1690,MergedCutCells.Batch140.certificate1691,MergedCutCells.Batch141.certificate1692],(886733123218877859/1000000000000000000),(some 64),(1/2),(525822955644040779/500000000000000000),(some (69314718055994531/100000000000000000)),(some (304904372308528179/200000000000000000))⟩
theorem numericValid435 : certificate435.NumericValid := by decide +kernel
theorem cellsSound435 : ∀ c∈certificate435.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1686,MergedCutCells.Batch140.certificate1687,MergedCutCells.Batch140.certificate1688,MergedCutCells.Batch140.certificate1689,MergedCutCells.Batch140.certificate1690,MergedCutCells.Batch140.certificate1691,MergedCutCells.Batch141.certificate1692], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1686,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1687,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1688,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1689,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1690,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.sound1691,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1692,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric435 : ∀ c∈certificate435.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1686,MergedCutCells.Batch140.certificate1687,MergedCutCells.Batch140.certificate1688,MergedCutCells.Batch140.certificate1689,MergedCutCells.Batch140.certificate1690,MergedCutCells.Batch140.certificate1691,MergedCutCells.Batch141.certificate1692], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1686,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1687,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1688,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1689,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1690,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch140.numericValid1691,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1692,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid435 : ∀ c∈certificate435.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1686,MergedCutCells.Batch140.certificate1687,MergedCutCells.Batch140.certificate1688,MergedCutCells.Batch140.certificate1689,MergedCutCells.Batch140.certificate1690,MergedCutCells.Batch140.certificate1691,MergedCutCells.Batch141.certificate1692], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid146,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid146,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid146,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid146,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid146,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid146,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid146,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches435 : ∀ c∈certificate435.cells, c.population=certificate435.population := by
  change ∀ c∈[MergedCutCells.Batch140.certificate1686,MergedCutCells.Batch140.certificate1687,MergedCutCells.Batch140.certificate1688,MergedCutCells.Batch140.certificate1689,MergedCutCells.Batch140.certificate1690,MergedCutCells.Batch140.certificate1691,MergedCutCells.Batch141.certificate1692], c.population=PopulationCertificates.Batch014.certificate290
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers435 {x : ℝ} (hx : certificate435.interval.Contains x) : ∃ c∈certificate435.cells, c.region.interval.Contains x := rat_cut_group_covers certificate435 numericValid435 hx

def certificate436 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate290,PopulationCertificates.Batch014.certificate290,[MergedCutCells.Batch141.certificate1693],64,none,(1/2),(47613575290139041/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid436 : certificate436.NumericValid := by decide +kernel
theorem cellsSound436 : ∀ c∈certificate436.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1693], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1693,List.forall_mem_nil _⟩
theorem cellsNumeric436 : ∀ c∈certificate436.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1693], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1693,List.forall_mem_nil _⟩
theorem cellsEntropyValid436 : ∀ c∈certificate436.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1693], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches436 : ∀ c∈certificate436.cells, c.population=certificate436.population := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1693], c.population=PopulationCertificates.Batch014.certificate290
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers436 {x : ℝ} (hx : certificate436.interval.Contains x) : ∃ c∈certificate436.cells, c.region.interval.Contains x := rat_cut_group_covers certificate436 numericValid436 hx

def certificate437 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate291,PopulationCertificates.Batch014.certificate291,[MergedCutCells.Batch141.certificate1694,MergedCutCells.Batch141.certificate1695,MergedCutCells.Batch141.certificate1696,MergedCutCells.Batch141.certificate1697],(31115351986343331/10000000000000000),none,(1/2),(271235482692956153/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid437 : certificate437.NumericValid := by decide +kernel
theorem cellsSound437 : ∀ c∈certificate437.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1694,MergedCutCells.Batch141.certificate1695,MergedCutCells.Batch141.certificate1696,MergedCutCells.Batch141.certificate1697], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1694,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1695,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1697,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric437 : ∀ c∈certificate437.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1694,MergedCutCells.Batch141.certificate1695,MergedCutCells.Batch141.certificate1696,MergedCutCells.Batch141.certificate1697], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1694,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1695,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1697,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid437 : ∀ c∈certificate437.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1694,MergedCutCells.Batch141.certificate1695,MergedCutCells.Batch141.certificate1696,MergedCutCells.Batch141.certificate1697], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches437 : ∀ c∈certificate437.cells, c.population=certificate437.population := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1694,MergedCutCells.Batch141.certificate1695,MergedCutCells.Batch141.certificate1696,MergedCutCells.Batch141.certificate1697], c.population=PopulationCertificates.Batch014.certificate291
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers437 {x : ℝ} (hx : certificate437.interval.Contains x) : ∃ c∈certificate437.cells, c.region.interval.Contains x := rat_cut_group_covers certificate437 numericValid437 hx

def certificate438 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate292,PopulationCertificates.Batch014.certificate292,[MergedCutCells.Batch141.certificate1698,MergedCutCells.Batch141.certificate1699,MergedCutCells.Batch141.certificate1700,MergedCutCells.Batch141.certificate1701,MergedCutCells.Batch141.certificate1702,MergedCutCells.Batch141.certificate1703,MergedCutCells.Batch142.certificate1704],(180340474522367589/200000000000000000),(some 64),(1/2),(1061130734087492881/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (305268699979081073/200000000000000000))⟩
theorem numericValid438 : certificate438.NumericValid := by decide +kernel
theorem cellsSound438 : ∀ c∈certificate438.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1698,MergedCutCells.Batch141.certificate1699,MergedCutCells.Batch141.certificate1700,MergedCutCells.Batch141.certificate1701,MergedCutCells.Batch141.certificate1702,MergedCutCells.Batch141.certificate1703,MergedCutCells.Batch142.certificate1704], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1699,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1700,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1701,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1702,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.sound1703,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1704,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric438 : ∀ c∈certificate438.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1698,MergedCutCells.Batch141.certificate1699,MergedCutCells.Batch141.certificate1700,MergedCutCells.Batch141.certificate1701,MergedCutCells.Batch141.certificate1702,MergedCutCells.Batch141.certificate1703,MergedCutCells.Batch142.certificate1704], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1699,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1700,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1701,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1702,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch141.numericValid1703,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1704,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid438 : ∀ c∈certificate438.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1698,MergedCutCells.Batch141.certificate1699,MergedCutCells.Batch141.certificate1700,MergedCutCells.Batch141.certificate1701,MergedCutCells.Batch141.certificate1702,MergedCutCells.Batch141.certificate1703,MergedCutCells.Batch142.certificate1704], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid147,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid147,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid147,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid147,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid147,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid147,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid147,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches438 : ∀ c∈certificate438.cells, c.population=certificate438.population := by
  change ∀ c∈[MergedCutCells.Batch141.certificate1698,MergedCutCells.Batch141.certificate1699,MergedCutCells.Batch141.certificate1700,MergedCutCells.Batch141.certificate1701,MergedCutCells.Batch141.certificate1702,MergedCutCells.Batch141.certificate1703,MergedCutCells.Batch142.certificate1704], c.population=PopulationCertificates.Batch014.certificate292
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers438 {x : ℝ} (hx : certificate438.interval.Contains x) : ∃ c∈certificate438.cells, c.region.interval.Contains x := rat_cut_group_covers certificate438 numericValid438 hx

def certificate439 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate292,PopulationCertificates.Batch014.certificate292,[MergedCutCells.Batch142.certificate1705],64,none,(1/2),(1189721289655235519/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid439 : certificate439.NumericValid := by decide +kernel
theorem cellsSound439 : ∀ c∈certificate439.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1705], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1705,List.forall_mem_nil _⟩
theorem cellsNumeric439 : ∀ c∈certificate439.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1705], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1705,List.forall_mem_nil _⟩
theorem cellsEntropyValid439 : ∀ c∈certificate439.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1705], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches439 : ∀ c∈certificate439.cells, c.population=certificate439.population := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1705], c.population=PopulationCertificates.Batch014.certificate292
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers439 {x : ℝ} (hx : certificate439.interval.Contains x) : ∃ c∈certificate439.cells, c.region.interval.Contains x := rat_cut_group_covers certificate439 numericValid439 hx

def certificate440 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate293,PopulationCertificates.Batch014.certificate293,[MergedCutCells.Batch142.certificate1706,MergedCutCells.Batch142.certificate1707,MergedCutCells.Batch142.certificate1708,MergedCutCells.Batch142.certificate1709],(774015596391450017/250000000000000000),none,(1/2),(1101888954490828097/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid440 : certificate440.NumericValid := by decide +kernel
theorem cellsSound440 : ∀ c∈certificate440.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1706,MergedCutCells.Batch142.certificate1707,MergedCutCells.Batch142.certificate1708,MergedCutCells.Batch142.certificate1709], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1706,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1707,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1708,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1709,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric440 : ∀ c∈certificate440.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1706,MergedCutCells.Batch142.certificate1707,MergedCutCells.Batch142.certificate1708,MergedCutCells.Batch142.certificate1709], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1706,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1707,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1708,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1709,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid440 : ∀ c∈certificate440.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1706,MergedCutCells.Batch142.certificate1707,MergedCutCells.Batch142.certificate1708,MergedCutCells.Batch142.certificate1709], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches440 : ∀ c∈certificate440.cells, c.population=certificate440.population := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1706,MergedCutCells.Batch142.certificate1707,MergedCutCells.Batch142.certificate1708,MergedCutCells.Batch142.certificate1709], c.population=PopulationCertificates.Batch014.certificate293
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers440 {x : ℝ} (hx : certificate440.interval.Contains x) : ∃ c∈certificate440.cells, c.region.interval.Contains x := rat_cut_group_covers certificate440 numericValid440 hx

def certificate441 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate294,PopulationCertificates.Batch014.certificate294,[MergedCutCells.Batch142.certificate1710,MergedCutCells.Batch142.certificate1711,MergedCutCells.Batch142.certificate1712,MergedCutCells.Batch142.certificate1713,MergedCutCells.Batch142.certificate1714,MergedCutCells.Batch142.certificate1715,MergedCutCells.Batch143.certificate1716],(872587166596620647/1000000000000000000),(some 64),(1/2),(533198087814200333/500000000000000000),(some (69314718055994531/100000000000000000)),(some (762783671913958667/500000000000000000))⟩
theorem numericValid441 : certificate441.NumericValid := by decide +kernel
theorem cellsSound441 : ∀ c∈certificate441.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1710,MergedCutCells.Batch142.certificate1711,MergedCutCells.Batch142.certificate1712,MergedCutCells.Batch142.certificate1713,MergedCutCells.Batch142.certificate1714,MergedCutCells.Batch142.certificate1715,MergedCutCells.Batch143.certificate1716], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1711,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1713,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.sound1715,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1716,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric441 : ∀ c∈certificate441.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1710,MergedCutCells.Batch142.certificate1711,MergedCutCells.Batch142.certificate1712,MergedCutCells.Batch142.certificate1713,MergedCutCells.Batch142.certificate1714,MergedCutCells.Batch142.certificate1715,MergedCutCells.Batch143.certificate1716], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1711,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1713,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch142.numericValid1715,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1716,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid441 : ∀ c∈certificate441.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1710,MergedCutCells.Batch142.certificate1711,MergedCutCells.Batch142.certificate1712,MergedCutCells.Batch142.certificate1713,MergedCutCells.Batch142.certificate1714,MergedCutCells.Batch142.certificate1715,MergedCutCells.Batch143.certificate1716], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid148,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid148,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid148,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid148,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid148,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid148,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid148,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches441 : ∀ c∈certificate441.cells, c.population=certificate441.population := by
  change ∀ c∈[MergedCutCells.Batch142.certificate1710,MergedCutCells.Batch142.certificate1711,MergedCutCells.Batch142.certificate1712,MergedCutCells.Batch142.certificate1713,MergedCutCells.Batch142.certificate1714,MergedCutCells.Batch142.certificate1715,MergedCutCells.Batch143.certificate1716], c.population=PopulationCertificates.Batch014.certificate294
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers441 {x : ℝ} (hx : certificate441.interval.Contains x) : ∃ c∈certificate441.cells, c.region.interval.Contains x := rat_cut_group_covers certificate441 numericValid441 hx

def certificate442 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate294,PopulationCertificates.Batch014.certificate294,[MergedCutCells.Batch143.certificate1717],64,none,(1/2),(2444984480535695891/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid442 : certificate442.NumericValid := by decide +kernel
theorem cellsSound442 : ∀ c∈certificate442.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1717], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1717,List.forall_mem_nil _⟩
theorem cellsNumeric442 : ∀ c∈certificate442.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1717], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1717,List.forall_mem_nil _⟩
theorem cellsEntropyValid442 : ∀ c∈certificate442.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1717], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches442 : ∀ c∈certificate442.cells, c.population=certificate442.population := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1717], c.population=PopulationCertificates.Batch014.certificate294
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers442 {x : ℝ} (hx : certificate442.interval.Contains x) : ∃ c∈certificate442.cells, c.region.interval.Contains x := rat_cut_group_covers certificate442 numericValid442 hx

def certificate443 : RatCutGroup := ⟨GeometryCertificates.Batch014.certificate295,PopulationCertificates.Batch014.certificate295,[MergedCutCells.Batch143.certificate1718,MergedCutCells.Batch143.certificate1719,MergedCutCells.Batch143.certificate1720,MergedCutCells.Batch143.certificate1721],(3079081416946597937/1000000000000000000),none,(1/2),(1116116377987659517/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid443 : certificate443.NumericValid := by decide +kernel
theorem cellsSound443 : ∀ c∈certificate443.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1718,MergedCutCells.Batch143.certificate1719,MergedCutCells.Batch143.certificate1720,MergedCutCells.Batch143.certificate1721], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1718,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1719,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1720,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.sound1721,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric443 : ∀ c∈certificate443.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1718,MergedCutCells.Batch143.certificate1719,MergedCutCells.Batch143.certificate1720,MergedCutCells.Batch143.certificate1721], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1718,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1719,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1720,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch143.numericValid1721,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid443 : ∀ c∈certificate443.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1718,MergedCutCells.Batch143.certificate1719,MergedCutCells.Batch143.certificate1720,MergedCutCells.Batch143.certificate1721], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches443 : ∀ c∈certificate443.cells, c.population=certificate443.population := by
  change ∀ c∈[MergedCutCells.Batch143.certificate1718,MergedCutCells.Batch143.certificate1719,MergedCutCells.Batch143.certificate1720,MergedCutCells.Batch143.certificate1721], c.population=PopulationCertificates.Batch014.certificate295
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers443 {x : ℝ} (hx : certificate443.interval.Contains x) : ∃ c∈certificate443.cells, c.region.interval.Contains x := rat_cut_group_covers certificate443 numericValid443 hx

end Cycle12.MergedCutGroups.Batch036
