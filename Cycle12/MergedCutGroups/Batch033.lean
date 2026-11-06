import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch013
import Cycle12.MergedCutCells.Batch128
import Cycle12.MergedCutCells.Batch129
import Cycle12.MergedCutCells.Batch130
import Cycle12.MergedCutCells.Batch131
import Cycle12.PopulationCertificates.Batch013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch033

def certificate396 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate264,PopulationCertificates.Batch013.certificate264,[MergedCutCells.Batch128.certificate1536,MergedCutCells.Batch128.certificate1537,MergedCutCells.Batch128.certificate1538,MergedCutCells.Batch128.certificate1539,MergedCutCells.Batch128.certificate1540,MergedCutCells.Batch128.certificate1541],(904479060065044863/1000000000000000000),(some 64),(1/2),(182159728844155699/200000000000000000),(some (69314718055994531/100000000000000000)),(some (11795780604515433/7812500000000000))⟩
theorem numericValid396 : certificate396.NumericValid := by decide +kernel
theorem cellsSound396 : ∀ c∈certificate396.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1536,MergedCutCells.Batch128.certificate1537,MergedCutCells.Batch128.certificate1538,MergedCutCells.Batch128.certificate1539,MergedCutCells.Batch128.certificate1540,MergedCutCells.Batch128.certificate1541], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1536,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1537,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1538,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1539,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1540,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1541,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric396 : ∀ c∈certificate396.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1536,MergedCutCells.Batch128.certificate1537,MergedCutCells.Batch128.certificate1538,MergedCutCells.Batch128.certificate1539,MergedCutCells.Batch128.certificate1540,MergedCutCells.Batch128.certificate1541], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1536,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1537,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1538,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1539,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1540,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1541,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid396 : ∀ c∈certificate396.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1536,MergedCutCells.Batch128.certificate1537,MergedCutCells.Batch128.certificate1538,MergedCutCells.Batch128.certificate1539,MergedCutCells.Batch128.certificate1540,MergedCutCells.Batch128.certificate1541], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid133,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid133,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid133,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid133,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid133,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid133,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches396 : ∀ c∈certificate396.cells, c.population=certificate396.population := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1536,MergedCutCells.Batch128.certificate1537,MergedCutCells.Batch128.certificate1538,MergedCutCells.Batch128.certificate1539,MergedCutCells.Batch128.certificate1540,MergedCutCells.Batch128.certificate1541], c.population=PopulationCertificates.Batch013.certificate264
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers396 {x : ℝ} (hx : certificate396.interval.Contains x) : ∃ c∈certificate396.cells, c.region.interval.Contains x := rat_cut_group_covers certificate396 numericValid396 hx

def certificate397 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate264,PopulationCertificates.Batch013.certificate264,[MergedCutCells.Batch128.certificate1542],64,none,(1/2),(2058435086535959813/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid397 : certificate397.NumericValid := by decide +kernel
theorem cellsSound397 : ∀ c∈certificate397.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1542], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1542,List.forall_mem_nil _⟩
theorem cellsNumeric397 : ∀ c∈certificate397.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1542], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1542,List.forall_mem_nil _⟩
theorem cellsEntropyValid397 : ∀ c∈certificate397.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1542], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches397 : ∀ c∈certificate397.cells, c.population=certificate397.population := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1542], c.population=PopulationCertificates.Batch013.certificate264
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers397 {x : ℝ} (hx : certificate397.interval.Contains x) : ∃ c∈certificate397.cells, c.region.interval.Contains x := rat_cut_group_covers certificate397 numericValid397 hx

def certificate398 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate265,PopulationCertificates.Batch013.certificate265,[MergedCutCells.Batch128.certificate1543,MergedCutCells.Batch128.certificate1544,MergedCutCells.Batch128.certificate1545,MergedCutCells.Batch128.certificate1546],(840586810601234109/250000000000000000),none,(1/2),(473861720404486639/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid398 : certificate398.NumericValid := by decide +kernel
theorem cellsSound398 : ∀ c∈certificate398.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1543,MergedCutCells.Batch128.certificate1544,MergedCutCells.Batch128.certificate1545,MergedCutCells.Batch128.certificate1546], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1543,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1544,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1545,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1546,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric398 : ∀ c∈certificate398.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1543,MergedCutCells.Batch128.certificate1544,MergedCutCells.Batch128.certificate1545,MergedCutCells.Batch128.certificate1546], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1543,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1544,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1545,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1546,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid398 : ∀ c∈certificate398.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1543,MergedCutCells.Batch128.certificate1544,MergedCutCells.Batch128.certificate1545,MergedCutCells.Batch128.certificate1546], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches398 : ∀ c∈certificate398.cells, c.population=certificate398.population := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1543,MergedCutCells.Batch128.certificate1544,MergedCutCells.Batch128.certificate1545,MergedCutCells.Batch128.certificate1546], c.population=PopulationCertificates.Batch013.certificate265
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers398 {x : ℝ} (hx : certificate398.interval.Contains x) : ∃ c∈certificate398.cells, c.region.interval.Contains x := rat_cut_group_covers certificate398 numericValid398 hx

def certificate399 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate266,PopulationCertificates.Batch013.certificate266,[MergedCutCells.Batch128.certificate1547,MergedCutCells.Batch129.certificate1548,MergedCutCells.Batch129.certificate1549,MergedCutCells.Batch129.certificate1550,MergedCutCells.Batch129.certificate1551,MergedCutCells.Batch129.certificate1552],(446602619053824163/500000000000000000),(some 64),(1/2),(114557934019975271/125000000000000000),(some (69314718055994531/100000000000000000)),(some (302258775878664799/200000000000000000))⟩
theorem numericValid399 : certificate399.NumericValid := by decide +kernel
theorem cellsSound399 : ∀ c∈certificate399.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1547,MergedCutCells.Batch129.certificate1548,MergedCutCells.Batch129.certificate1549,MergedCutCells.Batch129.certificate1550,MergedCutCells.Batch129.certificate1551,MergedCutCells.Batch129.certificate1552], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.sound1547,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1548,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1549,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1550,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1551,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1552,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric399 : ∀ c∈certificate399.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1547,MergedCutCells.Batch129.certificate1548,MergedCutCells.Batch129.certificate1549,MergedCutCells.Batch129.certificate1550,MergedCutCells.Batch129.certificate1551,MergedCutCells.Batch129.certificate1552], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch128.numericValid1547,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1548,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1549,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1550,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1551,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1552,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid399 : ∀ c∈certificate399.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1547,MergedCutCells.Batch129.certificate1548,MergedCutCells.Batch129.certificate1549,MergedCutCells.Batch129.certificate1550,MergedCutCells.Batch129.certificate1551,MergedCutCells.Batch129.certificate1552], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid134,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid134,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid134,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid134,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid134,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid134,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches399 : ∀ c∈certificate399.cells, c.population=certificate399.population := by
  change ∀ c∈[MergedCutCells.Batch128.certificate1547,MergedCutCells.Batch129.certificate1548,MergedCutCells.Batch129.certificate1549,MergedCutCells.Batch129.certificate1550,MergedCutCells.Batch129.certificate1551,MergedCutCells.Batch129.certificate1552], c.population=PopulationCertificates.Batch013.certificate266
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers399 {x : ℝ} (hx : certificate399.interval.Contains x) : ∃ c∈certificate399.cells, c.region.interval.Contains x := rat_cut_group_covers certificate399 numericValid399 hx

def certificate400 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate266,PopulationCertificates.Batch013.certificate266,[MergedCutCells.Batch129.certificate1553],64,none,(1/2),(2096424700224435637/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid400 : certificate400.NumericValid := by decide +kernel
theorem cellsSound400 : ∀ c∈certificate400.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1553], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1553,List.forall_mem_nil _⟩
theorem cellsNumeric400 : ∀ c∈certificate400.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1553], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1553,List.forall_mem_nil _⟩
theorem cellsEntropyValid400 : ∀ c∈certificate400.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1553], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches400 : ∀ c∈certificate400.cells, c.population=certificate400.population := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1553], c.population=PopulationCertificates.Batch013.certificate266
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers400 {x : ℝ} (hx : certificate400.interval.Contains x) : ∃ c∈certificate400.cells, c.region.interval.Contains x := rat_cut_group_covers certificate400 numericValid400 hx

def certificate401 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate267,PopulationCertificates.Batch013.certificate267,[MergedCutCells.Batch129.certificate1554,MergedCutCells.Batch129.certificate1555,MergedCutCells.Batch129.certificate1556],(33276291042337749/10000000000000000),none,(1/2),(190634810646072251/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid401 : certificate401.NumericValid := by decide +kernel
theorem cellsSound401 : ∀ c∈certificate401.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1554,MergedCutCells.Batch129.certificate1555,MergedCutCells.Batch129.certificate1556], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1554,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1555,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1556,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric401 : ∀ c∈certificate401.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1554,MergedCutCells.Batch129.certificate1555,MergedCutCells.Batch129.certificate1556], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1554,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1555,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1556,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid401 : ∀ c∈certificate401.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1554,MergedCutCells.Batch129.certificate1555,MergedCutCells.Batch129.certificate1556], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches401 : ∀ c∈certificate401.cells, c.population=certificate401.population := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1554,MergedCutCells.Batch129.certificate1555,MergedCutCells.Batch129.certificate1556], c.population=PopulationCertificates.Batch013.certificate267
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers401 {x : ℝ} (hx : certificate401.interval.Contains x) : ∃ c∈certificate401.cells, c.region.interval.Contains x := rat_cut_group_covers certificate401 numericValid401 hx

def certificate402 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate268,PopulationCertificates.Batch013.certificate268,[MergedCutCells.Batch129.certificate1557,MergedCutCells.Batch129.certificate1558,MergedCutCells.Batch129.certificate1559,MergedCutCells.Batch130.certificate1560,MergedCutCells.Batch130.certificate1561,MergedCutCells.Batch130.certificate1562],(915535368672746039/1000000000000000000),(some 64),(1/2),(930075583056789183/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (756975200861441221/500000000000000000))⟩
theorem numericValid402 : certificate402.NumericValid := by decide +kernel
theorem cellsSound402 : ∀ c∈certificate402.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1557,MergedCutCells.Batch129.certificate1558,MergedCutCells.Batch129.certificate1559,MergedCutCells.Batch130.certificate1560,MergedCutCells.Batch130.certificate1561,MergedCutCells.Batch130.certificate1562], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1558,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.sound1559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1560,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1561,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1562,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric402 : ∀ c∈certificate402.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1557,MergedCutCells.Batch129.certificate1558,MergedCutCells.Batch129.certificate1559,MergedCutCells.Batch130.certificate1560,MergedCutCells.Batch130.certificate1561,MergedCutCells.Batch130.certificate1562], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1558,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch129.numericValid1559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1560,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1561,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1562,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid402 : ∀ c∈certificate402.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1557,MergedCutCells.Batch129.certificate1558,MergedCutCells.Batch129.certificate1559,MergedCutCells.Batch130.certificate1560,MergedCutCells.Batch130.certificate1561,MergedCutCells.Batch130.certificate1562], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid135,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid135,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid135,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid135,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid135,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid135,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches402 : ∀ c∈certificate402.cells, c.population=certificate402.population := by
  change ∀ c∈[MergedCutCells.Batch129.certificate1557,MergedCutCells.Batch129.certificate1558,MergedCutCells.Batch129.certificate1559,MergedCutCells.Batch130.certificate1560,MergedCutCells.Batch130.certificate1561,MergedCutCells.Batch130.certificate1562], c.population=PopulationCertificates.Batch013.certificate268
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers402 {x : ℝ} (hx : certificate402.interval.Contains x) : ∃ c∈certificate402.cells, c.region.interval.Contains x := rat_cut_group_covers certificate402 numericValid402 hx

def certificate403 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate268,PopulationCertificates.Batch013.certificate268,[MergedCutCells.Batch130.certificate1563],64,none,(1/2),(2095897226055041701/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid403 : certificate403.NumericValid := by decide +kernel
theorem cellsSound403 : ∀ c∈certificate403.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1563], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1563,List.forall_mem_nil _⟩
theorem cellsNumeric403 : ∀ c∈certificate403.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1563], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1563,List.forall_mem_nil _⟩
theorem cellsEntropyValid403 : ∀ c∈certificate403.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1563], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches403 : ∀ c∈certificate403.cells, c.population=certificate403.population := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1563], c.population=PopulationCertificates.Batch013.certificate268
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers403 {x : ℝ} (hx : certificate403.interval.Contains x) : ∃ c∈certificate403.cells, c.region.interval.Contains x := rat_cut_group_covers certificate403 numericValid403 hx

def certificate404 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate269,PopulationCertificates.Batch013.certificate269,[MergedCutCells.Batch130.certificate1564,MergedCutCells.Batch130.certificate1565,MergedCutCells.Batch130.certificate1566],(660073319808676499/200000000000000000),none,(1/2),(977689249316433181/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid404 : certificate404.NumericValid := by decide +kernel
theorem cellsSound404 : ∀ c∈certificate404.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1564,MergedCutCells.Batch130.certificate1565,MergedCutCells.Batch130.certificate1566], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1564,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1566,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric404 : ∀ c∈certificate404.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1564,MergedCutCells.Batch130.certificate1565,MergedCutCells.Batch130.certificate1566], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1564,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1566,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid404 : ∀ c∈certificate404.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1564,MergedCutCells.Batch130.certificate1565,MergedCutCells.Batch130.certificate1566], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches404 : ∀ c∈certificate404.cells, c.population=certificate404.population := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1564,MergedCutCells.Batch130.certificate1565,MergedCutCells.Batch130.certificate1566], c.population=PopulationCertificates.Batch013.certificate269
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers404 {x : ℝ} (hx : certificate404.interval.Contains x) : ∃ c∈certificate404.cells, c.region.interval.Contains x := rat_cut_group_covers certificate404 numericValid404 hx

def certificate405 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate270,PopulationCertificates.Batch013.certificate270,[MergedCutCells.Batch130.certificate1567,MergedCutCells.Batch130.certificate1568,MergedCutCells.Batch130.certificate1569,MergedCutCells.Batch130.certificate1570,MergedCutCells.Batch130.certificate1571,MergedCutCells.Batch131.certificate1572],(228312522824057483/250000000000000000),(some 64),(1/2),(941839941404423107/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1514813026935329437/1000000000000000000))⟩
theorem numericValid405 : certificate405.NumericValid := by decide +kernel
theorem cellsSound405 : ∀ c∈certificate405.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1567,MergedCutCells.Batch130.certificate1568,MergedCutCells.Batch130.certificate1569,MergedCutCells.Batch130.certificate1570,MergedCutCells.Batch130.certificate1571,MergedCutCells.Batch131.certificate1572], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1568,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1569,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.sound1571,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1572,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric405 : ∀ c∈certificate405.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1567,MergedCutCells.Batch130.certificate1568,MergedCutCells.Batch130.certificate1569,MergedCutCells.Batch130.certificate1570,MergedCutCells.Batch130.certificate1571,MergedCutCells.Batch131.certificate1572], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1568,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1569,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch130.numericValid1571,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1572,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid405 : ∀ c∈certificate405.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1567,MergedCutCells.Batch130.certificate1568,MergedCutCells.Batch130.certificate1569,MergedCutCells.Batch130.certificate1570,MergedCutCells.Batch130.certificate1571,MergedCutCells.Batch131.certificate1572], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid136,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid136,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid136,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid136,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid136,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid136,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches405 : ∀ c∈certificate405.cells, c.population=certificate405.population := by
  change ∀ c∈[MergedCutCells.Batch130.certificate1567,MergedCutCells.Batch130.certificate1568,MergedCutCells.Batch130.certificate1569,MergedCutCells.Batch130.certificate1570,MergedCutCells.Batch130.certificate1571,MergedCutCells.Batch131.certificate1572], c.population=PopulationCertificates.Batch013.certificate270
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers405 {x : ℝ} (hx : certificate405.interval.Contains x) : ∃ c∈certificate405.cells, c.region.interval.Contains x := rat_cut_group_covers certificate405 numericValid405 hx

def certificate406 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate270,PopulationCertificates.Batch013.certificate270,[MergedCutCells.Batch131.certificate1573],64,none,(1/2),(2118694806585128493/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid406 : certificate406.NumericValid := by decide +kernel
theorem cellsSound406 : ∀ c∈certificate406.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1573], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1573,List.forall_mem_nil _⟩
theorem cellsNumeric406 : ∀ c∈certificate406.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1573], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1573,List.forall_mem_nil _⟩
theorem cellsEntropyValid406 : ∀ c∈certificate406.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1573], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches406 : ∀ c∈certificate406.cells, c.population=certificate406.population := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1573], c.population=PopulationCertificates.Batch013.certificate270
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers406 {x : ℝ} (hx : certificate406.interval.Contains x) : ∃ c∈certificate406.cells, c.region.interval.Contains x := rat_cut_group_covers certificate406 numericValid406 hx

def certificate407 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate271,PopulationCertificates.Batch013.certificate271,[MergedCutCells.Batch131.certificate1574,MergedCutCells.Batch131.certificate1575,MergedCutCells.Batch131.certificate1576,MergedCutCells.Batch131.certificate1577],(328153013736445709/100000000000000000),none,(1/2),(222226081108383409/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid407 : certificate407.NumericValid := by decide +kernel
theorem cellsSound407 : ∀ c∈certificate407.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1574,MergedCutCells.Batch131.certificate1575,MergedCutCells.Batch131.certificate1576,MergedCutCells.Batch131.certificate1577], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1574,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1575,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1576,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1577,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric407 : ∀ c∈certificate407.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1574,MergedCutCells.Batch131.certificate1575,MergedCutCells.Batch131.certificate1576,MergedCutCells.Batch131.certificate1577], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1574,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1575,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1576,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1577,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid407 : ∀ c∈certificate407.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1574,MergedCutCells.Batch131.certificate1575,MergedCutCells.Batch131.certificate1576,MergedCutCells.Batch131.certificate1577], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches407 : ∀ c∈certificate407.cells, c.population=certificate407.population := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1574,MergedCutCells.Batch131.certificate1575,MergedCutCells.Batch131.certificate1576,MergedCutCells.Batch131.certificate1577], c.population=PopulationCertificates.Batch013.certificate271
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers407 {x : ℝ} (hx : certificate407.interval.Contains x) : ∃ c∈certificate407.cells, c.region.interval.Contains x := rat_cut_group_covers certificate407 numericValid407 hx

end Cycle12.MergedCutGroups.Batch033
