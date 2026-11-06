import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch051
import Cycle12.GeometryCertificates.Batch052
import Cycle12.MergedCutCells.Batch423
import Cycle12.MergedCutCells.Batch424
import Cycle12.MergedCutCells.Batch425
import Cycle12.MergedCutCells.Batch426
import Cycle12.PopulationCertificates.Batch051
import Cycle12.PopulationCertificates.Batch052

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch127

def certificate1524 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1039,PopulationCertificates.Batch051.certificate1039,[MergedCutCells.Batch423.certificate5086,MergedCutCells.Batch423.certificate5087,MergedCutCells.Batch424.certificate5088,MergedCutCells.Batch424.certificate5089,MergedCutCells.Batch424.certificate5090],(747710074582007579/1000000000000000000),none,(1/40),(118650617352815819/1000000000000000000),none,none⟩
theorem numericValid1524 : certificate1524.NumericValid := by decide +kernel
theorem cellsSound1524 : ∀ c∈certificate1524.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5086,MergedCutCells.Batch423.certificate5087,MergedCutCells.Batch424.certificate5088,MergedCutCells.Batch424.certificate5089,MergedCutCells.Batch424.certificate5090], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5087,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5088,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5089,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5090,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1524 : ∀ c∈certificate1524.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5086,MergedCutCells.Batch423.certificate5087,MergedCutCells.Batch424.certificate5088,MergedCutCells.Batch424.certificate5089,MergedCutCells.Batch424.certificate5090], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5087,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5088,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5089,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5090,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1524 : ∀ c∈certificate1524.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5086,MergedCutCells.Batch423.certificate5087,MergedCutCells.Batch424.certificate5088,MergedCutCells.Batch424.certificate5089,MergedCutCells.Batch424.certificate5090], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid770,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid771,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid772,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid773,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid774,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1524 : ∀ c∈certificate1524.cells, c.population=certificate1524.population := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5086,MergedCutCells.Batch423.certificate5087,MergedCutCells.Batch424.certificate5088,MergedCutCells.Batch424.certificate5089,MergedCutCells.Batch424.certificate5090], c.population=PopulationCertificates.Batch051.certificate1039
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1524 {x : ℝ} (hx : certificate1524.interval.Contains x) : ∃ c∈certificate1524.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1524 numericValid1524 hx

def certificate1525 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1040,PopulationCertificates.Batch052.certificate1040,[MergedCutCells.Batch424.certificate5091,MergedCutCells.Batch424.certificate5092],(77317890830969837/125000000000000000),(some (1064499893/1000000000)),(1/2),(74177342382414503/250000000000000000),(some (38760512709024553/1000000000000000000)),(some (1282050258673597/200000000000000000))⟩
theorem numericValid1525 : certificate1525.NumericValid := by decide +kernel
theorem cellsSound1525 : ∀ c∈certificate1525.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5091,MergedCutCells.Batch424.certificate5092], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5091,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5092,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1525 : ∀ c∈certificate1525.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5091,MergedCutCells.Batch424.certificate5092], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5091,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5092,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1525 : ∀ c∈certificate1525.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5091,MergedCutCells.Batch424.certificate5092], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid775,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid775,List.forall_mem_nil _⟩⟩
theorem populationMatches1525 : ∀ c∈certificate1525.cells, c.population=certificate1525.population := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5091,MergedCutCells.Batch424.certificate5092], c.population=PopulationCertificates.Batch052.certificate1040
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1525 {x : ℝ} (hx : certificate1525.interval.Contains x) : ∃ c∈certificate1525.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1525 numericValid1525 hx

def certificate1526 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1040,PopulationCertificates.Batch052.certificate1040,[MergedCutCells.Batch424.certificate5093,MergedCutCells.Batch424.certificate5094,MergedCutCells.Batch424.certificate5095],(1064499893/1000000000),none,(1/2),(36719292165682271/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1526 : certificate1526.NumericValid := by decide +kernel
theorem cellsSound1526 : ∀ c∈certificate1526.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5093,MergedCutCells.Batch424.certificate5094,MergedCutCells.Batch424.certificate5095], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5093,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5095,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1526 : ∀ c∈certificate1526.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5093,MergedCutCells.Batch424.certificate5094,MergedCutCells.Batch424.certificate5095], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5093,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5095,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1526 : ∀ c∈certificate1526.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5093,MergedCutCells.Batch424.certificate5094,MergedCutCells.Batch424.certificate5095], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1526 : ∀ c∈certificate1526.cells, c.population=certificate1526.population := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5093,MergedCutCells.Batch424.certificate5094,MergedCutCells.Batch424.certificate5095], c.population=PopulationCertificates.Batch052.certificate1040
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1526 {x : ℝ} (hx : certificate1526.interval.Contains x) : ∃ c∈certificate1526.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1526 numericValid1526 hx

def certificate1527 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1041,PopulationCertificates.Batch052.certificate1041,[MergedCutCells.Batch424.certificate5096,MergedCutCells.Batch424.certificate5097],(22691123924733440863/500000000000000000),none,(1/2),(5657849450980220299/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1527 : certificate1527.NumericValid := by decide +kernel
theorem cellsSound1527 : ∀ c∈certificate1527.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5096,MergedCutCells.Batch424.certificate5097], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5096,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5097,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1527 : ∀ c∈certificate1527.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5096,MergedCutCells.Batch424.certificate5097], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5096,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5097,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1527 : ∀ c∈certificate1527.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5096,MergedCutCells.Batch424.certificate5097], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1527 : ∀ c∈certificate1527.cells, c.population=certificate1527.population := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5096,MergedCutCells.Batch424.certificate5097], c.population=PopulationCertificates.Batch052.certificate1041
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1527 {x : ℝ} (hx : certificate1527.interval.Contains x) : ∃ c∈certificate1527.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1527 numericValid1527 hx

def certificate1528 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1042,PopulationCertificates.Batch052.certificate1042,[MergedCutCells.Batch424.certificate5098,MergedCutCells.Batch424.certificate5099,MergedCutCells.Batch425.certificate5100,MergedCutCells.Batch425.certificate5101,MergedCutCells.Batch425.certificate5102],(75185136433055229/100000000000000000),none,(1/40),(129585819401738039/1000000000000000000),none,none⟩
theorem numericValid1528 : certificate1528.NumericValid := by decide +kernel
theorem cellsSound1528 : ∀ c∈certificate1528.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5098,MergedCutCells.Batch424.certificate5099,MergedCutCells.Batch425.certificate5100,MergedCutCells.Batch425.certificate5101,MergedCutCells.Batch425.certificate5102], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5098,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.sound5099,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5101,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5102,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1528 : ∀ c∈certificate1528.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5098,MergedCutCells.Batch424.certificate5099,MergedCutCells.Batch425.certificate5100,MergedCutCells.Batch425.certificate5101,MergedCutCells.Batch425.certificate5102], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5098,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch424.numericValid5099,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5101,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5102,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1528 : ∀ c∈certificate1528.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5098,MergedCutCells.Batch424.certificate5099,MergedCutCells.Batch425.certificate5100,MergedCutCells.Batch425.certificate5101,MergedCutCells.Batch425.certificate5102], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid776,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid777,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid778,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid779,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid780,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1528 : ∀ c∈certificate1528.cells, c.population=certificate1528.population := by
  change ∀ c∈[MergedCutCells.Batch424.certificate5098,MergedCutCells.Batch424.certificate5099,MergedCutCells.Batch425.certificate5100,MergedCutCells.Batch425.certificate5101,MergedCutCells.Batch425.certificate5102], c.population=PopulationCertificates.Batch052.certificate1042
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1528 {x : ℝ} (hx : certificate1528.interval.Contains x) : ∃ c∈certificate1528.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1528 numericValid1528 hx

def certificate1529 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1043,PopulationCertificates.Batch052.certificate1043,[MergedCutCells.Batch425.certificate5103,MergedCutCells.Batch425.certificate5104],(5047318325061113/8000000000000000),(some (528492169/500000000)),(1/2),(4729324183055673/12500000000000000),(some (77687643362999/1953125000000000)),(some (6612243111770193/1000000000000000000))⟩
theorem numericValid1529 : certificate1529.NumericValid := by decide +kernel
theorem cellsSound1529 : ∀ c∈certificate1529.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5103,MergedCutCells.Batch425.certificate5104], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5103,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5104,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1529 : ∀ c∈certificate1529.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5103,MergedCutCells.Batch425.certificate5104], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5103,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5104,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1529 : ∀ c∈certificate1529.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5103,MergedCutCells.Batch425.certificate5104], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid781,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid781,List.forall_mem_nil _⟩⟩
theorem populationMatches1529 : ∀ c∈certificate1529.cells, c.population=certificate1529.population := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5103,MergedCutCells.Batch425.certificate5104], c.population=PopulationCertificates.Batch052.certificate1043
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1529 {x : ℝ} (hx : certificate1529.interval.Contains x) : ∃ c∈certificate1529.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1529 numericValid1529 hx

def certificate1530 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1043,PopulationCertificates.Batch052.certificate1043,[MergedCutCells.Batch425.certificate5105,MergedCutCells.Batch425.certificate5106,MergedCutCells.Batch425.certificate5107,MergedCutCells.Batch425.certificate5108],(528492169/500000000),none,(1/2),(375303530067346769/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1530 : certificate1530.NumericValid := by decide +kernel
theorem cellsSound1530 : ∀ c∈certificate1530.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5105,MergedCutCells.Batch425.certificate5106,MergedCutCells.Batch425.certificate5107,MergedCutCells.Batch425.certificate5108], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5105,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5107,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5108,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1530 : ∀ c∈certificate1530.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5105,MergedCutCells.Batch425.certificate5106,MergedCutCells.Batch425.certificate5107,MergedCutCells.Batch425.certificate5108], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5105,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5107,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5108,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1530 : ∀ c∈certificate1530.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5105,MergedCutCells.Batch425.certificate5106,MergedCutCells.Batch425.certificate5107,MergedCutCells.Batch425.certificate5108], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1530 : ∀ c∈certificate1530.cells, c.population=certificate1530.population := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5105,MergedCutCells.Batch425.certificate5106,MergedCutCells.Batch425.certificate5107,MergedCutCells.Batch425.certificate5108], c.population=PopulationCertificates.Batch052.certificate1043
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1530 {x : ℝ} (hx : certificate1530.interval.Contains x) : ∃ c∈certificate1530.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1530 numericValid1530 hx

def certificate1531 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1044,PopulationCertificates.Batch052.certificate1044,[MergedCutCells.Batch425.certificate5109,MergedCutCells.Batch425.certificate5110],(285782926977396341/6250000000000000),none,(1/2),(11566547804335755069/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1531 : certificate1531.NumericValid := by decide +kernel
theorem cellsSound1531 : ∀ c∈certificate1531.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5109,MergedCutCells.Batch425.certificate5110], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5109,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5110,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1531 : ∀ c∈certificate1531.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5109,MergedCutCells.Batch425.certificate5110], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5109,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5110,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1531 : ∀ c∈certificate1531.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5109,MergedCutCells.Batch425.certificate5110], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1531 : ∀ c∈certificate1531.cells, c.population=certificate1531.population := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5109,MergedCutCells.Batch425.certificate5110], c.population=PopulationCertificates.Batch052.certificate1044
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1531 {x : ℝ} (hx : certificate1531.interval.Contains x) : ∃ c∈certificate1531.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1531 numericValid1531 hx

def certificate1532 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1045,PopulationCertificates.Batch052.certificate1045,[MergedCutCells.Batch425.certificate5111,MergedCutCells.Batch426.certificate5112,MergedCutCells.Batch426.certificate5113,MergedCutCells.Batch426.certificate5114,MergedCutCells.Batch426.certificate5115],(756031104195932181/1000000000000000000),none,(1/40),(141072873945988189/1000000000000000000),none,none⟩
theorem numericValid1532 : certificate1532.NumericValid := by decide +kernel
theorem cellsSound1532 : ∀ c∈certificate1532.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5111,MergedCutCells.Batch426.certificate5112,MergedCutCells.Batch426.certificate5113,MergedCutCells.Batch426.certificate5114,MergedCutCells.Batch426.certificate5115], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.sound5111,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5114,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5115,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1532 : ∀ c∈certificate1532.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5111,MergedCutCells.Batch426.certificate5112,MergedCutCells.Batch426.certificate5113,MergedCutCells.Batch426.certificate5114,MergedCutCells.Batch426.certificate5115], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch425.numericValid5111,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5114,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5115,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1532 : ∀ c∈certificate1532.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5111,MergedCutCells.Batch426.certificate5112,MergedCutCells.Batch426.certificate5113,MergedCutCells.Batch426.certificate5114,MergedCutCells.Batch426.certificate5115], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid782,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid783,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid784,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid785,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid786,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1532 : ∀ c∈certificate1532.cells, c.population=certificate1532.population := by
  change ∀ c∈[MergedCutCells.Batch425.certificate5111,MergedCutCells.Batch426.certificate5112,MergedCutCells.Batch426.certificate5113,MergedCutCells.Batch426.certificate5114,MergedCutCells.Batch426.certificate5115], c.population=PopulationCertificates.Batch052.certificate1045
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1532 {x : ℝ} (hx : certificate1532.interval.Contains x) : ∃ c∈certificate1532.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1532 numericValid1532 hx

def certificate1533 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1046,PopulationCertificates.Batch052.certificate1046,[MergedCutCells.Batch426.certificate5116,MergedCutCells.Batch426.certificate5117],(595264764199185457/1000000000000000000),(some (104863643/100000000)),(1/2),(27785155837186659/200000000000000000),(some (41479474397447223/1000000000000000000)),(some (3476918385075233/500000000000000000))⟩
theorem numericValid1533 : certificate1533.NumericValid := by decide +kernel
theorem cellsSound1533 : ∀ c∈certificate1533.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5116,MergedCutCells.Batch426.certificate5117], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5116,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5117,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1533 : ∀ c∈certificate1533.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5116,MergedCutCells.Batch426.certificate5117], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5116,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5117,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1533 : ∀ c∈certificate1533.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5116,MergedCutCells.Batch426.certificate5117], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid787,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid787,List.forall_mem_nil _⟩⟩
theorem populationMatches1533 : ∀ c∈certificate1533.cells, c.population=certificate1533.population := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5116,MergedCutCells.Batch426.certificate5117], c.population=PopulationCertificates.Batch052.certificate1046
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1533 {x : ℝ} (hx : certificate1533.interval.Contains x) : ∃ c∈certificate1533.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1533 numericValid1533 hx

def certificate1534 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1046,PopulationCertificates.Batch052.certificate1046,[MergedCutCells.Batch426.certificate5118,MergedCutCells.Batch426.certificate5119,MergedCutCells.Batch426.certificate5120],(104863643/100000000),none,(1/2),(135633545349597239/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1534 : certificate1534.NumericValid := by decide +kernel
theorem cellsSound1534 : ∀ c∈certificate1534.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5118,MergedCutCells.Batch426.certificate5119,MergedCutCells.Batch426.certificate5120], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5119,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5120,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1534 : ∀ c∈certificate1534.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5118,MergedCutCells.Batch426.certificate5119,MergedCutCells.Batch426.certificate5120], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5119,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5120,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1534 : ∀ c∈certificate1534.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5118,MergedCutCells.Batch426.certificate5119,MergedCutCells.Batch426.certificate5120], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1534 : ∀ c∈certificate1534.cells, c.population=certificate1534.population := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5118,MergedCutCells.Batch426.certificate5119,MergedCutCells.Batch426.certificate5120], c.population=PopulationCertificates.Batch052.certificate1046
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1534 {x : ℝ} (hx : certificate1534.interval.Contains x) : ∃ c∈certificate1534.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1534 numericValid1534 hx

def certificate1535 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1047,PopulationCertificates.Batch052.certificate1047,[MergedCutCells.Batch426.certificate5121,MergedCutCells.Batch426.certificate5122],(3071824663619598033/62500000000000000),none,(1/2),(5917541060862768043/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1535 : certificate1535.NumericValid := by decide +kernel
theorem cellsSound1535 : ∀ c∈certificate1535.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5121,MergedCutCells.Batch426.certificate5122], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5122,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1535 : ∀ c∈certificate1535.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5121,MergedCutCells.Batch426.certificate5122], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5122,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1535 : ∀ c∈certificate1535.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5121,MergedCutCells.Batch426.certificate5122], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1535 : ∀ c∈certificate1535.cells, c.population=certificate1535.population := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5121,MergedCutCells.Batch426.certificate5122], c.population=PopulationCertificates.Batch052.certificate1047
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1535 {x : ℝ} (hx : certificate1535.interval.Contains x) : ∃ c∈certificate1535.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1535 numericValid1535 hx

end Cycle12.MergedCutGroups.Batch127
