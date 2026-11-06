import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch050
import Cycle12.MergedCutCells.Batch411
import Cycle12.MergedCutCells.Batch412
import Cycle12.MergedCutCells.Batch413
import Cycle12.MergedCutCells.Batch414
import Cycle12.PopulationCertificates.Batch050

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch123

def certificate1476 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1003,PopulationCertificates.Batch050.certificate1003,[MergedCutCells.Batch411.certificate4940,MergedCutCells.Batch411.certificate4941,MergedCutCells.Batch411.certificate4942,MergedCutCells.Batch411.certificate4943,MergedCutCells.Batch412.certificate4944],(701056135598624679/1000000000000000000),none,(1/40),(2859652438557251/100000000000000000),none,none⟩
theorem numericValid1476 : certificate1476.NumericValid := by decide +kernel
theorem cellsSound1476 : ∀ c∈certificate1476.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4940,MergedCutCells.Batch411.certificate4941,MergedCutCells.Batch411.certificate4942,MergedCutCells.Batch411.certificate4943,MergedCutCells.Batch412.certificate4944], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4940,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4941,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4942,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4943,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4944,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1476 : ∀ c∈certificate1476.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4940,MergedCutCells.Batch411.certificate4941,MergedCutCells.Batch411.certificate4942,MergedCutCells.Batch411.certificate4943,MergedCutCells.Batch412.certificate4944], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4940,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4941,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4942,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4943,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4944,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1476 : ∀ c∈certificate1476.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4940,MergedCutCells.Batch411.certificate4941,MergedCutCells.Batch411.certificate4942,MergedCutCells.Batch411.certificate4943,MergedCutCells.Batch412.certificate4944], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid698,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid699,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid700,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid701,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid702,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1476 : ∀ c∈certificate1476.cells, c.population=certificate1476.population := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4940,MergedCutCells.Batch411.certificate4941,MergedCutCells.Batch411.certificate4942,MergedCutCells.Batch411.certificate4943,MergedCutCells.Batch412.certificate4944], c.population=PopulationCertificates.Batch050.certificate1003
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1476 {x : ℝ} (hx : certificate1476.interval.Contains x) : ∃ c∈certificate1476.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1476 numericValid1476 hx

def certificate1477 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1004,PopulationCertificates.Batch050.certificate1004,[MergedCutCells.Batch412.certificate4945,MergedCutCells.Batch412.certificate4946],(595353734000519347/1000000000000000000),(some (112916343/100000000)),(1/2),(233542114777994949/1000000000000000000),(some (1034595399426363/40000000000000000)),(some (3961438587287347/1000000000000000000))⟩
theorem numericValid1477 : certificate1477.NumericValid := by decide +kernel
theorem cellsSound1477 : ∀ c∈certificate1477.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4945,MergedCutCells.Batch412.certificate4946], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4945,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4946,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1477 : ∀ c∈certificate1477.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4945,MergedCutCells.Batch412.certificate4946], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4945,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4946,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1477 : ∀ c∈certificate1477.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4945,MergedCutCells.Batch412.certificate4946], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid703,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid703,List.forall_mem_nil _⟩⟩
theorem populationMatches1477 : ∀ c∈certificate1477.cells, c.population=certificate1477.population := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4945,MergedCutCells.Batch412.certificate4946], c.population=PopulationCertificates.Batch050.certificate1004
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1477 {x : ℝ} (hx : certificate1477.interval.Contains x) : ∃ c∈certificate1477.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1477 numericValid1477 hx

def certificate1478 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1004,PopulationCertificates.Batch050.certificate1004,[MergedCutCells.Batch412.certificate4947,MergedCutCells.Batch412.certificate4948,MergedCutCells.Batch412.certificate4949],(112916343/100000000),none,(1/2),(231918867135810011/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1478 : certificate1478.NumericValid := by decide +kernel
theorem cellsSound1478 : ∀ c∈certificate1478.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4947,MergedCutCells.Batch412.certificate4948,MergedCutCells.Batch412.certificate4949], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4947,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4948,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4949,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1478 : ∀ c∈certificate1478.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4947,MergedCutCells.Batch412.certificate4948,MergedCutCells.Batch412.certificate4949], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4947,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4948,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4949,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1478 : ∀ c∈certificate1478.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4947,MergedCutCells.Batch412.certificate4948,MergedCutCells.Batch412.certificate4949], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1478 : ∀ c∈certificate1478.cells, c.population=certificate1478.population := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4947,MergedCutCells.Batch412.certificate4948,MergedCutCells.Batch412.certificate4949], c.population=PopulationCertificates.Batch050.certificate1004
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1478 {x : ℝ} (hx : certificate1478.interval.Contains x) : ∃ c∈certificate1478.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1478 numericValid1478 hx

def certificate1479 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1005,PopulationCertificates.Batch050.certificate1005,[MergedCutCells.Batch412.certificate4950,MergedCutCells.Batch412.certificate4951],(1754149598222836653/50000000000000000),none,(1/2),(4378303969026023951/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1479 : certificate1479.NumericValid := by decide +kernel
theorem cellsSound1479 : ∀ c∈certificate1479.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4950,MergedCutCells.Batch412.certificate4951], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4950,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4951,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1479 : ∀ c∈certificate1479.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4950,MergedCutCells.Batch412.certificate4951], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4950,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4951,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1479 : ∀ c∈certificate1479.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4950,MergedCutCells.Batch412.certificate4951], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1479 : ∀ c∈certificate1479.cells, c.population=certificate1479.population := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4950,MergedCutCells.Batch412.certificate4951], c.population=PopulationCertificates.Batch050.certificate1005
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1479 {x : ℝ} (hx : certificate1479.interval.Contains x) : ∃ c∈certificate1479.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1479 numericValid1479 hx

def certificate1480 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1006,PopulationCertificates.Batch050.certificate1006,[MergedCutCells.Batch412.certificate4952,MergedCutCells.Batch412.certificate4953,MergedCutCells.Batch412.certificate4954,MergedCutCells.Batch412.certificate4955,MergedCutCells.Batch413.certificate4956],(351636506270422881/500000000000000000),none,(1/40),(15085618009520717/500000000000000000),none,none⟩
theorem numericValid1480 : certificate1480.NumericValid := by decide +kernel
theorem cellsSound1480 : ∀ c∈certificate1480.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4952,MergedCutCells.Batch412.certificate4953,MergedCutCells.Batch412.certificate4954,MergedCutCells.Batch412.certificate4955,MergedCutCells.Batch413.certificate4956], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4952,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4954,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.sound4955,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4956,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1480 : ∀ c∈certificate1480.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4952,MergedCutCells.Batch412.certificate4953,MergedCutCells.Batch412.certificate4954,MergedCutCells.Batch412.certificate4955,MergedCutCells.Batch413.certificate4956], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4952,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4954,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch412.numericValid4955,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4956,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1480 : ∀ c∈certificate1480.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4952,MergedCutCells.Batch412.certificate4953,MergedCutCells.Batch412.certificate4954,MergedCutCells.Batch412.certificate4955,MergedCutCells.Batch413.certificate4956], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid704,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid705,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid706,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid707,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid708,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1480 : ∀ c∈certificate1480.cells, c.population=certificate1480.population := by
  change ∀ c∈[MergedCutCells.Batch412.certificate4952,MergedCutCells.Batch412.certificate4953,MergedCutCells.Batch412.certificate4954,MergedCutCells.Batch412.certificate4955,MergedCutCells.Batch413.certificate4956], c.population=PopulationCertificates.Batch050.certificate1006
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1480 {x : ℝ} (hx : certificate1480.interval.Contains x) : ∃ c∈certificate1480.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1480 numericValid1480 hx

def certificate1481 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1007,PopulationCertificates.Batch050.certificate1007,[MergedCutCells.Batch413.certificate4957,MergedCutCells.Batch413.certificate4958],(298613245512299309/500000000000000000),(some (138089203/125000000)),(1/2),(237880035983997971/1000000000000000000),(some (26729587756635909/1000000000000000000)),(some (4118442030469111/1000000000000000000))⟩
theorem numericValid1481 : certificate1481.NumericValid := by decide +kernel
theorem cellsSound1481 : ∀ c∈certificate1481.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4957,MergedCutCells.Batch413.certificate4958], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4958,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1481 : ∀ c∈certificate1481.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4957,MergedCutCells.Batch413.certificate4958], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4958,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1481 : ∀ c∈certificate1481.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4957,MergedCutCells.Batch413.certificate4958], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid709,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid709,List.forall_mem_nil _⟩⟩
theorem populationMatches1481 : ∀ c∈certificate1481.cells, c.population=certificate1481.population := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4957,MergedCutCells.Batch413.certificate4958], c.population=PopulationCertificates.Batch050.certificate1007
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1481 {x : ℝ} (hx : certificate1481.interval.Contains x) : ∃ c∈certificate1481.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1481 numericValid1481 hx

def certificate1482 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1007,PopulationCertificates.Batch050.certificate1007,[MergedCutCells.Batch413.certificate4959,MergedCutCells.Batch413.certificate4960,MergedCutCells.Batch413.certificate4961],(138089203/125000000),none,(1/2),(118132112319700883/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1482 : certificate1482.NumericValid := by decide +kernel
theorem cellsSound1482 : ∀ c∈certificate1482.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4959,MergedCutCells.Batch413.certificate4960,MergedCutCells.Batch413.certificate4961], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4959,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4960,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4961,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1482 : ∀ c∈certificate1482.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4959,MergedCutCells.Batch413.certificate4960,MergedCutCells.Batch413.certificate4961], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4959,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4960,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4961,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1482 : ∀ c∈certificate1482.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4959,MergedCutCells.Batch413.certificate4960,MergedCutCells.Batch413.certificate4961], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1482 : ∀ c∈certificate1482.cells, c.population=certificate1482.population := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4959,MergedCutCells.Batch413.certificate4960,MergedCutCells.Batch413.certificate4961], c.population=PopulationCertificates.Batch050.certificate1007
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1482 {x : ℝ} (hx : certificate1482.interval.Contains x) : ∃ c∈certificate1482.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1482 numericValid1482 hx

def certificate1483 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1008,PopulationCertificates.Batch050.certificate1008,[MergedCutCells.Batch413.certificate4962,MergedCutCells.Batch413.certificate4963],(7162109324581337561/200000000000000000),none,(1/2),(8940382711372537393/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1483 : certificate1483.NumericValid := by decide +kernel
theorem cellsSound1483 : ∀ c∈certificate1483.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4962,MergedCutCells.Batch413.certificate4963], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4962,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4963,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1483 : ∀ c∈certificate1483.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4962,MergedCutCells.Batch413.certificate4963], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4962,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4963,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1483 : ∀ c∈certificate1483.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4962,MergedCutCells.Batch413.certificate4963], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1483 : ∀ c∈certificate1483.cells, c.population=certificate1483.population := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4962,MergedCutCells.Batch413.certificate4963], c.population=PopulationCertificates.Batch050.certificate1008
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1483 {x : ℝ} (hx : certificate1483.interval.Contains x) : ∃ c∈certificate1483.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1483 numericValid1483 hx

def certificate1484 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1009,PopulationCertificates.Batch050.certificate1009,[MergedCutCells.Batch413.certificate4964,MergedCutCells.Batch413.certificate4965,MergedCutCells.Batch413.certificate4966,MergedCutCells.Batch413.certificate4967,MergedCutCells.Batch414.certificate4968],(70724472473647877/100000000000000000),none,(1/40),(36081635069373803/1000000000000000000),none,none⟩
theorem numericValid1484 : certificate1484.NumericValid := by decide +kernel
theorem cellsSound1484 : ∀ c∈certificate1484.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4964,MergedCutCells.Batch413.certificate4965,MergedCutCells.Batch413.certificate4966,MergedCutCells.Batch413.certificate4967,MergedCutCells.Batch414.certificate4968], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4965,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4966,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.sound4967,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4968,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1484 : ∀ c∈certificate1484.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4964,MergedCutCells.Batch413.certificate4965,MergedCutCells.Batch413.certificate4966,MergedCutCells.Batch413.certificate4967,MergedCutCells.Batch414.certificate4968], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4965,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4966,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch413.numericValid4967,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4968,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1484 : ∀ c∈certificate1484.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4964,MergedCutCells.Batch413.certificate4965,MergedCutCells.Batch413.certificate4966,MergedCutCells.Batch413.certificate4967,MergedCutCells.Batch414.certificate4968], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid710,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid711,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid712,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid713,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid714,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1484 : ∀ c∈certificate1484.cells, c.population=certificate1484.population := by
  change ∀ c∈[MergedCutCells.Batch413.certificate4964,MergedCutCells.Batch413.certificate4965,MergedCutCells.Batch413.certificate4966,MergedCutCells.Batch413.certificate4967,MergedCutCells.Batch414.certificate4968], c.population=PopulationCertificates.Batch050.certificate1009
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1484 {x : ℝ} (hx : certificate1484.interval.Contains x) : ∃ c∈certificate1484.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1484 numericValid1484 hx

def certificate1485 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1010,PopulationCertificates.Batch050.certificate1010,[MergedCutCells.Batch414.certificate4969,MergedCutCells.Batch414.certificate4970],(599174741563189189/1000000000000000000),(some (110784253/100000000)),(1/2),(12130730642053147/50000000000000000),(some (868055928195239/31250000000000000)),(some (2155120188004941/500000000000000000))⟩
theorem numericValid1485 : certificate1485.NumericValid := by decide +kernel
theorem cellsSound1485 : ∀ c∈certificate1485.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4969,MergedCutCells.Batch414.certificate4970], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4970,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1485 : ∀ c∈certificate1485.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4969,MergedCutCells.Batch414.certificate4970], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4970,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1485 : ∀ c∈certificate1485.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4969,MergedCutCells.Batch414.certificate4970], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid715,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid715,List.forall_mem_nil _⟩⟩
theorem populationMatches1485 : ∀ c∈certificate1485.cells, c.population=certificate1485.population := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4969,MergedCutCells.Batch414.certificate4970], c.population=PopulationCertificates.Batch050.certificate1010
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1485 {x : ℝ} (hx : certificate1485.interval.Contains x) : ∃ c∈certificate1485.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1485 numericValid1485 hx

def certificate1486 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1010,PopulationCertificates.Batch050.certificate1010,[MergedCutCells.Batch414.certificate4971,MergedCutCells.Batch414.certificate4972,MergedCutCells.Batch414.certificate4973],(110784253/100000000),none,(1/2),(240730890141907699/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1486 : certificate1486.NumericValid := by decide +kernel
theorem cellsSound1486 : ∀ c∈certificate1486.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4971,MergedCutCells.Batch414.certificate4972,MergedCutCells.Batch414.certificate4973], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4972,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4973,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1486 : ∀ c∈certificate1486.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4971,MergedCutCells.Batch414.certificate4972,MergedCutCells.Batch414.certificate4973], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4972,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4973,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1486 : ∀ c∈certificate1486.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4971,MergedCutCells.Batch414.certificate4972,MergedCutCells.Batch414.certificate4973], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1486 : ∀ c∈certificate1486.cells, c.population=certificate1486.population := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4971,MergedCutCells.Batch414.certificate4972,MergedCutCells.Batch414.certificate4973], c.population=PopulationCertificates.Batch050.certificate1010
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1486 {x : ℝ} (hx : certificate1486.interval.Contains x) : ∃ c∈certificate1486.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1486 numericValid1486 hx

def certificate1487 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1011,PopulationCertificates.Batch050.certificate1011,[MergedCutCells.Batch414.certificate4974,MergedCutCells.Batch414.certificate4975],(2284929539080199469/62500000000000000),none,(1/2),(4564449869686019053/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1487 : certificate1487.NumericValid := by decide +kernel
theorem cellsSound1487 : ∀ c∈certificate1487.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4974,MergedCutCells.Batch414.certificate4975], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4974,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4975,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1487 : ∀ c∈certificate1487.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4974,MergedCutCells.Batch414.certificate4975], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4974,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4975,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1487 : ∀ c∈certificate1487.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4974,MergedCutCells.Batch414.certificate4975], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1487 : ∀ c∈certificate1487.cells, c.population=certificate1487.population := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4974,MergedCutCells.Batch414.certificate4975], c.population=PopulationCertificates.Batch050.certificate1011
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1487 {x : ℝ} (hx : certificate1487.interval.Contains x) : ∃ c∈certificate1487.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1487 numericValid1487 hx

end Cycle12.MergedCutGroups.Batch123
