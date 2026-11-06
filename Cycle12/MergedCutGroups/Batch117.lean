import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch047
import Cycle12.MergedCutCells.Batch394
import Cycle12.MergedCutCells.Batch395
import Cycle12.MergedCutCells.Batch396
import Cycle12.MergedCutCells.Batch397
import Cycle12.PopulationCertificates.Batch047

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch117

def certificate1404 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate949,PopulationCertificates.Batch047.certificate949,[MergedCutCells.Batch394.certificate4736,MergedCutCells.Batch394.certificate4737,MergedCutCells.Batch394.certificate4738,MergedCutCells.Batch394.certificate4739],(137612923561918003/200000000000000000),none,(1/40),(3453885352684759/100000000000000000),none,none⟩
theorem numericValid1404 : certificate1404.NumericValid := by decide +kernel
theorem cellsSound1404 : ∀ c∈certificate1404.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4736,MergedCutCells.Batch394.certificate4737,MergedCutCells.Batch394.certificate4738,MergedCutCells.Batch394.certificate4739], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4736,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4737,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4739,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1404 : ∀ c∈certificate1404.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4736,MergedCutCells.Batch394.certificate4737,MergedCutCells.Batch394.certificate4738,MergedCutCells.Batch394.certificate4739], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4736,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4737,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4739,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1404 : ∀ c∈certificate1404.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4736,MergedCutCells.Batch394.certificate4737,MergedCutCells.Batch394.certificate4738,MergedCutCells.Batch394.certificate4739], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid603,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid604,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid605,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid606,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1404 : ∀ c∈certificate1404.cells, c.population=certificate1404.population := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4736,MergedCutCells.Batch394.certificate4737,MergedCutCells.Batch394.certificate4738,MergedCutCells.Batch394.certificate4739], c.population=PopulationCertificates.Batch047.certificate949
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1404 {x : ℝ} (hx : certificate1404.interval.Contains x) : ∃ c∈certificate1404.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1404 numericValid1404 hx

def certificate1405 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate950,PopulationCertificates.Batch047.certificate950,[MergedCutCells.Batch395.certificate4740,MergedCutCells.Batch395.certificate4741],(17983856492281853/31250000000000000),(some (287032823/250000000)),(1/2),(18467521716192921/100000000000000000),(some (8785245162596903/500000000000000000)),(some (2515863671423739/1000000000000000000))⟩
theorem numericValid1405 : certificate1405.NumericValid := by decide +kernel
theorem cellsSound1405 : ∀ c∈certificate1405.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4740,MergedCutCells.Batch395.certificate4741], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4740,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4741,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1405 : ∀ c∈certificate1405.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4740,MergedCutCells.Batch395.certificate4741], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4740,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4741,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1405 : ∀ c∈certificate1405.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4740,MergedCutCells.Batch395.certificate4741], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid607,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid607,List.forall_mem_nil _⟩⟩
theorem populationMatches1405 : ∀ c∈certificate1405.cells, c.population=certificate1405.population := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4740,MergedCutCells.Batch395.certificate4741], c.population=PopulationCertificates.Batch047.certificate950
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1405 {x : ℝ} (hx : certificate1405.interval.Contains x) : ∃ c∈certificate1405.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1405 numericValid1405 hx

def certificate1406 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate950,PopulationCertificates.Batch047.certificate950,[MergedCutCells.Batch395.certificate4742,MergedCutCells.Batch395.certificate4743,MergedCutCells.Batch395.certificate4744],(287032823/250000000),none,(1/2),(22959287081196111/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1406 : certificate1406.NumericValid := by decide +kernel
theorem cellsSound1406 : ∀ c∈certificate1406.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4742,MergedCutCells.Batch395.certificate4743,MergedCutCells.Batch395.certificate4744], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4743,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4744,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1406 : ∀ c∈certificate1406.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4742,MergedCutCells.Batch395.certificate4743,MergedCutCells.Batch395.certificate4744], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4743,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4744,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1406 : ∀ c∈certificate1406.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4742,MergedCutCells.Batch395.certificate4743,MergedCutCells.Batch395.certificate4744], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1406 : ∀ c∈certificate1406.cells, c.population=certificate1406.population := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4742,MergedCutCells.Batch395.certificate4743,MergedCutCells.Batch395.certificate4744], c.population=PopulationCertificates.Batch047.certificate950
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1406 {x : ℝ} (hx : certificate1406.interval.Contains x) : ∃ c∈certificate1406.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1406 numericValid1406 hx

def certificate1407 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate951,PopulationCertificates.Batch047.certificate951,[MergedCutCells.Batch395.certificate4745,MergedCutCells.Batch395.certificate4746],(7486341369963121837/250000000000000000),none,(1/2),(1481768374927393369/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1407 : certificate1407.NumericValid := by decide +kernel
theorem cellsSound1407 : ∀ c∈certificate1407.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4745,MergedCutCells.Batch395.certificate4746], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4745,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4746,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1407 : ∀ c∈certificate1407.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4745,MergedCutCells.Batch395.certificate4746], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4745,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4746,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1407 : ∀ c∈certificate1407.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4745,MergedCutCells.Batch395.certificate4746], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1407 : ∀ c∈certificate1407.cells, c.population=certificate1407.population := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4745,MergedCutCells.Batch395.certificate4746], c.population=PopulationCertificates.Batch047.certificate951
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1407 {x : ℝ} (hx : certificate1407.interval.Contains x) : ∃ c∈certificate1407.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1407 numericValid1407 hx

def certificate1408 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate952,PopulationCertificates.Batch047.certificate952,[MergedCutCells.Batch395.certificate4747,MergedCutCells.Batch395.certificate4748,MergedCutCells.Batch395.certificate4749,MergedCutCells.Batch395.certificate4750],(3444754508381273/5000000000000000),none,(1/40),(18026045265504263/500000000000000000),none,none⟩
theorem numericValid1408 : certificate1408.NumericValid := by decide +kernel
theorem cellsSound1408 : ∀ c∈certificate1408.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4747,MergedCutCells.Batch395.certificate4748,MergedCutCells.Batch395.certificate4749,MergedCutCells.Batch395.certificate4750], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4747,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4748,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4750,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1408 : ∀ c∈certificate1408.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4747,MergedCutCells.Batch395.certificate4748,MergedCutCells.Batch395.certificate4749,MergedCutCells.Batch395.certificate4750], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4747,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4748,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4750,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1408 : ∀ c∈certificate1408.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4747,MergedCutCells.Batch395.certificate4748,MergedCutCells.Batch395.certificate4749,MergedCutCells.Batch395.certificate4750], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid608,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid609,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid610,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid611,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1408 : ∀ c∈certificate1408.cells, c.population=certificate1408.population := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4747,MergedCutCells.Batch395.certificate4748,MergedCutCells.Batch395.certificate4749,MergedCutCells.Batch395.certificate4750], c.population=PopulationCertificates.Batch047.certificate952
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1408 {x : ℝ} (hx : certificate1408.interval.Contains x) : ∃ c∈certificate1408.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1408 numericValid1408 hx

def certificate1409 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate953,PopulationCertificates.Batch047.certificate953,[MergedCutCells.Batch395.certificate4751,MergedCutCells.Batch396.certificate4752],(287863169261897333/500000000000000000),(some (574272447/500000000)),(1/2),(18511014724557883/100000000000000000),(some (17676688862697917/1000000000000000000)),(some (633406332106677/250000000000000000))⟩
theorem numericValid1409 : certificate1409.NumericValid := by decide +kernel
theorem cellsSound1409 : ∀ c∈certificate1409.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4751,MergedCutCells.Batch396.certificate4752], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.sound4751,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4752,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1409 : ∀ c∈certificate1409.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4751,MergedCutCells.Batch396.certificate4752], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch395.numericValid4751,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4752,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1409 : ∀ c∈certificate1409.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4751,MergedCutCells.Batch396.certificate4752], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid612,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid612,List.forall_mem_nil _⟩⟩
theorem populationMatches1409 : ∀ c∈certificate1409.cells, c.population=certificate1409.population := by
  change ∀ c∈[MergedCutCells.Batch395.certificate4751,MergedCutCells.Batch396.certificate4752], c.population=PopulationCertificates.Batch047.certificate953
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1409 {x : ℝ} (hx : certificate1409.interval.Contains x) : ∃ c∈certificate1409.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1409 numericValid1409 hx

def certificate1410 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate953,PopulationCertificates.Batch047.certificate953,[MergedCutCells.Batch396.certificate4753,MergedCutCells.Batch396.certificate4754,MergedCutCells.Batch396.certificate4755],(574272447/500000000),none,(1/2),(184087629145706283/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1410 : certificate1410.NumericValid := by decide +kernel
theorem cellsSound1410 : ∀ c∈certificate1410.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4753,MergedCutCells.Batch396.certificate4754,MergedCutCells.Batch396.certificate4755], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4753,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4755,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1410 : ∀ c∈certificate1410.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4753,MergedCutCells.Batch396.certificate4754,MergedCutCells.Batch396.certificate4755], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4753,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4755,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1410 : ∀ c∈certificate1410.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4753,MergedCutCells.Batch396.certificate4754,MergedCutCells.Batch396.certificate4755], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1410 : ∀ c∈certificate1410.cells, c.population=certificate1410.population := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4753,MergedCutCells.Batch396.certificate4754,MergedCutCells.Batch396.certificate4755], c.population=PopulationCertificates.Batch047.certificate953
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1410 {x : ℝ} (hx : certificate1410.interval.Contains x) : ∃ c∈certificate1410.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1410 numericValid1410 hx

def certificate1411 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate954,PopulationCertificates.Batch047.certificate954,[MergedCutCells.Batch396.certificate4756,MergedCutCells.Batch396.certificate4757],(30017682955219351027/1000000000000000000),none,(1/2),(7427453896918522411/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1411 : certificate1411.NumericValid := by decide +kernel
theorem cellsSound1411 : ∀ c∈certificate1411.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4756,MergedCutCells.Batch396.certificate4757], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4757,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1411 : ∀ c∈certificate1411.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4756,MergedCutCells.Batch396.certificate4757], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4757,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1411 : ∀ c∈certificate1411.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4756,MergedCutCells.Batch396.certificate4757], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1411 : ∀ c∈certificate1411.cells, c.population=certificate1411.population := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4756,MergedCutCells.Batch396.certificate4757], c.population=PopulationCertificates.Batch047.certificate954
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1411 {x : ℝ} (hx : certificate1411.interval.Contains x) : ∃ c∈certificate1411.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1411 numericValid1411 hx

def certificate1412 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate955,PopulationCertificates.Batch047.certificate955,[MergedCutCells.Batch396.certificate4758,MergedCutCells.Batch396.certificate4759,MergedCutCells.Batch396.certificate4760,MergedCutCells.Batch396.certificate4761],(172357114847360877/250000000000000000),none,(1/40),(18345276199123871/500000000000000000),none,none⟩
theorem numericValid1412 : certificate1412.NumericValid := by decide +kernel
theorem cellsSound1412 : ∀ c∈certificate1412.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4758,MergedCutCells.Batch396.certificate4759,MergedCutCells.Batch396.certificate4760,MergedCutCells.Batch396.certificate4761], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4759,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4760,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4761,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1412 : ∀ c∈certificate1412.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4758,MergedCutCells.Batch396.certificate4759,MergedCutCells.Batch396.certificate4760,MergedCutCells.Batch396.certificate4761], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4759,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4760,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4761,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1412 : ∀ c∈certificate1412.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4758,MergedCutCells.Batch396.certificate4759,MergedCutCells.Batch396.certificate4760,MergedCutCells.Batch396.certificate4761], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid613,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid614,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid615,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid616,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1412 : ∀ c∈certificate1412.cells, c.population=certificate1412.population := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4758,MergedCutCells.Batch396.certificate4759,MergedCutCells.Batch396.certificate4760,MergedCutCells.Batch396.certificate4761], c.population=PopulationCertificates.Batch047.certificate955
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1412 {x : ℝ} (hx : certificate1412.interval.Contains x) : ∃ c∈certificate1412.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1412 numericValid1412 hx

def certificate1413 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate956,PopulationCertificates.Batch047.certificate956,[MergedCutCells.Batch396.certificate4762,MergedCutCells.Batch396.certificate4763],(36245774847118113/62500000000000000),(some (1155701869/1000000000)),(1/2),(20375708516068161/100000000000000000),(some (4529304652431569/250000000000000000)),(some (2607526250711463/1000000000000000000))⟩
theorem numericValid1413 : certificate1413.NumericValid := by decide +kernel
theorem cellsSound1413 : ∀ c∈certificate1413.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4762,MergedCutCells.Batch396.certificate4763], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4762,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.sound4763,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1413 : ∀ c∈certificate1413.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4762,MergedCutCells.Batch396.certificate4763], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4762,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch396.numericValid4763,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1413 : ∀ c∈certificate1413.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4762,MergedCutCells.Batch396.certificate4763], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid617,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid617,List.forall_mem_nil _⟩⟩
theorem populationMatches1413 : ∀ c∈certificate1413.cells, c.population=certificate1413.population := by
  change ∀ c∈[MergedCutCells.Batch396.certificate4762,MergedCutCells.Batch396.certificate4763], c.population=PopulationCertificates.Batch047.certificate956
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1413 {x : ℝ} (hx : certificate1413.interval.Contains x) : ∃ c∈certificate1413.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1413 numericValid1413 hx

def certificate1414 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate956,PopulationCertificates.Batch047.certificate956,[MergedCutCells.Batch397.certificate4764,MergedCutCells.Batch397.certificate4765,MergedCutCells.Batch397.certificate4766],(1155701869/1000000000),none,(1/2),(202839919745563261/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1414 : certificate1414.NumericValid := by decide +kernel
theorem cellsSound1414 : ∀ c∈certificate1414.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4764,MergedCutCells.Batch397.certificate4765,MergedCutCells.Batch397.certificate4766], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4764,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4765,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4766,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1414 : ∀ c∈certificate1414.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4764,MergedCutCells.Batch397.certificate4765,MergedCutCells.Batch397.certificate4766], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4764,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4765,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4766,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1414 : ∀ c∈certificate1414.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4764,MergedCutCells.Batch397.certificate4765,MergedCutCells.Batch397.certificate4766], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1414 : ∀ c∈certificate1414.cells, c.population=certificate1414.population := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4764,MergedCutCells.Batch397.certificate4765,MergedCutCells.Batch397.certificate4766], c.population=PopulationCertificates.Batch047.certificate956
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1414 {x : ℝ} (hx : certificate1414.interval.Contains x) : ∃ c∈certificate1414.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1414 numericValid1414 hx

def certificate1415 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate957,PopulationCertificates.Batch047.certificate957,[MergedCutCells.Batch397.certificate4767,MergedCutCells.Batch397.certificate4768],(5984956242818387253/200000000000000000),none,(1/2),(372143241813271461/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1415 : certificate1415.NumericValid := by decide +kernel
theorem cellsSound1415 : ∀ c∈certificate1415.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4767,MergedCutCells.Batch397.certificate4768], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4767,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4768,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1415 : ∀ c∈certificate1415.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4767,MergedCutCells.Batch397.certificate4768], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4767,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4768,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1415 : ∀ c∈certificate1415.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4767,MergedCutCells.Batch397.certificate4768], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1415 : ∀ c∈certificate1415.cells, c.population=certificate1415.population := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4767,MergedCutCells.Batch397.certificate4768], c.population=PopulationCertificates.Batch047.certificate957
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1415 {x : ℝ} (hx : certificate1415.interval.Contains x) : ∃ c∈certificate1415.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1415 numericValid1415 hx

end Cycle12.MergedCutGroups.Batch117
