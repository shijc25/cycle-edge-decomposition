import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch053
import Cycle12.MergedCutCells.Batch433
import Cycle12.PopulationCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch130

def certificate1560 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1066,PopulationCertificates.Batch053.certificate1066,[MergedCutCells.Batch433.certificate5197,MergedCutCells.Batch433.certificate5198,MergedCutCells.Batch433.certificate5199,MergedCutCells.Batch433.certificate5200,MergedCutCells.Batch433.certificate5201],(98235667736918311/125000000000000000),none,(1/40),(240181685145640357/1000000000000000000),none,none⟩
theorem numericValid1560 : certificate1560.NumericValid := by decide +kernel
theorem cellsSound1560 : ∀ c∈certificate1560.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch433.certificate5197,MergedCutCells.Batch433.certificate5198,MergedCutCells.Batch433.certificate5199,MergedCutCells.Batch433.certificate5200,MergedCutCells.Batch433.certificate5201], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.sound5197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.sound5198,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.sound5199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.sound5200,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.sound5201,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1560 : ∀ c∈certificate1560.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch433.certificate5197,MergedCutCells.Batch433.certificate5198,MergedCutCells.Batch433.certificate5199,MergedCutCells.Batch433.certificate5200,MergedCutCells.Batch433.certificate5201], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.numericValid5197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.numericValid5198,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.numericValid5199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.numericValid5200,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.numericValid5201,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1560 : ∀ c∈certificate1560.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch433.certificate5197,MergedCutCells.Batch433.certificate5198,MergedCutCells.Batch433.certificate5199,MergedCutCells.Batch433.certificate5200,MergedCutCells.Batch433.certificate5201], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid824,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid825,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid826,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid827,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid828,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1560 : ∀ c∈certificate1560.cells, c.population=certificate1560.population := by
  change ∀ c∈[MergedCutCells.Batch433.certificate5197,MergedCutCells.Batch433.certificate5198,MergedCutCells.Batch433.certificate5199,MergedCutCells.Batch433.certificate5200,MergedCutCells.Batch433.certificate5201], c.population=PopulationCertificates.Batch053.certificate1066
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1560 {x : ℝ} (hx : certificate1560.interval.Contains x) : ∃ c∈certificate1560.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1560 numericValid1560 hx

end Cycle12.MergedCutGroups.Batch130
