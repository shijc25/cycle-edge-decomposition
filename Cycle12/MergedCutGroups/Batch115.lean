import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch046
import Cycle12.MergedCutCells.Batch389
import Cycle12.MergedCutCells.Batch390
import Cycle12.MergedCutCells.Batch391
import Cycle12.PopulationCertificates.Batch046

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch115

def certificate1380 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate931,PopulationCertificates.Batch046.certificate931,[MergedCutCells.Batch389.certificate4670,MergedCutCells.Batch389.certificate4671,MergedCutCells.Batch389.certificate4672,MergedCutCells.Batch389.certificate4673],(685880465143763741/1000000000000000000),none,(1/40),(1307747184185893/31250000000000000),none,none⟩
theorem numericValid1380 : certificate1380.NumericValid := by decide +kernel
theorem cellsSound1380 : ∀ c∈certificate1380.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4670,MergedCutCells.Batch389.certificate4671,MergedCutCells.Batch389.certificate4672,MergedCutCells.Batch389.certificate4673], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4671,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4672,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4673,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1380 : ∀ c∈certificate1380.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4670,MergedCutCells.Batch389.certificate4671,MergedCutCells.Batch389.certificate4672,MergedCutCells.Batch389.certificate4673], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4671,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4672,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4673,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1380 : ∀ c∈certificate1380.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4670,MergedCutCells.Batch389.certificate4671,MergedCutCells.Batch389.certificate4672,MergedCutCells.Batch389.certificate4673], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid573,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid574,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid575,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid576,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1380 : ∀ c∈certificate1380.cells, c.population=certificate1380.population := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4670,MergedCutCells.Batch389.certificate4671,MergedCutCells.Batch389.certificate4672,MergedCutCells.Batch389.certificate4673], c.population=PopulationCertificates.Batch046.certificate931
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1380 {x : ℝ} (hx : certificate1380.interval.Contains x) : ∃ c∈certificate1380.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1380 numericValid1380 hx

def certificate1381 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate932,PopulationCertificates.Batch046.certificate932,[MergedCutCells.Batch389.certificate4674,MergedCutCells.Batch389.certificate4675],(287148627574786199/500000000000000000),(some (1174747019/1000000000)),(1/2),(192222444476546421/1000000000000000000),(some (16134747941105311/1000000000000000000)),(some (2277827458667151/1000000000000000000))⟩
theorem numericValid1381 : certificate1381.NumericValid := by decide +kernel
theorem cellsSound1381 : ∀ c∈certificate1381.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4674,MergedCutCells.Batch389.certificate4675], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4675,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1381 : ∀ c∈certificate1381.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4674,MergedCutCells.Batch389.certificate4675], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4675,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1381 : ∀ c∈certificate1381.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4674,MergedCutCells.Batch389.certificate4675], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid577,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid577,List.forall_mem_nil _⟩⟩
theorem populationMatches1381 : ∀ c∈certificate1381.cells, c.population=certificate1381.population := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4674,MergedCutCells.Batch389.certificate4675], c.population=PopulationCertificates.Batch046.certificate932
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1381 {x : ℝ} (hx : certificate1381.interval.Contains x) : ∃ c∈certificate1381.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1381 numericValid1381 hx

def certificate1382 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate932,PopulationCertificates.Batch046.certificate932,[MergedCutCells.Batch389.certificate4676,MergedCutCells.Batch389.certificate4677,MergedCutCells.Batch389.certificate4678],(1174747019/1000000000),none,(1/2),(191332574335900931/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1382 : certificate1382.NumericValid := by decide +kernel
theorem cellsSound1382 : ∀ c∈certificate1382.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4676,MergedCutCells.Batch389.certificate4677,MergedCutCells.Batch389.certificate4678], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4676,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4677,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4678,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1382 : ∀ c∈certificate1382.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4676,MergedCutCells.Batch389.certificate4677,MergedCutCells.Batch389.certificate4678], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4676,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4677,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4678,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1382 : ∀ c∈certificate1382.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4676,MergedCutCells.Batch389.certificate4677,MergedCutCells.Batch389.certificate4678], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1382 : ∀ c∈certificate1382.cells, c.population=certificate1382.population := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4676,MergedCutCells.Batch389.certificate4677,MergedCutCells.Batch389.certificate4678], c.population=PopulationCertificates.Batch046.certificate932
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1382 {x : ℝ} (hx : certificate1382.interval.Contains x) : ∃ c∈certificate1382.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1382 numericValid1382 hx

def certificate1383 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate933,PopulationCertificates.Batch046.certificate933,[MergedCutCells.Batch389.certificate4679,MergedCutCells.Batch390.certificate4680],(28252501530893674889/1000000000000000000),none,(1/2),(1751825953242364193/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1383 : certificate1383.NumericValid := by decide +kernel
theorem cellsSound1383 : ∀ c∈certificate1383.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4679,MergedCutCells.Batch390.certificate4680], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4680,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1383 : ∀ c∈certificate1383.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4679,MergedCutCells.Batch390.certificate4680], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4680,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1383 : ∀ c∈certificate1383.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4679,MergedCutCells.Batch390.certificate4680], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1383 : ∀ c∈certificate1383.cells, c.population=certificate1383.population := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4679,MergedCutCells.Batch390.certificate4680], c.population=PopulationCertificates.Batch046.certificate933
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1383 {x : ℝ} (hx : certificate1383.interval.Contains x) : ∃ c∈certificate1383.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1383 numericValid1383 hx

def certificate1384 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate934,PopulationCertificates.Batch046.certificate934,[MergedCutCells.Batch390.certificate4681,MergedCutCells.Batch390.certificate4682,MergedCutCells.Batch390.certificate4683,MergedCutCells.Batch390.certificate4684],(135803074669049693/200000000000000000),none,(1/40),(10812060882442741/500000000000000000),none,none⟩
theorem numericValid1384 : certificate1384.NumericValid := by decide +kernel
theorem cellsSound1384 : ∀ c∈certificate1384.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4681,MergedCutCells.Batch390.certificate4682,MergedCutCells.Batch390.certificate4683,MergedCutCells.Batch390.certificate4684], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4681,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4683,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4684,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1384 : ∀ c∈certificate1384.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4681,MergedCutCells.Batch390.certificate4682,MergedCutCells.Batch390.certificate4683,MergedCutCells.Batch390.certificate4684], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4681,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4683,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4684,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1384 : ∀ c∈certificate1384.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4681,MergedCutCells.Batch390.certificate4682,MergedCutCells.Batch390.certificate4683,MergedCutCells.Batch390.certificate4684], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid578,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid579,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid580,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid581,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1384 : ∀ c∈certificate1384.cells, c.population=certificate1384.population := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4681,MergedCutCells.Batch390.certificate4682,MergedCutCells.Batch390.certificate4683,MergedCutCells.Batch390.certificate4684], c.population=PopulationCertificates.Batch046.certificate934
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1384 {x : ℝ} (hx : certificate1384.interval.Contains x) : ∃ c∈certificate1384.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1384 numericValid1384 hx

def certificate1385 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate935,PopulationCertificates.Batch046.certificate935,[MergedCutCells.Batch390.certificate4685,MergedCutCells.Batch390.certificate4686],(288029368302582717/500000000000000000),(some (45964431/40000000)),(1/2),(98416512445330437/500000000000000000),(some (16432216077432943/1000000000000000000)),(some (465364246176779/200000000000000000))⟩
theorem numericValid1385 : certificate1385.NumericValid := by decide +kernel
theorem cellsSound1385 : ∀ c∈certificate1385.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4685,MergedCutCells.Batch390.certificate4686], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4685,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4686,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1385 : ∀ c∈certificate1385.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4685,MergedCutCells.Batch390.certificate4686], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4685,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4686,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1385 : ∀ c∈certificate1385.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4685,MergedCutCells.Batch390.certificate4686], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid582,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid582,List.forall_mem_nil _⟩⟩
theorem populationMatches1385 : ∀ c∈certificate1385.cells, c.population=certificate1385.population := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4685,MergedCutCells.Batch390.certificate4686], c.population=PopulationCertificates.Batch046.certificate935
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1385 {x : ℝ} (hx : certificate1385.interval.Contains x) : ∃ c∈certificate1385.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1385 numericValid1385 hx

def certificate1386 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate935,PopulationCertificates.Batch046.certificate935,[MergedCutCells.Batch390.certificate4687,MergedCutCells.Batch390.certificate4688,MergedCutCells.Batch390.certificate4689],(45964431/40000000),none,(1/2),(313674793823079/1600000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1386 : certificate1386.NumericValid := by decide +kernel
theorem cellsSound1386 : ∀ c∈certificate1386.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4687,MergedCutCells.Batch390.certificate4688,MergedCutCells.Batch390.certificate4689], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4687,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4688,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4689,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1386 : ∀ c∈certificate1386.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4687,MergedCutCells.Batch390.certificate4688,MergedCutCells.Batch390.certificate4689], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4687,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4688,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4689,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1386 : ∀ c∈certificate1386.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4687,MergedCutCells.Batch390.certificate4688,MergedCutCells.Batch390.certificate4689], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1386 : ∀ c∈certificate1386.cells, c.population=certificate1386.population := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4687,MergedCutCells.Batch390.certificate4688,MergedCutCells.Batch390.certificate4689], c.population=PopulationCertificates.Batch046.certificate935
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1386 {x : ℝ} (hx : certificate1386.interval.Contains x) : ∃ c∈certificate1386.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1386 numericValid1386 hx

def certificate1387 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate936,PopulationCertificates.Batch046.certificate936,[MergedCutCells.Batch390.certificate4690,MergedCutCells.Batch390.certificate4691],(1799751479631376659/62500000000000000),none,(1/2),(3575517181763522297/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1387 : certificate1387.NumericValid := by decide +kernel
theorem cellsSound1387 : ∀ c∈certificate1387.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4690,MergedCutCells.Batch390.certificate4691], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4690,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.sound4691,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1387 : ∀ c∈certificate1387.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4690,MergedCutCells.Batch390.certificate4691], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4690,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch390.numericValid4691,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1387 : ∀ c∈certificate1387.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4690,MergedCutCells.Batch390.certificate4691], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1387 : ∀ c∈certificate1387.cells, c.population=certificate1387.population := by
  change ∀ c∈[MergedCutCells.Batch390.certificate4690,MergedCutCells.Batch390.certificate4691], c.population=PopulationCertificates.Batch046.certificate936
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1387 {x : ℝ} (hx : certificate1387.interval.Contains x) : ∃ c∈certificate1387.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1387 numericValid1387 hx

def certificate1388 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate937,PopulationCertificates.Batch046.certificate937,[MergedCutCells.Batch391.certificate4692,MergedCutCells.Batch391.certificate4693,MergedCutCells.Batch391.certificate4694,MergedCutCells.Batch391.certificate4695],(682569792992811899/1000000000000000000),none,(1/40),(3361581308139669/125000000000000000),none,none⟩
theorem numericValid1388 : certificate1388.NumericValid := by decide +kernel
theorem cellsSound1388 : ∀ c∈certificate1388.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4692,MergedCutCells.Batch391.certificate4693,MergedCutCells.Batch391.certificate4694,MergedCutCells.Batch391.certificate4695], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4692,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4693,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4694,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4695,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1388 : ∀ c∈certificate1388.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4692,MergedCutCells.Batch391.certificate4693,MergedCutCells.Batch391.certificate4694,MergedCutCells.Batch391.certificate4695], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4692,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4693,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4694,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4695,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1388 : ∀ c∈certificate1388.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4692,MergedCutCells.Batch391.certificate4693,MergedCutCells.Batch391.certificate4694,MergedCutCells.Batch391.certificate4695], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid583,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid584,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid585,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid586,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1388 : ∀ c∈certificate1388.cells, c.population=certificate1388.population := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4692,MergedCutCells.Batch391.certificate4693,MergedCutCells.Batch391.certificate4694,MergedCutCells.Batch391.certificate4695], c.population=PopulationCertificates.Batch046.certificate937
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1388 {x : ℝ} (hx : certificate1388.interval.Contains x) : ∃ c∈certificate1388.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1388 numericValid1388 hx

def certificate1389 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate938,PopulationCertificates.Batch046.certificate938,[MergedCutCells.Batch391.certificate4696,MergedCutCells.Batch391.certificate4697],(577008539601093049/1000000000000000000),(some (1150727479/1000000000)),(1/2),(39715857843334821/200000000000000000),(some (4211166738048369/250000000000000000)),(some (239503584267541/100000000000000000))⟩
theorem numericValid1389 : certificate1389.NumericValid := by decide +kernel
theorem cellsSound1389 : ∀ c∈certificate1389.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4696,MergedCutCells.Batch391.certificate4697], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4697,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1389 : ∀ c∈certificate1389.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4696,MergedCutCells.Batch391.certificate4697], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4697,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1389 : ∀ c∈certificate1389.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4696,MergedCutCells.Batch391.certificate4697], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid587,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid587,List.forall_mem_nil _⟩⟩
theorem populationMatches1389 : ∀ c∈certificate1389.cells, c.population=certificate1389.population := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4696,MergedCutCells.Batch391.certificate4697], c.population=PopulationCertificates.Batch046.certificate938
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1389 {x : ℝ} (hx : certificate1389.interval.Contains x) : ∃ c∈certificate1389.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1389 numericValid1389 hx

def certificate1390 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate938,PopulationCertificates.Batch046.certificate938,[MergedCutCells.Batch391.certificate4698,MergedCutCells.Batch391.certificate4699,MergedCutCells.Batch391.certificate4700],(1150727479/1000000000),none,(1/2),(98856799276861539/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1390 : certificate1390.NumericValid := by decide +kernel
theorem cellsSound1390 : ∀ c∈certificate1390.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4698,MergedCutCells.Batch391.certificate4699,MergedCutCells.Batch391.certificate4700], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4699,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4700,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1390 : ∀ c∈certificate1390.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4698,MergedCutCells.Batch391.certificate4699,MergedCutCells.Batch391.certificate4700], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4699,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4700,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1390 : ∀ c∈certificate1390.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4698,MergedCutCells.Batch391.certificate4699,MergedCutCells.Batch391.certificate4700], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1390 : ∀ c∈certificate1390.cells, c.population=certificate1390.population := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4698,MergedCutCells.Batch391.certificate4699,MergedCutCells.Batch391.certificate4700], c.population=PopulationCertificates.Batch046.certificate938
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1390 {x : ℝ} (hx : certificate1390.interval.Contains x) : ∃ c∈certificate1390.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1390 numericValid1390 hx

def certificate1391 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate939,PopulationCertificates.Batch046.certificate939,[MergedCutCells.Batch391.certificate4701,MergedCutCells.Batch391.certificate4702],(29072842144476235131/1000000000000000000),none,(1/2),(7222804519594165343/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1391 : certificate1391.NumericValid := by decide +kernel
theorem cellsSound1391 : ∀ c∈certificate1391.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4701,MergedCutCells.Batch391.certificate4702], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4701,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4702,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1391 : ∀ c∈certificate1391.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4701,MergedCutCells.Batch391.certificate4702], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4701,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4702,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1391 : ∀ c∈certificate1391.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4701,MergedCutCells.Batch391.certificate4702], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1391 : ∀ c∈certificate1391.cells, c.population=certificate1391.population := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4701,MergedCutCells.Batch391.certificate4702], c.population=PopulationCertificates.Batch046.certificate939
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1391 {x : ℝ} (hx : certificate1391.interval.Contains x) : ∃ c∈certificate1391.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1391 numericValid1391 hx

end Cycle12.MergedCutGroups.Batch115
