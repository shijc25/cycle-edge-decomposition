import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch047
import Cycle12.MergedCutCells.Batch391
import Cycle12.MergedCutCells.Batch392
import Cycle12.MergedCutCells.Batch393
import Cycle12.MergedCutCells.Batch394
import Cycle12.PopulationCertificates.Batch047

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch116

def certificate1392 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate940,PopulationCertificates.Batch047.certificate940,[MergedCutCells.Batch391.certificate4703,MergedCutCells.Batch392.certificate4704,MergedCutCells.Batch392.certificate4705,MergedCutCells.Batch392.certificate4706],(684420945606931351/1000000000000000000),none,(1/40),(14600463176884017/500000000000000000),none,none⟩
theorem numericValid1392 : certificate1392.NumericValid := by decide +kernel
theorem cellsSound1392 : ∀ c∈certificate1392.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4703,MergedCutCells.Batch392.certificate4704,MergedCutCells.Batch392.certificate4705,MergedCutCells.Batch392.certificate4706], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.sound4703,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4704,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4705,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4706,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1392 : ∀ c∈certificate1392.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4703,MergedCutCells.Batch392.certificate4704,MergedCutCells.Batch392.certificate4705,MergedCutCells.Batch392.certificate4706], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch391.numericValid4703,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4704,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4705,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4706,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1392 : ∀ c∈certificate1392.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4703,MergedCutCells.Batch392.certificate4704,MergedCutCells.Batch392.certificate4705,MergedCutCells.Batch392.certificate4706], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid588,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid589,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid590,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid591,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1392 : ∀ c∈certificate1392.cells, c.population=certificate1392.population := by
  change ∀ c∈[MergedCutCells.Batch391.certificate4703,MergedCutCells.Batch392.certificate4704,MergedCutCells.Batch392.certificate4705,MergedCutCells.Batch392.certificate4706], c.population=PopulationCertificates.Batch047.certificate940
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1392 {x : ℝ} (hx : certificate1392.interval.Contains x) : ∃ c∈certificate1392.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1392 numericValid1392 hx

def certificate1393 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate941,PopulationCertificates.Batch047.certificate941,[MergedCutCells.Batch392.certificate4707,MergedCutCells.Batch392.certificate4708],(143515073899120711/250000000000000000),(some (1145707859/1000000000)),(1/2),(45436761233503851/250000000000000000),(some (1065408836777491/62500000000000000)),(some (2428542085296809/1000000000000000000))⟩
theorem numericValid1393 : certificate1393.NumericValid := by decide +kernel
theorem cellsSound1393 : ∀ c∈certificate1393.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4707,MergedCutCells.Batch392.certificate4708], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4707,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4708,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1393 : ∀ c∈certificate1393.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4707,MergedCutCells.Batch392.certificate4708], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4707,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4708,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1393 : ∀ c∈certificate1393.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4707,MergedCutCells.Batch392.certificate4708], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid592,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid592,List.forall_mem_nil _⟩⟩
theorem populationMatches1393 : ∀ c∈certificate1393.cells, c.population=certificate1393.population := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4707,MergedCutCells.Batch392.certificate4708], c.population=PopulationCertificates.Batch047.certificate941
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1393 {x : ℝ} (hx : certificate1393.interval.Contains x) : ∃ c∈certificate1393.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1393 numericValid1393 hx

def certificate1394 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate941,PopulationCertificates.Batch047.certificate941,[MergedCutCells.Batch392.certificate4709,MergedCutCells.Batch392.certificate4710,MergedCutCells.Batch392.certificate4711],(1145707859/1000000000),none,(1/2),(180847815772903813/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1394 : certificate1394.NumericValid := by decide +kernel
theorem cellsSound1394 : ∀ c∈certificate1394.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4709,MergedCutCells.Batch392.certificate4710,MergedCutCells.Batch392.certificate4711], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4709,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4711,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1394 : ∀ c∈certificate1394.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4709,MergedCutCells.Batch392.certificate4710,MergedCutCells.Batch392.certificate4711], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4709,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4711,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1394 : ∀ c∈certificate1394.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4709,MergedCutCells.Batch392.certificate4710,MergedCutCells.Batch392.certificate4711], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1394 : ∀ c∈certificate1394.cells, c.population=certificate1394.population := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4709,MergedCutCells.Batch392.certificate4710,MergedCutCells.Batch392.certificate4711], c.population=PopulationCertificates.Batch047.certificate941
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1394 {x : ℝ} (hx : certificate1394.interval.Contains x) : ∃ c∈certificate1394.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1394 numericValid1394 hx

def certificate1395 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate942,PopulationCertificates.Batch047.certificate942,[MergedCutCells.Batch392.certificate4712,MergedCutCells.Batch392.certificate4713],(29516229040970144381/1000000000000000000),none,(1/2),(912217968130224277/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1395 : certificate1395.NumericValid := by decide +kernel
theorem cellsSound1395 : ∀ c∈certificate1395.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4712,MergedCutCells.Batch392.certificate4713], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4713,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1395 : ∀ c∈certificate1395.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4712,MergedCutCells.Batch392.certificate4713], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4713,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1395 : ∀ c∈certificate1395.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4712,MergedCutCells.Batch392.certificate4713], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1395 : ∀ c∈certificate1395.cells, c.population=certificate1395.population := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4712,MergedCutCells.Batch392.certificate4713], c.population=PopulationCertificates.Batch047.certificate942
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1395 {x : ℝ} (hx : certificate1395.interval.Contains x) : ∃ c∈certificate1395.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1395 numericValid1395 hx

def certificate1396 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate943,PopulationCertificates.Batch047.certificate943,[MergedCutCells.Batch392.certificate4714,MergedCutCells.Batch392.certificate4715,MergedCutCells.Batch393.certificate4716,MergedCutCells.Batch393.certificate4717],(171547868580580309/250000000000000000),none,(1/40),(125254992377127/3906250000000000),none,none⟩
theorem numericValid1396 : certificate1396.NumericValid := by decide +kernel
theorem cellsSound1396 : ∀ c∈certificate1396.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4714,MergedCutCells.Batch392.certificate4715,MergedCutCells.Batch393.certificate4716,MergedCutCells.Batch393.certificate4717], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.sound4715,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4716,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4717,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1396 : ∀ c∈certificate1396.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4714,MergedCutCells.Batch392.certificate4715,MergedCutCells.Batch393.certificate4716,MergedCutCells.Batch393.certificate4717], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch392.numericValid4715,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4716,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4717,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1396 : ∀ c∈certificate1396.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4714,MergedCutCells.Batch392.certificate4715,MergedCutCells.Batch393.certificate4716,MergedCutCells.Batch393.certificate4717], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid593,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid594,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid595,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid596,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1396 : ∀ c∈certificate1396.cells, c.population=certificate1396.population := by
  change ∀ c∈[MergedCutCells.Batch392.certificate4714,MergedCutCells.Batch392.certificate4715,MergedCutCells.Batch393.certificate4716,MergedCutCells.Batch393.certificate4717], c.population=PopulationCertificates.Batch047.certificate943
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1396 {x : ℝ} (hx : certificate1396.interval.Contains x) : ∃ c∈certificate1396.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1396 numericValid1396 hx

def certificate1397 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate944,PopulationCertificates.Batch047.certificate944,[MergedCutCells.Batch393.certificate4718,MergedCutCells.Batch393.certificate4719],(287271325630839073/500000000000000000),(some (1146529367/1000000000)),(1/2),(7303933992192549/40000000000000000),(some (17255851521242249/1000000000000000000)),(some (1231681982045001/500000000000000000))⟩
theorem numericValid1397 : certificate1397.NumericValid := by decide +kernel
theorem cellsSound1397 : ∀ c∈certificate1397.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4718,MergedCutCells.Batch393.certificate4719], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4718,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4719,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1397 : ∀ c∈certificate1397.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4718,MergedCutCells.Batch393.certificate4719], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4718,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4719,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1397 : ∀ c∈certificate1397.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4718,MergedCutCells.Batch393.certificate4719], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid597,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid597,List.forall_mem_nil _⟩⟩
theorem populationMatches1397 : ∀ c∈certificate1397.cells, c.population=certificate1397.population := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4718,MergedCutCells.Batch393.certificate4719], c.population=PopulationCertificates.Batch047.certificate944
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1397 {x : ℝ} (hx : certificate1397.interval.Contains x) : ∃ c∈certificate1397.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1397 numericValid1397 hx

def certificate1398 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate944,PopulationCertificates.Batch047.certificate944,[MergedCutCells.Batch393.certificate4720,MergedCutCells.Batch393.certificate4721,MergedCutCells.Batch393.certificate4722],(1146529367/1000000000),none,(1/2),(181657187317407693/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1398 : certificate1398.NumericValid := by decide +kernel
theorem cellsSound1398 : ∀ c∈certificate1398.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4720,MergedCutCells.Batch393.certificate4721,MergedCutCells.Batch393.certificate4722], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4720,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4721,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4722,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1398 : ∀ c∈certificate1398.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4720,MergedCutCells.Batch393.certificate4721,MergedCutCells.Batch393.certificate4722], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4720,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4721,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4722,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1398 : ∀ c∈certificate1398.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4720,MergedCutCells.Batch393.certificate4721,MergedCutCells.Batch393.certificate4722], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1398 : ∀ c∈certificate1398.cells, c.population=certificate1398.population := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4720,MergedCutCells.Batch393.certificate4721,MergedCutCells.Batch393.certificate4722], c.population=PopulationCertificates.Batch047.certificate944
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1398 {x : ℝ} (hx : certificate1398.interval.Contains x) : ∃ c∈certificate1398.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1398 numericValid1398 hx

def certificate1399 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate945,PopulationCertificates.Batch047.certificate945,[MergedCutCells.Batch393.certificate4723,MergedCutCells.Batch393.certificate4724],(29658336568448842767/1000000000000000000),none,(1/2),(1833564034352329501/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1399 : certificate1399.NumericValid := by decide +kernel
theorem cellsSound1399 : ∀ c∈certificate1399.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4723,MergedCutCells.Batch393.certificate4724], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4723,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4724,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1399 : ∀ c∈certificate1399.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4723,MergedCutCells.Batch393.certificate4724], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4723,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4724,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1399 : ∀ c∈certificate1399.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4723,MergedCutCells.Batch393.certificate4724], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1399 : ∀ c∈certificate1399.cells, c.population=certificate1399.population := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4723,MergedCutCells.Batch393.certificate4724], c.population=PopulationCertificates.Batch047.certificate945
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1399 {x : ℝ} (hx : certificate1399.interval.Contains x) : ∃ c∈certificate1399.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1399 numericValid1399 hx

def certificate1400 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate946,PopulationCertificates.Batch047.certificate946,[MergedCutCells.Batch393.certificate4725,MergedCutCells.Batch393.certificate4726,MergedCutCells.Batch393.certificate4727,MergedCutCells.Batch394.certificate4728],(137429058940752549/200000000000000000),none,(1/40),(33291784057239951/1000000000000000000),none,none⟩
theorem numericValid1400 : certificate1400.NumericValid := by decide +kernel
theorem cellsSound1400 : ∀ c∈certificate1400.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4725,MergedCutCells.Batch393.certificate4726,MergedCutCells.Batch393.certificate4727,MergedCutCells.Batch394.certificate4728], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4725,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4726,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.sound4727,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4728,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1400 : ∀ c∈certificate1400.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4725,MergedCutCells.Batch393.certificate4726,MergedCutCells.Batch393.certificate4727,MergedCutCells.Batch394.certificate4728], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4725,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4726,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch393.numericValid4727,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4728,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1400 : ∀ c∈certificate1400.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4725,MergedCutCells.Batch393.certificate4726,MergedCutCells.Batch393.certificate4727,MergedCutCells.Batch394.certificate4728], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid598,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy029.valid599,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid600,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid601,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1400 : ∀ c∈certificate1400.cells, c.population=certificate1400.population := by
  change ∀ c∈[MergedCutCells.Batch393.certificate4725,MergedCutCells.Batch393.certificate4726,MergedCutCells.Batch393.certificate4727,MergedCutCells.Batch394.certificate4728], c.population=PopulationCertificates.Batch047.certificate946
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1400 {x : ℝ} (hx : certificate1400.interval.Contains x) : ∃ c∈certificate1400.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1400 numericValid1400 hx

def certificate1401 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate947,PopulationCertificates.Batch047.certificate947,[MergedCutCells.Batch394.certificate4729,MergedCutCells.Batch394.certificate4730],(287512097470512127/500000000000000000),(some (114734939/100000000)),(1/2),(183452552039573229/1000000000000000000),(some (17466427100197029/1000000000000000000)),(some (312309937903303/125000000000000000))⟩
theorem numericValid1401 : certificate1401.NumericValid := by decide +kernel
theorem cellsSound1401 : ∀ c∈certificate1401.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4729,MergedCutCells.Batch394.certificate4730], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4729,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4730,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1401 : ∀ c∈certificate1401.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4729,MergedCutCells.Batch394.certificate4730], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4729,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4730,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1401 : ∀ c∈certificate1401.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4729,MergedCutCells.Batch394.certificate4730], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid602,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid602,List.forall_mem_nil _⟩⟩
theorem populationMatches1401 : ∀ c∈certificate1401.cells, c.population=certificate1401.population := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4729,MergedCutCells.Batch394.certificate4730], c.population=PopulationCertificates.Batch047.certificate947
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1401 {x : ℝ} (hx : certificate1401.interval.Contains x) : ∃ c∈certificate1401.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1401 numericValid1401 hx

def certificate1402 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate947,PopulationCertificates.Batch047.certificate947,[MergedCutCells.Batch394.certificate4731,MergedCutCells.Batch394.certificate4732,MergedCutCells.Batch394.certificate4733],(114734939/100000000),none,(1/2),(91236283950659061/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1402 : certificate1402.NumericValid := by decide +kernel
theorem cellsSound1402 : ∀ c∈certificate1402.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4731,MergedCutCells.Batch394.certificate4732,MergedCutCells.Batch394.certificate4733], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4732,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4733,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1402 : ∀ c∈certificate1402.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4731,MergedCutCells.Batch394.certificate4732,MergedCutCells.Batch394.certificate4733], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4732,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4733,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1402 : ∀ c∈certificate1402.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4731,MergedCutCells.Batch394.certificate4732,MergedCutCells.Batch394.certificate4733], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1402 : ∀ c∈certificate1402.cells, c.population=certificate1402.population := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4731,MergedCutCells.Batch394.certificate4732,MergedCutCells.Batch394.certificate4733], c.population=PopulationCertificates.Batch047.certificate947
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1402 {x : ℝ} (hx : certificate1402.interval.Contains x) : ∃ c∈certificate1402.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1402 numericValid1402 hx

def certificate1403 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate948,PopulationCertificates.Batch047.certificate948,[MergedCutCells.Batch394.certificate4734,MergedCutCells.Batch394.certificate4735],(29801355939048807611/1000000000000000000),none,(1/2),(7371036049780045069/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1403 : certificate1403.NumericValid := by decide +kernel
theorem cellsSound1403 : ∀ c∈certificate1403.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4734,MergedCutCells.Batch394.certificate4735], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4734,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.sound4735,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1403 : ∀ c∈certificate1403.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4734,MergedCutCells.Batch394.certificate4735], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4734,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch394.numericValid4735,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1403 : ∀ c∈certificate1403.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4734,MergedCutCells.Batch394.certificate4735], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1403 : ∀ c∈certificate1403.cells, c.population=certificate1403.population := by
  change ∀ c∈[MergedCutCells.Batch394.certificate4734,MergedCutCells.Batch394.certificate4735], c.population=PopulationCertificates.Batch047.certificate948
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1403 {x : ℝ} (hx : certificate1403.interval.Contains x) : ∃ c∈certificate1403.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1403 numericValid1403 hx

end Cycle12.MergedCutGroups.Batch116
