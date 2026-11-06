import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch049
import Cycle12.MergedCutCells.Batch405
import Cycle12.MergedCutCells.Batch406
import Cycle12.MergedCutCells.Batch407
import Cycle12.MergedCutCells.Batch408
import Cycle12.PopulationCertificates.Batch049

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch121

def certificate1452 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate985,PopulationCertificates.Batch049.certificate985,[MergedCutCells.Batch405.certificate4869,MergedCutCells.Batch405.certificate4870,MergedCutCells.Batch405.certificate4871,MergedCutCells.Batch406.certificate4872],(139253624884712909/200000000000000000),none,(1/40),(32773105159987441/1000000000000000000),none,none⟩
theorem numericValid1452 : certificate1452.NumericValid := by decide +kernel
theorem cellsSound1452 : ∀ c∈certificate1452.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4869,MergedCutCells.Batch405.certificate4870,MergedCutCells.Batch405.certificate4871,MergedCutCells.Batch406.certificate4872], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4869,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4870,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4871,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4872,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1452 : ∀ c∈certificate1452.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4869,MergedCutCells.Batch405.certificate4870,MergedCutCells.Batch405.certificate4871,MergedCutCells.Batch406.certificate4872], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4869,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4870,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4871,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4872,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1452 : ∀ c∈certificate1452.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4869,MergedCutCells.Batch405.certificate4870,MergedCutCells.Batch405.certificate4871,MergedCutCells.Batch406.certificate4872], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid663,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid664,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid665,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid666,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1452 : ∀ c∈certificate1452.cells, c.population=certificate1452.population := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4869,MergedCutCells.Batch405.certificate4870,MergedCutCells.Batch405.certificate4871,MergedCutCells.Batch406.certificate4872], c.population=PopulationCertificates.Batch049.certificate985
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1452 {x : ℝ} (hx : certificate1452.interval.Contains x) : ∃ c∈certificate1452.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1452 numericValid1452 hx

def certificate1453 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate986,PopulationCertificates.Batch049.certificate986,[MergedCutCells.Batch406.certificate4873,MergedCutCells.Batch406.certificate4874],(29468670153400417/50000000000000000),(some (279841587/250000000)),(1/2),(111376339570751573/500000000000000000),(some (22399505036902453/1000000000000000000)),(some (167185410301519/50000000000000000))⟩
theorem numericValid1453 : certificate1453.NumericValid := by decide +kernel
theorem cellsSound1453 : ∀ c∈certificate1453.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4873,MergedCutCells.Batch406.certificate4874], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4873,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4874,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1453 : ∀ c∈certificate1453.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4873,MergedCutCells.Batch406.certificate4874], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4873,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4874,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1453 : ∀ c∈certificate1453.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4873,MergedCutCells.Batch406.certificate4874], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid667,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid667,List.forall_mem_nil _⟩⟩
theorem populationMatches1453 : ∀ c∈certificate1453.cells, c.population=certificate1453.population := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4873,MergedCutCells.Batch406.certificate4874], c.population=PopulationCertificates.Batch049.certificate986
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1453 {x : ℝ} (hx : certificate1453.interval.Contains x) : ∃ c∈certificate1453.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1453 numericValid1453 hx

def certificate1454 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate986,PopulationCertificates.Batch049.certificate986,[MergedCutCells.Batch406.certificate4875,MergedCutCells.Batch406.certificate4876,MergedCutCells.Batch406.certificate4877],(279841587/250000000),none,(1/2),(110729731353759287/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1454 : certificate1454.NumericValid := by decide +kernel
theorem cellsSound1454 : ∀ c∈certificate1454.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4875,MergedCutCells.Batch406.certificate4876,MergedCutCells.Batch406.certificate4877], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4875,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4876,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4877,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1454 : ∀ c∈certificate1454.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4875,MergedCutCells.Batch406.certificate4876,MergedCutCells.Batch406.certificate4877], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4875,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4876,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4877,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1454 : ∀ c∈certificate1454.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4875,MergedCutCells.Batch406.certificate4876,MergedCutCells.Batch406.certificate4877], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1454 : ∀ c∈certificate1454.cells, c.population=certificate1454.population := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4875,MergedCutCells.Batch406.certificate4876,MergedCutCells.Batch406.certificate4877], c.population=PopulationCertificates.Batch049.certificate986
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1454 {x : ℝ} (hx : certificate1454.interval.Contains x) : ∃ c∈certificate1454.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1454 numericValid1454 hx

def certificate1455 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate987,PopulationCertificates.Batch049.certificate987,[MergedCutCells.Batch406.certificate4878,MergedCutCells.Batch406.certificate4879],(33017748347725111/1000000000000000),none,(1/2),(4117594461991676113/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1455 : certificate1455.NumericValid := by decide +kernel
theorem cellsSound1455 : ∀ c∈certificate1455.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4878,MergedCutCells.Batch406.certificate4879], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4879,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1455 : ∀ c∈certificate1455.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4878,MergedCutCells.Batch406.certificate4879], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4879,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1455 : ∀ c∈certificate1455.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4878,MergedCutCells.Batch406.certificate4879], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1455 : ∀ c∈certificate1455.cells, c.population=certificate1455.population := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4878,MergedCutCells.Batch406.certificate4879], c.population=PopulationCertificates.Batch049.certificate987
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1455 {x : ℝ} (hx : certificate1455.interval.Contains x) : ∃ c∈certificate1455.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1455 numericValid1455 hx

def certificate1456 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate988,PopulationCertificates.Batch049.certificate988,[MergedCutCells.Batch406.certificate4880,MergedCutCells.Batch406.certificate4881,MergedCutCells.Batch406.certificate4882,MergedCutCells.Batch406.certificate4883,MergedCutCells.Batch407.certificate4884],(691194519876703369/1000000000000000000),none,(1/40),(15797305996096847/1000000000000000000),none,none⟩
theorem numericValid1456 : certificate1456.NumericValid := by decide +kernel
theorem cellsSound1456 : ∀ c∈certificate1456.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4880,MergedCutCells.Batch406.certificate4881,MergedCutCells.Batch406.certificate4882,MergedCutCells.Batch406.certificate4883,MergedCutCells.Batch407.certificate4884], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4880,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4881,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4882,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.sound4883,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4884,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1456 : ∀ c∈certificate1456.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4880,MergedCutCells.Batch406.certificate4881,MergedCutCells.Batch406.certificate4882,MergedCutCells.Batch406.certificate4883,MergedCutCells.Batch407.certificate4884], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4880,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4881,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4882,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch406.numericValid4883,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4884,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1456 : ∀ c∈certificate1456.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4880,MergedCutCells.Batch406.certificate4881,MergedCutCells.Batch406.certificate4882,MergedCutCells.Batch406.certificate4883,MergedCutCells.Batch407.certificate4884], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid668,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid669,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid670,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid671,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid672,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1456 : ∀ c∈certificate1456.cells, c.population=certificate1456.population := by
  change ∀ c∈[MergedCutCells.Batch406.certificate4880,MergedCutCells.Batch406.certificate4881,MergedCutCells.Batch406.certificate4882,MergedCutCells.Batch406.certificate4883,MergedCutCells.Batch407.certificate4884], c.population=PopulationCertificates.Batch049.certificate988
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1456 {x : ℝ} (hx : certificate1456.interval.Contains x) : ∃ c∈certificate1456.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1456 numericValid1456 hx

def certificate1457 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate989,PopulationCertificates.Batch049.certificate989,[MergedCutCells.Batch407.certificate4885,MergedCutCells.Batch407.certificate4886],(9224290700315623/15625000000000000),(some (560487349/500000000)),(1/2),(56217679068669589/250000000000000000),(some (11438802143091071/500000000000000000)),(some (1713904684123549/500000000000000000))⟩
theorem numericValid1457 : certificate1457.NumericValid := by decide +kernel
theorem cellsSound1457 : ∀ c∈certificate1457.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4885,MergedCutCells.Batch407.certificate4886], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4885,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4886,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1457 : ∀ c∈certificate1457.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4885,MergedCutCells.Batch407.certificate4886], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4885,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4886,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1457 : ∀ c∈certificate1457.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4885,MergedCutCells.Batch407.certificate4886], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid673,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid673,List.forall_mem_nil _⟩⟩
theorem populationMatches1457 : ∀ c∈certificate1457.cells, c.population=certificate1457.population := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4885,MergedCutCells.Batch407.certificate4886], c.population=PopulationCertificates.Batch049.certificate989
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1457 {x : ℝ} (hx : certificate1457.interval.Contains x) : ∃ c∈certificate1457.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1457 numericValid1457 hx

def certificate1458 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate989,PopulationCertificates.Batch049.certificate989,[MergedCutCells.Batch407.certificate4887,MergedCutCells.Batch407.certificate4888,MergedCutCells.Batch407.certificate4889],(560487349/500000000),none,(1/2),(55865260441610623/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1458 : certificate1458.NumericValid := by decide +kernel
theorem cellsSound1458 : ∀ c∈certificate1458.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4887,MergedCutCells.Batch407.certificate4888,MergedCutCells.Batch407.certificate4889], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4887,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4888,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4889,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1458 : ∀ c∈certificate1458.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4887,MergedCutCells.Batch407.certificate4888,MergedCutCells.Batch407.certificate4889], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4887,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4888,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4889,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1458 : ∀ c∈certificate1458.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4887,MergedCutCells.Batch407.certificate4888,MergedCutCells.Batch407.certificate4889], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1458 : ∀ c∈certificate1458.cells, c.population=certificate1458.population := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4887,MergedCutCells.Batch407.certificate4888,MergedCutCells.Batch407.certificate4889], c.population=PopulationCertificates.Batch049.certificate989
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1458 {x : ℝ} (hx : certificate1458.interval.Contains x) : ∃ c∈certificate1458.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1458 numericValid1458 hx

def certificate1459 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate990,PopulationCertificates.Batch049.certificate990,[MergedCutCells.Batch407.certificate4890,MergedCutCells.Batch407.certificate4891],(16675172123435855551/500000000000000000),none,(1/2),(2080198272482366963/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1459 : certificate1459.NumericValid := by decide +kernel
theorem cellsSound1459 : ∀ c∈certificate1459.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4890,MergedCutCells.Batch407.certificate4891], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4890,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4891,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1459 : ∀ c∈certificate1459.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4890,MergedCutCells.Batch407.certificate4891], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4890,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4891,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1459 : ∀ c∈certificate1459.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4890,MergedCutCells.Batch407.certificate4891], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1459 : ∀ c∈certificate1459.cells, c.population=certificate1459.population := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4890,MergedCutCells.Batch407.certificate4891], c.population=PopulationCertificates.Batch049.certificate990
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1459 {x : ℝ} (hx : certificate1459.interval.Contains x) : ∃ c∈certificate1459.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1459 numericValid1459 hx

def certificate1460 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate991,PopulationCertificates.Batch049.certificate991,[MergedCutCells.Batch407.certificate4892,MergedCutCells.Batch407.certificate4893,MergedCutCells.Batch407.certificate4894,MergedCutCells.Batch407.certificate4895,MergedCutCells.Batch408.certificate4896],(693162329072815849/1000000000000000000),none,(1/40),(9086937306846559/500000000000000000),none,none⟩
theorem numericValid1460 : certificate1460.NumericValid := by decide +kernel
theorem cellsSound1460 : ∀ c∈certificate1460.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4892,MergedCutCells.Batch407.certificate4893,MergedCutCells.Batch407.certificate4894,MergedCutCells.Batch407.certificate4895,MergedCutCells.Batch408.certificate4896], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4892,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4893,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4894,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.sound4895,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4896,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1460 : ∀ c∈certificate1460.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4892,MergedCutCells.Batch407.certificate4893,MergedCutCells.Batch407.certificate4894,MergedCutCells.Batch407.certificate4895,MergedCutCells.Batch408.certificate4896], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4892,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4893,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4894,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch407.numericValid4895,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4896,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1460 : ∀ c∈certificate1460.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4892,MergedCutCells.Batch407.certificate4893,MergedCutCells.Batch407.certificate4894,MergedCutCells.Batch407.certificate4895,MergedCutCells.Batch408.certificate4896], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid674,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid675,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid676,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid677,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid678,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1460 : ∀ c∈certificate1460.cells, c.population=certificate1460.population := by
  change ∀ c∈[MergedCutCells.Batch407.certificate4892,MergedCutCells.Batch407.certificate4893,MergedCutCells.Batch407.certificate4894,MergedCutCells.Batch407.certificate4895,MergedCutCells.Batch408.certificate4896], c.population=PopulationCertificates.Batch049.certificate991
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1460 {x : ℝ} (hx : certificate1460.interval.Contains x) : ∃ c∈certificate1460.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1460 numericValid1460 hx

def certificate1461 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate992,PopulationCertificates.Batch049.certificate992,[MergedCutCells.Batch408.certificate4897,MergedCutCells.Batch408.certificate4898],(73916872007611759/125000000000000000),(some (280645331/250000000)),(1/2),(56691286696464663/250000000000000000),(some (23360827555466543/1000000000000000000)),(some (3513184410903341/1000000000000000000))⟩
theorem numericValid1461 : certificate1461.NumericValid := by decide +kernel
theorem cellsSound1461 : ∀ c∈certificate1461.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4897,MergedCutCells.Batch408.certificate4898], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4897,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4898,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1461 : ∀ c∈certificate1461.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4897,MergedCutCells.Batch408.certificate4898], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4897,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4898,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1461 : ∀ c∈certificate1461.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4897,MergedCutCells.Batch408.certificate4898], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid679,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid679,List.forall_mem_nil _⟩⟩
theorem populationMatches1461 : ∀ c∈certificate1461.cells, c.population=certificate1461.population := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4897,MergedCutCells.Batch408.certificate4898], c.population=PopulationCertificates.Batch049.certificate992
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1461 {x : ℝ} (hx : certificate1461.interval.Contains x) : ∃ c∈certificate1461.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1461 numericValid1461 hx

def certificate1462 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate992,PopulationCertificates.Batch049.certificate992,[MergedCutCells.Batch408.certificate4899,MergedCutCells.Batch408.certificate4900,MergedCutCells.Batch408.certificate4901],(280645331/250000000),none,(1/2),(45098171094319717/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1462 : certificate1462.NumericValid := by decide +kernel
theorem cellsSound1462 : ∀ c∈certificate1462.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4899,MergedCutCells.Batch408.certificate4900,MergedCutCells.Batch408.certificate4901], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4899,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4901,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1462 : ∀ c∈certificate1462.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4899,MergedCutCells.Batch408.certificate4900,MergedCutCells.Batch408.certificate4901], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4899,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4901,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1462 : ∀ c∈certificate1462.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4899,MergedCutCells.Batch408.certificate4900,MergedCutCells.Batch408.certificate4901], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1462 : ∀ c∈certificate1462.cells, c.population=certificate1462.population := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4899,MergedCutCells.Batch408.certificate4900,MergedCutCells.Batch408.certificate4901], c.population=PopulationCertificates.Batch049.certificate992
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1462 {x : ℝ} (hx : certificate1462.interval.Contains x) : ∃ c∈certificate1462.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1462 numericValid1462 hx

def certificate1463 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate993,PopulationCertificates.Batch049.certificate993,[MergedCutCells.Batch408.certificate4902,MergedCutCells.Batch408.certificate4903],(33687493866515866229/1000000000000000000),none,(1/2),(4203297056410273201/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1463 : certificate1463.NumericValid := by decide +kernel
theorem cellsSound1463 : ∀ c∈certificate1463.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4902,MergedCutCells.Batch408.certificate4903], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4902,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4903,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1463 : ∀ c∈certificate1463.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4902,MergedCutCells.Batch408.certificate4903], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4902,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4903,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1463 : ∀ c∈certificate1463.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4902,MergedCutCells.Batch408.certificate4903], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1463 : ∀ c∈certificate1463.cells, c.population=certificate1463.population := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4902,MergedCutCells.Batch408.certificate4903], c.population=PopulationCertificates.Batch049.certificate993
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1463 {x : ℝ} (hx : certificate1463.interval.Contains x) : ∃ c∈certificate1463.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1463 numericValid1463 hx

end Cycle12.MergedCutGroups.Batch121
