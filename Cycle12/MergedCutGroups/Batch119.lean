import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch048
import Cycle12.MergedCutCells.Batch400
import Cycle12.MergedCutCells.Batch401
import Cycle12.MergedCutCells.Batch402
import Cycle12.PopulationCertificates.Batch048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch119

def certificate1428 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate967,PopulationCertificates.Batch048.certificate967,[MergedCutCells.Batch400.certificate4803,MergedCutCells.Batch400.certificate4804,MergedCutCells.Batch400.certificate4805,MergedCutCells.Batch400.certificate4806],(342846035099422087/500000000000000000),none,(1/40),(10381772330787101/500000000000000000),none,none⟩
theorem numericValid1428 : certificate1428.NumericValid := by decide +kernel
theorem cellsSound1428 : ∀ c∈certificate1428.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4803,MergedCutCells.Batch400.certificate4804,MergedCutCells.Batch400.certificate4805,MergedCutCells.Batch400.certificate4806], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4804,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4806,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1428 : ∀ c∈certificate1428.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4803,MergedCutCells.Batch400.certificate4804,MergedCutCells.Batch400.certificate4805,MergedCutCells.Batch400.certificate4806], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4804,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4806,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1428 : ∀ c∈certificate1428.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4803,MergedCutCells.Batch400.certificate4804,MergedCutCells.Batch400.certificate4805,MergedCutCells.Batch400.certificate4806], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid633,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid634,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid635,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid636,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1428 : ∀ c∈certificate1428.cells, c.population=certificate1428.population := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4803,MergedCutCells.Batch400.certificate4804,MergedCutCells.Batch400.certificate4805,MergedCutCells.Batch400.certificate4806], c.population=PopulationCertificates.Batch048.certificate967
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1428 {x : ℝ} (hx : certificate1428.interval.Contains x) : ∃ c∈certificate1428.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1428 numericValid1428 hx

def certificate1429 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate968,PopulationCertificates.Batch048.certificate968,[MergedCutCells.Batch400.certificate4807,MergedCutCells.Batch400.certificate4808],(72828247479816877/125000000000000000),(some (113208361/100000000)),(1/2),(26265866917233499/125000000000000000),(some (9538440531199097/500000000000000000)),(some (2769735994194639/1000000000000000000))⟩
theorem numericValid1429 : certificate1429.NumericValid := by decide +kernel
theorem cellsSound1429 : ∀ c∈certificate1429.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4807,MergedCutCells.Batch400.certificate4808], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4808,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1429 : ∀ c∈certificate1429.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4807,MergedCutCells.Batch400.certificate4808], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4808,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1429 : ∀ c∈certificate1429.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4807,MergedCutCells.Batch400.certificate4808], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid637,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid637,List.forall_mem_nil _⟩⟩
theorem populationMatches1429 : ∀ c∈certificate1429.cells, c.population=certificate1429.population := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4807,MergedCutCells.Batch400.certificate4808], c.population=PopulationCertificates.Batch048.certificate968
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1429 {x : ℝ} (hx : certificate1429.interval.Contains x) : ∃ c∈certificate1429.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1429 numericValid1429 hx

def certificate1430 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate968,PopulationCertificates.Batch048.certificate968,[MergedCutCells.Batch400.certificate4809,MergedCutCells.Batch400.certificate4810,MergedCutCells.Batch400.certificate4811],(113208361/100000000),none,(1/2),(104494671041801989/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1430 : certificate1430.NumericValid := by decide +kernel
theorem cellsSound1430 : ∀ c∈certificate1430.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4809,MergedCutCells.Batch400.certificate4810,MergedCutCells.Batch400.certificate4811], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4809,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4810,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4811,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1430 : ∀ c∈certificate1430.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4809,MergedCutCells.Batch400.certificate4810,MergedCutCells.Batch400.certificate4811], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4809,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4810,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4811,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1430 : ∀ c∈certificate1430.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4809,MergedCutCells.Batch400.certificate4810,MergedCutCells.Batch400.certificate4811], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1430 : ∀ c∈certificate1430.cells, c.population=certificate1430.population := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4809,MergedCutCells.Batch400.certificate4810,MergedCutCells.Batch400.certificate4811], c.population=PopulationCertificates.Batch048.certificate968
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1430 {x : ℝ} (hx : certificate1430.interval.Contains x) : ∃ c∈certificate1430.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1430 numericValid1430 hx

def certificate1431 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate969,PopulationCertificates.Batch048.certificate969,[MergedCutCells.Batch401.certificate4812,MergedCutCells.Batch401.certificate4813],(30810454878883848783/1000000000000000000),none,(1/2),(7672577332344680001/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1431 : certificate1431.NumericValid := by decide +kernel
theorem cellsSound1431 : ∀ c∈certificate1431.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4812,MergedCutCells.Batch401.certificate4813], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4812,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4813,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1431 : ∀ c∈certificate1431.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4812,MergedCutCells.Batch401.certificate4813], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4812,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4813,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1431 : ∀ c∈certificate1431.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4812,MergedCutCells.Batch401.certificate4813], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1431 : ∀ c∈certificate1431.cells, c.population=certificate1431.population := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4812,MergedCutCells.Batch401.certificate4813], c.population=PopulationCertificates.Batch048.certificate969
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1431 {x : ℝ} (hx : certificate1431.interval.Contains x) : ∃ c∈certificate1431.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1431 numericValid1431 hx

def certificate1432 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate970,PopulationCertificates.Batch048.certificate970,[MergedCutCells.Batch401.certificate4814,MergedCutCells.Batch401.certificate4815,MergedCutCells.Batch401.certificate4816,MergedCutCells.Batch401.certificate4817],(1716526364981673/2500000000000000),none,(1/40),(684555967785001/31250000000000000),none,none⟩
theorem numericValid1432 : certificate1432.NumericValid := by decide +kernel
theorem cellsSound1432 : ∀ c∈certificate1432.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4814,MergedCutCells.Batch401.certificate4815,MergedCutCells.Batch401.certificate4816,MergedCutCells.Batch401.certificate4817], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4814,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4815,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4817,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1432 : ∀ c∈certificate1432.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4814,MergedCutCells.Batch401.certificate4815,MergedCutCells.Batch401.certificate4816,MergedCutCells.Batch401.certificate4817], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4814,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4815,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4817,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1432 : ∀ c∈certificate1432.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4814,MergedCutCells.Batch401.certificate4815,MergedCutCells.Batch401.certificate4816,MergedCutCells.Batch401.certificate4817], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid638,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid639,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid640,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid641,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1432 : ∀ c∈certificate1432.cells, c.population=certificate1432.population := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4814,MergedCutCells.Batch401.certificate4815,MergedCutCells.Batch401.certificate4816,MergedCutCells.Batch401.certificate4817], c.population=PopulationCertificates.Batch048.certificate970
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1432 {x : ℝ} (hx : certificate1432.interval.Contains x) : ∃ c∈certificate1432.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1432 numericValid1432 hx

def certificate1433 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate971,PopulationCertificates.Batch048.certificate971,[MergedCutCells.Batch401.certificate4818,MergedCutCells.Batch401.certificate4819],(583082661085296447/1000000000000000000),(some (1132845493/1000000000)),(1/2),(211474694168336629/1000000000000000000),(some (4796308662541193/250000000000000000)),(some (1394077191111319/500000000000000000))⟩
theorem numericValid1433 : certificate1433.NumericValid := by decide +kernel
theorem cellsSound1433 : ∀ c∈certificate1433.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4818,MergedCutCells.Batch401.certificate4819], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4818,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4819,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1433 : ∀ c∈certificate1433.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4818,MergedCutCells.Batch401.certificate4819], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4818,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4819,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1433 : ∀ c∈certificate1433.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4818,MergedCutCells.Batch401.certificate4819], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid642,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid642,List.forall_mem_nil _⟩⟩
theorem populationMatches1433 : ∀ c∈certificate1433.cells, c.population=certificate1433.population := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4818,MergedCutCells.Batch401.certificate4819], c.population=PopulationCertificates.Batch048.certificate971
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1433 {x : ℝ} (hx : certificate1433.interval.Contains x) : ∃ c∈certificate1433.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1433 numericValid1433 hx

def certificate1434 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate971,PopulationCertificates.Batch048.certificate971,[MergedCutCells.Batch401.certificate4820,MergedCutCells.Batch401.certificate4821,MergedCutCells.Batch401.certificate4822],(1132845493/1000000000),none,(1/2),(42062414108788971/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1434 : certificate1434.NumericValid := by decide +kernel
theorem cellsSound1434 : ∀ c∈certificate1434.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4820,MergedCutCells.Batch401.certificate4821,MergedCutCells.Batch401.certificate4822], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4820,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4821,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4822,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1434 : ∀ c∈certificate1434.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4820,MergedCutCells.Batch401.certificate4821,MergedCutCells.Batch401.certificate4822], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4820,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4821,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4822,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1434 : ∀ c∈certificate1434.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4820,MergedCutCells.Batch401.certificate4821,MergedCutCells.Batch401.certificate4822], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1434 : ∀ c∈certificate1434.cells, c.population=certificate1434.population := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4820,MergedCutCells.Batch401.certificate4821,MergedCutCells.Batch401.certificate4822], c.population=PopulationCertificates.Batch048.certificate971
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1434 {x : ℝ} (hx : certificate1434.interval.Contains x) : ∃ c∈certificate1434.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1434 numericValid1434 hx

def certificate1435 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate972,PopulationCertificates.Batch048.certificate972,[MergedCutCells.Batch401.certificate4823,MergedCutCells.Batch402.certificate4824],(30961511562218037573/1000000000000000000),none,(1/2),(7712236943092629969/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1435 : certificate1435.NumericValid := by decide +kernel
theorem cellsSound1435 : ∀ c∈certificate1435.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4823,MergedCutCells.Batch402.certificate4824], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.sound4823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4824,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1435 : ∀ c∈certificate1435.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4823,MergedCutCells.Batch402.certificate4824], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch401.numericValid4823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4824,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1435 : ∀ c∈certificate1435.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4823,MergedCutCells.Batch402.certificate4824], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1435 : ∀ c∈certificate1435.cells, c.population=certificate1435.population := by
  change ∀ c∈[MergedCutCells.Batch401.certificate4823,MergedCutCells.Batch402.certificate4824], c.population=PopulationCertificates.Batch048.certificate972
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1435 {x : ℝ} (hx : certificate1435.interval.Contains x) : ∃ c∈certificate1435.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1435 numericValid1435 hx

def certificate1436 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate973,PopulationCertificates.Batch048.certificate973,[MergedCutCells.Batch402.certificate4825,MergedCutCells.Batch402.certificate4826,MergedCutCells.Batch402.certificate4827,MergedCutCells.Batch402.certificate4828],(687556930704073633/1000000000000000000),none,(1/40),(2915341450777913/125000000000000000),none,none⟩
theorem numericValid1436 : certificate1436.NumericValid := by decide +kernel
theorem cellsSound1436 : ∀ c∈certificate1436.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4825,MergedCutCells.Batch402.certificate4826,MergedCutCells.Batch402.certificate4827,MergedCutCells.Batch402.certificate4828], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4825,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4826,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4827,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4828,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1436 : ∀ c∈certificate1436.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4825,MergedCutCells.Batch402.certificate4826,MergedCutCells.Batch402.certificate4827,MergedCutCells.Batch402.certificate4828], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4825,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4826,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4827,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4828,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1436 : ∀ c∈certificate1436.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4825,MergedCutCells.Batch402.certificate4826,MergedCutCells.Batch402.certificate4827,MergedCutCells.Batch402.certificate4828], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid643,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid644,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid645,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid646,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1436 : ∀ c∈certificate1436.cells, c.population=certificate1436.population := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4825,MergedCutCells.Batch402.certificate4826,MergedCutCells.Batch402.certificate4827,MergedCutCells.Batch402.certificate4828], c.population=PopulationCertificates.Batch048.certificate973
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1436 {x : ℝ} (hx : certificate1436.interval.Contains x) : ∃ c∈certificate1436.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1436 numericValid1436 hx

def certificate1437 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate974,PopulationCertificates.Batch048.certificate974,[MergedCutCells.Batch402.certificate4829,MergedCutCells.Batch402.certificate4830],(145830409352181873/250000000000000000),(some (226648829/200000000)),(1/2),(42349265248372261/200000000000000000),(some (19295619021985807/1000000000000000000)),(some (2806939333681323/1000000000000000000))⟩
theorem numericValid1437 : certificate1437.NumericValid := by decide +kernel
theorem cellsSound1437 : ∀ c∈certificate1437.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4829,MergedCutCells.Batch402.certificate4830], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4829,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4830,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1437 : ∀ c∈certificate1437.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4829,MergedCutCells.Batch402.certificate4830], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4829,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4830,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1437 : ∀ c∈certificate1437.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4829,MergedCutCells.Batch402.certificate4830], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid647,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid647,List.forall_mem_nil _⟩⟩
theorem populationMatches1437 : ∀ c∈certificate1437.cells, c.population=certificate1437.population := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4829,MergedCutCells.Batch402.certificate4830], c.population=PopulationCertificates.Batch048.certificate974
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1437 {x : ℝ} (hx : certificate1437.interval.Contains x) : ∃ c∈certificate1437.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1437 numericValid1437 hx

def certificate1438 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate974,PopulationCertificates.Batch048.certificate974,[MergedCutCells.Batch402.certificate4831,MergedCutCells.Batch402.certificate4832,MergedCutCells.Batch402.certificate4833],(226648829/200000000),none,(1/2),(210773030626352619/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1438 : certificate1438.NumericValid := by decide +kernel
theorem cellsSound1438 : ∀ c∈certificate1438.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4831,MergedCutCells.Batch402.certificate4832,MergedCutCells.Batch402.certificate4833], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4831,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4832,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4833,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1438 : ∀ c∈certificate1438.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4831,MergedCutCells.Batch402.certificate4832,MergedCutCells.Batch402.certificate4833], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4831,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4832,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4833,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1438 : ∀ c∈certificate1438.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4831,MergedCutCells.Batch402.certificate4832,MergedCutCells.Batch402.certificate4833], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1438 : ∀ c∈certificate1438.cells, c.population=certificate1438.population := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4831,MergedCutCells.Batch402.certificate4832,MergedCutCells.Batch402.certificate4833], c.population=PopulationCertificates.Batch048.certificate974
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1438 {x : ℝ} (hx : certificate1438.interval.Contains x) : ∃ c∈certificate1438.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1438 numericValid1438 hx

def certificate1439 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate975,PopulationCertificates.Batch048.certificate975,[MergedCutCells.Batch402.certificate4834,MergedCutCells.Batch402.certificate4835],(15518687270840378127/500000000000000000),none,(1/2),(3865872785490823637/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1439 : certificate1439.NumericValid := by decide +kernel
theorem cellsSound1439 : ∀ c∈certificate1439.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4834,MergedCutCells.Batch402.certificate4835], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4834,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.sound4835,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1439 : ∀ c∈certificate1439.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4834,MergedCutCells.Batch402.certificate4835], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4834,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch402.numericValid4835,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1439 : ∀ c∈certificate1439.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4834,MergedCutCells.Batch402.certificate4835], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1439 : ∀ c∈certificate1439.cells, c.population=certificate1439.population := by
  change ∀ c∈[MergedCutCells.Batch402.certificate4834,MergedCutCells.Batch402.certificate4835], c.population=PopulationCertificates.Batch048.certificate975
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1439 {x : ℝ} (hx : certificate1439.interval.Contains x) : ∃ c∈certificate1439.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1439 numericValid1439 hx

end Cycle12.MergedCutGroups.Batch119
