import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch052
import Cycle12.GeometryCertificates.Batch053
import Cycle12.MergedCutCells.Batch430
import Cycle12.MergedCutCells.Batch431
import Cycle12.MergedCutCells.Batch432
import Cycle12.MergedCutCells.Batch433
import Cycle12.PopulationCertificates.Batch052
import Cycle12.PopulationCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch129

def certificate1548 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1057,PopulationCertificates.Batch052.certificate1057,[MergedCutCells.Batch430.certificate5160,MergedCutCells.Batch430.certificate5161,MergedCutCells.Batch430.certificate5162,MergedCutCells.Batch430.certificate5163,MergedCutCells.Batch430.certificate5164],(386447588665718357/500000000000000000),none,(1/40),(24150381070529199/125000000000000000),none,none⟩
theorem numericValid1548 : certificate1548.NumericValid := by decide +kernel
theorem cellsSound1548 : ∀ c∈certificate1548.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5160,MergedCutCells.Batch430.certificate5161,MergedCutCells.Batch430.certificate5162,MergedCutCells.Batch430.certificate5163,MergedCutCells.Batch430.certificate5164], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5162,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5164,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1548 : ∀ c∈certificate1548.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5160,MergedCutCells.Batch430.certificate5161,MergedCutCells.Batch430.certificate5162,MergedCutCells.Batch430.certificate5163,MergedCutCells.Batch430.certificate5164], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5162,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5164,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1548 : ∀ c∈certificate1548.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5160,MergedCutCells.Batch430.certificate5161,MergedCutCells.Batch430.certificate5162,MergedCutCells.Batch430.certificate5163,MergedCutCells.Batch430.certificate5164], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid806,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid807,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid808,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid809,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid810,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1548 : ∀ c∈certificate1548.cells, c.population=certificate1548.population := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5160,MergedCutCells.Batch430.certificate5161,MergedCutCells.Batch430.certificate5162,MergedCutCells.Batch430.certificate5163,MergedCutCells.Batch430.certificate5164], c.population=PopulationCertificates.Batch052.certificate1057
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1548 {x : ℝ} (hx : certificate1548.interval.Contains x) : ∃ c∈certificate1548.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1548 numericValid1548 hx

def certificate1549 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1058,PopulationCertificates.Batch052.certificate1058,[MergedCutCells.Batch430.certificate5165,MergedCutCells.Batch430.certificate5166],(604055520014778331/1000000000000000000),(some (519724453/500000000)),(1/2),(161265461007240609/1000000000000000000),(some (46651843523187683/1000000000000000000)),(some (4005956938274481/500000000000000000))⟩
theorem numericValid1549 : certificate1549.NumericValid := by decide +kernel
theorem cellsSound1549 : ∀ c∈certificate1549.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5165,MergedCutCells.Batch430.certificate5166], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5166,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1549 : ∀ c∈certificate1549.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5165,MergedCutCells.Batch430.certificate5166], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5166,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1549 : ∀ c∈certificate1549.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5165,MergedCutCells.Batch430.certificate5166], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid811,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid811,List.forall_mem_nil _⟩⟩
theorem populationMatches1549 : ∀ c∈certificate1549.cells, c.population=certificate1549.population := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5165,MergedCutCells.Batch430.certificate5166], c.population=PopulationCertificates.Batch052.certificate1058
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1549 {x : ℝ} (hx : certificate1549.interval.Contains x) : ∃ c∈certificate1549.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1549 numericValid1549 hx

def certificate1550 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1058,PopulationCertificates.Batch052.certificate1058,[MergedCutCells.Batch430.certificate5167,MergedCutCells.Batch430.certificate5168,MergedCutCells.Batch430.certificate5169],(519724453/500000000),none,(1/2),(77275638077546707/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1550 : certificate1550.NumericValid := by decide +kernel
theorem cellsSound1550 : ∀ c∈certificate1550.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5167,MergedCutCells.Batch430.certificate5168,MergedCutCells.Batch430.certificate5169], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5167,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5169,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1550 : ∀ c∈certificate1550.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5167,MergedCutCells.Batch430.certificate5168,MergedCutCells.Batch430.certificate5169], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5167,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5169,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1550 : ∀ c∈certificate1550.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5167,MergedCutCells.Batch430.certificate5168,MergedCutCells.Batch430.certificate5169], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1550 : ∀ c∈certificate1550.cells, c.population=certificate1550.population := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5167,MergedCutCells.Batch430.certificate5168,MergedCutCells.Batch430.certificate5169], c.population=PopulationCertificates.Batch052.certificate1058
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1550 {x : ℝ} (hx : certificate1550.interval.Contains x) : ∃ c∈certificate1550.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1550 numericValid1550 hx

def certificate1551 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1059,PopulationCertificates.Batch052.certificate1059,[MergedCutCells.Batch430.certificate5170,MergedCutCells.Batch430.certificate5171],(53933615192920888281/1000000000000000000),none,(1/2),(647811240965192517/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1551 : certificate1551.NumericValid := by decide +kernel
theorem cellsSound1551 : ∀ c∈certificate1551.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5170,MergedCutCells.Batch430.certificate5171], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5170,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.sound5171,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1551 : ∀ c∈certificate1551.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5170,MergedCutCells.Batch430.certificate5171], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5170,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch430.numericValid5171,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1551 : ∀ c∈certificate1551.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5170,MergedCutCells.Batch430.certificate5171], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1551 : ∀ c∈certificate1551.cells, c.population=certificate1551.population := by
  change ∀ c∈[MergedCutCells.Batch430.certificate5170,MergedCutCells.Batch430.certificate5171], c.population=PopulationCertificates.Batch052.certificate1059
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1551 {x : ℝ} (hx : certificate1551.interval.Contains x) : ∃ c∈certificate1551.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1551 numericValid1551 hx

def certificate1552 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1060,PopulationCertificates.Batch053.certificate1060,[MergedCutCells.Batch431.certificate5172,MergedCutCells.Batch431.certificate5173,MergedCutCells.Batch431.certificate5174,MergedCutCells.Batch431.certificate5175,MergedCutCells.Batch431.certificate5176],(777288745070569103/1000000000000000000),none,(1/40),(41591880926219211/200000000000000000),none,none⟩
theorem numericValid1552 : certificate1552.NumericValid := by decide +kernel
theorem cellsSound1552 : ∀ c∈certificate1552.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5172,MergedCutCells.Batch431.certificate5173,MergedCutCells.Batch431.certificate5174,MergedCutCells.Batch431.certificate5175,MergedCutCells.Batch431.certificate5176], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5173,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5174,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5176,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1552 : ∀ c∈certificate1552.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5172,MergedCutCells.Batch431.certificate5173,MergedCutCells.Batch431.certificate5174,MergedCutCells.Batch431.certificate5175,MergedCutCells.Batch431.certificate5176], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5173,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5174,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5176,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1552 : ∀ c∈certificate1552.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5172,MergedCutCells.Batch431.certificate5173,MergedCutCells.Batch431.certificate5174,MergedCutCells.Batch431.certificate5175,MergedCutCells.Batch431.certificate5176], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid812,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid813,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid814,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid815,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid816,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1552 : ∀ c∈certificate1552.cells, c.population=certificate1552.population := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5172,MergedCutCells.Batch431.certificate5173,MergedCutCells.Batch431.certificate5174,MergedCutCells.Batch431.certificate5175,MergedCutCells.Batch431.certificate5176], c.population=PopulationCertificates.Batch053.certificate1060
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1552 {x : ℝ} (hx : certificate1552.interval.Contains x) : ∃ c∈certificate1552.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1552 numericValid1552 hx

def certificate1553 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1061,PopulationCertificates.Batch053.certificate1061,[MergedCutCells.Batch431.certificate5177,MergedCutCells.Batch431.certificate5178],(151271012462474691/250000000000000000),(some (1015652327/1000000000)),(1/2),(81107137342049821/500000000000000000),(some (23889622821484249/500000000000000000)),(some (8246585990984411/1000000000000000000))⟩
theorem numericValid1553 : certificate1553.NumericValid := by decide +kernel
theorem cellsSound1553 : ∀ c∈certificate1553.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5177,MergedCutCells.Batch431.certificate5178], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5178,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1553 : ∀ c∈certificate1553.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5177,MergedCutCells.Batch431.certificate5178], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5178,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1553 : ∀ c∈certificate1553.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5177,MergedCutCells.Batch431.certificate5178], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid817,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid817,List.forall_mem_nil _⟩⟩
theorem populationMatches1553 : ∀ c∈certificate1553.cells, c.population=certificate1553.population := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5177,MergedCutCells.Batch431.certificate5178], c.population=PopulationCertificates.Batch053.certificate1061
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1553 {x : ℝ} (hx : certificate1553.interval.Contains x) : ∃ c∈certificate1553.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1553 numericValid1553 hx

def certificate1554 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1061,PopulationCertificates.Batch053.certificate1061,[MergedCutCells.Batch431.certificate5179,MergedCutCells.Batch431.certificate5180,MergedCutCells.Batch431.certificate5181,MergedCutCells.Batch431.certificate5182],(1015652327/1000000000),none,(1/2),(15908937905094367/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1554 : certificate1554.NumericValid := by decide +kernel
theorem cellsSound1554 : ∀ c∈certificate1554.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5179,MergedCutCells.Batch431.certificate5180,MergedCutCells.Batch431.certificate5181,MergedCutCells.Batch431.certificate5182], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5182,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1554 : ∀ c∈certificate1554.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5179,MergedCutCells.Batch431.certificate5180,MergedCutCells.Batch431.certificate5181,MergedCutCells.Batch431.certificate5182], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5182,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1554 : ∀ c∈certificate1554.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5179,MergedCutCells.Batch431.certificate5180,MergedCutCells.Batch431.certificate5181,MergedCutCells.Batch431.certificate5182], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1554 : ∀ c∈certificate1554.cells, c.population=certificate1554.population := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5179,MergedCutCells.Batch431.certificate5180,MergedCutCells.Batch431.certificate5181,MergedCutCells.Batch431.certificate5182], c.population=PopulationCertificates.Batch053.certificate1061
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1554 {x : ℝ} (hx : certificate1554.interval.Contains x) : ∃ c∈certificate1554.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1554 numericValid1554 hx

def certificate1555 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1062,PopulationCertificates.Batch053.certificate1062,[MergedCutCells.Batch431.certificate5183,MergedCutCells.Batch432.certificate5184],(27615565224615491981/500000000000000000),none,(1/2),(25897162080199761/1953125000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1555 : certificate1555.NumericValid := by decide +kernel
theorem cellsSound1555 : ∀ c∈certificate1555.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5183,MergedCutCells.Batch432.certificate5184], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.sound5183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5184,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1555 : ∀ c∈certificate1555.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5183,MergedCutCells.Batch432.certificate5184], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch431.numericValid5183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5184,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1555 : ∀ c∈certificate1555.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5183,MergedCutCells.Batch432.certificate5184], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1555 : ∀ c∈certificate1555.cells, c.population=certificate1555.population := by
  change ∀ c∈[MergedCutCells.Batch431.certificate5183,MergedCutCells.Batch432.certificate5184], c.population=PopulationCertificates.Batch053.certificate1062
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1555 {x : ℝ} (hx : certificate1555.interval.Contains x) : ∃ c∈certificate1555.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1555 numericValid1555 hx

def certificate1556 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1063,PopulationCertificates.Batch053.certificate1063,[MergedCutCells.Batch432.certificate5185,MergedCutCells.Batch432.certificate5186,MergedCutCells.Batch432.certificate5187,MergedCutCells.Batch432.certificate5188,MergedCutCells.Batch432.certificate5189],(195393481198331639/250000000000000000),none,(1/40),(223674551052766899/1000000000000000000),none,none⟩
theorem numericValid1556 : certificate1556.NumericValid := by decide +kernel
theorem cellsSound1556 : ∀ c∈certificate1556.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5185,MergedCutCells.Batch432.certificate5186,MergedCutCells.Batch432.certificate5187,MergedCutCells.Batch432.certificate5188,MergedCutCells.Batch432.certificate5189], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5185,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5186,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5187,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5189,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1556 : ∀ c∈certificate1556.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5185,MergedCutCells.Batch432.certificate5186,MergedCutCells.Batch432.certificate5187,MergedCutCells.Batch432.certificate5188,MergedCutCells.Batch432.certificate5189], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5185,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5186,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5187,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5189,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1556 : ∀ c∈certificate1556.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5185,MergedCutCells.Batch432.certificate5186,MergedCutCells.Batch432.certificate5187,MergedCutCells.Batch432.certificate5188,MergedCutCells.Batch432.certificate5189], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid818,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid819,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid820,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid821,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid822,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1556 : ∀ c∈certificate1556.cells, c.population=certificate1556.population := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5185,MergedCutCells.Batch432.certificate5186,MergedCutCells.Batch432.certificate5187,MergedCutCells.Batch432.certificate5188,MergedCutCells.Batch432.certificate5189], c.population=PopulationCertificates.Batch053.certificate1063
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1556 {x : ℝ} (hx : certificate1556.interval.Contains x) : ∃ c∈certificate1556.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1556 numericValid1556 hx

def certificate1557 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1064,PopulationCertificates.Batch053.certificate1064,[MergedCutCells.Batch432.certificate5190,MergedCutCells.Batch432.certificate5191],(607350989989147791/1000000000000000000),(some (509516981/500000000)),(1/2),(42398842930509253/250000000000000000),(some (49144938533520913/1000000000000000000)),(some (2133188033172489/250000000000000000))⟩
theorem numericValid1557 : certificate1557.NumericValid := by decide +kernel
theorem cellsSound1557 : ∀ c∈certificate1557.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5190,MergedCutCells.Batch432.certificate5191], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5191,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1557 : ∀ c∈certificate1557.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5190,MergedCutCells.Batch432.certificate5191], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5191,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1557 : ∀ c∈certificate1557.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5190,MergedCutCells.Batch432.certificate5191], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid823,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy041.valid823,List.forall_mem_nil _⟩⟩
theorem populationMatches1557 : ∀ c∈certificate1557.cells, c.population=certificate1557.population := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5190,MergedCutCells.Batch432.certificate5191], c.population=PopulationCertificates.Batch053.certificate1064
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1557 {x : ℝ} (hx : certificate1557.interval.Contains x) : ∃ c∈certificate1557.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1557 numericValid1557 hx

def certificate1558 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1064,PopulationCertificates.Batch053.certificate1064,[MergedCutCells.Batch432.certificate5192,MergedCutCells.Batch432.certificate5193,MergedCutCells.Batch432.certificate5194],(509516981/500000000),none,(1/2),(164964798857652981/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1558 : certificate1558.NumericValid := by decide +kernel
theorem cellsSound1558 : ∀ c∈certificate1558.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5192,MergedCutCells.Batch432.certificate5193,MergedCutCells.Batch432.certificate5194], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5192,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5194,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1558 : ∀ c∈certificate1558.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5192,MergedCutCells.Batch432.certificate5193,MergedCutCells.Batch432.certificate5194], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5192,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5194,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1558 : ∀ c∈certificate1558.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5192,MergedCutCells.Batch432.certificate5193,MergedCutCells.Batch432.certificate5194], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1558 : ∀ c∈certificate1558.cells, c.population=certificate1558.population := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5192,MergedCutCells.Batch432.certificate5193,MergedCutCells.Batch432.certificate5194], c.population=PopulationCertificates.Batch053.certificate1064
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1558 {x : ℝ} (hx : certificate1558.interval.Contains x) : ∃ c∈certificate1558.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1558 numericValid1558 hx

def certificate1559 : RatCutGroup := ⟨GeometryCertificates.Batch053.certificate1065,PopulationCertificates.Batch053.certificate1065,[MergedCutCells.Batch432.certificate5195,MergedCutCells.Batch433.certificate5196],(56572755757340626393/1000000000000000000),none,(1/2),(13572631670586502881/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1559 : certificate1559.NumericValid := by decide +kernel
theorem cellsSound1559 : ∀ c∈certificate1559.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5195,MergedCutCells.Batch433.certificate5196], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.sound5195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.sound5196,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1559 : ∀ c∈certificate1559.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5195,MergedCutCells.Batch433.certificate5196], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch432.numericValid5195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch433.numericValid5196,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1559 : ∀ c∈certificate1559.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5195,MergedCutCells.Batch433.certificate5196], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1559 : ∀ c∈certificate1559.cells, c.population=certificate1559.population := by
  change ∀ c∈[MergedCutCells.Batch432.certificate5195,MergedCutCells.Batch433.certificate5196], c.population=PopulationCertificates.Batch053.certificate1065
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1559 {x : ℝ} (hx : certificate1559.interval.Contains x) : ∃ c∈certificate1559.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1559 numericValid1559 hx

end Cycle12.MergedCutGroups.Batch129
