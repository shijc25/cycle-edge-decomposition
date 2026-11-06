import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch052
import Cycle12.MergedCutCells.Batch426
import Cycle12.MergedCutCells.Batch427
import Cycle12.MergedCutCells.Batch428
import Cycle12.MergedCutCells.Batch429
import Cycle12.PopulationCertificates.Batch052

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch128

def certificate1536 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1048,PopulationCertificates.Batch052.certificate1048,[MergedCutCells.Batch426.certificate5123,MergedCutCells.Batch427.certificate5124,MergedCutCells.Batch427.certificate5125,MergedCutCells.Batch427.certificate5126,MergedCutCells.Batch427.certificate5127],(2375616412030897/3125000000000000),none,(1/40),(76583595893440821/500000000000000000),none,none⟩
theorem numericValid1536 : certificate1536.NumericValid := by decide +kernel
theorem cellsSound1536 : ∀ c∈certificate1536.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5123,MergedCutCells.Batch427.certificate5124,MergedCutCells.Batch427.certificate5125,MergedCutCells.Batch427.certificate5126,MergedCutCells.Batch427.certificate5127], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.sound5123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5124,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5126,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5127,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1536 : ∀ c∈certificate1536.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5123,MergedCutCells.Batch427.certificate5124,MergedCutCells.Batch427.certificate5125,MergedCutCells.Batch427.certificate5126,MergedCutCells.Batch427.certificate5127], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch426.numericValid5123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5124,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5126,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5127,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1536 : ∀ c∈certificate1536.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5123,MergedCutCells.Batch427.certificate5124,MergedCutCells.Batch427.certificate5125,MergedCutCells.Batch427.certificate5126,MergedCutCells.Batch427.certificate5127], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid788,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid789,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid790,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid791,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid792,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1536 : ∀ c∈certificate1536.cells, c.population=certificate1536.population := by
  change ∀ c∈[MergedCutCells.Batch426.certificate5123,MergedCutCells.Batch427.certificate5124,MergedCutCells.Batch427.certificate5125,MergedCutCells.Batch427.certificate5126,MergedCutCells.Batch427.certificate5127], c.population=PopulationCertificates.Batch052.certificate1048
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1536 {x : ℝ} (hx : certificate1536.interval.Contains x) : ∃ c∈certificate1536.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1536 numericValid1536 hx

def certificate1537 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1049,PopulationCertificates.Batch052.certificate1049,[MergedCutCells.Batch427.certificate5128,MergedCutCells.Batch427.certificate5129],(74670943681314867/125000000000000000),(some (525945823/500000000)),(1/2),(143805437733167161/1000000000000000000),(some (42794278483209717/1000000000000000000)),(some (7219858902679457/1000000000000000000))⟩
theorem numericValid1537 : certificate1537.NumericValid := by decide +kernel
theorem cellsSound1537 : ∀ c∈certificate1537.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5128,MergedCutCells.Batch427.certificate5129], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5128,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5129,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1537 : ∀ c∈certificate1537.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5128,MergedCutCells.Batch427.certificate5129], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5128,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5129,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1537 : ∀ c∈certificate1537.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5128,MergedCutCells.Batch427.certificate5129], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid793,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid793,List.forall_mem_nil _⟩⟩
theorem populationMatches1537 : ∀ c∈certificate1537.cells, c.population=certificate1537.population := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5128,MergedCutCells.Batch427.certificate5129], c.population=PopulationCertificates.Batch052.certificate1049
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1537 {x : ℝ} (hx : certificate1537.interval.Contains x) : ∃ c∈certificate1537.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1537 numericValid1537 hx

def certificate1538 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1049,PopulationCertificates.Batch052.certificate1049,[MergedCutCells.Batch427.certificate5130,MergedCutCells.Batch427.certificate5131,MergedCutCells.Batch427.certificate5132],(525945823/500000000),none,(1/2),(35022292632953347/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1538 : certificate1538.NumericValid := by decide +kernel
theorem cellsSound1538 : ∀ c∈certificate1538.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5130,MergedCutCells.Batch427.certificate5131,MergedCutCells.Batch427.certificate5132], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5130,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5132,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1538 : ∀ c∈certificate1538.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5130,MergedCutCells.Batch427.certificate5131,MergedCutCells.Batch427.certificate5132], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5130,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5132,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1538 : ∀ c∈certificate1538.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5130,MergedCutCells.Batch427.certificate5131,MergedCutCells.Batch427.certificate5132], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1538 : ∀ c∈certificate1538.cells, c.population=certificate1538.population := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5130,MergedCutCells.Batch427.certificate5131,MergedCutCells.Batch427.certificate5132], c.population=PopulationCertificates.Batch052.certificate1049
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1538 {x : ℝ} (hx : certificate1538.interval.Contains x) : ∃ c∈certificate1538.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1538 numericValid1538 hx

def certificate1539 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1050,PopulationCertificates.Batch052.certificate1050,[MergedCutCells.Batch427.certificate5133,MergedCutCells.Batch427.certificate5134],(50287791709272955471/1000000000000000000),none,(1/2),(3025871109378247983/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1539 : certificate1539.NumericValid := by decide +kernel
theorem cellsSound1539 : ∀ c∈certificate1539.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5133,MergedCutCells.Batch427.certificate5134], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5134,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1539 : ∀ c∈certificate1539.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5133,MergedCutCells.Batch427.certificate5134], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5134,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1539 : ∀ c∈certificate1539.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5133,MergedCutCells.Batch427.certificate5134], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1539 : ∀ c∈certificate1539.cells, c.population=certificate1539.population := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5133,MergedCutCells.Batch427.certificate5134], c.population=PopulationCertificates.Batch052.certificate1050
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1539 {x : ℝ} (hx : certificate1539.interval.Contains x) : ∃ c∈certificate1539.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1539 numericValid1539 hx

def certificate1540 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1051,PopulationCertificates.Batch052.certificate1051,[MergedCutCells.Batch427.certificate5135,MergedCutCells.Batch428.certificate5136,MergedCutCells.Batch428.certificate5137,MergedCutCells.Batch428.certificate5138,MergedCutCells.Batch428.certificate5139],(76440453437701569/100000000000000000),none,(1/40),(8293162832424177/50000000000000000),none,none⟩
theorem numericValid1540 : certificate1540.NumericValid := by decide +kernel
theorem cellsSound1540 : ∀ c∈certificate1540.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5135,MergedCutCells.Batch428.certificate5136,MergedCutCells.Batch428.certificate5137,MergedCutCells.Batch428.certificate5138,MergedCutCells.Batch428.certificate5139], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.sound5135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5137,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5138,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5139,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1540 : ∀ c∈certificate1540.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5135,MergedCutCells.Batch428.certificate5136,MergedCutCells.Batch428.certificate5137,MergedCutCells.Batch428.certificate5138,MergedCutCells.Batch428.certificate5139], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch427.numericValid5135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5137,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5138,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5139,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1540 : ∀ c∈certificate1540.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5135,MergedCutCells.Batch428.certificate5136,MergedCutCells.Batch428.certificate5137,MergedCutCells.Batch428.certificate5138,MergedCutCells.Batch428.certificate5139], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid794,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid795,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid796,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid797,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid798,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1540 : ∀ c∈certificate1540.cells, c.population=certificate1540.population := by
  change ∀ c∈[MergedCutCells.Batch427.certificate5135,MergedCutCells.Batch428.certificate5136,MergedCutCells.Batch428.certificate5137,MergedCutCells.Batch428.certificate5138,MergedCutCells.Batch428.certificate5139], c.population=PopulationCertificates.Batch052.certificate1051
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1540 {x : ℝ} (hx : certificate1540.interval.Contains x) : ∃ c∈certificate1540.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1540 numericValid1540 hx

def certificate1541 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1052,PopulationCertificates.Batch052.certificate1052,[MergedCutCells.Batch428.certificate5140,MergedCutCells.Batch428.certificate5141],(11986416775646551/20000000000000000),(some (64331063/62500000)),(1/2),(148525990007218261/1000000000000000000),(some (877340411601773/20000000000000000)),(some (7438403219436779/1000000000000000000))⟩
theorem numericValid1541 : certificate1541.NumericValid := by decide +kernel
theorem cellsSound1541 : ∀ c∈certificate1541.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5140,MergedCutCells.Batch428.certificate5141], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5141,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1541 : ∀ c∈certificate1541.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5140,MergedCutCells.Batch428.certificate5141], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5141,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1541 : ∀ c∈certificate1541.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5140,MergedCutCells.Batch428.certificate5141], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid799,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy039.valid799,List.forall_mem_nil _⟩⟩
theorem populationMatches1541 : ∀ c∈certificate1541.cells, c.population=certificate1541.population := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5140,MergedCutCells.Batch428.certificate5141], c.population=PopulationCertificates.Batch052.certificate1052
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1541 {x : ℝ} (hx : certificate1541.interval.Contains x) : ∃ c∈certificate1541.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1541 numericValid1541 hx

def certificate1542 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1052,PopulationCertificates.Batch052.certificate1052,[MergedCutCells.Batch428.certificate5142,MergedCutCells.Batch428.certificate5143,MergedCutCells.Batch428.certificate5144,MergedCutCells.Batch428.certificate5145],(64331063/62500000),none,(1/2),(18089728146670129/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1542 : certificate1542.NumericValid := by decide +kernel
theorem cellsSound1542 : ∀ c∈certificate1542.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5142,MergedCutCells.Batch428.certificate5143,MergedCutCells.Batch428.certificate5144,MergedCutCells.Batch428.certificate5145], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5143,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5145,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1542 : ∀ c∈certificate1542.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5142,MergedCutCells.Batch428.certificate5143,MergedCutCells.Batch428.certificate5144,MergedCutCells.Batch428.certificate5145], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5143,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5145,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1542 : ∀ c∈certificate1542.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5142,MergedCutCells.Batch428.certificate5143,MergedCutCells.Batch428.certificate5144,MergedCutCells.Batch428.certificate5145], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1542 : ∀ c∈certificate1542.cells, c.population=certificate1542.population := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5142,MergedCutCells.Batch428.certificate5143,MergedCutCells.Batch428.certificate5144,MergedCutCells.Batch428.certificate5145], c.population=PopulationCertificates.Batch052.certificate1052
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1542 {x : ℝ} (hx : certificate1542.interval.Contains x) : ∃ c∈certificate1542.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1542 numericValid1542 hx

def certificate1543 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1053,PopulationCertificates.Batch052.certificate1053,[MergedCutCells.Batch428.certificate5146,MergedCutCells.Batch428.certificate5147],(5146365471236872331/100000000000000000),none,(1/2),(1547768005154936777/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1543 : certificate1543.NumericValid := by decide +kernel
theorem cellsSound1543 : ∀ c∈certificate1543.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5146,MergedCutCells.Batch428.certificate5147], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.sound5147,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1543 : ∀ c∈certificate1543.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5146,MergedCutCells.Batch428.certificate5147], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch428.numericValid5147,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1543 : ∀ c∈certificate1543.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5146,MergedCutCells.Batch428.certificate5147], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1543 : ∀ c∈certificate1543.cells, c.population=certificate1543.population := by
  change ∀ c∈[MergedCutCells.Batch428.certificate5146,MergedCutCells.Batch428.certificate5147], c.population=PopulationCertificates.Batch052.certificate1053
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1543 {x : ℝ} (hx : certificate1543.interval.Contains x) : ∃ c∈certificate1543.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1543 numericValid1543 hx

def certificate1544 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1054,PopulationCertificates.Batch052.certificate1054,[MergedCutCells.Batch429.certificate5148,MergedCutCells.Batch429.certificate5149,MergedCutCells.Batch429.certificate5150,MergedCutCells.Batch429.certificate5151,MergedCutCells.Batch429.certificate5152],(768636558961092541/1000000000000000000),none,(1/40),(179198467681091611/1000000000000000000),none,none⟩
theorem numericValid1544 : certificate1544.NumericValid := by decide +kernel
theorem cellsSound1544 : ∀ c∈certificate1544.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5148,MergedCutCells.Batch429.certificate5149,MergedCutCells.Batch429.certificate5150,MergedCutCells.Batch429.certificate5151,MergedCutCells.Batch429.certificate5152], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5150,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5151,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5152,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1544 : ∀ c∈certificate1544.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5148,MergedCutCells.Batch429.certificate5149,MergedCutCells.Batch429.certificate5150,MergedCutCells.Batch429.certificate5151,MergedCutCells.Batch429.certificate5152], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5150,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5151,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5152,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1544 : ∀ c∈certificate1544.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5148,MergedCutCells.Batch429.certificate5149,MergedCutCells.Batch429.certificate5150,MergedCutCells.Batch429.certificate5151,MergedCutCells.Batch429.certificate5152], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid800,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid801,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid802,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid803,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid804,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1544 : ∀ c∈certificate1544.cells, c.population=certificate1544.population := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5148,MergedCutCells.Batch429.certificate5149,MergedCutCells.Batch429.certificate5150,MergedCutCells.Batch429.certificate5151,MergedCutCells.Batch429.certificate5152], c.population=PopulationCertificates.Batch052.certificate1054
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1544 {x : ℝ} (hx : certificate1544.interval.Contains x) : ∃ c∈certificate1544.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1544 numericValid1544 hx

def certificate1545 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1055,PopulationCertificates.Batch052.certificate1055,[MergedCutCells.Batch429.certificate5153,MergedCutCells.Batch429.certificate5154],(300691133048781729/500000000000000000),(some (41297073/40000000)),(1/2),(153636383607524447/1000000000000000000),(some (4520596757908701/100000000000000000)),(some (1542608911993319/200000000000000000))⟩
theorem numericValid1545 : certificate1545.NumericValid := by decide +kernel
theorem cellsSound1545 : ∀ c∈certificate1545.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5153,MergedCutCells.Batch429.certificate5154], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5153,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5154,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1545 : ∀ c∈certificate1545.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5153,MergedCutCells.Batch429.certificate5154], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5153,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5154,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1545 : ∀ c∈certificate1545.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5153,MergedCutCells.Batch429.certificate5154], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid805,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy040.valid805,List.forall_mem_nil _⟩⟩
theorem populationMatches1545 : ∀ c∈certificate1545.cells, c.population=certificate1545.population := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5153,MergedCutCells.Batch429.certificate5154], c.population=PopulationCertificates.Batch052.certificate1055
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1545 {x : ℝ} (hx : certificate1545.interval.Contains x) : ∃ c∈certificate1545.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1545 numericValid1545 hx

def certificate1546 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1055,PopulationCertificates.Batch052.certificate1055,[MergedCutCells.Batch429.certificate5155,MergedCutCells.Batch429.certificate5156,MergedCutCells.Batch429.certificate5157],(41297073/40000000),none,(1/2),(149540030699330123/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1546 : certificate1546.NumericValid := by decide +kernel
theorem cellsSound1546 : ∀ c∈certificate1546.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5155,MergedCutCells.Batch429.certificate5156,MergedCutCells.Batch429.certificate5157], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5157,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1546 : ∀ c∈certificate1546.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5155,MergedCutCells.Batch429.certificate5156,MergedCutCells.Batch429.certificate5157], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5157,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1546 : ∀ c∈certificate1546.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5155,MergedCutCells.Batch429.certificate5156,MergedCutCells.Batch429.certificate5157], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1546 : ∀ c∈certificate1546.cells, c.population=certificate1546.population := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5155,MergedCutCells.Batch429.certificate5156,MergedCutCells.Batch429.certificate5157], c.population=PopulationCertificates.Batch052.certificate1055
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1546 {x : ℝ} (hx : certificate1546.interval.Contains x) : ∃ c∈certificate1546.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1546 numericValid1546 hx

def certificate1547 : RatCutGroup := ⟨GeometryCertificates.Batch052.certificate1056,PopulationCertificates.Batch052.certificate1056,[MergedCutCells.Batch429.certificate5158,MergedCutCells.Batch429.certificate5159],(52678373288214900293/1000000000000000000),none,(1/2),(6331888619133563713/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1547 : certificate1547.NumericValid := by decide +kernel
theorem cellsSound1547 : ∀ c∈certificate1547.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5158,MergedCutCells.Batch429.certificate5159], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.sound5159,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1547 : ∀ c∈certificate1547.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5158,MergedCutCells.Batch429.certificate5159], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch429.numericValid5159,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1547 : ∀ c∈certificate1547.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5158,MergedCutCells.Batch429.certificate5159], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1547 : ∀ c∈certificate1547.cells, c.population=certificate1547.population := by
  change ∀ c∈[MergedCutCells.Batch429.certificate5158,MergedCutCells.Batch429.certificate5159], c.population=PopulationCertificates.Batch052.certificate1056
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1547 {x : ℝ} (hx : certificate1547.interval.Contains x) : ∃ c∈certificate1547.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1547 numericValid1547 hx

end Cycle12.MergedCutGroups.Batch128
