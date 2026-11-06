import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch051
import Cycle12.MergedCutCells.Batch420
import Cycle12.MergedCutCells.Batch421
import Cycle12.MergedCutCells.Batch422
import Cycle12.MergedCutCells.Batch423
import Cycle12.PopulationCertificates.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch126

def certificate1512 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1030,PopulationCertificates.Batch051.certificate1030,[MergedCutCells.Batch420.certificate5049,MergedCutCells.Batch420.certificate5050,MergedCutCells.Batch420.certificate5051,MergedCutCells.Batch421.certificate5052,MergedCutCells.Batch421.certificate5053],(367723120246581571/500000000000000000),none,(1/40),(44511434824706623/500000000000000000),none,none⟩
theorem numericValid1512 : certificate1512.NumericValid := by decide +kernel
theorem cellsSound1512 : ∀ c∈certificate1512.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5049,MergedCutCells.Batch420.certificate5050,MergedCutCells.Batch420.certificate5051,MergedCutCells.Batch421.certificate5052,MergedCutCells.Batch421.certificate5053], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5050,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5051,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5052,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5053,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1512 : ∀ c∈certificate1512.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5049,MergedCutCells.Batch420.certificate5050,MergedCutCells.Batch420.certificate5051,MergedCutCells.Batch421.certificate5052,MergedCutCells.Batch421.certificate5053], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5050,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5051,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5052,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5053,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1512 : ∀ c∈certificate1512.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5049,MergedCutCells.Batch420.certificate5050,MergedCutCells.Batch420.certificate5051,MergedCutCells.Batch421.certificate5052,MergedCutCells.Batch421.certificate5053], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid752,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid753,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid754,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid755,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid756,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1512 : ∀ c∈certificate1512.cells, c.population=certificate1512.population := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5049,MergedCutCells.Batch420.certificate5050,MergedCutCells.Batch420.certificate5051,MergedCutCells.Batch421.certificate5052,MergedCutCells.Batch421.certificate5053], c.population=PopulationCertificates.Batch051.certificate1030
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1512 {x : ℝ} (hx : certificate1512.interval.Contains x) : ∃ c∈certificate1512.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1512 numericValid1512 hx

def certificate1513 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1031,PopulationCertificates.Batch051.certificate1031,[MergedCutCells.Batch421.certificate5054,MergedCutCells.Batch421.certificate5055],(61275350484765983/100000000000000000),(some (1078875517/1000000000)),(1/2),(3481886261927397/12500000000000000),(some (8823124483573523/250000000000000000)),(some (1432522209415839/250000000000000000))⟩
theorem numericValid1513 : certificate1513.NumericValid := by decide +kernel
theorem cellsSound1513 : ∀ c∈certificate1513.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5054,MergedCutCells.Batch421.certificate5055], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5054,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5055,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1513 : ∀ c∈certificate1513.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5054,MergedCutCells.Batch421.certificate5055], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5054,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5055,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1513 : ∀ c∈certificate1513.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5054,MergedCutCells.Batch421.certificate5055], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid757,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid757,List.forall_mem_nil _⟩⟩
theorem populationMatches1513 : ∀ c∈certificate1513.cells, c.population=certificate1513.population := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5054,MergedCutCells.Batch421.certificate5055], c.population=PopulationCertificates.Batch051.certificate1031
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1513 {x : ℝ} (hx : certificate1513.interval.Contains x) : ∃ c∈certificate1513.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1513 numericValid1513 hx

def certificate1514 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1031,PopulationCertificates.Batch051.certificate1031,[MergedCutCells.Batch421.certificate5056,MergedCutCells.Batch421.certificate5057,MergedCutCells.Batch421.certificate5058],(1078875517/1000000000),none,(1/2),(69020134048368423/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1514 : certificate1514.NumericValid := by decide +kernel
theorem cellsSound1514 : ∀ c∈certificate1514.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5056,MergedCutCells.Batch421.certificate5057,MergedCutCells.Batch421.certificate5058], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5056,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5057,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5058,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1514 : ∀ c∈certificate1514.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5056,MergedCutCells.Batch421.certificate5057,MergedCutCells.Batch421.certificate5058], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5056,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5057,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5058,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1514 : ∀ c∈certificate1514.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5056,MergedCutCells.Batch421.certificate5057,MergedCutCells.Batch421.certificate5058], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1514 : ∀ c∈certificate1514.cells, c.population=certificate1514.population := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5056,MergedCutCells.Batch421.certificate5057,MergedCutCells.Batch421.certificate5058], c.population=PopulationCertificates.Batch051.certificate1031
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1514 {x : ℝ} (hx : certificate1514.interval.Contains x) : ∃ c∈certificate1514.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1514 numericValid1514 hx

def certificate1515 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1032,PopulationCertificates.Batch051.certificate1032,[MergedCutCells.Batch421.certificate5059,MergedCutCells.Batch421.certificate5060],(8490301818705650677/200000000000000000),none,(1/2),(10596401925645696761/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1515 : certificate1515.NumericValid := by decide +kernel
theorem cellsSound1515 : ∀ c∈certificate1515.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5059,MergedCutCells.Batch421.certificate5060], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5059,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5060,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1515 : ∀ c∈certificate1515.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5059,MergedCutCells.Batch421.certificate5060], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5059,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5060,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1515 : ∀ c∈certificate1515.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5059,MergedCutCells.Batch421.certificate5060], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1515 : ∀ c∈certificate1515.cells, c.population=certificate1515.population := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5059,MergedCutCells.Batch421.certificate5060], c.population=PopulationCertificates.Batch051.certificate1032
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1515 {x : ℝ} (hx : certificate1515.interval.Contains x) : ∃ c∈certificate1515.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1515 numericValid1515 hx

def certificate1516 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1033,PopulationCertificates.Batch051.certificate1033,[MergedCutCells.Batch421.certificate5061,MergedCutCells.Batch421.certificate5062,MergedCutCells.Batch421.certificate5063,MergedCutCells.Batch422.certificate5064,MergedCutCells.Batch422.certificate5065],(739487826958138751/1000000000000000000),none,(1/40),(98384171700088901/1000000000000000000),none,none⟩
theorem numericValid1516 : certificate1516.NumericValid := by decide +kernel
theorem cellsSound1516 : ∀ c∈certificate1516.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5061,MergedCutCells.Batch421.certificate5062,MergedCutCells.Batch421.certificate5063,MergedCutCells.Batch422.certificate5064,MergedCutCells.Batch422.certificate5065], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5061,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5062,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.sound5063,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5064,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5065,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1516 : ∀ c∈certificate1516.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5061,MergedCutCells.Batch421.certificate5062,MergedCutCells.Batch421.certificate5063,MergedCutCells.Batch422.certificate5064,MergedCutCells.Batch422.certificate5065], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5061,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5062,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch421.numericValid5063,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5064,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5065,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1516 : ∀ c∈certificate1516.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5061,MergedCutCells.Batch421.certificate5062,MergedCutCells.Batch421.certificate5063,MergedCutCells.Batch422.certificate5064,MergedCutCells.Batch422.certificate5065], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid758,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid759,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid760,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid761,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid762,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1516 : ∀ c∈certificate1516.cells, c.population=certificate1516.population := by
  change ∀ c∈[MergedCutCells.Batch421.certificate5061,MergedCutCells.Batch421.certificate5062,MergedCutCells.Batch421.certificate5063,MergedCutCells.Batch422.certificate5064,MergedCutCells.Batch422.certificate5065], c.population=PopulationCertificates.Batch051.certificate1033
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1516 {x : ℝ} (hx : certificate1516.interval.Contains x) : ∃ c∈certificate1516.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1516 numericValid1516 hx

def certificate1517 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1034,PopulationCertificates.Batch051.certificate1034,[MergedCutCells.Batch422.certificate5066,MergedCutCells.Batch422.certificate5067],(307360929081625283/500000000000000000),(some (216383771/200000000)),(1/2),(71163287069146059/250000000000000000),(some (36497218922324967/1000000000000000000)),(some (2982327233625441/500000000000000000))⟩
theorem numericValid1517 : certificate1517.NumericValid := by decide +kernel
theorem cellsSound1517 : ∀ c∈certificate1517.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5066,MergedCutCells.Batch422.certificate5067], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5066,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5067,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1517 : ∀ c∈certificate1517.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5066,MergedCutCells.Batch422.certificate5067], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5066,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5067,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1517 : ∀ c∈certificate1517.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5066,MergedCutCells.Batch422.certificate5067], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid763,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid763,List.forall_mem_nil _⟩⟩
theorem populationMatches1517 : ∀ c∈certificate1517.cells, c.population=certificate1517.population := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5066,MergedCutCells.Batch422.certificate5067], c.population=PopulationCertificates.Batch051.certificate1034
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1517 {x : ℝ} (hx : certificate1517.interval.Contains x) : ∃ c∈certificate1517.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1517 numericValid1517 hx

def certificate1518 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1034,PopulationCertificates.Batch051.certificate1034,[MergedCutCells.Batch422.certificate5068,MergedCutCells.Batch422.certificate5069,MergedCutCells.Batch422.certificate5070],(216383771/200000000),none,(1/2),(11271309829629271/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1518 : certificate1518.NumericValid := by decide +kernel
theorem cellsSound1518 : ∀ c∈certificate1518.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5068,MergedCutCells.Batch422.certificate5069,MergedCutCells.Batch422.certificate5070], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5069,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5070,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1518 : ∀ c∈certificate1518.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5068,MergedCutCells.Batch422.certificate5069,MergedCutCells.Batch422.certificate5070], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5069,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5070,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1518 : ∀ c∈certificate1518.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5068,MergedCutCells.Batch422.certificate5069,MergedCutCells.Batch422.certificate5070], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1518 : ∀ c∈certificate1518.cells, c.population=certificate1518.population := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5068,MergedCutCells.Batch422.certificate5069,MergedCutCells.Batch422.certificate5070], c.population=PopulationCertificates.Batch051.certificate1034
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1518 {x : ℝ} (hx : certificate1518.interval.Contains x) : ∃ c∈certificate1518.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1518 numericValid1518 hx

def certificate1519 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1035,PopulationCertificates.Batch051.certificate1035,[MergedCutCells.Batch422.certificate5071,MergedCutCells.Batch422.certificate5072],(21699228970666862277/500000000000000000),none,(1/2),(10829634144304476919/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1519 : certificate1519.NumericValid := by decide +kernel
theorem cellsSound1519 : ∀ c∈certificate1519.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5071,MergedCutCells.Batch422.certificate5072], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5071,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5072,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1519 : ∀ c∈certificate1519.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5071,MergedCutCells.Batch422.certificate5072], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5071,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5072,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1519 : ∀ c∈certificate1519.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5071,MergedCutCells.Batch422.certificate5072], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1519 : ∀ c∈certificate1519.cells, c.population=certificate1519.population := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5071,MergedCutCells.Batch422.certificate5072], c.population=PopulationCertificates.Batch051.certificate1035
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1519 {x : ℝ} (hx : certificate1519.interval.Contains x) : ∃ c∈certificate1519.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1519 numericValid1519 hx

def certificate1520 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1036,PopulationCertificates.Batch051.certificate1036,[MergedCutCells.Batch422.certificate5073,MergedCutCells.Batch422.certificate5074,MergedCutCells.Batch422.certificate5075,MergedCutCells.Batch423.certificate5076,MergedCutCells.Batch423.certificate5077],(148717819254534381/200000000000000000),none,(1/40),(108257251638595577/1000000000000000000),none,none⟩
theorem numericValid1520 : certificate1520.NumericValid := by decide +kernel
theorem cellsSound1520 : ∀ c∈certificate1520.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5073,MergedCutCells.Batch422.certificate5074,MergedCutCells.Batch422.certificate5075,MergedCutCells.Batch423.certificate5076,MergedCutCells.Batch423.certificate5077], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5074,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.sound5075,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5077,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1520 : ∀ c∈certificate1520.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5073,MergedCutCells.Batch422.certificate5074,MergedCutCells.Batch422.certificate5075,MergedCutCells.Batch423.certificate5076,MergedCutCells.Batch423.certificate5077], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5074,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch422.numericValid5075,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5077,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1520 : ∀ c∈certificate1520.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5073,MergedCutCells.Batch422.certificate5074,MergedCutCells.Batch422.certificate5075,MergedCutCells.Batch423.certificate5076,MergedCutCells.Batch423.certificate5077], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid764,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid765,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid766,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid767,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid768,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1520 : ∀ c∈certificate1520.cells, c.population=certificate1520.population := by
  change ∀ c∈[MergedCutCells.Batch422.certificate5073,MergedCutCells.Batch422.certificate5074,MergedCutCells.Batch422.certificate5075,MergedCutCells.Batch423.certificate5076,MergedCutCells.Batch423.certificate5077], c.population=PopulationCertificates.Batch051.certificate1036
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1520 {x : ℝ} (hx : certificate1520.interval.Contains x) : ∃ c∈certificate1520.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1520 numericValid1520 hx

def certificate1521 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1037,PopulationCertificates.Batch051.certificate1037,[MergedCutCells.Batch423.certificate5078,MergedCutCells.Batch423.certificate5079],(616583839239860019/1000000000000000000),(some (211695031/200000000)),(1/2),(18161698340531357/62500000000000000),(some (9373128326422299/250000000000000000)),(some (3079912030804319/500000000000000000))⟩
theorem numericValid1521 : certificate1521.NumericValid := by decide +kernel
theorem cellsSound1521 : ∀ c∈certificate1521.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5078,MergedCutCells.Batch423.certificate5079], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5078,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5079,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1521 : ∀ c∈certificate1521.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5078,MergedCutCells.Batch423.certificate5079], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5078,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5079,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1521 : ∀ c∈certificate1521.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5078,MergedCutCells.Batch423.certificate5079], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid769,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy038.valid769,List.forall_mem_nil _⟩⟩
theorem populationMatches1521 : ∀ c∈certificate1521.cells, c.population=certificate1521.population := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5078,MergedCutCells.Batch423.certificate5079], c.population=PopulationCertificates.Batch051.certificate1037
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1521 {x : ℝ} (hx : certificate1521.interval.Contains x) : ∃ c∈certificate1521.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1521 numericValid1521 hx

def certificate1522 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1037,PopulationCertificates.Batch051.certificate1037,[MergedCutCells.Batch423.certificate5080,MergedCutCells.Batch423.certificate5081,MergedCutCells.Batch423.certificate5082,MergedCutCells.Batch423.certificate5083],(211695031/200000000),none,(1/2),(287677703081296277/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1522 : certificate1522.NumericValid := by decide +kernel
theorem cellsSound1522 : ∀ c∈certificate1522.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5080,MergedCutCells.Batch423.certificate5081,MergedCutCells.Batch423.certificate5082,MergedCutCells.Batch423.certificate5083], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5080,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5083,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1522 : ∀ c∈certificate1522.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5080,MergedCutCells.Batch423.certificate5081,MergedCutCells.Batch423.certificate5082,MergedCutCells.Batch423.certificate5083], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5080,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5083,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1522 : ∀ c∈certificate1522.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5080,MergedCutCells.Batch423.certificate5081,MergedCutCells.Batch423.certificate5082,MergedCutCells.Batch423.certificate5083], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1522 : ∀ c∈certificate1522.cells, c.population=certificate1522.population := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5080,MergedCutCells.Batch423.certificate5081,MergedCutCells.Batch423.certificate5082,MergedCutCells.Batch423.certificate5083], c.population=PopulationCertificates.Batch051.certificate1037
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1522 {x : ℝ} (hx : certificate1522.interval.Contains x) : ∃ c∈certificate1522.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1522 numericValid1522 hx

def certificate1523 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1038,PopulationCertificates.Batch051.certificate1038,[MergedCutCells.Batch423.certificate5084,MergedCutCells.Batch423.certificate5085],(44374963460000941761/1000000000000000000),none,(1/2),(2702462754760731/244140625000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1523 : certificate1523.NumericValid := by decide +kernel
theorem cellsSound1523 : ∀ c∈certificate1523.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5084,MergedCutCells.Batch423.certificate5085], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5084,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.sound5085,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1523 : ∀ c∈certificate1523.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5084,MergedCutCells.Batch423.certificate5085], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5084,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch423.numericValid5085,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1523 : ∀ c∈certificate1523.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5084,MergedCutCells.Batch423.certificate5085], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1523 : ∀ c∈certificate1523.cells, c.population=certificate1523.population := by
  change ∀ c∈[MergedCutCells.Batch423.certificate5084,MergedCutCells.Batch423.certificate5085], c.population=PopulationCertificates.Batch051.certificate1038
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1523 {x : ℝ} (hx : certificate1523.interval.Contains x) : ∃ c∈certificate1523.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1523 numericValid1523 hx

end Cycle12.MergedCutGroups.Batch126
