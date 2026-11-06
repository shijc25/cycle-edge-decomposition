import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch040
import Cycle12.MergedCutCells.Batch351
import Cycle12.MergedCutCells.Batch352
import Cycle12.MergedCutCells.Batch353
import Cycle12.MergedCutCells.Batch354
import Cycle12.PopulationCertificates.Batch040

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch101

def certificate1212 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate808,PopulationCertificates.Batch040.certificate808,[MergedCutCells.Batch351.certificate4217,MergedCutCells.Batch351.certificate4218],(390624841713787601/500000000000000000),(some (1102657099/1000000000)),(1/2),(137065080367396939/100000000000000000),(some (147285614333369259/1000000000000000000)),(some (33672670702528971/1000000000000000000))⟩
theorem numericValid1212 : certificate1212.NumericValid := by decide +kernel
theorem cellsSound1212 : ∀ c∈certificate1212.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4217,MergedCutCells.Batch351.certificate4218], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4217,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4218,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1212 : ∀ c∈certificate1212.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4217,MergedCutCells.Batch351.certificate4218], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4217,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4218,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1212 : ∀ c∈certificate1212.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4217,MergedCutCells.Batch351.certificate4218], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid405,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid405,List.forall_mem_nil _⟩⟩
theorem populationMatches1212 : ∀ c∈certificate1212.cells, c.population=certificate1212.population := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4217,MergedCutCells.Batch351.certificate4218], c.population=PopulationCertificates.Batch040.certificate808
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1212 {x : ℝ} (hx : certificate1212.interval.Contains x) : ∃ c∈certificate1212.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1212 numericValid1212 hx

def certificate1213 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate808,PopulationCertificates.Batch040.certificate808,[MergedCutCells.Batch351.certificate4219,MergedCutCells.Batch351.certificate4220,MergedCutCells.Batch351.certificate4221,MergedCutCells.Batch351.certificate4222,MergedCutCells.Batch351.certificate4223],(1102657099/1000000000),none,(1/2),(1357714653707876383/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1213 : certificate1213.NumericValid := by decide +kernel
theorem cellsSound1213 : ∀ c∈certificate1213.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4219,MergedCutCells.Batch351.certificate4220,MergedCutCells.Batch351.certificate4221,MergedCutCells.Batch351.certificate4222,MergedCutCells.Batch351.certificate4223], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4220,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4221,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4222,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4223,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1213 : ∀ c∈certificate1213.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4219,MergedCutCells.Batch351.certificate4220,MergedCutCells.Batch351.certificate4221,MergedCutCells.Batch351.certificate4222,MergedCutCells.Batch351.certificate4223], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4220,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4221,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4222,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4223,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1213 : ∀ c∈certificate1213.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4219,MergedCutCells.Batch351.certificate4220,MergedCutCells.Batch351.certificate4221,MergedCutCells.Batch351.certificate4222,MergedCutCells.Batch351.certificate4223], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1213 : ∀ c∈certificate1213.cells, c.population=certificate1213.population := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4219,MergedCutCells.Batch351.certificate4220,MergedCutCells.Batch351.certificate4221,MergedCutCells.Batch351.certificate4222,MergedCutCells.Batch351.certificate4223], c.population=PopulationCertificates.Batch040.certificate808
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1213 {x : ℝ} (hx : certificate1213.interval.Contains x) : ∃ c∈certificate1213.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1213 numericValid1213 hx

def certificate1214 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate809,PopulationCertificates.Batch040.certificate809,[MergedCutCells.Batch352.certificate4224,MergedCutCells.Batch352.certificate4225],(2987928939751716707/125000000000000000),none,(1/2),(5503083864523191737/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1214 : certificate1214.NumericValid := by decide +kernel
theorem cellsSound1214 : ∀ c∈certificate1214.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4224,MergedCutCells.Batch352.certificate4225], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4225,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1214 : ∀ c∈certificate1214.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4224,MergedCutCells.Batch352.certificate4225], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4225,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1214 : ∀ c∈certificate1214.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4224,MergedCutCells.Batch352.certificate4225], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1214 : ∀ c∈certificate1214.cells, c.population=certificate1214.population := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4224,MergedCutCells.Batch352.certificate4225], c.population=PopulationCertificates.Batch040.certificate809
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1214 {x : ℝ} (hx : certificate1214.interval.Contains x) : ∃ c∈certificate1214.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1214 numericValid1214 hx

def certificate1215 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate810,PopulationCertificates.Batch040.certificate810,[MergedCutCells.Batch352.certificate4226,MergedCutCells.Batch352.certificate4227],(793530495577265143/1000000000000000000),(some (140098093/125000000)),(1/2),(1514430482571610161/1000000000000000000),(some (4667759115885961/31250000000000000)),(some (34294864757325913/1000000000000000000))⟩
theorem numericValid1215 : certificate1215.NumericValid := by decide +kernel
theorem cellsSound1215 : ∀ c∈certificate1215.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4226,MergedCutCells.Batch352.certificate4227], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4226,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4227,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1215 : ∀ c∈certificate1215.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4226,MergedCutCells.Batch352.certificate4227], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4226,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4227,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1215 : ∀ c∈certificate1215.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4226,MergedCutCells.Batch352.certificate4227], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid406,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid406,List.forall_mem_nil _⟩⟩
theorem populationMatches1215 : ∀ c∈certificate1215.cells, c.population=certificate1215.population := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4226,MergedCutCells.Batch352.certificate4227], c.population=PopulationCertificates.Batch040.certificate810
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1215 {x : ℝ} (hx : certificate1215.interval.Contains x) : ∃ c∈certificate1215.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1215 numericValid1215 hx

def certificate1216 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate810,PopulationCertificates.Batch040.certificate810,[MergedCutCells.Batch352.certificate4228,MergedCutCells.Batch352.certificate4229,MergedCutCells.Batch352.certificate4230,MergedCutCells.Batch352.certificate4231],(140098093/125000000),none,(1/2),(1501154633276754883/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1216 : certificate1216.NumericValid := by decide +kernel
theorem cellsSound1216 : ∀ c∈certificate1216.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4228,MergedCutCells.Batch352.certificate4229,MergedCutCells.Batch352.certificate4230,MergedCutCells.Batch352.certificate4231], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4228,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4229,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4231,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1216 : ∀ c∈certificate1216.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4228,MergedCutCells.Batch352.certificate4229,MergedCutCells.Batch352.certificate4230,MergedCutCells.Batch352.certificate4231], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4228,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4229,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4231,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1216 : ∀ c∈certificate1216.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4228,MergedCutCells.Batch352.certificate4229,MergedCutCells.Batch352.certificate4230,MergedCutCells.Batch352.certificate4231], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1216 : ∀ c∈certificate1216.cells, c.population=certificate1216.population := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4228,MergedCutCells.Batch352.certificate4229,MergedCutCells.Batch352.certificate4230,MergedCutCells.Batch352.certificate4231], c.population=PopulationCertificates.Batch040.certificate810
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1216 {x : ℝ} (hx : certificate1216.interval.Contains x) : ∃ c∈certificate1216.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1216 numericValid1216 hx

def certificate1217 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate811,PopulationCertificates.Batch040.certificate811,[MergedCutCells.Batch352.certificate4232,MergedCutCells.Batch352.certificate4233],(23633873690209958823/1000000000000000000),none,(1/2),(5623436245223231241/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1217 : certificate1217.NumericValid := by decide +kernel
theorem cellsSound1217 : ∀ c∈certificate1217.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4232,MergedCutCells.Batch352.certificate4233], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4232,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4233,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1217 : ∀ c∈certificate1217.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4232,MergedCutCells.Batch352.certificate4233], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4232,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4233,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1217 : ∀ c∈certificate1217.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4232,MergedCutCells.Batch352.certificate4233], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1217 : ∀ c∈certificate1217.cells, c.population=certificate1217.population := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4232,MergedCutCells.Batch352.certificate4233], c.population=PopulationCertificates.Batch040.certificate811
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1217 {x : ℝ} (hx : certificate1217.interval.Contains x) : ∃ c∈certificate1217.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1217 numericValid1217 hx

def certificate1218 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate812,PopulationCertificates.Batch040.certificate812,[MergedCutCells.Batch352.certificate4234,MergedCutCells.Batch352.certificate4235],(799997172712609559/1000000000000000000),(some (28229931/25000000)),(1/2),(792911205361600639/500000000000000000),(some (18933282248412921/125000000000000000)),(some (17462593519345381/500000000000000000))⟩
theorem numericValid1218 : certificate1218.NumericValid := by decide +kernel
theorem cellsSound1218 : ∀ c∈certificate1218.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4234,MergedCutCells.Batch352.certificate4235], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4234,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.sound4235,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1218 : ∀ c∈certificate1218.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4234,MergedCutCells.Batch352.certificate4235], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4234,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch352.numericValid4235,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1218 : ∀ c∈certificate1218.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4234,MergedCutCells.Batch352.certificate4235], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid407,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid407,List.forall_mem_nil _⟩⟩
theorem populationMatches1218 : ∀ c∈certificate1218.cells, c.population=certificate1218.population := by
  change ∀ c∈[MergedCutCells.Batch352.certificate4234,MergedCutCells.Batch352.certificate4235], c.population=PopulationCertificates.Batch040.certificate812
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1218 {x : ℝ} (hx : certificate1218.interval.Contains x) : ∃ c∈certificate1218.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1218 numericValid1218 hx

def certificate1219 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate812,PopulationCertificates.Batch040.certificate812,[MergedCutCells.Batch353.certificate4236,MergedCutCells.Batch353.certificate4237,MergedCutCells.Batch353.certificate4238,MergedCutCells.Batch353.certificate4239],(28229931/25000000),none,(1/2),(31454198460685449/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1219 : certificate1219.NumericValid := by decide +kernel
theorem cellsSound1219 : ∀ c∈certificate1219.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4236,MergedCutCells.Batch353.certificate4237,MergedCutCells.Batch353.certificate4238,MergedCutCells.Batch353.certificate4239], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4237,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4238,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4239,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1219 : ∀ c∈certificate1219.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4236,MergedCutCells.Batch353.certificate4237,MergedCutCells.Batch353.certificate4238,MergedCutCells.Batch353.certificate4239], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4237,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4238,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4239,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1219 : ∀ c∈certificate1219.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4236,MergedCutCells.Batch353.certificate4237,MergedCutCells.Batch353.certificate4238,MergedCutCells.Batch353.certificate4239], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1219 : ∀ c∈certificate1219.cells, c.population=certificate1219.population := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4236,MergedCutCells.Batch353.certificate4237,MergedCutCells.Batch353.certificate4238,MergedCutCells.Batch353.certificate4239], c.population=PopulationCertificates.Batch040.certificate812
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1219 {x : ℝ} (hx : certificate1219.interval.Contains x) : ∃ c∈certificate1219.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1219 numericValid1219 hx

def certificate1220 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate813,PopulationCertificates.Batch040.certificate813,[MergedCutCells.Batch353.certificate4240,MergedCutCells.Batch353.certificate4241],(23552680151868765813/1000000000000000000),none,(1/2),(2842639814922456567/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1220 : certificate1220.NumericValid := by decide +kernel
theorem cellsSound1220 : ∀ c∈certificate1220.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4240,MergedCutCells.Batch353.certificate4241], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4241,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1220 : ∀ c∈certificate1220.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4240,MergedCutCells.Batch353.certificate4241], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4241,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1220 : ∀ c∈certificate1220.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4240,MergedCutCells.Batch353.certificate4241], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1220 : ∀ c∈certificate1220.cells, c.population=certificate1220.population := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4240,MergedCutCells.Batch353.certificate4241], c.population=PopulationCertificates.Batch040.certificate813
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1220 {x : ℝ} (hx : certificate1220.interval.Contains x) : ∃ c∈certificate1220.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1220 numericValid1220 hx

def certificate1221 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate814,PopulationCertificates.Batch040.certificate814,[MergedCutCells.Batch353.certificate4242,MergedCutCells.Batch353.certificate4243],(80773270597556771/100000000000000000),(some (277902391/250000000)),(1/2),(1681731469325649991/1000000000000000000),(some (76303444183151623/500000000000000000)),(some (17634691016274993/500000000000000000))⟩
theorem numericValid1221 : certificate1221.NumericValid := by decide +kernel
theorem cellsSound1221 : ∀ c∈certificate1221.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4242,MergedCutCells.Batch353.certificate4243], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4243,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1221 : ∀ c∈certificate1221.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4242,MergedCutCells.Batch353.certificate4243], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4243,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1221 : ∀ c∈certificate1221.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4242,MergedCutCells.Batch353.certificate4243], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid408,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid408,List.forall_mem_nil _⟩⟩
theorem populationMatches1221 : ∀ c∈certificate1221.cells, c.population=certificate1221.population := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4242,MergedCutCells.Batch353.certificate4243], c.population=PopulationCertificates.Batch040.certificate814
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1221 {x : ℝ} (hx : certificate1221.interval.Contains x) : ∃ c∈certificate1221.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1221 numericValid1221 hx

def certificate1222 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate814,PopulationCertificates.Batch040.certificate814,[MergedCutCells.Batch353.certificate4244,MergedCutCells.Batch353.certificate4245,MergedCutCells.Batch353.certificate4246,MergedCutCells.Batch353.certificate4247,MergedCutCells.Batch354.certificate4248],(277902391/250000000),none,(1/2),(1669049965247518013/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1222 : certificate1222.NumericValid := by decide +kernel
theorem cellsSound1222 : ∀ c∈certificate1222.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4244,MergedCutCells.Batch353.certificate4245,MergedCutCells.Batch353.certificate4246,MergedCutCells.Batch353.certificate4247,MergedCutCells.Batch354.certificate4248], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4244,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4245,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.sound4247,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4248,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1222 : ∀ c∈certificate1222.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4244,MergedCutCells.Batch353.certificate4245,MergedCutCells.Batch353.certificate4246,MergedCutCells.Batch353.certificate4247,MergedCutCells.Batch354.certificate4248], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4244,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4245,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch353.numericValid4247,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4248,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1222 : ∀ c∈certificate1222.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4244,MergedCutCells.Batch353.certificate4245,MergedCutCells.Batch353.certificate4246,MergedCutCells.Batch353.certificate4247,MergedCutCells.Batch354.certificate4248], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1222 : ∀ c∈certificate1222.cells, c.population=certificate1222.population := by
  change ∀ c∈[MergedCutCells.Batch353.certificate4244,MergedCutCells.Batch353.certificate4245,MergedCutCells.Batch353.certificate4246,MergedCutCells.Batch353.certificate4247,MergedCutCells.Batch354.certificate4248], c.population=PopulationCertificates.Batch040.certificate814
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1222 {x : ℝ} (hx : certificate1222.interval.Contains x) : ∃ c∈certificate1222.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1222 numericValid1222 hx

def certificate1223 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate815,PopulationCertificates.Batch040.certificate815,[MergedCutCells.Batch354.certificate4249,MergedCutCells.Batch354.certificate4250],(11688400872658513551/500000000000000000),none,(1/2),(114954139880817013/10000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1223 : certificate1223.NumericValid := by decide +kernel
theorem cellsSound1223 : ∀ c∈certificate1223.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4249,MergedCutCells.Batch354.certificate4250], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4250,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1223 : ∀ c∈certificate1223.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4249,MergedCutCells.Batch354.certificate4250], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4250,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1223 : ∀ c∈certificate1223.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4249,MergedCutCells.Batch354.certificate4250], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1223 : ∀ c∈certificate1223.cells, c.population=certificate1223.population := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4249,MergedCutCells.Batch354.certificate4250], c.population=PopulationCertificates.Batch040.certificate815
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1223 {x : ℝ} (hx : certificate1223.interval.Contains x) : ∃ c∈certificate1223.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1223 numericValid1223 hx

end Cycle12.MergedCutGroups.Batch101
