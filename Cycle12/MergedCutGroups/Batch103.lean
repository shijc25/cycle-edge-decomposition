import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch041
import Cycle12.MergedCutCells.Batch356
import Cycle12.MergedCutCells.Batch357
import Cycle12.MergedCutCells.Batch358
import Cycle12.MergedCutCells.Batch359
import Cycle12.PopulationCertificates.Batch041

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch103

def certificate1236 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate824,PopulationCertificates.Batch041.certificate824,[MergedCutCells.Batch356.certificate4283,MergedCutCells.Batch357.certificate4284],(843957171975753497/1000000000000000000),(some (226737131/200000000)),(1/2),(2155083800072372359/1000000000000000000),(some (8118476164821971/50000000000000000)),(some (9564625596881201/250000000000000000))⟩
theorem numericValid1236 : certificate1236.NumericValid := by decide +kernel
theorem cellsSound1236 : ∀ c∈certificate1236.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4283,MergedCutCells.Batch357.certificate4284], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4283,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4284,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1236 : ∀ c∈certificate1236.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4283,MergedCutCells.Batch357.certificate4284], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4283,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4284,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1236 : ∀ c∈certificate1236.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4283,MergedCutCells.Batch357.certificate4284], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid413,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid413,List.forall_mem_nil _⟩⟩
theorem populationMatches1236 : ∀ c∈certificate1236.cells, c.population=certificate1236.population := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4283,MergedCutCells.Batch357.certificate4284], c.population=PopulationCertificates.Batch041.certificate824
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1236 {x : ℝ} (hx : certificate1236.interval.Contains x) : ∃ c∈certificate1236.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1236 numericValid1236 hx

def certificate1237 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate824,PopulationCertificates.Batch041.certificate824,[MergedCutCells.Batch357.certificate4285,MergedCutCells.Batch357.certificate4286,MergedCutCells.Batch357.certificate4287,MergedCutCells.Batch357.certificate4288],(226737131/200000000),none,(1/2),(2141670025716774391/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1237 : certificate1237.NumericValid := by decide +kernel
theorem cellsSound1237 : ∀ c∈certificate1237.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4285,MergedCutCells.Batch357.certificate4286,MergedCutCells.Batch357.certificate4287,MergedCutCells.Batch357.certificate4288], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4286,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4288,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1237 : ∀ c∈certificate1237.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4285,MergedCutCells.Batch357.certificate4286,MergedCutCells.Batch357.certificate4287,MergedCutCells.Batch357.certificate4288], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4286,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4288,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1237 : ∀ c∈certificate1237.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4285,MergedCutCells.Batch357.certificate4286,MergedCutCells.Batch357.certificate4287,MergedCutCells.Batch357.certificate4288], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1237 : ∀ c∈certificate1237.cells, c.population=certificate1237.population := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4285,MergedCutCells.Batch357.certificate4286,MergedCutCells.Batch357.certificate4287,MergedCutCells.Batch357.certificate4288], c.population=PopulationCertificates.Batch041.certificate824
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1237 {x : ℝ} (hx : certificate1237.interval.Contains x) : ∃ c∈certificate1237.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1237 numericValid1237 hx

def certificate1238 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate825,PopulationCertificates.Batch041.certificate825,[MergedCutCells.Batch357.certificate4289,MergedCutCells.Batch357.certificate4290],(22481671574538696189/1000000000000000000),none,(1/2),(12129070952690570177/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1238 : certificate1238.NumericValid := by decide +kernel
theorem cellsSound1238 : ∀ c∈certificate1238.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4289,MergedCutCells.Batch357.certificate4290], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4289,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4290,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1238 : ∀ c∈certificate1238.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4289,MergedCutCells.Batch357.certificate4290], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4289,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4290,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1238 : ∀ c∈certificate1238.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4289,MergedCutCells.Batch357.certificate4290], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1238 : ∀ c∈certificate1238.cells, c.population=certificate1238.population := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4289,MergedCutCells.Batch357.certificate4290], c.population=PopulationCertificates.Batch041.certificate825
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1238 {x : ℝ} (hx : certificate1238.interval.Contains x) : ∃ c∈certificate1238.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1238 numericValid1238 hx

def certificate1239 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate826,PopulationCertificates.Batch041.certificate826,[MergedCutCells.Batch357.certificate4291,MergedCutCells.Batch357.certificate4292],(106475821737397883/125000000000000000),(some (1145433673/1000000000)),(1/2),(2268953022995385291/1000000000000000000),(some (164594041912592819/1000000000000000000)),(some (38950414304627399/1000000000000000000))⟩
theorem numericValid1239 : certificate1239.NumericValid := by decide +kernel
theorem cellsSound1239 : ∀ c∈certificate1239.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4291,MergedCutCells.Batch357.certificate4292], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4292,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1239 : ∀ c∈certificate1239.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4291,MergedCutCells.Batch357.certificate4292], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4292,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1239 : ∀ c∈certificate1239.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4291,MergedCutCells.Batch357.certificate4292], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid414,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid414,List.forall_mem_nil _⟩⟩
theorem populationMatches1239 : ∀ c∈certificate1239.cells, c.population=certificate1239.population := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4291,MergedCutCells.Batch357.certificate4292], c.population=PopulationCertificates.Batch041.certificate826
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1239 {x : ℝ} (hx : certificate1239.interval.Contains x) : ∃ c∈certificate1239.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1239 numericValid1239 hx

def certificate1240 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate826,PopulationCertificates.Batch041.certificate826,[MergedCutCells.Batch357.certificate4293,MergedCutCells.Batch357.certificate4294,MergedCutCells.Batch357.certificate4295,MergedCutCells.Batch358.certificate4296],(1145433673/1000000000),none,(1/2),(5635838004166251/2500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1240 : certificate1240.NumericValid := by decide +kernel
theorem cellsSound1240 : ∀ c∈certificate1240.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4293,MergedCutCells.Batch357.certificate4294,MergedCutCells.Batch357.certificate4295,MergedCutCells.Batch358.certificate4296], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4294,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.sound4295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4296,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1240 : ∀ c∈certificate1240.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4293,MergedCutCells.Batch357.certificate4294,MergedCutCells.Batch357.certificate4295,MergedCutCells.Batch358.certificate4296], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4294,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch357.numericValid4295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4296,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1240 : ∀ c∈certificate1240.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4293,MergedCutCells.Batch357.certificate4294,MergedCutCells.Batch357.certificate4295,MergedCutCells.Batch358.certificate4296], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1240 : ∀ c∈certificate1240.cells, c.population=certificate1240.population := by
  change ∀ c∈[MergedCutCells.Batch357.certificate4293,MergedCutCells.Batch357.certificate4294,MergedCutCells.Batch357.certificate4295,MergedCutCells.Batch358.certificate4296], c.population=PopulationCertificates.Batch041.certificate826
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1240 {x : ℝ} (hx : certificate1240.interval.Contains x) : ∃ c∈certificate1240.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1240 numericValid1240 hx

def certificate1241 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate827,PopulationCertificates.Batch041.certificate827,[MergedCutCells.Batch358.certificate4297,MergedCutCells.Batch358.certificate4298],(22206295365177758759/1000000000000000000),none,(1/2),(1531871274541981419/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1241 : certificate1241.NumericValid := by decide +kernel
theorem cellsSound1241 : ∀ c∈certificate1241.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4297,MergedCutCells.Batch358.certificate4298], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4297,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4298,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1241 : ∀ c∈certificate1241.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4297,MergedCutCells.Batch358.certificate4298], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4297,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4298,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1241 : ∀ c∈certificate1241.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4297,MergedCutCells.Batch358.certificate4298], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1241 : ∀ c∈certificate1241.cells, c.population=certificate1241.population := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4297,MergedCutCells.Batch358.certificate4298], c.population=PopulationCertificates.Batch041.certificate827
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1241 {x : ℝ} (hx : certificate1241.interval.Contains x) : ∃ c∈certificate1241.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1241 numericValid1241 hx

def certificate1242 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate828,PopulationCertificates.Batch041.certificate828,[MergedCutCells.Batch358.certificate4299,MergedCutCells.Batch358.certificate4300],(859553707722200273/1000000000000000000),(some (1155133961/1000000000)),(1/2),(119222995875391913/50000000000000000),(some (16676066399626097/100000000000000000)),(some (7925635105289079/200000000000000000))⟩
theorem numericValid1242 : certificate1242.NumericValid := by decide +kernel
theorem cellsSound1242 : ∀ c∈certificate1242.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4299,MergedCutCells.Batch358.certificate4300], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4299,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4300,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1242 : ∀ c∈certificate1242.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4299,MergedCutCells.Batch358.certificate4300], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4299,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4300,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1242 : ∀ c∈certificate1242.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4299,MergedCutCells.Batch358.certificate4300], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid415,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid415,List.forall_mem_nil _⟩⟩
theorem populationMatches1242 : ∀ c∈certificate1242.cells, c.population=certificate1242.population := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4299,MergedCutCells.Batch358.certificate4300], c.population=PopulationCertificates.Batch041.certificate828
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1242 {x : ℝ} (hx : certificate1242.interval.Contains x) : ∃ c∈certificate1242.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1242 numericValid1242 hx

def certificate1243 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate828,PopulationCertificates.Batch041.certificate828,[MergedCutCells.Batch358.certificate4301,MergedCutCells.Batch358.certificate4302,MergedCutCells.Batch358.certificate4303,MergedCutCells.Batch358.certificate4304],(1155133961/1000000000),none,(1/2),(2370244663627695361/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1243 : certificate1243.NumericValid := by decide +kernel
theorem cellsSound1243 : ∀ c∈certificate1243.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4301,MergedCutCells.Batch358.certificate4302,MergedCutCells.Batch358.certificate4303,MergedCutCells.Batch358.certificate4304], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4301,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4302,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4303,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4304,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1243 : ∀ c∈certificate1243.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4301,MergedCutCells.Batch358.certificate4302,MergedCutCells.Batch358.certificate4303,MergedCutCells.Batch358.certificate4304], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4301,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4302,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4303,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4304,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1243 : ∀ c∈certificate1243.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4301,MergedCutCells.Batch358.certificate4302,MergedCutCells.Batch358.certificate4303,MergedCutCells.Batch358.certificate4304], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1243 : ∀ c∈certificate1243.cells, c.population=certificate1243.population := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4301,MergedCutCells.Batch358.certificate4302,MergedCutCells.Batch358.certificate4303,MergedCutCells.Batch358.certificate4304], c.population=PopulationCertificates.Batch041.certificate828
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1243 {x : ℝ} (hx : certificate1243.interval.Contains x) : ∃ c∈certificate1243.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1243 numericValid1243 hx

def certificate1244 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate829,PopulationCertificates.Batch041.certificate829,[MergedCutCells.Batch358.certificate4305,MergedCutCells.Batch358.certificate4306],(22032724629189966667/1000000000000000000),none,(1/2),(12394461651300085957/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1244 : certificate1244.NumericValid := by decide +kernel
theorem cellsSound1244 : ∀ c∈certificate1244.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4305,MergedCutCells.Batch358.certificate4306], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4305,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4306,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1244 : ∀ c∈certificate1244.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4305,MergedCutCells.Batch358.certificate4306], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4305,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4306,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1244 : ∀ c∈certificate1244.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4305,MergedCutCells.Batch358.certificate4306], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1244 : ∀ c∈certificate1244.cells, c.population=certificate1244.population := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4305,MergedCutCells.Batch358.certificate4306], c.population=PopulationCertificates.Batch041.certificate829
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1244 {x : ℝ} (hx : certificate1244.interval.Contains x) : ∃ c∈certificate1244.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1244 numericValid1244 hx

def certificate1245 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate830,PopulationCertificates.Batch041.certificate830,[MergedCutCells.Batch358.certificate4307,MergedCutCells.Batch359.certificate4308],(284103060135010773/500000000000000000),(some (79986631/62500000)),(1/2),(77830415420006443/250000000000000000),(some (275544425600057/1000000000000000000)),(some (23647316815651/1000000000000000000))⟩
theorem numericValid1245 : certificate1245.NumericValid := by decide +kernel
theorem cellsSound1245 : ∀ c∈certificate1245.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4307,MergedCutCells.Batch359.certificate4308], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.sound4307,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4308,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1245 : ∀ c∈certificate1245.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4307,MergedCutCells.Batch359.certificate4308], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch358.numericValid4307,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4308,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1245 : ∀ c∈certificate1245.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4307,MergedCutCells.Batch359.certificate4308], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid416,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid416,List.forall_mem_nil _⟩⟩
theorem populationMatches1245 : ∀ c∈certificate1245.cells, c.population=certificate1245.population := by
  change ∀ c∈[MergedCutCells.Batch358.certificate4307,MergedCutCells.Batch359.certificate4308], c.population=PopulationCertificates.Batch041.certificate830
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1245 {x : ℝ} (hx : certificate1245.interval.Contains x) : ∃ c∈certificate1245.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1245 numericValid1245 hx

def certificate1246 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate830,PopulationCertificates.Batch041.certificate830,[MergedCutCells.Batch359.certificate4309,MergedCutCells.Batch359.certificate4310,MergedCutCells.Batch359.certificate4311],(79986631/62500000),none,(1/2),(59381210073697699/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1246 : certificate1246.NumericValid := by decide +kernel
theorem cellsSound1246 : ∀ c∈certificate1246.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4309,MergedCutCells.Batch359.certificate4310,MergedCutCells.Batch359.certificate4311], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4311,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1246 : ∀ c∈certificate1246.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4309,MergedCutCells.Batch359.certificate4310,MergedCutCells.Batch359.certificate4311], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4311,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1246 : ∀ c∈certificate1246.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4309,MergedCutCells.Batch359.certificate4310,MergedCutCells.Batch359.certificate4311], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1246 : ∀ c∈certificate1246.cells, c.population=certificate1246.population := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4309,MergedCutCells.Batch359.certificate4310,MergedCutCells.Batch359.certificate4311], c.population=PopulationCertificates.Batch041.certificate830
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1246 {x : ℝ} (hx : certificate1246.interval.Contains x) : ∃ c∈certificate1246.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1246 numericValid1246 hx

def certificate1247 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate831,PopulationCertificates.Batch041.certificate831,[MergedCutCells.Batch359.certificate4312,MergedCutCells.Batch359.certificate4313],(1862186741982826351/125000000000000000),none,(1/2),(1832307852010938487/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1247 : certificate1247.NumericValid := by decide +kernel
theorem cellsSound1247 : ∀ c∈certificate1247.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4312,MergedCutCells.Batch359.certificate4313], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4312,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4313,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1247 : ∀ c∈certificate1247.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4312,MergedCutCells.Batch359.certificate4313], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4312,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4313,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1247 : ∀ c∈certificate1247.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4312,MergedCutCells.Batch359.certificate4313], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1247 : ∀ c∈certificate1247.cells, c.population=certificate1247.population := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4312,MergedCutCells.Batch359.certificate4313], c.population=PopulationCertificates.Batch041.certificate831
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1247 {x : ℝ} (hx : certificate1247.interval.Contains x) : ∃ c∈certificate1247.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1247 numericValid1247 hx

end Cycle12.MergedCutGroups.Batch103
