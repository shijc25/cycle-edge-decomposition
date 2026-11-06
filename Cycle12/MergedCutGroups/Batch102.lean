import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch040
import Cycle12.GeometryCertificates.Batch041
import Cycle12.MergedCutCells.Batch354
import Cycle12.MergedCutCells.Batch355
import Cycle12.MergedCutCells.Batch356
import Cycle12.PopulationCertificates.Batch040
import Cycle12.PopulationCertificates.Batch041

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch102

def certificate1224 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate816,PopulationCertificates.Batch040.certificate816,[MergedCutCells.Batch354.certificate4251,MergedCutCells.Batch354.certificate4252],(162821982634771569/200000000000000000),(some (560880493/500000000)),(1/2),(879080881146835749/500000000000000000),(some (154786610444930333/1000000000000000000)),(some (35930067472794033/1000000000000000000))⟩
theorem numericValid1224 : certificate1224.NumericValid := by decide +kernel
theorem cellsSound1224 : ∀ c∈certificate1224.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4251,MergedCutCells.Batch354.certificate4252], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4251,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4252,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1224 : ∀ c∈certificate1224.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4251,MergedCutCells.Batch354.certificate4252], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4251,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4252,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1224 : ∀ c∈certificate1224.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4251,MergedCutCells.Batch354.certificate4252], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid409,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid409,List.forall_mem_nil _⟩⟩
theorem populationMatches1224 : ∀ c∈certificate1224.cells, c.population=certificate1224.population := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4251,MergedCutCells.Batch354.certificate4252], c.population=PopulationCertificates.Batch040.certificate816
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1224 {x : ℝ} (hx : certificate1224.interval.Contains x) : ∃ c∈certificate1224.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1224 numericValid1224 hx

def certificate1225 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate816,PopulationCertificates.Batch040.certificate816,[MergedCutCells.Batch354.certificate4253,MergedCutCells.Batch354.certificate4254,MergedCutCells.Batch354.certificate4255,MergedCutCells.Batch354.certificate4256],(560880493/500000000),none,(1/2),(348914204456424463/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1225 : certificate1225.NumericValid := by decide +kernel
theorem cellsSound1225 : ∀ c∈certificate1225.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4253,MergedCutCells.Batch354.certificate4254,MergedCutCells.Batch354.certificate4255,MergedCutCells.Batch354.certificate4256], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4253,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4254,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4255,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4256,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1225 : ∀ c∈certificate1225.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4253,MergedCutCells.Batch354.certificate4254,MergedCutCells.Batch354.certificate4255,MergedCutCells.Batch354.certificate4256], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4253,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4254,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4255,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4256,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1225 : ∀ c∈certificate1225.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4253,MergedCutCells.Batch354.certificate4254,MergedCutCells.Batch354.certificate4255,MergedCutCells.Batch354.certificate4256], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1225 : ∀ c∈certificate1225.cells, c.population=certificate1225.population := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4253,MergedCutCells.Batch354.certificate4254,MergedCutCells.Batch354.certificate4255,MergedCutCells.Batch354.certificate4256], c.population=PopulationCertificates.Batch040.certificate816
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1225 {x : ℝ} (hx : certificate1225.interval.Contains x) : ∃ c∈certificate1225.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1225 numericValid1225 hx

def certificate1226 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate817,PopulationCertificates.Batch040.certificate817,[MergedCutCells.Batch354.certificate4257,MergedCutCells.Batch354.certificate4258],(23187650981621730537/1000000000000000000),none,(1/2),(5805857588199737383/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1226 : certificate1226.NumericValid := by decide +kernel
theorem cellsSound1226 : ∀ c∈certificate1226.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4257,MergedCutCells.Batch354.certificate4258], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4258,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1226 : ∀ c∈certificate1226.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4257,MergedCutCells.Batch354.certificate4258], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4258,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1226 : ∀ c∈certificate1226.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4257,MergedCutCells.Batch354.certificate4258], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1226 : ∀ c∈certificate1226.cells, c.population=certificate1226.population := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4257,MergedCutCells.Batch354.certificate4258], c.population=PopulationCertificates.Batch040.certificate817
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1226 {x : ℝ} (hx : certificate1226.interval.Contains x) : ∃ c∈certificate1226.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1226 numericValid1226 hx

def certificate1227 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate818,PopulationCertificates.Batch040.certificate818,[MergedCutCells.Batch354.certificate4259,MergedCutCells.Batch355.certificate4260],(82208774217968743/100000000000000000),(some (226388521/200000000)),(1/2),(1858819518679208383/1000000000000000000),(some (78446090889644441/500000000000000000)),(some (36571936194153781/1000000000000000000))⟩
theorem numericValid1227 : certificate1227.NumericValid := by decide +kernel
theorem cellsSound1227 : ∀ c∈certificate1227.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4259,MergedCutCells.Batch355.certificate4260], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.sound4259,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4260,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1227 : ∀ c∈certificate1227.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4259,MergedCutCells.Batch355.certificate4260], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch354.numericValid4259,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4260,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1227 : ∀ c∈certificate1227.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4259,MergedCutCells.Batch355.certificate4260], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid410,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid410,List.forall_mem_nil _⟩⟩
theorem populationMatches1227 : ∀ c∈certificate1227.cells, c.population=certificate1227.population := by
  change ∀ c∈[MergedCutCells.Batch354.certificate4259,MergedCutCells.Batch355.certificate4260], c.population=PopulationCertificates.Batch040.certificate818
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1227 {x : ℝ} (hx : certificate1227.interval.Contains x) : ∃ c∈certificate1227.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1227 numericValid1227 hx

def certificate1228 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate818,PopulationCertificates.Batch040.certificate818,[MergedCutCells.Batch355.certificate4261,MergedCutCells.Batch355.certificate4262,MergedCutCells.Batch355.certificate4263,MergedCutCells.Batch355.certificate4264],(226388521/200000000),none,(1/2),(1845798674586266843/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1228 : certificate1228.NumericValid := by decide +kernel
theorem cellsSound1228 : ∀ c∈certificate1228.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4261,MergedCutCells.Batch355.certificate4262,MergedCutCells.Batch355.certificate4263,MergedCutCells.Batch355.certificate4264], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4262,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4263,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4264,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1228 : ∀ c∈certificate1228.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4261,MergedCutCells.Batch355.certificate4262,MergedCutCells.Batch355.certificate4263,MergedCutCells.Batch355.certificate4264], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4262,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4263,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4264,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1228 : ∀ c∈certificate1228.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4261,MergedCutCells.Batch355.certificate4262,MergedCutCells.Batch355.certificate4263,MergedCutCells.Batch355.certificate4264], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1228 : ∀ c∈certificate1228.cells, c.population=certificate1228.population := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4261,MergedCutCells.Batch355.certificate4262,MergedCutCells.Batch355.certificate4263,MergedCutCells.Batch355.certificate4264], c.population=PopulationCertificates.Batch040.certificate818
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1228 {x : ℝ} (hx : certificate1228.interval.Contains x) : ∃ c∈certificate1228.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1228 numericValid1228 hx

def certificate1229 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate819,PopulationCertificates.Batch040.certificate819,[MergedCutCells.Batch355.certificate4265,MergedCutCells.Batch355.certificate4266],(23013161769427137349/1000000000000000000),none,(1/2),(5870282622460276329/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1229 : certificate1229.NumericValid := by decide +kernel
theorem cellsSound1229 : ∀ c∈certificate1229.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4265,MergedCutCells.Batch355.certificate4266], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4265,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4266,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1229 : ∀ c∈certificate1229.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4265,MergedCutCells.Batch355.certificate4266], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4265,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4266,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1229 : ∀ c∈certificate1229.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4265,MergedCutCells.Batch355.certificate4266], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1229 : ∀ c∈certificate1229.cells, c.population=certificate1229.population := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4265,MergedCutCells.Batch355.certificate4266], c.population=PopulationCertificates.Batch040.certificate819
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1229 {x : ℝ} (hx : certificate1229.interval.Contains x) : ∃ c∈certificate1229.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1229 numericValid1229 hx

def certificate1230 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate820,PopulationCertificates.Batch041.certificate820,[MergedCutCells.Batch355.certificate4267,MergedCutCells.Batch355.certificate4268],(33208518012847147/40000000000000000),(some (22887559/20000000)),(1/2),(392832560997190671/200000000000000000),(some (15910831173756991/100000000000000000)),(some (37251390587961293/1000000000000000000))⟩
theorem numericValid1230 : certificate1230.NumericValid := by decide +kernel
theorem cellsSound1230 : ∀ c∈certificate1230.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4267,MergedCutCells.Batch355.certificate4268], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4267,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4268,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1230 : ∀ c∈certificate1230.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4267,MergedCutCells.Batch355.certificate4268], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4267,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4268,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1230 : ∀ c∈certificate1230.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4267,MergedCutCells.Batch355.certificate4268], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid411,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid411,List.forall_mem_nil _⟩⟩
theorem populationMatches1230 : ∀ c∈certificate1230.cells, c.population=certificate1230.population := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4267,MergedCutCells.Batch355.certificate4268], c.population=PopulationCertificates.Batch041.certificate820
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1230 {x : ℝ} (hx : certificate1230.interval.Contains x) : ∃ c∈certificate1230.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1230 numericValid1230 hx

def certificate1231 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate820,PopulationCertificates.Batch041.certificate820,[MergedCutCells.Batch355.certificate4269,MergedCutCells.Batch355.certificate4270,MergedCutCells.Batch355.certificate4271,MergedCutCells.Batch356.certificate4272],(22887559/20000000),none,(1/2),(487462809080951509/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1231 : certificate1231.NumericValid := by decide +kernel
theorem cellsSound1231 : ∀ c∈certificate1231.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4269,MergedCutCells.Batch355.certificate4270,MergedCutCells.Batch355.certificate4271,MergedCutCells.Batch356.certificate4272], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4270,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.sound4271,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4272,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1231 : ∀ c∈certificate1231.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4269,MergedCutCells.Batch355.certificate4270,MergedCutCells.Batch355.certificate4271,MergedCutCells.Batch356.certificate4272], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4270,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch355.numericValid4271,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4272,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1231 : ∀ c∈certificate1231.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4269,MergedCutCells.Batch355.certificate4270,MergedCutCells.Batch355.certificate4271,MergedCutCells.Batch356.certificate4272], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1231 : ∀ c∈certificate1231.cells, c.population=certificate1231.population := by
  change ∀ c∈[MergedCutCells.Batch355.certificate4269,MergedCutCells.Batch355.certificate4270,MergedCutCells.Batch355.certificate4271,MergedCutCells.Batch356.certificate4272], c.population=PopulationCertificates.Batch041.certificate820
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1231 {x : ℝ} (hx : certificate1231.interval.Contains x) : ∃ c∈certificate1231.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1231 numericValid1231 hx

def certificate1232 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate821,PopulationCertificates.Batch041.certificate821,[MergedCutCells.Batch356.certificate4273,MergedCutCells.Batch356.certificate4274],(22838287855339009149/1000000000000000000),none,(1/2),(11871459731731194271/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1232 : certificate1232.NumericValid := by decide +kernel
theorem cellsSound1232 : ∀ c∈certificate1232.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4273,MergedCutCells.Batch356.certificate4274], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4273,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4274,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1232 : ∀ c∈certificate1232.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4273,MergedCutCells.Batch356.certificate4274], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4273,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4274,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1232 : ∀ c∈certificate1232.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4273,MergedCutCells.Batch356.certificate4274], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1232 : ∀ c∈certificate1232.cells, c.population=certificate1232.population := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4273,MergedCutCells.Batch356.certificate4274], c.population=PopulationCertificates.Batch041.certificate821
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1232 {x : ℝ} (hx : certificate1232.interval.Contains x) : ∃ c∈certificate1232.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1232 numericValid1232 hx

def certificate1233 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate822,PopulationCertificates.Batch041.certificate822,[MergedCutCells.Batch356.certificate4275,MergedCutCells.Batch356.certificate4276],(837855431985250361/1000000000000000000),(some (281511541/250000000)),(1/2),(1035482264168425967/500000000000000000),(some (160220289719504979/1000000000000000000)),(some (7518763520299381/200000000000000000))⟩
theorem numericValid1233 : certificate1233.NumericValid := by decide +kernel
theorem cellsSound1233 : ∀ c∈certificate1233.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4275,MergedCutCells.Batch356.certificate4276], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4276,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1233 : ∀ c∈certificate1233.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4275,MergedCutCells.Batch356.certificate4276], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4276,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1233 : ∀ c∈certificate1233.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4275,MergedCutCells.Batch356.certificate4276], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid412,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid412,List.forall_mem_nil _⟩⟩
theorem populationMatches1233 : ∀ c∈certificate1233.cells, c.population=certificate1233.population := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4275,MergedCutCells.Batch356.certificate4276], c.population=PopulationCertificates.Batch041.certificate822
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1233 {x : ℝ} (hx : certificate1233.interval.Contains x) : ∃ c∈certificate1233.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1233 numericValid1233 hx

def certificate1234 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate822,PopulationCertificates.Batch041.certificate822,[MergedCutCells.Batch356.certificate4277,MergedCutCells.Batch356.certificate4278,MergedCutCells.Batch356.certificate4279,MergedCutCells.Batch356.certificate4280],(281511541/250000000),none,(1/2),(2057035952001207619/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1234 : certificate1234.NumericValid := by decide +kernel
theorem cellsSound1234 : ∀ c∈certificate1234.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4277,MergedCutCells.Batch356.certificate4278,MergedCutCells.Batch356.certificate4279,MergedCutCells.Batch356.certificate4280], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4277,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4278,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4279,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4280,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1234 : ∀ c∈certificate1234.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4277,MergedCutCells.Batch356.certificate4278,MergedCutCells.Batch356.certificate4279,MergedCutCells.Batch356.certificate4280], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4277,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4278,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4279,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4280,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1234 : ∀ c∈certificate1234.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4277,MergedCutCells.Batch356.certificate4278,MergedCutCells.Batch356.certificate4279,MergedCutCells.Batch356.certificate4280], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1234 : ∀ c∈certificate1234.cells, c.population=certificate1234.population := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4277,MergedCutCells.Batch356.certificate4278,MergedCutCells.Batch356.certificate4279,MergedCutCells.Batch356.certificate4280], c.population=PopulationCertificates.Batch041.certificate822
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1234 {x : ℝ} (hx : certificate1234.interval.Contains x) : ∃ c∈certificate1234.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1234 numericValid1234 hx

def certificate1235 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate823,PopulationCertificates.Batch041.certificate823,[MergedCutCells.Batch356.certificate4281,MergedCutCells.Batch356.certificate4282],(22559071014967306293/1000000000000000000),none,(1/2),(5996537182553424627/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1235 : certificate1235.NumericValid := by decide +kernel
theorem cellsSound1235 : ∀ c∈certificate1235.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4281,MergedCutCells.Batch356.certificate4282], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4281,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.sound4282,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1235 : ∀ c∈certificate1235.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4281,MergedCutCells.Batch356.certificate4282], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4281,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch356.numericValid4282,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1235 : ∀ c∈certificate1235.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4281,MergedCutCells.Batch356.certificate4282], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1235 : ∀ c∈certificate1235.cells, c.population=certificate1235.population := by
  change ∀ c∈[MergedCutCells.Batch356.certificate4281,MergedCutCells.Batch356.certificate4282], c.population=PopulationCertificates.Batch041.certificate823
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1235 {x : ℝ} (hx : certificate1235.interval.Contains x) : ∃ c∈certificate1235.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1235 numericValid1235 hx

end Cycle12.MergedCutGroups.Batch102
