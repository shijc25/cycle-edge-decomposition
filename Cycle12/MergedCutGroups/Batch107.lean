import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch042
import Cycle12.GeometryCertificates.Batch043
import Cycle12.MergedCutCells.Batch366
import Cycle12.MergedCutCells.Batch367
import Cycle12.MergedCutCells.Batch368
import Cycle12.MergedCutCells.Batch369
import Cycle12.PopulationCertificates.Batch042
import Cycle12.PopulationCertificates.Batch043

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch107

def certificate1284 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate859,PopulationCertificates.Batch042.certificate859,[MergedCutCells.Batch366.certificate4403,MergedCutCells.Batch367.certificate4404,MergedCutCells.Batch367.certificate4405,MergedCutCells.Batch367.certificate4406],(164856619564054827/250000000000000000),none,(1/40),(59557126345653697/1000000000000000000),none,none⟩
theorem numericValid1284 : certificate1284.NumericValid := by decide +kernel
theorem cellsSound1284 : ∀ c∈certificate1284.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4403,MergedCutCells.Batch367.certificate4404,MergedCutCells.Batch367.certificate4405,MergedCutCells.Batch367.certificate4406], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4403,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4404,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4405,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4406,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1284 : ∀ c∈certificate1284.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4403,MergedCutCells.Batch367.certificate4404,MergedCutCells.Batch367.certificate4405,MergedCutCells.Batch367.certificate4406], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4403,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4404,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4405,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4406,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1284 : ∀ c∈certificate1284.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4403,MergedCutCells.Batch367.certificate4404,MergedCutCells.Batch367.certificate4405,MergedCutCells.Batch367.certificate4406], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid453,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid454,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid455,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid456,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1284 : ∀ c∈certificate1284.cells, c.population=certificate1284.population := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4403,MergedCutCells.Batch367.certificate4404,MergedCutCells.Batch367.certificate4405,MergedCutCells.Batch367.certificate4406], c.population=PopulationCertificates.Batch042.certificate859
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1284 {x : ℝ} (hx : certificate1284.interval.Contains x) : ∃ c∈certificate1284.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1284 numericValid1284 hx

def certificate1285 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate860,PopulationCertificates.Batch043.certificate860,[MergedCutCells.Batch367.certificate4407,MergedCutCells.Batch367.certificate4408],(147556396243375137/250000000000000000),(some (1267858449/1000000000)),(1/2),(213093518353844983/500000000000000000),(some (170212688811061/62500000000000000)),(some (149379404738687/500000000000000000))⟩
theorem numericValid1285 : certificate1285.NumericValid := by decide +kernel
theorem cellsSound1285 : ∀ c∈certificate1285.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4407,MergedCutCells.Batch367.certificate4408], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4408,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1285 : ∀ c∈certificate1285.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4407,MergedCutCells.Batch367.certificate4408], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4408,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1285 : ∀ c∈certificate1285.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4407,MergedCutCells.Batch367.certificate4408], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid457,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid457,List.forall_mem_nil _⟩⟩
theorem populationMatches1285 : ∀ c∈certificate1285.cells, c.population=certificate1285.population := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4407,MergedCutCells.Batch367.certificate4408], c.population=PopulationCertificates.Batch043.certificate860
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1285 {x : ℝ} (hx : certificate1285.interval.Contains x) : ∃ c∈certificate1285.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1285 numericValid1285 hx

def certificate1286 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate860,PopulationCertificates.Batch043.certificate860,[MergedCutCells.Batch367.certificate4409,MergedCutCells.Batch367.certificate4410,MergedCutCells.Batch367.certificate4411],(1267858449/1000000000),none,(1/2),(85106804718980091/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1286 : certificate1286.NumericValid := by decide +kernel
theorem cellsSound1286 : ∀ c∈certificate1286.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4409,MergedCutCells.Batch367.certificate4410,MergedCutCells.Batch367.certificate4411], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4409,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4410,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4411,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1286 : ∀ c∈certificate1286.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4409,MergedCutCells.Batch367.certificate4410,MergedCutCells.Batch367.certificate4411], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4409,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4410,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4411,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1286 : ∀ c∈certificate1286.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4409,MergedCutCells.Batch367.certificate4410,MergedCutCells.Batch367.certificate4411], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1286 : ∀ c∈certificate1286.cells, c.population=certificate1286.population := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4409,MergedCutCells.Batch367.certificate4410,MergedCutCells.Batch367.certificate4411], c.population=PopulationCertificates.Batch043.certificate860
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1286 {x : ℝ} (hx : certificate1286.interval.Contains x) : ∃ c∈certificate1286.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1286 numericValid1286 hx

def certificate1287 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate861,PopulationCertificates.Batch043.certificate861,[MergedCutCells.Batch367.certificate4412,MergedCutCells.Batch367.certificate4413],(4153433896437213359/250000000000000000),none,(1/2),(1116324656269161833/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1287 : certificate1287.NumericValid := by decide +kernel
theorem cellsSound1287 : ∀ c∈certificate1287.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4412,MergedCutCells.Batch367.certificate4413], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4413,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1287 : ∀ c∈certificate1287.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4412,MergedCutCells.Batch367.certificate4413], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4413,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1287 : ∀ c∈certificate1287.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4412,MergedCutCells.Batch367.certificate4413], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1287 : ∀ c∈certificate1287.cells, c.population=certificate1287.population := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4412,MergedCutCells.Batch367.certificate4413], c.population=PopulationCertificates.Batch043.certificate861
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1287 {x : ℝ} (hx : certificate1287.interval.Contains x) : ∃ c∈certificate1287.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1287 numericValid1287 hx

def certificate1288 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate862,PopulationCertificates.Batch043.certificate862,[MergedCutCells.Batch367.certificate4414,MergedCutCells.Batch367.certificate4415,MergedCutCells.Batch368.certificate4416,MergedCutCells.Batch368.certificate4417],(20697957548078243/31250000000000000),none,(1/40),(64073628517823677/1000000000000000000),none,none⟩
theorem numericValid1288 : certificate1288.NumericValid := by decide +kernel
theorem cellsSound1288 : ∀ c∈certificate1288.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4414,MergedCutCells.Batch367.certificate4415,MergedCutCells.Batch368.certificate4416,MergedCutCells.Batch368.certificate4417], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4414,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.sound4415,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4416,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4417,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1288 : ∀ c∈certificate1288.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4414,MergedCutCells.Batch367.certificate4415,MergedCutCells.Batch368.certificate4416,MergedCutCells.Batch368.certificate4417], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4414,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch367.numericValid4415,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4416,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4417,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1288 : ∀ c∈certificate1288.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4414,MergedCutCells.Batch367.certificate4415,MergedCutCells.Batch368.certificate4416,MergedCutCells.Batch368.certificate4417], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid458,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid459,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid460,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid461,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1288 : ∀ c∈certificate1288.cells, c.population=certificate1288.population := by
  change ∀ c∈[MergedCutCells.Batch367.certificate4414,MergedCutCells.Batch367.certificate4415,MergedCutCells.Batch368.certificate4416,MergedCutCells.Batch368.certificate4417], c.population=PopulationCertificates.Batch043.certificate862
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1288 {x : ℝ} (hx : certificate1288.interval.Contains x) : ∃ c∈certificate1288.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1288 numericValid1288 hx

def certificate1289 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate863,PopulationCertificates.Batch043.certificate863,[MergedCutCells.Batch368.certificate4418,MergedCutCells.Batch368.certificate4419],(595981097177843343/1000000000000000000),(some (255639287/200000000)),(1/2),(224311837656373191/500000000000000000),(some (3098690758940683/1000000000000000000)),(some (172714650615681/500000000000000000))⟩
theorem numericValid1289 : certificate1289.NumericValid := by decide +kernel
theorem cellsSound1289 : ∀ c∈certificate1289.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4418,MergedCutCells.Batch368.certificate4419], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4418,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4419,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1289 : ∀ c∈certificate1289.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4418,MergedCutCells.Batch368.certificate4419], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4418,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4419,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1289 : ∀ c∈certificate1289.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4418,MergedCutCells.Batch368.certificate4419], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid462,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid462,List.forall_mem_nil _⟩⟩
theorem populationMatches1289 : ∀ c∈certificate1289.cells, c.population=certificate1289.population := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4418,MergedCutCells.Batch368.certificate4419], c.population=PopulationCertificates.Batch043.certificate863
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1289 {x : ℝ} (hx : certificate1289.interval.Contains x) : ∃ c∈certificate1289.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1289 numericValid1289 hx

def certificate1290 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate863,PopulationCertificates.Batch043.certificate863,[MergedCutCells.Batch368.certificate4420,MergedCutCells.Batch368.certificate4421,MergedCutCells.Batch368.certificate4422],(255639287/200000000),none,(1/2),(223636416194917443/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1290 : certificate1290.NumericValid := by decide +kernel
theorem cellsSound1290 : ∀ c∈certificate1290.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4420,MergedCutCells.Batch368.certificate4421,MergedCutCells.Batch368.certificate4422], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4420,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4421,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4422,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1290 : ∀ c∈certificate1290.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4420,MergedCutCells.Batch368.certificate4421,MergedCutCells.Batch368.certificate4422], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4420,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4421,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4422,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1290 : ∀ c∈certificate1290.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4420,MergedCutCells.Batch368.certificate4421,MergedCutCells.Batch368.certificate4422], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1290 : ∀ c∈certificate1290.cells, c.population=certificate1290.population := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4420,MergedCutCells.Batch368.certificate4421,MergedCutCells.Batch368.certificate4422], c.population=PopulationCertificates.Batch043.certificate863
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1290 {x : ℝ} (hx : certificate1290.interval.Contains x) : ∃ c∈certificate1290.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1290 numericValid1290 hx

def certificate1291 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate864,PopulationCertificates.Batch043.certificate864,[MergedCutCells.Batch368.certificate4423,MergedCutCells.Batch368.certificate4424],(16803934404520606377/1000000000000000000),none,(1/2),(4551390020494545399/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1291 : certificate1291.NumericValid := by decide +kernel
theorem cellsSound1291 : ∀ c∈certificate1291.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4423,MergedCutCells.Batch368.certificate4424], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4423,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4424,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1291 : ∀ c∈certificate1291.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4423,MergedCutCells.Batch368.certificate4424], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4423,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4424,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1291 : ∀ c∈certificate1291.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4423,MergedCutCells.Batch368.certificate4424], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1291 : ∀ c∈certificate1291.cells, c.population=certificate1291.population := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4423,MergedCutCells.Batch368.certificate4424], c.population=PopulationCertificates.Batch043.certificate864
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1291 {x : ℝ} (hx : certificate1291.interval.Contains x) : ∃ c∈certificate1291.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1291 numericValid1291 hx

def certificate1292 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate865,PopulationCertificates.Batch043.certificate865,[MergedCutCells.Batch368.certificate4425,MergedCutCells.Batch368.certificate4426,MergedCutCells.Batch368.certificate4427,MergedCutCells.Batch369.certificate4428],(166315536801124989/250000000000000000),none,(1/40),(68773452964919943/1000000000000000000),none,none⟩
theorem numericValid1292 : certificate1292.NumericValid := by decide +kernel
theorem cellsSound1292 : ∀ c∈certificate1292.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4425,MergedCutCells.Batch368.certificate4426,MergedCutCells.Batch368.certificate4427,MergedCutCells.Batch369.certificate4428], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4426,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.sound4427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4428,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1292 : ∀ c∈certificate1292.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4425,MergedCutCells.Batch368.certificate4426,MergedCutCells.Batch368.certificate4427,MergedCutCells.Batch369.certificate4428], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4426,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch368.numericValid4427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4428,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1292 : ∀ c∈certificate1292.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4425,MergedCutCells.Batch368.certificate4426,MergedCutCells.Batch368.certificate4427,MergedCutCells.Batch369.certificate4428], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid463,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid464,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid465,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid466,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1292 : ∀ c∈certificate1292.cells, c.population=certificate1292.population := by
  change ∀ c∈[MergedCutCells.Batch368.certificate4425,MergedCutCells.Batch368.certificate4426,MergedCutCells.Batch368.certificate4427,MergedCutCells.Batch369.certificate4428], c.population=PopulationCertificates.Batch043.certificate865
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1292 {x : ℝ} (hx : certificate1292.interval.Contains x) : ∃ c∈certificate1292.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1292 numericValid1292 hx

def certificate1293 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate866,PopulationCertificates.Batch043.certificate866,[MergedCutCells.Batch369.certificate4429,MergedCutCells.Batch369.certificate4430],(600141904017421419/1000000000000000000),(some (642829941/500000000)),(1/2),(468240896180363709/1000000000000000000),(some (436355418867333/125000000000000000)),(some (395058010641621/1000000000000000000))⟩
theorem numericValid1293 : certificate1293.NumericValid := by decide +kernel
theorem cellsSound1293 : ∀ c∈certificate1293.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4429,MergedCutCells.Batch369.certificate4430], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4429,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4430,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1293 : ∀ c∈certificate1293.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4429,MergedCutCells.Batch369.certificate4430], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4429,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4430,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1293 : ∀ c∈certificate1293.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4429,MergedCutCells.Batch369.certificate4430], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid467,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid467,List.forall_mem_nil _⟩⟩
theorem populationMatches1293 : ∀ c∈certificate1293.cells, c.population=certificate1293.population := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4429,MergedCutCells.Batch369.certificate4430], c.population=PopulationCertificates.Batch043.certificate866
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1293 {x : ℝ} (hx : certificate1293.interval.Contains x) : ∃ c∈certificate1293.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1293 numericValid1293 hx

def certificate1294 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate866,PopulationCertificates.Batch043.certificate866,[MergedCutCells.Batch369.certificate4431,MergedCutCells.Batch369.certificate4432,MergedCutCells.Batch369.certificate4433],(642829941/500000000),none,(1/2),(468204837651373967/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1294 : certificate1294.NumericValid := by decide +kernel
theorem cellsSound1294 : ∀ c∈certificate1294.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4431,MergedCutCells.Batch369.certificate4432,MergedCutCells.Batch369.certificate4433], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4431,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4433,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1294 : ∀ c∈certificate1294.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4431,MergedCutCells.Batch369.certificate4432,MergedCutCells.Batch369.certificate4433], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4431,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4433,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1294 : ∀ c∈certificate1294.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4431,MergedCutCells.Batch369.certificate4432,MergedCutCells.Batch369.certificate4433], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1294 : ∀ c∈certificate1294.cells, c.population=certificate1294.population := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4431,MergedCutCells.Batch369.certificate4432,MergedCutCells.Batch369.certificate4433], c.population=PopulationCertificates.Batch043.certificate866
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1294 {x : ℝ} (hx : certificate1294.interval.Contains x) : ∃ c∈certificate1294.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1294 numericValid1294 hx

def certificate1295 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate867,PopulationCertificates.Batch043.certificate867,[MergedCutCells.Batch369.certificate4434,MergedCutCells.Batch369.certificate4435],(2124736048827398507/125000000000000000),none,(1/2),(2319689473334097903/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1295 : certificate1295.NumericValid := by decide +kernel
theorem cellsSound1295 : ∀ c∈certificate1295.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4434,MergedCutCells.Batch369.certificate4435], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4434,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4435,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1295 : ∀ c∈certificate1295.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4434,MergedCutCells.Batch369.certificate4435], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4434,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4435,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1295 : ∀ c∈certificate1295.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4434,MergedCutCells.Batch369.certificate4435], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1295 : ∀ c∈certificate1295.cells, c.population=certificate1295.population := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4434,MergedCutCells.Batch369.certificate4435], c.population=PopulationCertificates.Batch043.certificate867
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1295 {x : ℝ} (hx : certificate1295.interval.Contains x) : ∃ c∈certificate1295.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1295 numericValid1295 hx

end Cycle12.MergedCutGroups.Batch107
