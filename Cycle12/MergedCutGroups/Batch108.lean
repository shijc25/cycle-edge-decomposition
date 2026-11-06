import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch043
import Cycle12.MergedCutCells.Batch369
import Cycle12.MergedCutCells.Batch370
import Cycle12.MergedCutCells.Batch371
import Cycle12.MergedCutCells.Batch372
import Cycle12.PopulationCertificates.Batch043

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch108

def certificate1296 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate868,PopulationCertificates.Batch043.certificate868,[MergedCutCells.Batch369.certificate4436,MergedCutCells.Batch369.certificate4437,MergedCutCells.Batch369.certificate4438,MergedCutCells.Batch369.certificate4439],(66820769607750147/100000000000000000),none,(1/40),(71933801435119/976562500000000),none,none⟩
theorem numericValid1296 : certificate1296.NumericValid := by decide +kernel
theorem cellsSound1296 : ∀ c∈certificate1296.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4436,MergedCutCells.Batch369.certificate4437,MergedCutCells.Batch369.certificate4438,MergedCutCells.Batch369.certificate4439], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4436,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4437,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.sound4439,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1296 : ∀ c∈certificate1296.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4436,MergedCutCells.Batch369.certificate4437,MergedCutCells.Batch369.certificate4438,MergedCutCells.Batch369.certificate4439], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4436,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4437,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch369.numericValid4439,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1296 : ∀ c∈certificate1296.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4436,MergedCutCells.Batch369.certificate4437,MergedCutCells.Batch369.certificate4438,MergedCutCells.Batch369.certificate4439], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid468,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid469,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid470,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid471,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1296 : ∀ c∈certificate1296.cells, c.population=certificate1296.population := by
  change ∀ c∈[MergedCutCells.Batch369.certificate4436,MergedCutCells.Batch369.certificate4437,MergedCutCells.Batch369.certificate4438,MergedCutCells.Batch369.certificate4439], c.population=PopulationCertificates.Batch043.certificate868
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1296 {x : ℝ} (hx : certificate1296.interval.Contains x) : ∃ c∈certificate1296.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1296 numericValid1296 hx

def certificate1297 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate869,PopulationCertificates.Batch043.certificate869,[MergedCutCells.Batch370.certificate4440,MergedCutCells.Batch370.certificate4441],(604401151938475349/1000000000000000000),(some (1266866319/1000000000)),(1/2),(3823803625161943/7812500000000000),(some (3878580150077691/1000000000000000000)),(some (111231211617983/250000000000000000))⟩
theorem numericValid1297 : certificate1297.NumericValid := by decide +kernel
theorem cellsSound1297 : ∀ c∈certificate1297.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4440,MergedCutCells.Batch370.certificate4441], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4440,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4441,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1297 : ∀ c∈certificate1297.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4440,MergedCutCells.Batch370.certificate4441], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4440,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4441,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1297 : ∀ c∈certificate1297.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4440,MergedCutCells.Batch370.certificate4441], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid472,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid472,List.forall_mem_nil _⟩⟩
theorem populationMatches1297 : ∀ c∈certificate1297.cells, c.population=certificate1297.population := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4440,MergedCutCells.Batch370.certificate4441], c.population=PopulationCertificates.Batch043.certificate869
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1297 {x : ℝ} (hx : certificate1297.interval.Contains x) : ∃ c∈certificate1297.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1297 numericValid1297 hx

def certificate1298 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate869,PopulationCertificates.Batch043.certificate869,[MergedCutCells.Batch370.certificate4442,MergedCutCells.Batch370.certificate4443,MergedCutCells.Batch370.certificate4444],(1266866319/1000000000),none,(1/2),(244731423417265399/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1298 : certificate1298.NumericValid := by decide +kernel
theorem cellsSound1298 : ∀ c∈certificate1298.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4442,MergedCutCells.Batch370.certificate4443,MergedCutCells.Batch370.certificate4444], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4442,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4443,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4444,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1298 : ∀ c∈certificate1298.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4442,MergedCutCells.Batch370.certificate4443,MergedCutCells.Batch370.certificate4444], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4442,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4443,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4444,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1298 : ∀ c∈certificate1298.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4442,MergedCutCells.Batch370.certificate4443,MergedCutCells.Batch370.certificate4444], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1298 : ∀ c∈certificate1298.cells, c.population=certificate1298.population := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4442,MergedCutCells.Batch370.certificate4443,MergedCutCells.Batch370.certificate4444], c.population=PopulationCertificates.Batch043.certificate869
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1298 {x : ℝ} (hx : certificate1298.interval.Contains x) : ∃ c∈certificate1298.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1298 numericValid1298 hx

def certificate1299 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate870,PopulationCertificates.Batch043.certificate870,[MergedCutCells.Batch370.certificate4445,MergedCutCells.Batch370.certificate4446],(17195704096029440333/1000000000000000000),none,(1/2),(2364481353189313629/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1299 : certificate1299.NumericValid := by decide +kernel
theorem cellsSound1299 : ∀ c∈certificate1299.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4445,MergedCutCells.Batch370.certificate4446], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4445,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4446,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1299 : ∀ c∈certificate1299.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4445,MergedCutCells.Batch370.certificate4446], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4445,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4446,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1299 : ∀ c∈certificate1299.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4445,MergedCutCells.Batch370.certificate4446], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1299 : ∀ c∈certificate1299.cells, c.population=certificate1299.population := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4445,MergedCutCells.Batch370.certificate4446], c.population=PopulationCertificates.Batch043.certificate870
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1299 {x : ℝ} (hx : certificate1299.interval.Contains x) : ∃ c∈certificate1299.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1299 numericValid1299 hx

def certificate1300 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate871,PopulationCertificates.Batch043.certificate871,[MergedCutCells.Batch370.certificate4447,MergedCutCells.Batch370.certificate4448,MergedCutCells.Batch370.certificate4449,MergedCutCells.Batch370.certificate4450],(671175749458073293/1000000000000000000),none,(1/40),(39368796447788789/500000000000000000),none,none⟩
theorem numericValid1300 : certificate1300.NumericValid := by decide +kernel
theorem cellsSound1300 : ∀ c∈certificate1300.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4447,MergedCutCells.Batch370.certificate4448,MergedCutCells.Batch370.certificate4449,MergedCutCells.Batch370.certificate4450], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4447,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4448,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4449,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4450,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1300 : ∀ c∈certificate1300.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4447,MergedCutCells.Batch370.certificate4448,MergedCutCells.Batch370.certificate4449,MergedCutCells.Batch370.certificate4450], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4447,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4448,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4449,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4450,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1300 : ∀ c∈certificate1300.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4447,MergedCutCells.Batch370.certificate4448,MergedCutCells.Batch370.certificate4449,MergedCutCells.Batch370.certificate4450], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid473,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid474,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid475,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid476,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1300 : ∀ c∈certificate1300.cells, c.population=certificate1300.population := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4447,MergedCutCells.Batch370.certificate4448,MergedCutCells.Batch370.certificate4449,MergedCutCells.Batch370.certificate4450], c.population=PopulationCertificates.Batch043.certificate871
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1300 {x : ℝ} (hx : certificate1300.interval.Contains x) : ∃ c∈certificate1300.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1300 numericValid1300 hx

def certificate1301 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate872,PopulationCertificates.Batch043.certificate872,[MergedCutCells.Batch370.certificate4451,MergedCutCells.Batch371.certificate4452],(608046395450615409/1000000000000000000),(some (1273291123/1000000000)),(1/2),(31873689124433269/62500000000000000),(some (860821567144351/200000000000000000)),(some (500497588714269/1000000000000000000))⟩
theorem numericValid1301 : certificate1301.NumericValid := by decide +kernel
theorem cellsSound1301 : ∀ c∈certificate1301.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4451,MergedCutCells.Batch371.certificate4452], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.sound4451,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4452,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1301 : ∀ c∈certificate1301.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4451,MergedCutCells.Batch371.certificate4452], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch370.numericValid4451,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4452,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1301 : ∀ c∈certificate1301.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4451,MergedCutCells.Batch371.certificate4452], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid477,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid477,List.forall_mem_nil _⟩⟩
theorem populationMatches1301 : ∀ c∈certificate1301.cells, c.population=certificate1301.population := by
  change ∀ c∈[MergedCutCells.Batch370.certificate4451,MergedCutCells.Batch371.certificate4452], c.population=PopulationCertificates.Batch043.certificate872
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1301 {x : ℝ} (hx : certificate1301.interval.Contains x) : ∃ c∈certificate1301.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1301 numericValid1301 hx

def certificate1302 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate872,PopulationCertificates.Batch043.certificate872,[MergedCutCells.Batch371.certificate4453,MergedCutCells.Batch371.certificate4454,MergedCutCells.Batch371.certificate4455],(1273291123/1000000000),none,(1/2),(510033239707567721/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1302 : certificate1302.NumericValid := by decide +kernel
theorem cellsSound1302 : ∀ c∈certificate1302.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4453,MergedCutCells.Batch371.certificate4454,MergedCutCells.Batch371.certificate4455], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4454,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4455,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1302 : ∀ c∈certificate1302.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4453,MergedCutCells.Batch371.certificate4454,MergedCutCells.Batch371.certificate4455], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4454,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4455,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1302 : ∀ c∈certificate1302.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4453,MergedCutCells.Batch371.certificate4454,MergedCutCells.Batch371.certificate4455], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1302 : ∀ c∈certificate1302.cells, c.population=certificate1302.population := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4453,MergedCutCells.Batch371.certificate4454,MergedCutCells.Batch371.certificate4455], c.population=PopulationCertificates.Batch043.certificate872
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1302 {x : ℝ} (hx : certificate1302.interval.Contains x) : ∃ c∈certificate1302.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1302 numericValid1302 hx

def certificate1303 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate873,PopulationCertificates.Batch043.certificate873,[MergedCutCells.Batch371.certificate4456,MergedCutCells.Batch371.certificate4457],(8698746124664660087/500000000000000000),none,(1/2),(4809712274844787483/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1303 : certificate1303.NumericValid := by decide +kernel
theorem cellsSound1303 : ∀ c∈certificate1303.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4456,MergedCutCells.Batch371.certificate4457], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4456,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4457,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1303 : ∀ c∈certificate1303.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4456,MergedCutCells.Batch371.certificate4457], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4456,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4457,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1303 : ∀ c∈certificate1303.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4456,MergedCutCells.Batch371.certificate4457], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1303 : ∀ c∈certificate1303.cells, c.population=certificate1303.population := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4456,MergedCutCells.Batch371.certificate4457], c.population=PopulationCertificates.Batch043.certificate873
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1303 {x : ℝ} (hx : certificate1303.interval.Contains x) : ∃ c∈certificate1303.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1303 numericValid1303 hx

def certificate1304 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate874,PopulationCertificates.Batch043.certificate874,[MergedCutCells.Batch371.certificate4458,MergedCutCells.Batch371.certificate4459,MergedCutCells.Batch371.certificate4460,MergedCutCells.Batch371.certificate4461],(168541172063268489/250000000000000000),none,(1/40),(42004970579158039/500000000000000000),none,none⟩
theorem numericValid1304 : certificate1304.NumericValid := by decide +kernel
theorem cellsSound1304 : ∀ c∈certificate1304.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4458,MergedCutCells.Batch371.certificate4459,MergedCutCells.Batch371.certificate4460,MergedCutCells.Batch371.certificate4461], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4460,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4461,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1304 : ∀ c∈certificate1304.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4458,MergedCutCells.Batch371.certificate4459,MergedCutCells.Batch371.certificate4460,MergedCutCells.Batch371.certificate4461], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4460,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4461,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1304 : ∀ c∈certificate1304.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4458,MergedCutCells.Batch371.certificate4459,MergedCutCells.Batch371.certificate4460,MergedCutCells.Batch371.certificate4461], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid478,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy023.valid479,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid480,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid481,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1304 : ∀ c∈certificate1304.cells, c.population=certificate1304.population := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4458,MergedCutCells.Batch371.certificate4459,MergedCutCells.Batch371.certificate4460,MergedCutCells.Batch371.certificate4461], c.population=PopulationCertificates.Batch043.certificate874
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1304 {x : ℝ} (hx : certificate1304.interval.Contains x) : ∃ c∈certificate1304.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1304 numericValid1304 hx

def certificate1305 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate875,PopulationCertificates.Batch043.certificate875,[MergedCutCells.Batch371.certificate4462,MergedCutCells.Batch371.certificate4463],(306490328124407327/500000000000000000),(some (320494529/250000000)),(1/2),(266694756722153391/500000000000000000),(some (2378951912830617/500000000000000000)),(some (560670459951393/1000000000000000000))⟩
theorem numericValid1305 : certificate1305.NumericValid := by decide +kernel
theorem cellsSound1305 : ∀ c∈certificate1305.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4462,MergedCutCells.Batch371.certificate4463], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4462,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.sound4463,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1305 : ∀ c∈certificate1305.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4462,MergedCutCells.Batch371.certificate4463], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4462,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch371.numericValid4463,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1305 : ∀ c∈certificate1305.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4462,MergedCutCells.Batch371.certificate4463], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid482,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid482,List.forall_mem_nil _⟩⟩
theorem populationMatches1305 : ∀ c∈certificate1305.cells, c.population=certificate1305.population := by
  change ∀ c∈[MergedCutCells.Batch371.certificate4462,MergedCutCells.Batch371.certificate4463], c.population=PopulationCertificates.Batch043.certificate875
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1305 {x : ℝ} (hx : certificate1305.interval.Contains x) : ∃ c∈certificate1305.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1305 numericValid1305 hx

def certificate1306 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate875,PopulationCertificates.Batch043.certificate875,[MergedCutCells.Batch372.certificate4464,MergedCutCells.Batch372.certificate4465,MergedCutCells.Batch372.certificate4466],(320494529/250000000),none,(1/2),(106654030833539781/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1306 : certificate1306.NumericValid := by decide +kernel
theorem cellsSound1306 : ∀ c∈certificate1306.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4464,MergedCutCells.Batch372.certificate4465,MergedCutCells.Batch372.certificate4466], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4464,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4466,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1306 : ∀ c∈certificate1306.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4464,MergedCutCells.Batch372.certificate4465,MergedCutCells.Batch372.certificate4466], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4464,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4466,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1306 : ∀ c∈certificate1306.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4464,MergedCutCells.Batch372.certificate4465,MergedCutCells.Batch372.certificate4466], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1306 : ∀ c∈certificate1306.cells, c.population=certificate1306.population := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4464,MergedCutCells.Batch372.certificate4465,MergedCutCells.Batch372.certificate4466], c.population=PopulationCertificates.Batch043.certificate875
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1306 {x : ℝ} (hx : certificate1306.interval.Contains x) : ∃ c∈certificate1306.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1306 numericValid1306 hx

def certificate1307 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate876,PopulationCertificates.Batch043.certificate876,[MergedCutCells.Batch372.certificate4467,MergedCutCells.Batch372.certificate4468],(8801683970370830627/500000000000000000),none,(1/2),(49134596146514969/10000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1307 : certificate1307.NumericValid := by decide +kernel
theorem cellsSound1307 : ∀ c∈certificate1307.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4467,MergedCutCells.Batch372.certificate4468], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4467,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4468,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1307 : ∀ c∈certificate1307.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4467,MergedCutCells.Batch372.certificate4468], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4467,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4468,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1307 : ∀ c∈certificate1307.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4467,MergedCutCells.Batch372.certificate4468], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1307 : ∀ c∈certificate1307.cells, c.population=certificate1307.population := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4467,MergedCutCells.Batch372.certificate4468], c.population=PopulationCertificates.Batch043.certificate876
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1307 {x : ℝ} (hx : certificate1307.interval.Contains x) : ∃ c∈certificate1307.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1307 numericValid1307 hx

end Cycle12.MergedCutGroups.Batch108
