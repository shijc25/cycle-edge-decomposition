import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch044
import Cycle12.MergedCutCells.Batch375
import Cycle12.MergedCutCells.Batch376
import Cycle12.MergedCutCells.Batch377
import Cycle12.PopulationCertificates.Batch044

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch110

def certificate1320 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate886,PopulationCertificates.Batch044.certificate886,[MergedCutCells.Batch375.certificate4502,MergedCutCells.Batch375.certificate4503,MergedCutCells.Batch375.certificate4504,MergedCutCells.Batch375.certificate4505],(134081258328103031/200000000000000000),none,(1/40),(3688867566187919/62500000000000000),none,none⟩
theorem numericValid1320 : certificate1320.NumericValid := by decide +kernel
theorem cellsSound1320 : ∀ c∈certificate1320.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4502,MergedCutCells.Batch375.certificate4503,MergedCutCells.Batch375.certificate4504,MergedCutCells.Batch375.certificate4505], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4504,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4505,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1320 : ∀ c∈certificate1320.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4502,MergedCutCells.Batch375.certificate4503,MergedCutCells.Batch375.certificate4504,MergedCutCells.Batch375.certificate4505], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4504,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4505,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1320 : ∀ c∈certificate1320.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4502,MergedCutCells.Batch375.certificate4503,MergedCutCells.Batch375.certificate4504,MergedCutCells.Batch375.certificate4505], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid498,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid499,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid500,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid501,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1320 : ∀ c∈certificate1320.cells, c.population=certificate1320.population := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4502,MergedCutCells.Batch375.certificate4503,MergedCutCells.Batch375.certificate4504,MergedCutCells.Batch375.certificate4505], c.population=PopulationCertificates.Batch044.certificate886
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1320 {x : ℝ} (hx : certificate1320.interval.Contains x) : ∃ c∈certificate1320.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1320 numericValid1320 hx

def certificate1321 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate887,PopulationCertificates.Batch044.certificate887,[MergedCutCells.Batch375.certificate4506,MergedCutCells.Batch375.certificate4507],(6303104825147587/10000000000000000),(some (1254335283/1000000000)),(1/2),(626617223272028841/1000000000000000000),(some (1335083906685097/200000000000000000)),(some (824035903360659/1000000000000000000))⟩
theorem numericValid1321 : certificate1321.NumericValid := by decide +kernel
theorem cellsSound1321 : ∀ c∈certificate1321.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4506,MergedCutCells.Batch375.certificate4507], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4507,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1321 : ∀ c∈certificate1321.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4506,MergedCutCells.Batch375.certificate4507], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4507,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1321 : ∀ c∈certificate1321.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4506,MergedCutCells.Batch375.certificate4507], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid502,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid502,List.forall_mem_nil _⟩⟩
theorem populationMatches1321 : ∀ c∈certificate1321.cells, c.population=certificate1321.population := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4506,MergedCutCells.Batch375.certificate4507], c.population=PopulationCertificates.Batch044.certificate887
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1321 {x : ℝ} (hx : certificate1321.interval.Contains x) : ∃ c∈certificate1321.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1321 numericValid1321 hx

def certificate1322 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate887,PopulationCertificates.Batch044.certificate887,[MergedCutCells.Batch375.certificate4508,MergedCutCells.Batch375.certificate4509,MergedCutCells.Batch375.certificate4510],(1254335283/1000000000),none,(1/2),(78303921453585939/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1322 : certificate1322.NumericValid := by decide +kernel
theorem cellsSound1322 : ∀ c∈certificate1322.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4508,MergedCutCells.Batch375.certificate4509,MergedCutCells.Batch375.certificate4510], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4508,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4509,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4510,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1322 : ∀ c∈certificate1322.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4508,MergedCutCells.Batch375.certificate4509,MergedCutCells.Batch375.certificate4510], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4508,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4509,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4510,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1322 : ∀ c∈certificate1322.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4508,MergedCutCells.Batch375.certificate4509,MergedCutCells.Batch375.certificate4510], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1322 : ∀ c∈certificate1322.cells, c.population=certificate1322.population := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4508,MergedCutCells.Batch375.certificate4509,MergedCutCells.Batch375.certificate4510], c.population=PopulationCertificates.Batch044.certificate887
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1322 {x : ℝ} (hx : certificate1322.interval.Contains x) : ∃ c∈certificate1322.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1322 numericValid1322 hx

def certificate1323 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate888,PopulationCertificates.Batch044.certificate888,[MergedCutCells.Batch375.certificate4511,MergedCutCells.Batch376.certificate4512],(2308776454547314993/125000000000000000),none,(1/2),(1326307174468684249/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1323 : certificate1323.NumericValid := by decide +kernel
theorem cellsSound1323 : ∀ c∈certificate1323.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4511,MergedCutCells.Batch376.certificate4512], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4512,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1323 : ∀ c∈certificate1323.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4511,MergedCutCells.Batch376.certificate4512], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4512,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1323 : ∀ c∈certificate1323.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4511,MergedCutCells.Batch376.certificate4512], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1323 : ∀ c∈certificate1323.cells, c.population=certificate1323.population := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4511,MergedCutCells.Batch376.certificate4512], c.population=PopulationCertificates.Batch044.certificate888
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1323 {x : ℝ} (hx : certificate1323.interval.Contains x) : ∃ c∈certificate1323.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1323 numericValid1323 hx

def certificate1324 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate889,PopulationCertificates.Batch044.certificate889,[MergedCutCells.Batch376.certificate4513,MergedCutCells.Batch376.certificate4514,MergedCutCells.Batch376.certificate4515,MergedCutCells.Batch376.certificate4516],(336804525469761199/500000000000000000),none,(1/40),(31958993759511051/500000000000000000),none,none⟩
theorem numericValid1324 : certificate1324.NumericValid := by decide +kernel
theorem cellsSound1324 : ∀ c∈certificate1324.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4513,MergedCutCells.Batch376.certificate4514,MergedCutCells.Batch376.certificate4515,MergedCutCells.Batch376.certificate4516], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4513,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4514,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4515,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4516,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1324 : ∀ c∈certificate1324.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4513,MergedCutCells.Batch376.certificate4514,MergedCutCells.Batch376.certificate4515,MergedCutCells.Batch376.certificate4516], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4513,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4514,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4515,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4516,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1324 : ∀ c∈certificate1324.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4513,MergedCutCells.Batch376.certificate4514,MergedCutCells.Batch376.certificate4515,MergedCutCells.Batch376.certificate4516], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid503,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid504,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid505,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid506,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1324 : ∀ c∈certificate1324.cells, c.population=certificate1324.population := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4513,MergedCutCells.Batch376.certificate4514,MergedCutCells.Batch376.certificate4515,MergedCutCells.Batch376.certificate4516], c.population=PopulationCertificates.Batch044.certificate889
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1324 {x : ℝ} (hx : certificate1324.interval.Contains x) : ∃ c∈certificate1324.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1324 numericValid1324 hx

def certificate1325 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate890,PopulationCertificates.Batch044.certificate890,[MergedCutCells.Batch376.certificate4517,MergedCutCells.Batch376.certificate4518],(317852881327956603/500000000000000000),(some (1268116581/1000000000)),(1/2),(65085315011846707/100000000000000000),(some (1811773726446019/250000000000000000)),(some (905092571176711/1000000000000000000))⟩
theorem numericValid1325 : certificate1325.NumericValid := by decide +kernel
theorem cellsSound1325 : ∀ c∈certificate1325.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4517,MergedCutCells.Batch376.certificate4518], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4517,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4518,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1325 : ∀ c∈certificate1325.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4517,MergedCutCells.Batch376.certificate4518], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4517,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4518,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1325 : ∀ c∈certificate1325.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4517,MergedCutCells.Batch376.certificate4518], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid507,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid507,List.forall_mem_nil _⟩⟩
theorem populationMatches1325 : ∀ c∈certificate1325.cells, c.population=certificate1325.population := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4517,MergedCutCells.Batch376.certificate4518], c.population=PopulationCertificates.Batch044.certificate890
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1325 {x : ℝ} (hx : certificate1325.interval.Contains x) : ∃ c∈certificate1325.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1325 numericValid1325 hx

def certificate1326 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate890,PopulationCertificates.Batch044.certificate890,[MergedCutCells.Batch376.certificate4519,MergedCutCells.Batch376.certificate4520,MergedCutCells.Batch376.certificate4521],(1268116581/1000000000),none,(1/2),(162698856091137357/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1326 : certificate1326.NumericValid := by decide +kernel
theorem cellsSound1326 : ∀ c∈certificate1326.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4519,MergedCutCells.Batch376.certificate4520,MergedCutCells.Batch376.certificate4521], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4519,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4520,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4521,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1326 : ∀ c∈certificate1326.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4519,MergedCutCells.Batch376.certificate4520,MergedCutCells.Batch376.certificate4521], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4519,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4520,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4521,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1326 : ∀ c∈certificate1326.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4519,MergedCutCells.Batch376.certificate4520,MergedCutCells.Batch376.certificate4521], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1326 : ∀ c∈certificate1326.cells, c.population=certificate1326.population := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4519,MergedCutCells.Batch376.certificate4520,MergedCutCells.Batch376.certificate4521], c.population=PopulationCertificates.Batch044.certificate890
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1326 {x : ℝ} (hx : certificate1326.interval.Contains x) : ∃ c∈certificate1326.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1326 numericValid1326 hx

def certificate1327 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate891,PopulationCertificates.Batch044.certificate891,[MergedCutCells.Batch376.certificate4522,MergedCutCells.Batch376.certificate4523],(18698418081753556621/1000000000000000000),none,(1/2),(2704118928278785479/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1327 : certificate1327.NumericValid := by decide +kernel
theorem cellsSound1327 : ∀ c∈certificate1327.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4522,MergedCutCells.Batch376.certificate4523], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4522,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.sound4523,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1327 : ∀ c∈certificate1327.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4522,MergedCutCells.Batch376.certificate4523], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4522,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch376.numericValid4523,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1327 : ∀ c∈certificate1327.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4522,MergedCutCells.Batch376.certificate4523], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1327 : ∀ c∈certificate1327.cells, c.population=certificate1327.population := by
  change ∀ c∈[MergedCutCells.Batch376.certificate4522,MergedCutCells.Batch376.certificate4523], c.population=PopulationCertificates.Batch044.certificate891
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1327 {x : ℝ} (hx : certificate1327.interval.Contains x) : ∃ c∈certificate1327.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1327 numericValid1327 hx

def certificate1328 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate892,PopulationCertificates.Batch044.certificate892,[MergedCutCells.Batch377.certificate4524,MergedCutCells.Batch377.certificate4525,MergedCutCells.Batch377.certificate4526,MergedCutCells.Batch377.certificate4527],(676272471107163023/1000000000000000000),none,(1/40),(13797399687839573/200000000000000000),none,none⟩
theorem numericValid1328 : certificate1328.NumericValid := by decide +kernel
theorem cellsSound1328 : ∀ c∈certificate1328.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4524,MergedCutCells.Batch377.certificate4525,MergedCutCells.Batch377.certificate4526,MergedCutCells.Batch377.certificate4527], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4525,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4526,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4527,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1328 : ∀ c∈certificate1328.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4524,MergedCutCells.Batch377.certificate4525,MergedCutCells.Batch377.certificate4526,MergedCutCells.Batch377.certificate4527], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4525,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4526,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4527,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1328 : ∀ c∈certificate1328.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4524,MergedCutCells.Batch377.certificate4525,MergedCutCells.Batch377.certificate4526,MergedCutCells.Batch377.certificate4527], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid508,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid509,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid510,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid511,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1328 : ∀ c∈certificate1328.cells, c.population=certificate1328.population := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4524,MergedCutCells.Batch377.certificate4525,MergedCutCells.Batch377.certificate4526,MergedCutCells.Batch377.certificate4527], c.population=PopulationCertificates.Batch044.certificate892
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1328 {x : ℝ} (hx : certificate1328.interval.Contains x) : ∃ c∈certificate1328.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1328 numericValid1328 hx

def certificate1329 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate893,PopulationCertificates.Batch044.certificate893,[MergedCutCells.Batch377.certificate4528,MergedCutCells.Batch377.certificate4529],(63889709254007833/100000000000000000),(some (1273527453/1000000000)),(1/2),(676567314654271003/1000000000000000000),(some (389434674723713/50000000000000000)),(some (24571384614283/25000000000000000))⟩
theorem numericValid1329 : certificate1329.NumericValid := by decide +kernel
theorem cellsSound1329 : ∀ c∈certificate1329.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4528,MergedCutCells.Batch377.certificate4529], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4529,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1329 : ∀ c∈certificate1329.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4528,MergedCutCells.Batch377.certificate4529], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4529,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1329 : ∀ c∈certificate1329.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4528,MergedCutCells.Batch377.certificate4529], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid512,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid512,List.forall_mem_nil _⟩⟩
theorem populationMatches1329 : ∀ c∈certificate1329.cells, c.population=certificate1329.population := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4528,MergedCutCells.Batch377.certificate4529], c.population=PopulationCertificates.Batch044.certificate893
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1329 {x : ℝ} (hx : certificate1329.interval.Contains x) : ∃ c∈certificate1329.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1329 numericValid1329 hx

def certificate1330 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate893,PopulationCertificates.Batch044.certificate893,[MergedCutCells.Batch377.certificate4530,MergedCutCells.Batch377.certificate4531,MergedCutCells.Batch377.certificate4532],(1273527453/1000000000),none,(1/2),(5407433146497389/8000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1330 : certificate1330.NumericValid := by decide +kernel
theorem cellsSound1330 : ∀ c∈certificate1330.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4530,MergedCutCells.Batch377.certificate4531,MergedCutCells.Batch377.certificate4532], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4530,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4531,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4532,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1330 : ∀ c∈certificate1330.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4530,MergedCutCells.Batch377.certificate4531,MergedCutCells.Batch377.certificate4532], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4530,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4531,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4532,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1330 : ∀ c∈certificate1330.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4530,MergedCutCells.Batch377.certificate4531,MergedCutCells.Batch377.certificate4532], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1330 : ∀ c∈certificate1330.cells, c.population=certificate1330.population := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4530,MergedCutCells.Batch377.certificate4531,MergedCutCells.Batch377.certificate4532], c.population=PopulationCertificates.Batch044.certificate893
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1330 {x : ℝ} (hx : certificate1330.interval.Contains x) : ∃ c∈certificate1330.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1330 numericValid1330 hx

def certificate1331 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate894,PopulationCertificates.Batch044.certificate894,[MergedCutCells.Batch377.certificate4533,MergedCutCells.Batch377.certificate4534],(18931505681420751009/1000000000000000000),none,(1/2),(5513397017235715299/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1331 : certificate1331.NumericValid := by decide +kernel
theorem cellsSound1331 : ∀ c∈certificate1331.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4533,MergedCutCells.Batch377.certificate4534], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4533,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4534,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1331 : ∀ c∈certificate1331.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4533,MergedCutCells.Batch377.certificate4534], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4533,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4534,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1331 : ∀ c∈certificate1331.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4533,MergedCutCells.Batch377.certificate4534], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1331 : ∀ c∈certificate1331.cells, c.population=certificate1331.population := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4533,MergedCutCells.Batch377.certificate4534], c.population=PopulationCertificates.Batch044.certificate894
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1331 {x : ℝ} (hx : certificate1331.interval.Contains x) : ∃ c∈certificate1331.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1331 numericValid1331 hx

end Cycle12.MergedCutGroups.Batch110
