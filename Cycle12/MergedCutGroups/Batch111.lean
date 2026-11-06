import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch044
import Cycle12.GeometryCertificates.Batch045
import Cycle12.MergedCutCells.Batch377
import Cycle12.MergedCutCells.Batch378
import Cycle12.MergedCutCells.Batch379
import Cycle12.MergedCutCells.Batch380
import Cycle12.PopulationCertificates.Batch044
import Cycle12.PopulationCertificates.Batch045

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch111

def certificate1332 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate895,PopulationCertificates.Batch044.certificate895,[MergedCutCells.Batch377.certificate4535,MergedCutCells.Batch378.certificate4536,MergedCutCells.Batch378.certificate4537,MergedCutCells.Batch378.certificate4538],(680065162603920073/1000000000000000000),none,(1/40),(74373294432264573/1000000000000000000),none,none⟩
theorem numericValid1332 : certificate1332.NumericValid := by decide +kernel
theorem cellsSound1332 : ∀ c∈certificate1332.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4535,MergedCutCells.Batch378.certificate4536,MergedCutCells.Batch378.certificate4537,MergedCutCells.Batch378.certificate4538], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.sound4535,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4536,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4537,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4538,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1332 : ∀ c∈certificate1332.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4535,MergedCutCells.Batch378.certificate4536,MergedCutCells.Batch378.certificate4537,MergedCutCells.Batch378.certificate4538], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch377.numericValid4535,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4536,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4537,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4538,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1332 : ∀ c∈certificate1332.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4535,MergedCutCells.Batch378.certificate4536,MergedCutCells.Batch378.certificate4537,MergedCutCells.Batch378.certificate4538], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid513,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid514,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid515,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid516,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1332 : ∀ c∈certificate1332.cells, c.population=certificate1332.population := by
  change ∀ c∈[MergedCutCells.Batch377.certificate4535,MergedCutCells.Batch378.certificate4536,MergedCutCells.Batch378.certificate4537,MergedCutCells.Batch378.certificate4538], c.population=PopulationCertificates.Batch044.certificate895
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1332 {x : ℝ} (hx : certificate1332.interval.Contains x) : ∃ c∈certificate1332.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1332 numericValid1332 hx

def certificate1333 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate896,PopulationCertificates.Batch044.certificate896,[MergedCutCells.Batch378.certificate4539,MergedCutCells.Batch378.certificate4540],(160990163543941083/250000000000000000),(some (625478709/500000000)),(1/2),(350907710859302587/500000000000000000),(some (4164418601275501/500000000000000000)),(some (1061306059734253/1000000000000000000))⟩
theorem numericValid1333 : certificate1333.NumericValid := by decide +kernel
theorem cellsSound1333 : ∀ c∈certificate1333.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4539,MergedCutCells.Batch378.certificate4540], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4539,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4540,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1333 : ∀ c∈certificate1333.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4539,MergedCutCells.Batch378.certificate4540], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4539,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4540,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1333 : ∀ c∈certificate1333.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4539,MergedCutCells.Batch378.certificate4540], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid517,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid517,List.forall_mem_nil _⟩⟩
theorem populationMatches1333 : ∀ c∈certificate1333.cells, c.population=certificate1333.population := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4539,MergedCutCells.Batch378.certificate4540], c.population=PopulationCertificates.Batch044.certificate896
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1333 {x : ℝ} (hx : certificate1333.interval.Contains x) : ∃ c∈certificate1333.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1333 numericValid1333 hx

def certificate1334 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate896,PopulationCertificates.Batch044.certificate896,[MergedCutCells.Batch378.certificate4541,MergedCutCells.Batch378.certificate4542,MergedCutCells.Batch378.certificate4543],(625478709/500000000),none,(1/2),(175399237002786779/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1334 : certificate1334.NumericValid := by decide +kernel
theorem cellsSound1334 : ∀ c∈certificate1334.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4541,MergedCutCells.Batch378.certificate4542,MergedCutCells.Batch378.certificate4543], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4541,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4542,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4543,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1334 : ∀ c∈certificate1334.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4541,MergedCutCells.Batch378.certificate4542,MergedCutCells.Batch378.certificate4543], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4541,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4542,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4543,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1334 : ∀ c∈certificate1334.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4541,MergedCutCells.Batch378.certificate4542,MergedCutCells.Batch378.certificate4543], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1334 : ∀ c∈certificate1334.cells, c.population=certificate1334.population := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4541,MergedCutCells.Batch378.certificate4542,MergedCutCells.Batch378.certificate4543], c.population=PopulationCertificates.Batch044.certificate896
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1334 {x : ℝ} (hx : certificate1334.interval.Contains x) : ∃ c∈certificate1334.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1334 numericValid1334 hx

def certificate1335 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate897,PopulationCertificates.Batch044.certificate897,[MergedCutCells.Batch378.certificate4544,MergedCutCells.Batch378.certificate4545],(19169626002582000879/1000000000000000000),none,(1/2),(5620760295823794101/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1335 : certificate1335.NumericValid := by decide +kernel
theorem cellsSound1335 : ∀ c∈certificate1335.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4544,MergedCutCells.Batch378.certificate4545], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4544,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4545,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1335 : ∀ c∈certificate1335.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4544,MergedCutCells.Batch378.certificate4545], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4544,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4545,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1335 : ∀ c∈certificate1335.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4544,MergedCutCells.Batch378.certificate4545], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1335 : ∀ c∈certificate1335.cells, c.population=certificate1335.population := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4544,MergedCutCells.Batch378.certificate4545], c.population=PopulationCertificates.Batch044.certificate897
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1335 {x : ℝ} (hx : certificate1335.interval.Contains x) : ∃ c∈certificate1335.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1335 numericValid1335 hx

def certificate1336 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate898,PopulationCertificates.Batch044.certificate898,[MergedCutCells.Batch378.certificate4546,MergedCutCells.Batch378.certificate4547,MergedCutCells.Batch379.certificate4548,MergedCutCells.Batch379.certificate4549],(164389881691621661/250000000000000000),none,(1/40),(8848942344292529/500000000000000000),none,none⟩
theorem numericValid1336 : certificate1336.NumericValid := by decide +kernel
theorem cellsSound1336 : ∀ c∈certificate1336.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4546,MergedCutCells.Batch378.certificate4547,MergedCutCells.Batch379.certificate4548,MergedCutCells.Batch379.certificate4549], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4546,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.sound4547,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4548,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4549,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1336 : ∀ c∈certificate1336.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4546,MergedCutCells.Batch378.certificate4547,MergedCutCells.Batch379.certificate4548,MergedCutCells.Batch379.certificate4549], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4546,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch378.numericValid4547,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4548,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4549,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1336 : ∀ c∈certificate1336.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4546,MergedCutCells.Batch378.certificate4547,MergedCutCells.Batch379.certificate4548,MergedCutCells.Batch379.certificate4549], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid518,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy025.valid519,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid520,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid521,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1336 : ∀ c∈certificate1336.cells, c.population=certificate1336.population := by
  change ∀ c∈[MergedCutCells.Batch378.certificate4546,MergedCutCells.Batch378.certificate4547,MergedCutCells.Batch379.certificate4548,MergedCutCells.Batch379.certificate4549], c.population=PopulationCertificates.Batch044.certificate898
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1336 {x : ℝ} (hx : certificate1336.interval.Contains x) : ∃ c∈certificate1336.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1336 numericValid1336 hx

def certificate1337 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate899,PopulationCertificates.Batch044.certificate899,[MergedCutCells.Batch379.certificate4550,MergedCutCells.Batch379.certificate4551],(162008591329462297/250000000000000000),(some (1262217289/1000000000)),(1/2),(728167406703637061/1000000000000000000),(some (8931107479072499/1000000000000000000)),(some (1149789660376397/1000000000000000000))⟩
theorem numericValid1337 : certificate1337.NumericValid := by decide +kernel
theorem cellsSound1337 : ∀ c∈certificate1337.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4550,MergedCutCells.Batch379.certificate4551], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4550,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4551,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1337 : ∀ c∈certificate1337.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4550,MergedCutCells.Batch379.certificate4551], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4550,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4551,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1337 : ∀ c∈certificate1337.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4550,MergedCutCells.Batch379.certificate4551], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid522,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid522,List.forall_mem_nil _⟩⟩
theorem populationMatches1337 : ∀ c∈certificate1337.cells, c.population=certificate1337.population := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4550,MergedCutCells.Batch379.certificate4551], c.population=PopulationCertificates.Batch044.certificate899
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1337 {x : ℝ} (hx : certificate1337.interval.Contains x) : ∃ c∈certificate1337.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1337 numericValid1337 hx

def certificate1338 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate899,PopulationCertificates.Batch044.certificate899,[MergedCutCells.Batch379.certificate4552,MergedCutCells.Batch379.certificate4553,MergedCutCells.Batch379.certificate4554],(1262217289/1000000000),none,(1/2),(72776582051196153/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1338 : certificate1338.NumericValid := by decide +kernel
theorem cellsSound1338 : ∀ c∈certificate1338.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4552,MergedCutCells.Batch379.certificate4553,MergedCutCells.Batch379.certificate4554], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4552,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4553,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4554,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1338 : ∀ c∈certificate1338.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4552,MergedCutCells.Batch379.certificate4553,MergedCutCells.Batch379.certificate4554], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4552,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4553,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4554,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1338 : ∀ c∈certificate1338.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4552,MergedCutCells.Batch379.certificate4553,MergedCutCells.Batch379.certificate4554], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1338 : ∀ c∈certificate1338.cells, c.population=certificate1338.population := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4552,MergedCutCells.Batch379.certificate4553,MergedCutCells.Batch379.certificate4554], c.population=PopulationCertificates.Batch044.certificate899
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1338 {x : ℝ} (hx : certificate1338.interval.Contains x) : ∃ c∈certificate1338.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1338 numericValid1338 hx

def certificate1339 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate900,PopulationCertificates.Batch045.certificate900,[MergedCutCells.Batch379.certificate4555,MergedCutCells.Batch379.certificate4556],(3882587359225456913/200000000000000000),none,(1/2),(5730425883252588253/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1339 : certificate1339.NumericValid := by decide +kernel
theorem cellsSound1339 : ∀ c∈certificate1339.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4555,MergedCutCells.Batch379.certificate4556], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4555,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4556,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1339 : ∀ c∈certificate1339.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4555,MergedCutCells.Batch379.certificate4556], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4555,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4556,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1339 : ∀ c∈certificate1339.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4555,MergedCutCells.Batch379.certificate4556], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1339 : ∀ c∈certificate1339.cells, c.population=certificate1339.population := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4555,MergedCutCells.Batch379.certificate4556], c.population=PopulationCertificates.Batch045.certificate900
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1339 {x : ℝ} (hx : certificate1339.interval.Contains x) : ∃ c∈certificate1339.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1339 numericValid1339 hx

def certificate1340 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate901,PopulationCertificates.Batch045.certificate901,[MergedCutCells.Batch379.certificate4557,MergedCutCells.Batch379.certificate4558,MergedCutCells.Batch379.certificate4559,MergedCutCells.Batch380.certificate4560],(132208716751808347/200000000000000000),none,(1/40),(10503589703820499/500000000000000000),none,none⟩
theorem numericValid1340 : certificate1340.NumericValid := by decide +kernel
theorem cellsSound1340 : ∀ c∈certificate1340.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4557,MergedCutCells.Batch379.certificate4558,MergedCutCells.Batch379.certificate4559,MergedCutCells.Batch380.certificate4560], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4558,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.sound4559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4560,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1340 : ∀ c∈certificate1340.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4557,MergedCutCells.Batch379.certificate4558,MergedCutCells.Batch379.certificate4559,MergedCutCells.Batch380.certificate4560], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4558,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch379.numericValid4559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4560,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1340 : ∀ c∈certificate1340.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4557,MergedCutCells.Batch379.certificate4558,MergedCutCells.Batch379.certificate4559,MergedCutCells.Batch380.certificate4560], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid523,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid524,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid525,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid526,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1340 : ∀ c∈certificate1340.cells, c.population=certificate1340.population := by
  change ∀ c∈[MergedCutCells.Batch379.certificate4557,MergedCutCells.Batch379.certificate4558,MergedCutCells.Batch379.certificate4559,MergedCutCells.Batch380.certificate4560], c.population=PopulationCertificates.Batch045.certificate901
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1340 {x : ℝ} (hx : certificate1340.interval.Contains x) : ∃ c∈certificate1340.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1340 numericValid1340 hx

def certificate1341 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate902,PopulationCertificates.Batch045.certificate902,[MergedCutCells.Batch380.certificate4561,MergedCutCells.Batch380.certificate4562],(652627637804430661/1000000000000000000),(some (247787393/200000000)),(1/2),(150963704525809909/200000000000000000),(some (948904368100163/100000000000000000)),(some (616335304844319/500000000000000000))⟩
theorem numericValid1341 : certificate1341.NumericValid := by decide +kernel
theorem cellsSound1341 : ∀ c∈certificate1341.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4561,MergedCutCells.Batch380.certificate4562], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4561,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4562,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1341 : ∀ c∈certificate1341.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4561,MergedCutCells.Batch380.certificate4562], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4561,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4562,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1341 : ∀ c∈certificate1341.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4561,MergedCutCells.Batch380.certificate4562], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid527,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid527,List.forall_mem_nil _⟩⟩
theorem populationMatches1341 : ∀ c∈certificate1341.cells, c.population=certificate1341.population := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4561,MergedCutCells.Batch380.certificate4562], c.population=PopulationCertificates.Batch045.certificate902
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1341 {x : ℝ} (hx : certificate1341.interval.Contains x) : ∃ c∈certificate1341.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1341 numericValid1341 hx

def certificate1342 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate902,PopulationCertificates.Batch045.certificate902,[MergedCutCells.Batch380.certificate4563,MergedCutCells.Batch380.certificate4564,MergedCutCells.Batch380.certificate4565,MergedCutCells.Batch380.certificate4566],(247787393/200000000),none,(1/2),(75450744570718489/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1342 : certificate1342.NumericValid := by decide +kernel
theorem cellsSound1342 : ∀ c∈certificate1342.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4563,MergedCutCells.Batch380.certificate4564,MergedCutCells.Batch380.certificate4565,MergedCutCells.Batch380.certificate4566], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4563,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4564,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4566,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1342 : ∀ c∈certificate1342.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4563,MergedCutCells.Batch380.certificate4564,MergedCutCells.Batch380.certificate4565,MergedCutCells.Batch380.certificate4566], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4563,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4564,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4566,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1342 : ∀ c∈certificate1342.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4563,MergedCutCells.Batch380.certificate4564,MergedCutCells.Batch380.certificate4565,MergedCutCells.Batch380.certificate4566], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1342 : ∀ c∈certificate1342.cells, c.population=certificate1342.population := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4563,MergedCutCells.Batch380.certificate4564,MergedCutCells.Batch380.certificate4565,MergedCutCells.Batch380.certificate4566], c.population=PopulationCertificates.Batch045.certificate902
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1342 {x : ℝ} (hx : certificate1342.interval.Contains x) : ∃ c∈certificate1342.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1342 numericValid1342 hx

def certificate1343 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate903,PopulationCertificates.Batch045.certificate903,[MergedCutCells.Batch380.certificate4567,MergedCutCells.Batch380.certificate4568],(19661602274635897567/1000000000000000000),none,(1/2),(2921205364169474769/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1343 : certificate1343.NumericValid := by decide +kernel
theorem cellsSound1343 : ∀ c∈certificate1343.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4567,MergedCutCells.Batch380.certificate4568], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4568,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1343 : ∀ c∈certificate1343.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4567,MergedCutCells.Batch380.certificate4568], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4568,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1343 : ∀ c∈certificate1343.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4567,MergedCutCells.Batch380.certificate4568], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1343 : ∀ c∈certificate1343.cells, c.population=certificate1343.population := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4567,MergedCutCells.Batch380.certificate4568], c.population=PopulationCertificates.Batch045.certificate903
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1343 {x : ℝ} (hx : certificate1343.interval.Contains x) : ∃ c∈certificate1343.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1343 numericValid1343 hx

end Cycle12.MergedCutGroups.Batch111
