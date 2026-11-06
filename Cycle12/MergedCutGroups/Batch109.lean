import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch043
import Cycle12.GeometryCertificates.Batch044
import Cycle12.MergedCutCells.Batch372
import Cycle12.MergedCutCells.Batch373
import Cycle12.MergedCutCells.Batch374
import Cycle12.MergedCutCells.Batch375
import Cycle12.PopulationCertificates.Batch043
import Cycle12.PopulationCertificates.Batch044

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch109

def certificate1308 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate877,PopulationCertificates.Batch043.certificate877,[MergedCutCells.Batch372.certificate4469,MergedCutCells.Batch372.certificate4470,MergedCutCells.Batch372.certificate4471,MergedCutCells.Batch372.certificate4472],(677172774811097403/1000000000000000000),none,(1/40),(17896235332074363/200000000000000000),none,none⟩
theorem numericValid1308 : certificate1308.NumericValid := by decide +kernel
theorem cellsSound1308 : ∀ c∈certificate1308.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4469,MergedCutCells.Batch372.certificate4470,MergedCutCells.Batch372.certificate4471,MergedCutCells.Batch372.certificate4472], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4469,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4470,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4472,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1308 : ∀ c∈certificate1308.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4469,MergedCutCells.Batch372.certificate4470,MergedCutCells.Batch372.certificate4471,MergedCutCells.Batch372.certificate4472], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4469,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4470,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4472,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1308 : ∀ c∈certificate1308.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4469,MergedCutCells.Batch372.certificate4470,MergedCutCells.Batch372.certificate4471,MergedCutCells.Batch372.certificate4472], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid483,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid484,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid485,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid486,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1308 : ∀ c∈certificate1308.cells, c.population=certificate1308.population := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4469,MergedCutCells.Batch372.certificate4470,MergedCutCells.Batch372.certificate4471,MergedCutCells.Batch372.certificate4472], c.population=PopulationCertificates.Batch043.certificate877
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1308 {x : ℝ} (hx : certificate1308.interval.Contains x) : ∃ c∈certificate1308.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1308 numericValid1308 hx

def certificate1309 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate878,PopulationCertificates.Batch043.certificate878,[MergedCutCells.Batch372.certificate4473,MergedCutCells.Batch372.certificate4474],(617622391581774283/1000000000000000000),(some (1263624351/1000000000)),(1/2),(111284507061781517/200000000000000000),(some (5200101235035377/1000000000000000000)),(some (620149356491779/1000000000000000000))⟩
theorem numericValid1309 : certificate1309.NumericValid := by decide +kernel
theorem cellsSound1309 : ∀ c∈certificate1309.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4473,MergedCutCells.Batch372.certificate4474], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4474,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1309 : ∀ c∈certificate1309.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4473,MergedCutCells.Batch372.certificate4474], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4474,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1309 : ∀ c∈certificate1309.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4473,MergedCutCells.Batch372.certificate4474], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid487,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid487,List.forall_mem_nil _⟩⟩
theorem populationMatches1309 : ∀ c∈certificate1309.cells, c.population=certificate1309.population := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4473,MergedCutCells.Batch372.certificate4474], c.population=PopulationCertificates.Batch043.certificate878
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1309 {x : ℝ} (hx : certificate1309.interval.Contains x) : ∃ c∈certificate1309.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1309 numericValid1309 hx

def certificate1310 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate878,PopulationCertificates.Batch043.certificate878,[MergedCutCells.Batch372.certificate4475,MergedCutCells.Batch373.certificate4476,MergedCutCells.Batch373.certificate4477],(1263624351/1000000000),none,(1/2),(555796578055639481/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1310 : certificate1310.NumericValid := by decide +kernel
theorem cellsSound1310 : ∀ c∈certificate1310.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4475,MergedCutCells.Batch373.certificate4476,MergedCutCells.Batch373.certificate4477], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.sound4475,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4476,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4477,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1310 : ∀ c∈certificate1310.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4475,MergedCutCells.Batch373.certificate4476,MergedCutCells.Batch373.certificate4477], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch372.numericValid4475,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4476,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4477,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1310 : ∀ c∈certificate1310.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4475,MergedCutCells.Batch373.certificate4476,MergedCutCells.Batch373.certificate4477], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1310 : ∀ c∈certificate1310.cells, c.population=certificate1310.population := by
  change ∀ c∈[MergedCutCells.Batch372.certificate4475,MergedCutCells.Batch373.certificate4476,MergedCutCells.Batch373.certificate4477], c.population=PopulationCertificates.Batch043.certificate878
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1310 {x : ℝ} (hx : certificate1310.interval.Contains x) : ∃ c∈certificate1310.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1310 numericValid1310 hx

def certificate1311 : RatCutGroup := ⟨GeometryCertificates.Batch043.certificate879,PopulationCertificates.Batch043.certificate879,[MergedCutCells.Batch373.certificate4478,MergedCutCells.Batch373.certificate4479],(17813450815624083751/1000000000000000000),none,(1/2),(1001694801554496231/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1311 : certificate1311.NumericValid := by decide +kernel
theorem cellsSound1311 : ∀ c∈certificate1311.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4478,MergedCutCells.Batch373.certificate4479], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4478,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4479,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1311 : ∀ c∈certificate1311.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4478,MergedCutCells.Batch373.certificate4479], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4478,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4479,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1311 : ∀ c∈certificate1311.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4478,MergedCutCells.Batch373.certificate4479], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1311 : ∀ c∈certificate1311.cells, c.population=certificate1311.population := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4478,MergedCutCells.Batch373.certificate4479], c.population=PopulationCertificates.Batch043.certificate879
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1311 {x : ℝ} (hx : certificate1311.interval.Contains x) : ∃ c∈certificate1311.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1311 numericValid1311 hx

def certificate1312 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate880,PopulationCertificates.Batch044.certificate880,[MergedCutCells.Batch373.certificate4480,MergedCutCells.Batch373.certificate4481,MergedCutCells.Batch373.certificate4482,MergedCutCells.Batch373.certificate4483],(680202597400687293/1000000000000000000),none,(1/40),(11894466597485221/125000000000000000),none,none⟩
theorem numericValid1312 : certificate1312.NumericValid := by decide +kernel
theorem cellsSound1312 : ∀ c∈certificate1312.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4480,MergedCutCells.Batch373.certificate4481,MergedCutCells.Batch373.certificate4482,MergedCutCells.Batch373.certificate4483], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4481,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4482,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4483,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1312 : ∀ c∈certificate1312.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4480,MergedCutCells.Batch373.certificate4481,MergedCutCells.Batch373.certificate4482,MergedCutCells.Batch373.certificate4483], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4481,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4482,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4483,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1312 : ∀ c∈certificate1312.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4480,MergedCutCells.Batch373.certificate4481,MergedCutCells.Batch373.certificate4482,MergedCutCells.Batch373.certificate4483], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid488,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid489,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid490,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid491,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1312 : ∀ c∈certificate1312.cells, c.population=certificate1312.population := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4480,MergedCutCells.Batch373.certificate4481,MergedCutCells.Batch373.certificate4482,MergedCutCells.Batch373.certificate4483], c.population=PopulationCertificates.Batch044.certificate880
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1312 {x : ℝ} (hx : certificate1312.interval.Contains x) : ∃ c∈certificate1312.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1312 numericValid1312 hx

def certificate1313 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate881,PopulationCertificates.Batch044.certificate881,[MergedCutCells.Batch373.certificate4484,MergedCutCells.Batch373.certificate4485],(310841914339471963/500000000000000000),(some (317662127/250000000)),(1/2),(578917738528462113/1000000000000000000),(some (1421771655142843/250000000000000000)),(some (686557940551871/1000000000000000000))⟩
theorem numericValid1313 : certificate1313.NumericValid := by decide +kernel
theorem cellsSound1313 : ∀ c∈certificate1313.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4484,MergedCutCells.Batch373.certificate4485], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4485,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1313 : ∀ c∈certificate1313.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4484,MergedCutCells.Batch373.certificate4485], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4485,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1313 : ∀ c∈certificate1313.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4484,MergedCutCells.Batch373.certificate4485], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid492,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid492,List.forall_mem_nil _⟩⟩
theorem populationMatches1313 : ∀ c∈certificate1313.cells, c.population=certificate1313.population := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4484,MergedCutCells.Batch373.certificate4485], c.population=PopulationCertificates.Batch044.certificate881
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1313 {x : ℝ} (hx : certificate1313.interval.Contains x) : ∃ c∈certificate1313.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1313 numericValid1313 hx

def certificate1314 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate881,PopulationCertificates.Batch044.certificate881,[MergedCutCells.Batch373.certificate4486,MergedCutCells.Batch373.certificate4487,MergedCutCells.Batch374.certificate4488],(317662127/250000000),none,(1/2),(115779688270906761/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1314 : certificate1314.NumericValid := by decide +kernel
theorem cellsSound1314 : ∀ c∈certificate1314.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4486,MergedCutCells.Batch373.certificate4487,MergedCutCells.Batch374.certificate4488], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4486,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.sound4487,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4488,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1314 : ∀ c∈certificate1314.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4486,MergedCutCells.Batch373.certificate4487,MergedCutCells.Batch374.certificate4488], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4486,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch373.numericValid4487,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4488,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1314 : ∀ c∈certificate1314.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4486,MergedCutCells.Batch373.certificate4487,MergedCutCells.Batch374.certificate4488], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1314 : ∀ c∈certificate1314.cells, c.population=certificate1314.population := by
  change ∀ c∈[MergedCutCells.Batch373.certificate4486,MergedCutCells.Batch373.certificate4487,MergedCutCells.Batch374.certificate4488], c.population=PopulationCertificates.Batch044.certificate881
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1314 {x : ℝ} (hx : certificate1314.interval.Contains x) : ∃ c∈certificate1314.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1314 numericValid1314 hx

def certificate1315 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate882,PopulationCertificates.Batch044.certificate882,[MergedCutCells.Batch374.certificate4489,MergedCutCells.Batch374.certificate4490],(9013932638405853357/500000000000000000),none,(1/2),(5105405228266817713/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1315 : certificate1315.NumericValid := by decide +kernel
theorem cellsSound1315 : ∀ c∈certificate1315.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4489,MergedCutCells.Batch374.certificate4490], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4489,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4490,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1315 : ∀ c∈certificate1315.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4489,MergedCutCells.Batch374.certificate4490], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4489,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4490,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1315 : ∀ c∈certificate1315.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4489,MergedCutCells.Batch374.certificate4490], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1315 : ∀ c∈certificate1315.cells, c.population=certificate1315.population := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4489,MergedCutCells.Batch374.certificate4490], c.population=PopulationCertificates.Batch044.certificate882
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1315 {x : ℝ} (hx : certificate1315.interval.Contains x) : ∃ c∈certificate1315.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1315 numericValid1315 hx

def certificate1316 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate883,PopulationCertificates.Batch044.certificate883,[MergedCutCells.Batch374.certificate4491,MergedCutCells.Batch374.certificate4492,MergedCutCells.Batch374.certificate4493,MergedCutCells.Batch374.certificate4494],(83754885971425397/125000000000000000),none,(1/40),(26826483299432029/500000000000000000),none,none⟩
theorem numericValid1316 : certificate1316.NumericValid := by decide +kernel
theorem cellsSound1316 : ∀ c∈certificate1316.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4491,MergedCutCells.Batch374.certificate4492,MergedCutCells.Batch374.certificate4493,MergedCutCells.Batch374.certificate4494], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4491,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4492,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4494,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1316 : ∀ c∈certificate1316.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4491,MergedCutCells.Batch374.certificate4492,MergedCutCells.Batch374.certificate4493,MergedCutCells.Batch374.certificate4494], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4491,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4492,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4494,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1316 : ∀ c∈certificate1316.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4491,MergedCutCells.Batch374.certificate4492,MergedCutCells.Batch374.certificate4493,MergedCutCells.Batch374.certificate4494], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid493,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid494,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid495,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid496,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1316 : ∀ c∈certificate1316.cells, c.population=certificate1316.population := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4491,MergedCutCells.Batch374.certificate4492,MergedCutCells.Batch374.certificate4493,MergedCutCells.Batch374.certificate4494], c.population=PopulationCertificates.Batch044.certificate883
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1316 {x : ℝ} (hx : certificate1316.interval.Contains x) : ∃ c∈certificate1316.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1316 numericValid1316 hx

def certificate1317 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate884,PopulationCertificates.Batch044.certificate884,[MergedCutCells.Batch374.certificate4495,MergedCutCells.Batch374.certificate4496],(313473793444522917/500000000000000000),(some (1279741531/1000000000)),(1/2),(18999063906763371/31250000000000000),(some (6186919555681417/1000000000000000000)),(some (94456147819733/125000000000000000))⟩
theorem numericValid1317 : certificate1317.NumericValid := by decide +kernel
theorem cellsSound1317 : ∀ c∈certificate1317.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4495,MergedCutCells.Batch374.certificate4496], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4495,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4496,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1317 : ∀ c∈certificate1317.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4495,MergedCutCells.Batch374.certificate4496], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4495,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4496,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1317 : ∀ c∈certificate1317.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4495,MergedCutCells.Batch374.certificate4496], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid497,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy024.valid497,List.forall_mem_nil _⟩⟩
theorem populationMatches1317 : ∀ c∈certificate1317.cells, c.population=certificate1317.population := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4495,MergedCutCells.Batch374.certificate4496], c.population=PopulationCertificates.Batch044.certificate884
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1317 {x : ℝ} (hx : certificate1317.interval.Contains x) : ∃ c∈certificate1317.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1317 numericValid1317 hx

def certificate1318 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate884,PopulationCertificates.Batch044.certificate884,[MergedCutCells.Batch374.certificate4497,MergedCutCells.Batch374.certificate4498,MergedCutCells.Batch374.certificate4499],(1279741531/1000000000),none,(1/2),(18814814472311741/31250000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1318 : certificate1318.NumericValid := by decide +kernel
theorem cellsSound1318 : ∀ c∈certificate1318.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4497,MergedCutCells.Batch374.certificate4498,MergedCutCells.Batch374.certificate4499], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4497,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.sound4499,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1318 : ∀ c∈certificate1318.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4497,MergedCutCells.Batch374.certificate4498,MergedCutCells.Batch374.certificate4499], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4497,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch374.numericValid4499,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1318 : ∀ c∈certificate1318.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4497,MergedCutCells.Batch374.certificate4498,MergedCutCells.Batch374.certificate4499], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1318 : ∀ c∈certificate1318.cells, c.population=certificate1318.population := by
  change ∀ c∈[MergedCutCells.Batch374.certificate4497,MergedCutCells.Batch374.certificate4498,MergedCutCells.Batch374.certificate4499], c.population=PopulationCertificates.Batch044.certificate884
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1318 {x : ℝ} (hx : certificate1318.interval.Contains x) : ∃ c∈certificate1318.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1318 numericValid1318 hx

def certificate1319 : RatCutGroup := ⟨GeometryCertificates.Batch044.certificate885,PopulationCertificates.Batch044.certificate885,[MergedCutCells.Batch375.certificate4500,MergedCutCells.Batch375.certificate4501],(3649348139249986293/200000000000000000),none,(1/2),(5204302744302063903/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1319 : certificate1319.NumericValid := by decide +kernel
theorem cellsSound1319 : ∀ c∈certificate1319.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4500,MergedCutCells.Batch375.certificate4501], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4500,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.sound4501,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1319 : ∀ c∈certificate1319.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4500,MergedCutCells.Batch375.certificate4501], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4500,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch375.numericValid4501,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1319 : ∀ c∈certificate1319.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4500,MergedCutCells.Batch375.certificate4501], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1319 : ∀ c∈certificate1319.cells, c.population=certificate1319.population := by
  change ∀ c∈[MergedCutCells.Batch375.certificate4500,MergedCutCells.Batch375.certificate4501], c.population=PopulationCertificates.Batch044.certificate885
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1319 {x : ℝ} (hx : certificate1319.interval.Contains x) : ∃ c∈certificate1319.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1319 numericValid1319 hx

end Cycle12.MergedCutGroups.Batch109
