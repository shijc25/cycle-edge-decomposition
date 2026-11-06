import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch045
import Cycle12.MergedCutCells.Batch380
import Cycle12.MergedCutCells.Batch381
import Cycle12.MergedCutCells.Batch382
import Cycle12.MergedCutCells.Batch383
import Cycle12.PopulationCertificates.Batch045

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch112

def certificate1344 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate904,PopulationCertificates.Batch045.certificate904,[MergedCutCells.Batch380.certificate4569,MergedCutCells.Batch380.certificate4570,MergedCutCells.Batch380.certificate4571,MergedCutCells.Batch381.certificate4572],(166134015847177457/250000000000000000),none,(1/40),(6141294534276733/250000000000000000),none,none⟩
theorem numericValid1344 : certificate1344.NumericValid := by decide +kernel
theorem cellsSound1344 : ∀ c∈certificate1344.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4569,MergedCutCells.Batch380.certificate4570,MergedCutCells.Batch380.certificate4571,MergedCutCells.Batch381.certificate4572], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4569,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.sound4571,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4572,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1344 : ∀ c∈certificate1344.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4569,MergedCutCells.Batch380.certificate4570,MergedCutCells.Batch380.certificate4571,MergedCutCells.Batch381.certificate4572], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4569,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch380.numericValid4571,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4572,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1344 : ∀ c∈certificate1344.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4569,MergedCutCells.Batch380.certificate4570,MergedCutCells.Batch380.certificate4571,MergedCutCells.Batch381.certificate4572], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid528,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid529,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid530,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid531,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1344 : ∀ c∈certificate1344.cells, c.population=certificate1344.population := by
  change ∀ c∈[MergedCutCells.Batch380.certificate4569,MergedCutCells.Batch380.certificate4570,MergedCutCells.Batch380.certificate4571,MergedCutCells.Batch381.certificate4572], c.population=PopulationCertificates.Batch045.certificate904
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1344 {x : ℝ} (hx : certificate1344.interval.Contains x) : ∃ c∈certificate1344.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1344 numericValid1344 hx

def certificate1345 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate905,PopulationCertificates.Batch045.certificate905,[MergedCutCells.Batch381.certificate4573,MergedCutCells.Batch381.certificate4574],(657020625070622909/1000000000000000000),(some (1246107423/1000000000)),(1/2),(782024406113139497/1000000000000000000),(some (5061694444104327/500000000000000000)),(some (1327923174289399/1000000000000000000))⟩
theorem numericValid1345 : certificate1345.NumericValid := by decide +kernel
theorem cellsSound1345 : ∀ c∈certificate1345.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4573,MergedCutCells.Batch381.certificate4574], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4573,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4574,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1345 : ∀ c∈certificate1345.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4573,MergedCutCells.Batch381.certificate4574], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4573,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4574,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1345 : ∀ c∈certificate1345.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4573,MergedCutCells.Batch381.certificate4574], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid532,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid532,List.forall_mem_nil _⟩⟩
theorem populationMatches1345 : ∀ c∈certificate1345.cells, c.population=certificate1345.population := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4573,MergedCutCells.Batch381.certificate4574], c.population=PopulationCertificates.Batch045.certificate905
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1345 {x : ℝ} (hx : certificate1345.interval.Contains x) : ∃ c∈certificate1345.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1345 numericValid1345 hx

def certificate1346 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate905,PopulationCertificates.Batch045.certificate905,[MergedCutCells.Batch381.certificate4575,MergedCutCells.Batch381.certificate4576,MergedCutCells.Batch381.certificate4577],(1246107423/1000000000),none,(1/2),(195461419331968231/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1346 : certificate1346.NumericValid := by decide +kernel
theorem cellsSound1346 : ∀ c∈certificate1346.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4575,MergedCutCells.Batch381.certificate4576,MergedCutCells.Batch381.certificate4577], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4575,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4576,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4577,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1346 : ∀ c∈certificate1346.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4575,MergedCutCells.Batch381.certificate4576,MergedCutCells.Batch381.certificate4577], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4575,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4576,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4577,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1346 : ∀ c∈certificate1346.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4575,MergedCutCells.Batch381.certificate4576,MergedCutCells.Batch381.certificate4577], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1346 : ∀ c∈certificate1346.cells, c.population=certificate1346.population := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4575,MergedCutCells.Batch381.certificate4576,MergedCutCells.Batch381.certificate4577], c.population=PopulationCertificates.Batch045.certificate905
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1346 {x : ℝ} (hx : certificate1346.interval.Contains x) : ∃ c∈certificate1346.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1346 numericValid1346 hx

def certificate1347 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate906,PopulationCertificates.Batch045.certificate906,[MergedCutCells.Batch381.certificate4578,MergedCutCells.Batch381.certificate4579],(19915793403484897453/1000000000000000000),none,(1/2),(1489205718330281913/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1347 : certificate1347.NumericValid := by decide +kernel
theorem cellsSound1347 : ∀ c∈certificate1347.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4578,MergedCutCells.Batch381.certificate4579], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4578,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4579,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1347 : ∀ c∈certificate1347.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4578,MergedCutCells.Batch381.certificate4579], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4578,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4579,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1347 : ∀ c∈certificate1347.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4578,MergedCutCells.Batch381.certificate4579], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1347 : ∀ c∈certificate1347.cells, c.population=certificate1347.population := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4578,MergedCutCells.Batch381.certificate4579], c.population=PopulationCertificates.Batch045.certificate906
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1347 {x : ℝ} (hx : certificate1347.interval.Contains x) : ∃ c∈certificate1347.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1347 numericValid1347 hx

def certificate1348 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate907,PopulationCertificates.Batch045.certificate907,[MergedCutCells.Batch381.certificate4580,MergedCutCells.Batch381.certificate4581,MergedCutCells.Batch381.certificate4582,MergedCutCells.Batch381.certificate4583],(668031695970605897/1000000000000000000),none,(1/40),(14187179433273519/500000000000000000),none,none⟩
theorem numericValid1348 : certificate1348.NumericValid := by decide +kernel
theorem cellsSound1348 : ∀ c∈certificate1348.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4580,MergedCutCells.Batch381.certificate4581,MergedCutCells.Batch381.certificate4582,MergedCutCells.Batch381.certificate4583], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4580,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4581,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.sound4583,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1348 : ∀ c∈certificate1348.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4580,MergedCutCells.Batch381.certificate4581,MergedCutCells.Batch381.certificate4582,MergedCutCells.Batch381.certificate4583], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4580,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4581,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch381.numericValid4583,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1348 : ∀ c∈certificate1348.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4580,MergedCutCells.Batch381.certificate4581,MergedCutCells.Batch381.certificate4582,MergedCutCells.Batch381.certificate4583], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid533,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid534,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid535,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid536,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1348 : ∀ c∈certificate1348.cells, c.population=certificate1348.population := by
  change ∀ c∈[MergedCutCells.Batch381.certificate4580,MergedCutCells.Batch381.certificate4581,MergedCutCells.Batch381.certificate4582,MergedCutCells.Batch381.certificate4583], c.population=PopulationCertificates.Batch045.certificate907
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1348 {x : ℝ} (hx : certificate1348.interval.Contains x) : ∃ c∈certificate1348.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1348 numericValid1348 hx

def certificate1349 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate908,PopulationCertificates.Batch045.certificate908,[MergedCutCells.Batch382.certificate4584,MergedCutCells.Batch382.certificate4585],(308903412305451663/500000000000000000),(some (77070441/62500000)),(1/2),(494805548762473299/1000000000000000000),(some (5451903192670357/500000000000000000)),(some (361634789137533/250000000000000000))⟩
theorem numericValid1349 : certificate1349.NumericValid := by decide +kernel
theorem cellsSound1349 : ∀ c∈certificate1349.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4584,MergedCutCells.Batch382.certificate4585], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4584,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4585,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1349 : ∀ c∈certificate1349.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4584,MergedCutCells.Batch382.certificate4585], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4584,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4585,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1349 : ∀ c∈certificate1349.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4584,MergedCutCells.Batch382.certificate4585], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid537,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid537,List.forall_mem_nil _⟩⟩
theorem populationMatches1349 : ∀ c∈certificate1349.cells, c.population=certificate1349.population := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4584,MergedCutCells.Batch382.certificate4585], c.population=PopulationCertificates.Batch045.certificate908
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1349 {x : ℝ} (hx : certificate1349.interval.Contains x) : ∃ c∈certificate1349.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1349 numericValid1349 hx

def certificate1350 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate908,PopulationCertificates.Batch045.certificate908,[MergedCutCells.Batch382.certificate4586,MergedCutCells.Batch382.certificate4587,MergedCutCells.Batch382.certificate4588],(77070441/62500000),none,(1/2),(494277809016924661/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1350 : certificate1350.NumericValid := by decide +kernel
theorem cellsSound1350 : ∀ c∈certificate1350.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4586,MergedCutCells.Batch382.certificate4587,MergedCutCells.Batch382.certificate4588], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4586,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4587,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4588,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1350 : ∀ c∈certificate1350.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4586,MergedCutCells.Batch382.certificate4587,MergedCutCells.Batch382.certificate4588], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4586,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4587,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4588,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1350 : ∀ c∈certificate1350.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4586,MergedCutCells.Batch382.certificate4587,MergedCutCells.Batch382.certificate4588], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1350 : ∀ c∈certificate1350.cells, c.population=certificate1350.population := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4586,MergedCutCells.Batch382.certificate4587,MergedCutCells.Batch382.certificate4588], c.population=PopulationCertificates.Batch045.certificate908
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1350 {x : ℝ} (hx : certificate1350.interval.Contains x) : ∃ c∈certificate1350.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1350 numericValid1350 hx

def certificate1351 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate909,PopulationCertificates.Batch045.certificate909,[MergedCutCells.Batch382.certificate4589,MergedCutCells.Batch382.certificate4590],(5584342271231188367/250000000000000000),none,(1/2),(3045002771235107127/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1351 : certificate1351.NumericValid := by decide +kernel
theorem cellsSound1351 : ∀ c∈certificate1351.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4589,MergedCutCells.Batch382.certificate4590], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4590,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1351 : ∀ c∈certificate1351.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4589,MergedCutCells.Batch382.certificate4590], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4590,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1351 : ∀ c∈certificate1351.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4589,MergedCutCells.Batch382.certificate4590], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1351 : ∀ c∈certificate1351.cells, c.population=certificate1351.population := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4589,MergedCutCells.Batch382.certificate4590], c.population=PopulationCertificates.Batch045.certificate909
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1351 {x : ℝ} (hx : certificate1351.interval.Contains x) : ∃ c∈certificate1351.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1351 numericValid1351 hx

def certificate1352 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate910,PopulationCertificates.Batch045.certificate910,[MergedCutCells.Batch382.certificate4591,MergedCutCells.Batch382.certificate4592,MergedCutCells.Batch382.certificate4593,MergedCutCells.Batch382.certificate4594],(671550397518599149/1000000000000000000),none,(1/40),(8109391191574139/250000000000000000),none,none⟩
theorem numericValid1352 : certificate1352.NumericValid := by decide +kernel
theorem cellsSound1352 : ∀ c∈certificate1352.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4591,MergedCutCells.Batch382.certificate4592,MergedCutCells.Batch382.certificate4593,MergedCutCells.Batch382.certificate4594], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4593,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4594,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1352 : ∀ c∈certificate1352.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4591,MergedCutCells.Batch382.certificate4592,MergedCutCells.Batch382.certificate4593,MergedCutCells.Batch382.certificate4594], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4593,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4594,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1352 : ∀ c∈certificate1352.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4591,MergedCutCells.Batch382.certificate4592,MergedCutCells.Batch382.certificate4593,MergedCutCells.Batch382.certificate4594], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid538,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy026.valid539,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid540,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid541,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1352 : ∀ c∈certificate1352.cells, c.population=certificate1352.population := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4591,MergedCutCells.Batch382.certificate4592,MergedCutCells.Batch382.certificate4593,MergedCutCells.Batch382.certificate4594], c.population=PopulationCertificates.Batch045.certificate910
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1352 {x : ℝ} (hx : certificate1352.interval.Contains x) : ∃ c∈certificate1352.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1352 numericValid1352 hx

def certificate1353 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate911,PopulationCertificates.Batch045.certificate911,[MergedCutCells.Batch382.certificate4595,MergedCutCells.Batch383.certificate4596],(35930440085400161/62500000000000000),(some (293942549/250000000)),(1/2),(230033237999124919/1000000000000000000),(some (2324055917159189/200000000000000000)),(some (778383660805789/500000000000000000))⟩
theorem numericValid1353 : certificate1353.NumericValid := by decide +kernel
theorem cellsSound1353 : ∀ c∈certificate1353.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4595,MergedCutCells.Batch383.certificate4596], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.sound4595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4596,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1353 : ∀ c∈certificate1353.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4595,MergedCutCells.Batch383.certificate4596], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch382.numericValid4595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4596,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1353 : ∀ c∈certificate1353.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4595,MergedCutCells.Batch383.certificate4596], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid542,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid542,List.forall_mem_nil _⟩⟩
theorem populationMatches1353 : ∀ c∈certificate1353.cells, c.population=certificate1353.population := by
  change ∀ c∈[MergedCutCells.Batch382.certificate4595,MergedCutCells.Batch383.certificate4596], c.population=PopulationCertificates.Batch045.certificate911
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1353 {x : ℝ} (hx : certificate1353.interval.Contains x) : ∃ c∈certificate1353.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1353 numericValid1353 hx

def certificate1354 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate911,PopulationCertificates.Batch045.certificate911,[MergedCutCells.Batch383.certificate4597,MergedCutCells.Batch383.certificate4598,MergedCutCells.Batch383.certificate4599,MergedCutCells.Batch383.certificate4600],(293942549/250000000),none,(1/2),(227588223888812691/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1354 : certificate1354.NumericValid := by decide +kernel
theorem cellsSound1354 : ∀ c∈certificate1354.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4597,MergedCutCells.Batch383.certificate4598,MergedCutCells.Batch383.certificate4599,MergedCutCells.Batch383.certificate4600], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4597,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4599,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4600,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1354 : ∀ c∈certificate1354.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4597,MergedCutCells.Batch383.certificate4598,MergedCutCells.Batch383.certificate4599,MergedCutCells.Batch383.certificate4600], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4597,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4599,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4600,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1354 : ∀ c∈certificate1354.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4597,MergedCutCells.Batch383.certificate4598,MergedCutCells.Batch383.certificate4599,MergedCutCells.Batch383.certificate4600], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1354 : ∀ c∈certificate1354.cells, c.population=certificate1354.population := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4597,MergedCutCells.Batch383.certificate4598,MergedCutCells.Batch383.certificate4599,MergedCutCells.Batch383.certificate4600], c.population=PopulationCertificates.Batch045.certificate911
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1354 {x : ℝ} (hx : certificate1354.interval.Contains x) : ∃ c∈certificate1354.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1354 numericValid1354 hx

def certificate1355 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate912,PopulationCertificates.Batch045.certificate912,[MergedCutCells.Batch383.certificate4601,MergedCutCells.Batch383.certificate4602],(24821787527572240607/1000000000000000000),none,(1/2),(622419352594860739/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1355 : certificate1355.NumericValid := by decide +kernel
theorem cellsSound1355 : ∀ c∈certificate1355.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4601,MergedCutCells.Batch383.certificate4602], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4601,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4602,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1355 : ∀ c∈certificate1355.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4601,MergedCutCells.Batch383.certificate4602], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4601,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4602,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1355 : ∀ c∈certificate1355.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4601,MergedCutCells.Batch383.certificate4602], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1355 : ∀ c∈certificate1355.cells, c.population=certificate1355.population := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4601,MergedCutCells.Batch383.certificate4602], c.population=PopulationCertificates.Batch045.certificate912
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1355 {x : ℝ} (hx : certificate1355.interval.Contains x) : ∃ c∈certificate1355.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1355 numericValid1355 hx

end Cycle12.MergedCutGroups.Batch112
