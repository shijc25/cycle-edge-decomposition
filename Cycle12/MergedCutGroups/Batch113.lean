import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch045
import Cycle12.GeometryCertificates.Batch046
import Cycle12.MergedCutCells.Batch383
import Cycle12.MergedCutCells.Batch384
import Cycle12.MergedCutCells.Batch385
import Cycle12.MergedCutCells.Batch386
import Cycle12.PopulationCertificates.Batch045
import Cycle12.PopulationCertificates.Batch046

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch113

def certificate1356 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate913,PopulationCertificates.Batch045.certificate913,[MergedCutCells.Batch383.certificate4603,MergedCutCells.Batch383.certificate4604,MergedCutCells.Batch383.certificate4605,MergedCutCells.Batch383.certificate4606],(333056303990033419/500000000000000000),none,(1/40),(17492838730790557/1000000000000000000),none,none⟩
theorem numericValid1356 : certificate1356.NumericValid := by decide +kernel
theorem cellsSound1356 : ∀ c∈certificate1356.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4603,MergedCutCells.Batch383.certificate4604,MergedCutCells.Batch383.certificate4605,MergedCutCells.Batch383.certificate4606], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4605,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4606,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1356 : ∀ c∈certificate1356.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4603,MergedCutCells.Batch383.certificate4604,MergedCutCells.Batch383.certificate4605,MergedCutCells.Batch383.certificate4606], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4605,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4606,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1356 : ∀ c∈certificate1356.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4603,MergedCutCells.Batch383.certificate4604,MergedCutCells.Batch383.certificate4605,MergedCutCells.Batch383.certificate4606], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid543,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid544,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid545,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid546,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1356 : ∀ c∈certificate1356.cells, c.population=certificate1356.population := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4603,MergedCutCells.Batch383.certificate4604,MergedCutCells.Batch383.certificate4605,MergedCutCells.Batch383.certificate4606], c.population=PopulationCertificates.Batch045.certificate913
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1356 {x : ℝ} (hx : certificate1356.interval.Contains x) : ∃ c∈certificate1356.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1356 numericValid1356 hx

def certificate1357 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate914,PopulationCertificates.Batch045.certificate914,[MergedCutCells.Batch383.certificate4607,MergedCutCells.Batch384.certificate4608],(564924329444591919/1000000000000000000),(some (1182925567/1000000000)),(1/2),(176818934891587333/1000000000000000000),(some (12377558850809259/1000000000000000000)),(some (1674602434999671/1000000000000000000))⟩
theorem numericValid1357 : certificate1357.NumericValid := by decide +kernel
theorem cellsSound1357 : ∀ c∈certificate1357.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4607,MergedCutCells.Batch384.certificate4608], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.sound4607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4608,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1357 : ∀ c∈certificate1357.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4607,MergedCutCells.Batch384.certificate4608], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch383.numericValid4607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4608,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1357 : ∀ c∈certificate1357.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4607,MergedCutCells.Batch384.certificate4608], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid547,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid547,List.forall_mem_nil _⟩⟩
theorem populationMatches1357 : ∀ c∈certificate1357.cells, c.population=certificate1357.population := by
  change ∀ c∈[MergedCutCells.Batch383.certificate4607,MergedCutCells.Batch384.certificate4608], c.population=PopulationCertificates.Batch045.certificate914
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1357 {x : ℝ} (hx : certificate1357.interval.Contains x) : ∃ c∈certificate1357.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1357 numericValid1357 hx

def certificate1358 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate914,PopulationCertificates.Batch045.certificate914,[MergedCutCells.Batch384.certificate4609,MergedCutCells.Batch384.certificate4610,MergedCutCells.Batch384.certificate4611],(1182925567/1000000000),none,(1/2),(88142697592018479/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1358 : certificate1358.NumericValid := by decide +kernel
theorem cellsSound1358 : ∀ c∈certificate1358.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4609,MergedCutCells.Batch384.certificate4610,MergedCutCells.Batch384.certificate4611], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4609,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4610,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4611,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1358 : ∀ c∈certificate1358.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4609,MergedCutCells.Batch384.certificate4610,MergedCutCells.Batch384.certificate4611], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4609,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4610,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4611,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1358 : ∀ c∈certificate1358.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4609,MergedCutCells.Batch384.certificate4610,MergedCutCells.Batch384.certificate4611], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1358 : ∀ c∈certificate1358.cells, c.population=certificate1358.population := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4609,MergedCutCells.Batch384.certificate4610,MergedCutCells.Batch384.certificate4611], c.population=PopulationCertificates.Batch045.certificate914
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1358 {x : ℝ} (hx : certificate1358.interval.Contains x) : ∃ c∈certificate1358.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1358 numericValid1358 hx

def certificate1359 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate915,PopulationCertificates.Batch045.certificate915,[MergedCutCells.Batch384.certificate4612,MergedCutCells.Batch384.certificate4613],(1286446251076297099/50000000000000000),none,(1/2),(6349512610549344373/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1359 : certificate1359.NumericValid := by decide +kernel
theorem cellsSound1359 : ∀ c∈certificate1359.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4612,MergedCutCells.Batch384.certificate4613], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4612,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4613,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1359 : ∀ c∈certificate1359.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4612,MergedCutCells.Batch384.certificate4613], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4612,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4613,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1359 : ∀ c∈certificate1359.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4612,MergedCutCells.Batch384.certificate4613], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1359 : ∀ c∈certificate1359.cells, c.population=certificate1359.population := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4612,MergedCutCells.Batch384.certificate4613], c.population=PopulationCertificates.Batch045.certificate915
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1359 {x : ℝ} (hx : certificate1359.interval.Contains x) : ∃ c∈certificate1359.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1359 numericValid1359 hx

def certificate1360 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate916,PopulationCertificates.Batch045.certificate916,[MergedCutCells.Batch384.certificate4614,MergedCutCells.Batch384.certificate4615,MergedCutCells.Batch384.certificate4616,MergedCutCells.Batch384.certificate4617],(669719969257038989/1000000000000000000),none,(1/40),(21129981921430323/1000000000000000000),none,none⟩
theorem numericValid1360 : certificate1360.NumericValid := by decide +kernel
theorem cellsSound1360 : ∀ c∈certificate1360.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4614,MergedCutCells.Batch384.certificate4615,MergedCutCells.Batch384.certificate4616,MergedCutCells.Batch384.certificate4617], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4614,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4615,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4616,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4617,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1360 : ∀ c∈certificate1360.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4614,MergedCutCells.Batch384.certificate4615,MergedCutCells.Batch384.certificate4616,MergedCutCells.Batch384.certificate4617], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4614,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4615,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4616,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4617,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1360 : ∀ c∈certificate1360.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4614,MergedCutCells.Batch384.certificate4615,MergedCutCells.Batch384.certificate4616,MergedCutCells.Batch384.certificate4617], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid548,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid549,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid550,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid551,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1360 : ∀ c∈certificate1360.cells, c.population=certificate1360.population := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4614,MergedCutCells.Batch384.certificate4615,MergedCutCells.Batch384.certificate4616,MergedCutCells.Batch384.certificate4617], c.population=PopulationCertificates.Batch045.certificate916
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1360 {x : ℝ} (hx : certificate1360.interval.Contains x) : ∃ c∈certificate1360.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1360 numericValid1360 hx

def certificate1361 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate917,PopulationCertificates.Batch045.certificate917,[MergedCutCells.Batch384.certificate4618,MergedCutCells.Batch384.certificate4619],(141695334191912401/250000000000000000),(some (593102819/500000000)),(1/2),(179811600127770707/1000000000000000000),(some (6553264868432677/500000000000000000)),(some (447318813969649/250000000000000000))⟩
theorem numericValid1361 : certificate1361.NumericValid := by decide +kernel
theorem cellsSound1361 : ∀ c∈certificate1361.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4618,MergedCutCells.Batch384.certificate4619], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.sound4619,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1361 : ∀ c∈certificate1361.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4618,MergedCutCells.Batch384.certificate4619], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch384.numericValid4619,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1361 : ∀ c∈certificate1361.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4618,MergedCutCells.Batch384.certificate4619], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid552,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid552,List.forall_mem_nil _⟩⟩
theorem populationMatches1361 : ∀ c∈certificate1361.cells, c.population=certificate1361.population := by
  change ∀ c∈[MergedCutCells.Batch384.certificate4618,MergedCutCells.Batch384.certificate4619], c.population=PopulationCertificates.Batch045.certificate917
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1361 {x : ℝ} (hx : certificate1361.interval.Contains x) : ∃ c∈certificate1361.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1361 numericValid1361 hx

def certificate1362 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate917,PopulationCertificates.Batch045.certificate917,[MergedCutCells.Batch385.certificate4620,MergedCutCells.Batch385.certificate4621,MergedCutCells.Batch385.certificate4622],(593102819/500000000),none,(1/2),(179161194617058101/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1362 : certificate1362.NumericValid := by decide +kernel
theorem cellsSound1362 : ∀ c∈certificate1362.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4620,MergedCutCells.Batch385.certificate4621,MergedCutCells.Batch385.certificate4622], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4620,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4622,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1362 : ∀ c∈certificate1362.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4620,MergedCutCells.Batch385.certificate4621,MergedCutCells.Batch385.certificate4622], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4620,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4622,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1362 : ∀ c∈certificate1362.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4620,MergedCutCells.Batch385.certificate4621,MergedCutCells.Batch385.certificate4622], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1362 : ∀ c∈certificate1362.cells, c.population=certificate1362.population := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4620,MergedCutCells.Batch385.certificate4621,MergedCutCells.Batch385.certificate4622], c.population=PopulationCertificates.Batch045.certificate917
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1362 {x : ℝ} (hx : certificate1362.interval.Contains x) : ∃ c∈certificate1362.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1362 numericValid1362 hx

def certificate1363 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate918,PopulationCertificates.Batch045.certificate918,[MergedCutCells.Batch385.certificate4623,MergedCutCells.Batch385.certificate4624],(5241874322976524153/200000000000000000),none,(1/2),(6475225835658199259/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1363 : certificate1363.NumericValid := by decide +kernel
theorem cellsSound1363 : ∀ c∈certificate1363.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4623,MergedCutCells.Batch385.certificate4624], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4623,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4624,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1363 : ∀ c∈certificate1363.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4623,MergedCutCells.Batch385.certificate4624], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4623,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4624,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1363 : ∀ c∈certificate1363.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4623,MergedCutCells.Batch385.certificate4624], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1363 : ∀ c∈certificate1363.cells, c.population=certificate1363.population := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4623,MergedCutCells.Batch385.certificate4624], c.population=PopulationCertificates.Batch045.certificate918
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1363 {x : ℝ} (hx : certificate1363.interval.Contains x) : ∃ c∈certificate1363.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1363 numericValid1363 hx

def certificate1364 : RatCutGroup := ⟨GeometryCertificates.Batch045.certificate919,PopulationCertificates.Batch045.certificate919,[MergedCutCells.Batch385.certificate4625,MergedCutCells.Batch385.certificate4626,MergedCutCells.Batch385.certificate4627,MergedCutCells.Batch385.certificate4628],(336668937064529371/500000000000000000),none,(1/40),(3130005831664529/125000000000000000),none,none⟩
theorem numericValid1364 : certificate1364.NumericValid := by decide +kernel
theorem cellsSound1364 : ∀ c∈certificate1364.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4625,MergedCutCells.Batch385.certificate4626,MergedCutCells.Batch385.certificate4627,MergedCutCells.Batch385.certificate4628], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4626,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4628,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1364 : ∀ c∈certificate1364.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4625,MergedCutCells.Batch385.certificate4626,MergedCutCells.Batch385.certificate4627,MergedCutCells.Batch385.certificate4628], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4626,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4628,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1364 : ∀ c∈certificate1364.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4625,MergedCutCells.Batch385.certificate4626,MergedCutCells.Batch385.certificate4627,MergedCutCells.Batch385.certificate4628], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid553,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid554,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid555,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid556,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1364 : ∀ c∈certificate1364.cells, c.population=certificate1364.population := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4625,MergedCutCells.Batch385.certificate4626,MergedCutCells.Batch385.certificate4627,MergedCutCells.Batch385.certificate4628], c.population=PopulationCertificates.Batch045.certificate919
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1364 {x : ℝ} (hx : certificate1364.interval.Contains x) : ∃ c∈certificate1364.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1364 numericValid1364 hx

def certificate1365 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate920,PopulationCertificates.Batch046.certificate920,[MergedCutCells.Batch385.certificate4629,MergedCutCells.Batch385.certificate4630],(568597966056554031/1000000000000000000),(some (1160508567/1000000000)),(1/2),(45680056649022651/250000000000000000),(some (6882779549304061/500000000000000000)),(some (59186233958649/31250000000000000))⟩
theorem numericValid1365 : certificate1365.NumericValid := by decide +kernel
theorem cellsSound1365 : ∀ c∈certificate1365.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4629,MergedCutCells.Batch385.certificate4630], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4630,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1365 : ∀ c∈certificate1365.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4629,MergedCutCells.Batch385.certificate4630], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4630,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1365 : ∀ c∈certificate1365.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4629,MergedCutCells.Batch385.certificate4630], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid557,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid557,List.forall_mem_nil _⟩⟩
theorem populationMatches1365 : ∀ c∈certificate1365.cells, c.population=certificate1365.population := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4629,MergedCutCells.Batch385.certificate4630], c.population=PopulationCertificates.Batch046.certificate920
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1365 {x : ℝ} (hx : certificate1365.interval.Contains x) : ∃ c∈certificate1365.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1365 numericValid1365 hx

def certificate1366 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate920,PopulationCertificates.Batch046.certificate920,[MergedCutCells.Batch385.certificate4631,MergedCutCells.Batch386.certificate4632,MergedCutCells.Batch386.certificate4633,MergedCutCells.Batch386.certificate4634],(1160508567/1000000000),none,(1/2),(11381630810841243/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1366 : certificate1366.NumericValid := by decide +kernel
theorem cellsSound1366 : ∀ c∈certificate1366.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4631,MergedCutCells.Batch386.certificate4632,MergedCutCells.Batch386.certificate4633,MergedCutCells.Batch386.certificate4634], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.sound4631,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4632,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4634,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1366 : ∀ c∈certificate1366.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4631,MergedCutCells.Batch386.certificate4632,MergedCutCells.Batch386.certificate4633,MergedCutCells.Batch386.certificate4634], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch385.numericValid4631,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4632,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4634,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1366 : ∀ c∈certificate1366.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4631,MergedCutCells.Batch386.certificate4632,MergedCutCells.Batch386.certificate4633,MergedCutCells.Batch386.certificate4634], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1366 : ∀ c∈certificate1366.cells, c.population=certificate1366.population := by
  change ∀ c∈[MergedCutCells.Batch385.certificate4631,MergedCutCells.Batch386.certificate4632,MergedCutCells.Batch386.certificate4633,MergedCutCells.Batch386.certificate4634], c.population=PopulationCertificates.Batch046.certificate920
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1366 {x : ℝ} (hx : certificate1366.interval.Contains x) : ∃ c∈certificate1366.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1366 numericValid1366 hx

def certificate1367 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate921,PopulationCertificates.Batch046.certificate921,[MergedCutCells.Batch386.certificate4635,MergedCutCells.Batch386.certificate4636],(5340308616893727523/200000000000000000),none,(1/2),(6603816615917731873/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1367 : certificate1367.NumericValid := by decide +kernel
theorem cellsSound1367 : ∀ c∈certificate1367.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4635,MergedCutCells.Batch386.certificate4636], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4635,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4636,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1367 : ∀ c∈certificate1367.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4635,MergedCutCells.Batch386.certificate4636], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4635,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4636,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1367 : ∀ c∈certificate1367.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4635,MergedCutCells.Batch386.certificate4636], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1367 : ∀ c∈certificate1367.cells, c.population=certificate1367.population := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4635,MergedCutCells.Batch386.certificate4636], c.population=PopulationCertificates.Batch046.certificate921
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1367 {x : ℝ} (hx : certificate1367.interval.Contains x) : ∃ c∈certificate1367.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1367 numericValid1367 hx

end Cycle12.MergedCutGroups.Batch113
