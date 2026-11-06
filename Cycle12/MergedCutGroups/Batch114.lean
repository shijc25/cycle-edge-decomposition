import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch046
import Cycle12.MergedCutCells.Batch386
import Cycle12.MergedCutCells.Batch387
import Cycle12.MergedCutCells.Batch388
import Cycle12.MergedCutCells.Batch389
import Cycle12.PopulationCertificates.Batch046

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch114

def certificate1368 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate922,PopulationCertificates.Batch046.certificate922,[MergedCutCells.Batch386.certificate4637,MergedCutCells.Batch386.certificate4638,MergedCutCells.Batch386.certificate4639,MergedCutCells.Batch386.certificate4640],(169241181694504659/250000000000000000),none,(1/40),(730658993302199/25000000000000000),none,none⟩
theorem numericValid1368 : certificate1368.NumericValid := by decide +kernel
theorem cellsSound1368 : ∀ c∈certificate1368.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4637,MergedCutCells.Batch386.certificate4638,MergedCutCells.Batch386.certificate4639,MergedCutCells.Batch386.certificate4640], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4637,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4638,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4639,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4640,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1368 : ∀ c∈certificate1368.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4637,MergedCutCells.Batch386.certificate4638,MergedCutCells.Batch386.certificate4639,MergedCutCells.Batch386.certificate4640], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4637,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4638,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4639,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4640,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1368 : ∀ c∈certificate1368.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4637,MergedCutCells.Batch386.certificate4638,MergedCutCells.Batch386.certificate4639,MergedCutCells.Batch386.certificate4640], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid558,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy027.valid559,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid560,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid561,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1368 : ∀ c∈certificate1368.cells, c.population=certificate1368.population := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4637,MergedCutCells.Batch386.certificate4638,MergedCutCells.Batch386.certificate4639,MergedCutCells.Batch386.certificate4640], c.population=PopulationCertificates.Batch046.certificate922
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1368 {x : ℝ} (hx : certificate1368.interval.Contains x) : ∃ c∈certificate1368.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1368 numericValid1368 hx

def certificate1369 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate923,PopulationCertificates.Batch046.certificate923,[MergedCutCells.Batch386.certificate4641,MergedCutCells.Batch386.certificate4642],(285240739383341127/500000000000000000),(some (7273571/6250000)),(1/2),(185878905760727011/1000000000000000000),(some (7264839342271899/500000000000000000)),(some (504125960382493/250000000000000000))⟩
theorem numericValid1369 : certificate1369.NumericValid := by decide +kernel
theorem cellsSound1369 : ∀ c∈certificate1369.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4641,MergedCutCells.Batch386.certificate4642], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4641,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4642,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1369 : ∀ c∈certificate1369.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4641,MergedCutCells.Batch386.certificate4642], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4641,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4642,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1369 : ∀ c∈certificate1369.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4641,MergedCutCells.Batch386.certificate4642], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid562,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid562,List.forall_mem_nil _⟩⟩
theorem populationMatches1369 : ∀ c∈certificate1369.cells, c.population=certificate1369.population := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4641,MergedCutCells.Batch386.certificate4642], c.population=PopulationCertificates.Batch046.certificate923
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1369 {x : ℝ} (hx : certificate1369.interval.Contains x) : ∃ c∈certificate1369.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1369 numericValid1369 hx

def certificate1370 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate923,PopulationCertificates.Batch046.certificate923,[MergedCutCells.Batch386.certificate4643,MergedCutCells.Batch387.certificate4644,MergedCutCells.Batch387.certificate4645],(7273571/6250000),none,(1/2),(11569434109559203/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1370 : certificate1370.NumericValid := by decide +kernel
theorem cellsSound1370 : ∀ c∈certificate1370.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4643,MergedCutCells.Batch387.certificate4644,MergedCutCells.Batch387.certificate4645], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.sound4643,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4644,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4645,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1370 : ∀ c∈certificate1370.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4643,MergedCutCells.Batch387.certificate4644,MergedCutCells.Batch387.certificate4645], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch386.numericValid4643,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4644,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4645,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1370 : ∀ c∈certificate1370.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4643,MergedCutCells.Batch387.certificate4644,MergedCutCells.Batch387.certificate4645], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1370 : ∀ c∈certificate1370.cells, c.population=certificate1370.population := by
  change ∀ c∈[MergedCutCells.Batch386.certificate4643,MergedCutCells.Batch387.certificate4644,MergedCutCells.Batch387.certificate4645], c.population=PopulationCertificates.Batch046.certificate923
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1370 {x : ℝ} (hx : certificate1370.interval.Contains x) : ∃ c∈certificate1370.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1370 numericValid1370 hx

def certificate1371 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate924,PopulationCertificates.Batch046.certificate924,[MergedCutCells.Batch387.certificate4646,MergedCutCells.Batch387.certificate4647],(2720584017209755229/100000000000000000),none,(1/2),(3367634456098560283/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1371 : certificate1371.NumericValid := by decide +kernel
theorem cellsSound1371 : ∀ c∈certificate1371.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4646,MergedCutCells.Batch387.certificate4647], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4646,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4647,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1371 : ∀ c∈certificate1371.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4646,MergedCutCells.Batch387.certificate4647], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4646,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4647,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1371 : ∀ c∈certificate1371.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4646,MergedCutCells.Batch387.certificate4647], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1371 : ∀ c∈certificate1371.cells, c.population=certificate1371.population := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4646,MergedCutCells.Batch387.certificate4647], c.population=PopulationCertificates.Batch046.certificate924
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1371 {x : ℝ} (hx : certificate1371.interval.Contains x) : ∃ c∈certificate1371.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1371 numericValid1371 hx

def certificate1372 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate925,PopulationCertificates.Batch046.certificate925,[MergedCutCells.Batch387.certificate4648,MergedCutCells.Batch387.certificate4649,MergedCutCells.Batch387.certificate4650,MergedCutCells.Batch387.certificate4651],(680602248496017433/1000000000000000000),none,(1/40),(33692424299284421/1000000000000000000),none,none⟩
theorem numericValid1372 : certificate1372.NumericValid := by decide +kernel
theorem cellsSound1372 : ∀ c∈certificate1372.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4648,MergedCutCells.Batch387.certificate4649,MergedCutCells.Batch387.certificate4650,MergedCutCells.Batch387.certificate4651], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4648,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4650,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4651,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1372 : ∀ c∈certificate1372.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4648,MergedCutCells.Batch387.certificate4649,MergedCutCells.Batch387.certificate4650,MergedCutCells.Batch387.certificate4651], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4648,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4650,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4651,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1372 : ∀ c∈certificate1372.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4648,MergedCutCells.Batch387.certificate4649,MergedCutCells.Batch387.certificate4650,MergedCutCells.Batch387.certificate4651], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid563,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid564,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid565,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid566,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1372 : ∀ c∈certificate1372.cells, c.population=certificate1372.population := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4648,MergedCutCells.Batch387.certificate4649,MergedCutCells.Batch387.certificate4650,MergedCutCells.Batch387.certificate4651], c.population=PopulationCertificates.Batch046.certificate925
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1372 {x : ℝ} (hx : certificate1372.interval.Contains x) : ∃ c∈certificate1372.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1372 numericValid1372 hx

def certificate1373 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate926,PopulationCertificates.Batch046.certificate926,[MergedCutCells.Batch387.certificate4652,MergedCutCells.Batch387.certificate4653],(57230182315698993/100000000000000000),(some (1166923181/1000000000)),(1/2),(190239986497757249/1000000000000000000),(some (14914432636985181/1000000000000000000)),(some (1039335202394133/500000000000000000))⟩
theorem numericValid1373 : certificate1373.NumericValid := by decide +kernel
theorem cellsSound1373 : ∀ c∈certificate1373.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4652,MergedCutCells.Batch387.certificate4653], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4652,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4653,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1373 : ∀ c∈certificate1373.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4652,MergedCutCells.Batch387.certificate4653], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4652,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4653,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1373 : ∀ c∈certificate1373.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4652,MergedCutCells.Batch387.certificate4653], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid567,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid567,List.forall_mem_nil _⟩⟩
theorem populationMatches1373 : ∀ c∈certificate1373.cells, c.population=certificate1373.population := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4652,MergedCutCells.Batch387.certificate4653], c.population=PopulationCertificates.Batch046.certificate926
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1373 {x : ℝ} (hx : certificate1373.interval.Contains x) : ∃ c∈certificate1373.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1373 numericValid1373 hx

def certificate1374 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate926,PopulationCertificates.Batch046.certificate926,[MergedCutCells.Batch387.certificate4654,MergedCutCells.Batch387.certificate4655,MergedCutCells.Batch388.certificate4656],(1166923181/1000000000),none,(1/2),(189574747793403163/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1374 : certificate1374.NumericValid := by decide +kernel
theorem cellsSound1374 : ∀ c∈certificate1374.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4654,MergedCutCells.Batch387.certificate4655,MergedCutCells.Batch388.certificate4656], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4654,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.sound4655,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4656,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1374 : ∀ c∈certificate1374.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4654,MergedCutCells.Batch387.certificate4655,MergedCutCells.Batch388.certificate4656], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4654,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch387.numericValid4655,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4656,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1374 : ∀ c∈certificate1374.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4654,MergedCutCells.Batch387.certificate4655,MergedCutCells.Batch388.certificate4656], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1374 : ∀ c∈certificate1374.cells, c.population=certificate1374.population := by
  change ∀ c∈[MergedCutCells.Batch387.certificate4654,MergedCutCells.Batch387.certificate4655,MergedCutCells.Batch388.certificate4656], c.population=PopulationCertificates.Batch046.certificate926
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1374 {x : ℝ} (hx : certificate1374.interval.Contains x) : ∃ c∈certificate1374.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1374 numericValid1374 hx

def certificate1375 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate927,PopulationCertificates.Batch046.certificate927,[MergedCutCells.Batch388.certificate4657,MergedCutCells.Batch388.certificate4658],(13861464289384307547/500000000000000000),none,(1/2),(6872585091006554109/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1375 : certificate1375.NumericValid := by decide +kernel
theorem cellsSound1375 : ∀ c∈certificate1375.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4657,MergedCutCells.Batch388.certificate4658], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4657,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4658,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1375 : ∀ c∈certificate1375.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4657,MergedCutCells.Batch388.certificate4658], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4657,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4658,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1375 : ∀ c∈certificate1375.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4657,MergedCutCells.Batch388.certificate4658], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1375 : ∀ c∈certificate1375.cells, c.population=certificate1375.population := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4657,MergedCutCells.Batch388.certificate4658], c.population=PopulationCertificates.Batch046.certificate927
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1375 {x : ℝ} (hx : certificate1375.interval.Contains x) : ∃ c∈certificate1375.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1375 numericValid1375 hx

def certificate1376 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate928,PopulationCertificates.Batch046.certificate928,[MergedCutCells.Batch388.certificate4659,MergedCutCells.Batch388.certificate4660,MergedCutCells.Batch388.certificate4661,MergedCutCells.Batch388.certificate4662],(684054873109333577/1000000000000000000),none,(1/40),(786870586970757/20000000000000000),none,none⟩
theorem numericValid1376 : certificate1376.NumericValid := by decide +kernel
theorem cellsSound1376 : ∀ c∈certificate1376.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4659,MergedCutCells.Batch388.certificate4660,MergedCutCells.Batch388.certificate4661,MergedCutCells.Batch388.certificate4662], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4659,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4660,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4662,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1376 : ∀ c∈certificate1376.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4659,MergedCutCells.Batch388.certificate4660,MergedCutCells.Batch388.certificate4661,MergedCutCells.Batch388.certificate4662], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4659,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4660,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4662,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1376 : ∀ c∈certificate1376.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4659,MergedCutCells.Batch388.certificate4660,MergedCutCells.Batch388.certificate4661,MergedCutCells.Batch388.certificate4662], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid568,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid569,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid570,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid571,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1376 : ∀ c∈certificate1376.cells, c.population=certificate1376.population := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4659,MergedCutCells.Batch388.certificate4660,MergedCutCells.Batch388.certificate4661,MergedCutCells.Batch388.certificate4662], c.population=PopulationCertificates.Batch046.certificate928
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1376 {x : ℝ} (hx : certificate1376.interval.Contains x) : ∃ c∈certificate1376.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1376 numericValid1376 hx

def certificate1377 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate929,PopulationCertificates.Batch046.certificate929,[MergedCutCells.Batch388.certificate4663,MergedCutCells.Batch388.certificate4664],(114652212763835309/200000000000000000),(some (36654657/31250000)),(1/2),(191901360537778911/1000000000000000000),(some (1532415776790331/100000000000000000)),(some (2145204999554671/1000000000000000000))⟩
theorem numericValid1377 : certificate1377.NumericValid := by decide +kernel
theorem cellsSound1377 : ∀ c∈certificate1377.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4663,MergedCutCells.Batch388.certificate4664], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4663,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4664,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1377 : ∀ c∈certificate1377.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4663,MergedCutCells.Batch388.certificate4664], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4663,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4664,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1377 : ∀ c∈certificate1377.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4663,MergedCutCells.Batch388.certificate4664], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid572,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy028.valid572,List.forall_mem_nil _⟩⟩
theorem populationMatches1377 : ∀ c∈certificate1377.cells, c.population=certificate1377.population := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4663,MergedCutCells.Batch388.certificate4664], c.population=PopulationCertificates.Batch046.certificate929
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1377 {x : ℝ} (hx : certificate1377.interval.Contains x) : ∃ c∈certificate1377.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1377 numericValid1377 hx

def certificate1378 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate929,PopulationCertificates.Batch046.certificate929,[MergedCutCells.Batch388.certificate4665,MergedCutCells.Batch388.certificate4666,MergedCutCells.Batch388.certificate4667],(36654657/31250000),none,(1/2),(191161445469902479/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1378 : certificate1378.NumericValid := by decide +kernel
theorem cellsSound1378 : ∀ c∈certificate1378.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4665,MergedCutCells.Batch388.certificate4666,MergedCutCells.Batch388.certificate4667], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4665,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4666,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.sound4667,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1378 : ∀ c∈certificate1378.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4665,MergedCutCells.Batch388.certificate4666,MergedCutCells.Batch388.certificate4667], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4665,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4666,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch388.numericValid4667,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1378 : ∀ c∈certificate1378.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4665,MergedCutCells.Batch388.certificate4666,MergedCutCells.Batch388.certificate4667], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1378 : ∀ c∈certificate1378.cells, c.population=certificate1378.population := by
  change ∀ c∈[MergedCutCells.Batch388.certificate4665,MergedCutCells.Batch388.certificate4666,MergedCutCells.Batch388.certificate4667], c.population=PopulationCertificates.Batch046.certificate929
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1378 {x : ℝ} (hx : certificate1378.interval.Contains x) : ∃ c∈certificate1378.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1378 numericValid1378 hx

def certificate1379 : RatCutGroup := ⟨GeometryCertificates.Batch046.certificate930,PopulationCertificates.Batch046.certificate930,[MergedCutCells.Batch389.certificate4668,MergedCutCells.Batch389.certificate4669],(6996548262667684657/250000000000000000),none,(1/2),(6941024075734397431/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1379 : certificate1379.NumericValid := by decide +kernel
theorem cellsSound1379 : ∀ c∈certificate1379.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4668,MergedCutCells.Batch389.certificate4669], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4668,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.sound4669,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1379 : ∀ c∈certificate1379.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4668,MergedCutCells.Batch389.certificate4669], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4668,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch389.numericValid4669,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1379 : ∀ c∈certificate1379.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4668,MergedCutCells.Batch389.certificate4669], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1379 : ∀ c∈certificate1379.cells, c.population=certificate1379.population := by
  change ∀ c∈[MergedCutCells.Batch389.certificate4668,MergedCutCells.Batch389.certificate4669], c.population=PopulationCertificates.Batch046.certificate930
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1379 {x : ℝ} (hx : certificate1379.interval.Contains x) : ∃ c∈certificate1379.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1379 numericValid1379 hx

end Cycle12.MergedCutGroups.Batch114
