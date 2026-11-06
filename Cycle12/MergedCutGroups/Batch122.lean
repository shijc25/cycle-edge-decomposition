import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch049
import Cycle12.GeometryCertificates.Batch050
import Cycle12.MergedCutCells.Batch408
import Cycle12.MergedCutCells.Batch409
import Cycle12.MergedCutCells.Batch410
import Cycle12.MergedCutCells.Batch411
import Cycle12.PopulationCertificates.Batch049
import Cycle12.PopulationCertificates.Batch050

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch122

def certificate1464 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate994,PopulationCertificates.Batch049.certificate994,[MergedCutCells.Batch408.certificate4904,MergedCutCells.Batch408.certificate4905,MergedCutCells.Batch408.certificate4906,MergedCutCells.Batch408.certificate4907,MergedCutCells.Batch409.certificate4908],(695132326906251343/1000000000000000000),none,(1/40),(825648779447007/40000000000000000),none,none⟩
theorem numericValid1464 : certificate1464.NumericValid := by decide +kernel
theorem cellsSound1464 : ∀ c∈certificate1464.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4904,MergedCutCells.Batch408.certificate4905,MergedCutCells.Batch408.certificate4906,MergedCutCells.Batch408.certificate4907,MergedCutCells.Batch409.certificate4908], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4904,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4905,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4906,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.sound4907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4908,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1464 : ∀ c∈certificate1464.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4904,MergedCutCells.Batch408.certificate4905,MergedCutCells.Batch408.certificate4906,MergedCutCells.Batch408.certificate4907,MergedCutCells.Batch409.certificate4908], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4904,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4905,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4906,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch408.numericValid4907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4908,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1464 : ∀ c∈certificate1464.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4904,MergedCutCells.Batch408.certificate4905,MergedCutCells.Batch408.certificate4906,MergedCutCells.Batch408.certificate4907,MergedCutCells.Batch409.certificate4908], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid680,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid681,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid682,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid683,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid684,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1464 : ∀ c∈certificate1464.cells, c.population=certificate1464.population := by
  change ∀ c∈[MergedCutCells.Batch408.certificate4904,MergedCutCells.Batch408.certificate4905,MergedCutCells.Batch408.certificate4906,MergedCutCells.Batch408.certificate4907,MergedCutCells.Batch409.certificate4908], c.population=PopulationCertificates.Batch049.certificate994
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1464 {x : ℝ} (hx : certificate1464.interval.Contains x) : ∃ c∈certificate1464.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1464 numericValid1464 hx

def certificate1465 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate995,PopulationCertificates.Batch049.certificate995,[MergedCutCells.Batch409.certificate4909,MergedCutCells.Batch409.certificate4910],(148078631278807129/250000000000000000),(some (281046559/250000000)),(1/2),(1144715320051249/5000000000000000),(some (4769837054546003/200000000000000000)),(some (359984277775627/100000000000000000))⟩
theorem numericValid1465 : certificate1465.NumericValid := by decide +kernel
theorem cellsSound1465 : ∀ c∈certificate1465.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4909,MergedCutCells.Batch409.certificate4910], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4909,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4910,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1465 : ∀ c∈certificate1465.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4909,MergedCutCells.Batch409.certificate4910], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4909,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4910,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1465 : ∀ c∈certificate1465.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4909,MergedCutCells.Batch409.certificate4910], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid685,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid685,List.forall_mem_nil _⟩⟩
theorem populationMatches1465 : ∀ c∈certificate1465.cells, c.population=certificate1465.population := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4909,MergedCutCells.Batch409.certificate4910], c.population=PopulationCertificates.Batch049.certificate995
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1465 {x : ℝ} (hx : certificate1465.interval.Contains x) : ∃ c∈certificate1465.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1465 numericValid1465 hx

def certificate1466 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate995,PopulationCertificates.Batch049.certificate995,[MergedCutCells.Batch409.certificate4911,MergedCutCells.Batch409.certificate4912,MergedCutCells.Batch409.certificate4913],(281046559/250000000),none,(1/2),(113774747672797489/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1466 : certificate1466.NumericValid := by decide +kernel
theorem cellsSound1466 : ∀ c∈certificate1466.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4911,MergedCutCells.Batch409.certificate4912,MergedCutCells.Batch409.certificate4913], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4911,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4913,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1466 : ∀ c∈certificate1466.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4911,MergedCutCells.Batch409.certificate4912,MergedCutCells.Batch409.certificate4913], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4911,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4913,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1466 : ∀ c∈certificate1466.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4911,MergedCutCells.Batch409.certificate4912,MergedCutCells.Batch409.certificate4913], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1466 : ∀ c∈certificate1466.cells, c.population=certificate1466.population := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4911,MergedCutCells.Batch409.certificate4912,MergedCutCells.Batch409.certificate4913], c.population=PopulationCertificates.Batch049.certificate995
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1466 {x : ℝ} (hx : certificate1466.interval.Contains x) : ∃ c∈certificate1466.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1466 numericValid1466 hx

def certificate1467 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate996,PopulationCertificates.Batch049.certificate996,[MergedCutCells.Batch409.certificate4914,MergedCutCells.Batch409.certificate4915],(3402928242502243139/100000000000000000),none,(1/2),(2123344362972391299/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1467 : certificate1467.NumericValid := by decide +kernel
theorem cellsSound1467 : ∀ c∈certificate1467.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4914,MergedCutCells.Batch409.certificate4915], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4915,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1467 : ∀ c∈certificate1467.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4914,MergedCutCells.Batch409.certificate4915], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4915,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1467 : ∀ c∈certificate1467.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4914,MergedCutCells.Batch409.certificate4915], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1467 : ∀ c∈certificate1467.cells, c.population=certificate1467.population := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4914,MergedCutCells.Batch409.certificate4915], c.population=PopulationCertificates.Batch049.certificate996
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1467 {x : ℝ} (hx : certificate1467.interval.Contains x) : ∃ c∈certificate1467.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1467 numericValid1467 hx

def certificate1468 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate997,PopulationCertificates.Batch049.certificate997,[MergedCutCells.Batch409.certificate4916,MergedCutCells.Batch409.certificate4917,MergedCutCells.Batch409.certificate4918,MergedCutCells.Batch409.certificate4919,MergedCutCells.Batch410.certificate4920],(348552208969343597/500000000000000000),none,(1/40),(23200018932650019/1000000000000000000),none,none⟩
theorem numericValid1468 : certificate1468.NumericValid := by decide +kernel
theorem cellsSound1468 : ∀ c∈certificate1468.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4916,MergedCutCells.Batch409.certificate4917,MergedCutCells.Batch409.certificate4918,MergedCutCells.Batch409.certificate4919,MergedCutCells.Batch410.certificate4920], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4916,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4917,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4918,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.sound4919,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4920,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1468 : ∀ c∈certificate1468.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4916,MergedCutCells.Batch409.certificate4917,MergedCutCells.Batch409.certificate4918,MergedCutCells.Batch409.certificate4919,MergedCutCells.Batch410.certificate4920], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4916,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4917,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4918,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch409.numericValid4919,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4920,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1468 : ∀ c∈certificate1468.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4916,MergedCutCells.Batch409.certificate4917,MergedCutCells.Batch409.certificate4918,MergedCutCells.Batch409.certificate4919,MergedCutCells.Batch410.certificate4920], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid686,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid687,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid688,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid689,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid690,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1468 : ∀ c∈certificate1468.cells, c.population=certificate1468.population := by
  change ∀ c∈[MergedCutCells.Batch409.certificate4916,MergedCutCells.Batch409.certificate4917,MergedCutCells.Batch409.certificate4918,MergedCutCells.Batch409.certificate4919,MergedCutCells.Batch410.certificate4920], c.population=PopulationCertificates.Batch049.certificate997
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1468 {x : ℝ} (hx : certificate1468.interval.Contains x) : ∃ c∈certificate1468.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1468 numericValid1468 hx

def certificate1469 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate998,PopulationCertificates.Batch049.certificate998,[MergedCutCells.Batch410.certificate4921,MergedCutCells.Batch410.certificate4922],(593293179960146709/1000000000000000000),(some (1125789323/1000000000)),(1/2),(4623065463991663/20000000000000000),(some (2434268841824501/100000000000000000)),(some (3687794055610639/1000000000000000000))⟩
theorem numericValid1469 : certificate1469.NumericValid := by decide +kernel
theorem cellsSound1469 : ∀ c∈certificate1469.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4921,MergedCutCells.Batch410.certificate4922], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4921,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4922,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1469 : ∀ c∈certificate1469.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4921,MergedCutCells.Batch410.certificate4922], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4921,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4922,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1469 : ∀ c∈certificate1469.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4921,MergedCutCells.Batch410.certificate4922], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid691,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid691,List.forall_mem_nil _⟩⟩
theorem populationMatches1469 : ∀ c∈certificate1469.cells, c.population=certificate1469.population := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4921,MergedCutCells.Batch410.certificate4922], c.population=PopulationCertificates.Batch049.certificate998
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1469 {x : ℝ} (hx : certificate1469.interval.Contains x) : ∃ c∈certificate1469.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1469 numericValid1469 hx

def certificate1470 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate998,PopulationCertificates.Batch049.certificate998,[MergedCutCells.Batch410.certificate4923,MergedCutCells.Batch410.certificate4924,MergedCutCells.Batch410.certificate4925],(1125789323/1000000000),none,(1/2),(114818795199297161/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1470 : certificate1470.NumericValid := by decide +kernel
theorem cellsSound1470 : ∀ c∈certificate1470.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4923,MergedCutCells.Batch410.certificate4924,MergedCutCells.Batch410.certificate4925], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4923,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4925,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1470 : ∀ c∈certificate1470.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4923,MergedCutCells.Batch410.certificate4924,MergedCutCells.Batch410.certificate4925], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4923,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4925,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1470 : ∀ c∈certificate1470.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4923,MergedCutCells.Batch410.certificate4924,MergedCutCells.Batch410.certificate4925], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1470 : ∀ c∈certificate1470.cells, c.population=certificate1470.population := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4923,MergedCutCells.Batch410.certificate4924,MergedCutCells.Batch410.certificate4925], c.population=PopulationCertificates.Batch049.certificate998
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1470 {x : ℝ} (hx : certificate1470.interval.Contains x) : ∃ c∈certificate1470.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1470 numericValid1470 hx

def certificate1471 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate999,PopulationCertificates.Batch049.certificate999,[MergedCutCells.Batch410.certificate4926,MergedCutCells.Batch410.certificate4927],(34375797063276508917/1000000000000000000),none,(1/2),(1716292817621215419/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1471 : certificate1471.NumericValid := by decide +kernel
theorem cellsSound1471 : ∀ c∈certificate1471.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4926,MergedCutCells.Batch410.certificate4927], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4926,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4927,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1471 : ∀ c∈certificate1471.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4926,MergedCutCells.Batch410.certificate4927], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4926,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4927,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1471 : ∀ c∈certificate1471.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4926,MergedCutCells.Batch410.certificate4927], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1471 : ∀ c∈certificate1471.cells, c.population=certificate1471.population := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4926,MergedCutCells.Batch410.certificate4927], c.population=PopulationCertificates.Batch049.certificate999
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1471 {x : ℝ} (hx : certificate1471.interval.Contains x) : ∃ c∈certificate1471.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1471 numericValid1471 hx

def certificate1472 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1000,PopulationCertificates.Batch050.certificate1000,[MergedCutCells.Batch410.certificate4928,MergedCutCells.Batch410.certificate4929,MergedCutCells.Batch410.certificate4930,MergedCutCells.Batch410.certificate4931,MergedCutCells.Batch411.certificate4932],(349539614744881821/500000000000000000),none,(1/40),(25851732458484933/1000000000000000000),none,none⟩
theorem numericValid1472 : certificate1472.NumericValid := by decide +kernel
theorem cellsSound1472 : ∀ c∈certificate1472.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4928,MergedCutCells.Batch410.certificate4929,MergedCutCells.Batch410.certificate4930,MergedCutCells.Batch410.certificate4931,MergedCutCells.Batch411.certificate4932], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4928,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4930,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.sound4931,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4932,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1472 : ∀ c∈certificate1472.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4928,MergedCutCells.Batch410.certificate4929,MergedCutCells.Batch410.certificate4930,MergedCutCells.Batch410.certificate4931,MergedCutCells.Batch411.certificate4932], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4928,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4930,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch410.numericValid4931,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4932,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1472 : ∀ c∈certificate1472.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4928,MergedCutCells.Batch410.certificate4929,MergedCutCells.Batch410.certificate4930,MergedCutCells.Batch410.certificate4931,MergedCutCells.Batch411.certificate4932], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid692,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid693,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid694,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid695,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid696,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1472 : ∀ c∈certificate1472.cells, c.population=certificate1472.population := by
  change ∀ c∈[MergedCutCells.Batch410.certificate4928,MergedCutCells.Batch410.certificate4929,MergedCutCells.Batch410.certificate4930,MergedCutCells.Batch410.certificate4931,MergedCutCells.Batch411.certificate4932], c.population=PopulationCertificates.Batch050.certificate1000
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1472 {x : ℝ} (hx : certificate1472.interval.Contains x) : ∃ c∈certificate1472.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1472 numericValid1472 hx

def certificate1473 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1001,PopulationCertificates.Batch050.certificate1001,[MergedCutCells.Batch411.certificate4933,MergedCutCells.Batch411.certificate4934],(594270851700883867/1000000000000000000),(some (563695217/500000000)),(1/2),(933586192310727/4000000000000000),(some (12420671799406711/500000000000000000)),(some (1888523546672771/500000000000000000))⟩
theorem numericValid1473 : certificate1473.NumericValid := by decide +kernel
theorem cellsSound1473 : ∀ c∈certificate1473.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4933,MergedCutCells.Batch411.certificate4934], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4934,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1473 : ∀ c∈certificate1473.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4933,MergedCutCells.Batch411.certificate4934], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4934,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1473 : ∀ c∈certificate1473.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4933,MergedCutCells.Batch411.certificate4934], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid697,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy034.valid697,List.forall_mem_nil _⟩⟩
theorem populationMatches1473 : ∀ c∈certificate1473.cells, c.population=certificate1473.population := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4933,MergedCutCells.Batch411.certificate4934], c.population=PopulationCertificates.Batch050.certificate1001
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1473 {x : ℝ} (hx : certificate1473.interval.Contains x) : ∃ c∈certificate1473.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1473 numericValid1473 hx

def certificate1474 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1001,PopulationCertificates.Batch050.certificate1001,[MergedCutCells.Batch411.certificate4935,MergedCutCells.Batch411.certificate4936,MergedCutCells.Batch411.certificate4937],(563695217/500000000),none,(1/2),(5793894232599633/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1474 : certificate1474.NumericValid := by decide +kernel
theorem cellsSound1474 : ∀ c∈certificate1474.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4935,MergedCutCells.Batch411.certificate4936,MergedCutCells.Batch411.certificate4937], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4935,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4936,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4937,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1474 : ∀ c∈certificate1474.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4935,MergedCutCells.Batch411.certificate4936,MergedCutCells.Batch411.certificate4937], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4935,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4936,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4937,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1474 : ∀ c∈certificate1474.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4935,MergedCutCells.Batch411.certificate4936,MergedCutCells.Batch411.certificate4937], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1474 : ∀ c∈certificate1474.cells, c.population=certificate1474.population := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4935,MergedCutCells.Batch411.certificate4936,MergedCutCells.Batch411.certificate4937], c.population=PopulationCertificates.Batch050.certificate1001
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1474 {x : ℝ} (hx : certificate1474.interval.Contains x) : ∃ c∈certificate1474.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1474 numericValid1474 hx

def certificate1475 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1002,PopulationCertificates.Batch050.certificate1002,[MergedCutCells.Batch411.certificate4938,MergedCutCells.Batch411.certificate4939],(17363563446128046143/500000000000000000),none,(1/2),(1734105014949053567/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1475 : certificate1475.NumericValid := by decide +kernel
theorem cellsSound1475 : ∀ c∈certificate1475.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4938,MergedCutCells.Batch411.certificate4939], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4938,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.sound4939,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1475 : ∀ c∈certificate1475.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4938,MergedCutCells.Batch411.certificate4939], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4938,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch411.numericValid4939,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1475 : ∀ c∈certificate1475.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4938,MergedCutCells.Batch411.certificate4939], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1475 : ∀ c∈certificate1475.cells, c.population=certificate1475.population := by
  change ∀ c∈[MergedCutCells.Batch411.certificate4938,MergedCutCells.Batch411.certificate4939], c.population=PopulationCertificates.Batch050.certificate1002
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1475 {x : ℝ} (hx : certificate1475.interval.Contains x) : ∃ c∈certificate1475.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1475 numericValid1475 hx

end Cycle12.MergedCutGroups.Batch122
