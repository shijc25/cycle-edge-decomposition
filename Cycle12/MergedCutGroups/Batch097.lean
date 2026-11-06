import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch038
import Cycle12.GeometryCertificates.Batch039
import Cycle12.MergedCutCells.Batch340
import Cycle12.MergedCutCells.Batch341
import Cycle12.MergedCutCells.Batch342
import Cycle12.MergedCutCells.Batch343
import Cycle12.PopulationCertificates.Batch038
import Cycle12.PopulationCertificates.Batch039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch097

def certificate1164 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate776,PopulationCertificates.Batch038.certificate776,[MergedCutCells.Batch340.certificate4086,MergedCutCells.Batch340.certificate4087],(334937958272287857/500000000000000000),(some (219330223/200000000)),(1/2),(59925891188063021/125000000000000000),(some (22761810042928423/200000000000000000)),(some (6039609813084243/250000000000000000))⟩
theorem numericValid1164 : certificate1164.NumericValid := by decide +kernel
theorem cellsSound1164 : ∀ c∈certificate1164.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4086,MergedCutCells.Batch340.certificate4087], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4087,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1164 : ∀ c∈certificate1164.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4086,MergedCutCells.Batch340.certificate4087], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4087,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1164 : ∀ c∈certificate1164.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4086,MergedCutCells.Batch340.certificate4087], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid389,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid389,List.forall_mem_nil _⟩⟩
theorem populationMatches1164 : ∀ c∈certificate1164.cells, c.population=certificate1164.population := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4086,MergedCutCells.Batch340.certificate4087], c.population=PopulationCertificates.Batch038.certificate776
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1164 {x : ℝ} (hx : certificate1164.interval.Contains x) : ∃ c∈certificate1164.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1164 numericValid1164 hx

def certificate1165 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate776,PopulationCertificates.Batch038.certificate776,[MergedCutCells.Batch340.certificate4088,MergedCutCells.Batch340.certificate4089,MergedCutCells.Batch340.certificate4090,MergedCutCells.Batch340.certificate4091],(219330223/200000000),none,(1/2),(469265075243448099/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1165 : certificate1165.NumericValid := by decide +kernel
theorem cellsSound1165 : ∀ c∈certificate1165.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4088,MergedCutCells.Batch340.certificate4089,MergedCutCells.Batch340.certificate4090,MergedCutCells.Batch340.certificate4091], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4088,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4089,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4090,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4091,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1165 : ∀ c∈certificate1165.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4088,MergedCutCells.Batch340.certificate4089,MergedCutCells.Batch340.certificate4090,MergedCutCells.Batch340.certificate4091], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4088,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4089,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4090,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4091,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1165 : ∀ c∈certificate1165.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4088,MergedCutCells.Batch340.certificate4089,MergedCutCells.Batch340.certificate4090,MergedCutCells.Batch340.certificate4091], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1165 : ∀ c∈certificate1165.cells, c.population=certificate1165.population := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4088,MergedCutCells.Batch340.certificate4089,MergedCutCells.Batch340.certificate4090,MergedCutCells.Batch340.certificate4091], c.population=PopulationCertificates.Batch038.certificate776
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1165 {x : ℝ} (hx : certificate1165.interval.Contains x) : ∃ c∈certificate1165.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1165 numericValid1165 hx

def certificate1166 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate777,PopulationCertificates.Batch038.certificate777,[MergedCutCells.Batch341.certificate4092,MergedCutCells.Batch341.certificate4093],(12661725285250508153/500000000000000000),none,(1/2),(9165200289511241559/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1166 : certificate1166.NumericValid := by decide +kernel
theorem cellsSound1166 : ∀ c∈certificate1166.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4092,MergedCutCells.Batch341.certificate4093], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4092,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4093,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1166 : ∀ c∈certificate1166.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4092,MergedCutCells.Batch341.certificate4093], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4092,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4093,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1166 : ∀ c∈certificate1166.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4092,MergedCutCells.Batch341.certificate4093], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1166 : ∀ c∈certificate1166.cells, c.population=certificate1166.population := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4092,MergedCutCells.Batch341.certificate4093], c.population=PopulationCertificates.Batch038.certificate777
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1166 {x : ℝ} (hx : certificate1166.interval.Contains x) : ∃ c∈certificate1166.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1166 numericValid1166 hx

def certificate1167 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate778,PopulationCertificates.Batch038.certificate778,[MergedCutCells.Batch341.certificate4094,MergedCutCells.Batch341.certificate4095],(337398549912476071/500000000000000000),(some (1103833751/1000000000)),(1/2),(509291197473546209/1000000000000000000),(some (57851745771883681/500000000000000000)),(some (771004308279847/31250000000000000))⟩
theorem numericValid1167 : certificate1167.NumericValid := by decide +kernel
theorem cellsSound1167 : ∀ c∈certificate1167.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4094,MergedCutCells.Batch341.certificate4095], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4095,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1167 : ∀ c∈certificate1167.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4094,MergedCutCells.Batch341.certificate4095], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4095,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1167 : ∀ c∈certificate1167.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4094,MergedCutCells.Batch341.certificate4095], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid390,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid390,List.forall_mem_nil _⟩⟩
theorem populationMatches1167 : ∀ c∈certificate1167.cells, c.population=certificate1167.population := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4094,MergedCutCells.Batch341.certificate4095], c.population=PopulationCertificates.Batch038.certificate778
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1167 {x : ℝ} (hx : certificate1167.interval.Contains x) : ∃ c∈certificate1167.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1167 numericValid1167 hx

def certificate1168 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate778,PopulationCertificates.Batch038.certificate778,[MergedCutCells.Batch341.certificate4096,MergedCutCells.Batch341.certificate4097,MergedCutCells.Batch341.certificate4098,MergedCutCells.Batch341.certificate4099],(1103833751/1000000000),none,(1/2),(99893903321765719/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1168 : certificate1168.NumericValid := by decide +kernel
theorem cellsSound1168 : ∀ c∈certificate1168.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4096,MergedCutCells.Batch341.certificate4097,MergedCutCells.Batch341.certificate4098,MergedCutCells.Batch341.certificate4099], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4096,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4097,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4098,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4099,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1168 : ∀ c∈certificate1168.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4096,MergedCutCells.Batch341.certificate4097,MergedCutCells.Batch341.certificate4098,MergedCutCells.Batch341.certificate4099], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4096,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4097,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4098,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4099,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1168 : ∀ c∈certificate1168.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4096,MergedCutCells.Batch341.certificate4097,MergedCutCells.Batch341.certificate4098,MergedCutCells.Batch341.certificate4099], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1168 : ∀ c∈certificate1168.cells, c.population=certificate1168.population := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4096,MergedCutCells.Batch341.certificate4097,MergedCutCells.Batch341.certificate4098,MergedCutCells.Batch341.certificate4099], c.population=PopulationCertificates.Batch038.certificate778
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1168 {x : ℝ} (hx : certificate1168.interval.Contains x) : ∃ c∈certificate1168.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1168 numericValid1168 hx

def certificate1169 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate779,PopulationCertificates.Batch038.certificate779,[MergedCutCells.Batch341.certificate4100,MergedCutCells.Batch341.certificate4101],(2530656025904066357/100000000000000000),none,(1/2),(1851371653382693713/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1169 : certificate1169.NumericValid := by decide +kernel
theorem cellsSound1169 : ∀ c∈certificate1169.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4100,MergedCutCells.Batch341.certificate4101], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4101,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1169 : ∀ c∈certificate1169.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4100,MergedCutCells.Batch341.certificate4101], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4101,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1169 : ∀ c∈certificate1169.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4100,MergedCutCells.Batch341.certificate4101], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1169 : ∀ c∈certificate1169.cells, c.population=certificate1169.population := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4100,MergedCutCells.Batch341.certificate4101], c.population=PopulationCertificates.Batch038.certificate779
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1169 {x : ℝ} (hx : certificate1169.interval.Contains x) : ∃ c∈certificate1169.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1169 numericValid1169 hx

def certificate1170 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate780,PopulationCertificates.Batch039.certificate780,[MergedCutCells.Batch341.certificate4102,MergedCutCells.Batch341.certificate4103],(135970251772825923/200000000000000000),(some (1111204577/1000000000)),(1/2),(270214624529933623/500000000000000000),(some (5880918724419717/50000000000000000)),(some (393662936930521/15625000000000000))⟩
theorem numericValid1170 : certificate1170.NumericValid := by decide +kernel
theorem cellsSound1170 : ∀ c∈certificate1170.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4102,MergedCutCells.Batch341.certificate4103], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4102,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.sound4103,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1170 : ∀ c∈certificate1170.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4102,MergedCutCells.Batch341.certificate4103], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4102,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch341.numericValid4103,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1170 : ∀ c∈certificate1170.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4102,MergedCutCells.Batch341.certificate4103], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid391,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid391,List.forall_mem_nil _⟩⟩
theorem populationMatches1170 : ∀ c∈certificate1170.cells, c.population=certificate1170.population := by
  change ∀ c∈[MergedCutCells.Batch341.certificate4102,MergedCutCells.Batch341.certificate4103], c.population=PopulationCertificates.Batch039.certificate780
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1170 {x : ℝ} (hx : certificate1170.interval.Contains x) : ∃ c∈certificate1170.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1170 numericValid1170 hx

def certificate1171 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate780,PopulationCertificates.Batch039.certificate780,[MergedCutCells.Batch342.certificate4104,MergedCutCells.Batch342.certificate4105,MergedCutCells.Batch342.certificate4106,MergedCutCells.Batch342.certificate4107],(1111204577/1000000000),none,(1/2),(66281001767610577/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1171 : certificate1171.NumericValid := by decide +kernel
theorem cellsSound1171 : ∀ c∈certificate1171.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4104,MergedCutCells.Batch342.certificate4105,MergedCutCells.Batch342.certificate4106,MergedCutCells.Batch342.certificate4107], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4104,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4105,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4107,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1171 : ∀ c∈certificate1171.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4104,MergedCutCells.Batch342.certificate4105,MergedCutCells.Batch342.certificate4106,MergedCutCells.Batch342.certificate4107], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4104,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4105,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4107,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1171 : ∀ c∈certificate1171.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4104,MergedCutCells.Batch342.certificate4105,MergedCutCells.Batch342.certificate4106,MergedCutCells.Batch342.certificate4107], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1171 : ∀ c∈certificate1171.cells, c.population=certificate1171.population := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4104,MergedCutCells.Batch342.certificate4105,MergedCutCells.Batch342.certificate4106,MergedCutCells.Batch342.certificate4107], c.population=PopulationCertificates.Batch039.certificate780
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1171 {x : ℝ} (hx : certificate1171.interval.Contains x) : ∃ c∈certificate1171.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1171 numericValid1171 hx

def certificate1172 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate781,PopulationCertificates.Batch039.certificate781,[MergedCutCells.Batch342.certificate4108,MergedCutCells.Batch342.certificate4109],(1264571813073683317/50000000000000000),none,(1/2),(2337474021487680253/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1172 : certificate1172.NumericValid := by decide +kernel
theorem cellsSound1172 : ∀ c∈certificate1172.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4108,MergedCutCells.Batch342.certificate4109], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4109,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1172 : ∀ c∈certificate1172.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4108,MergedCutCells.Batch342.certificate4109], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4109,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1172 : ∀ c∈certificate1172.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4108,MergedCutCells.Batch342.certificate4109], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1172 : ∀ c∈certificate1172.cells, c.population=certificate1172.population := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4108,MergedCutCells.Batch342.certificate4109], c.population=PopulationCertificates.Batch039.certificate781
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1172 {x : ℝ} (hx : certificate1172.interval.Contains x) : ∃ c∈certificate1172.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1172 numericValid1172 hx

def certificate1173 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate782,PopulationCertificates.Batch039.certificate782,[MergedCutCells.Batch342.certificate4110,MergedCutCells.Batch342.certificate4111],(171145482160859579/250000000000000000),(some (1093773151/1000000000)),(1/2),(572231795885255761/1000000000000000000),(some (23779358122836799/200000000000000000)),(some (25544821643442893/1000000000000000000))⟩
theorem numericValid1173 : certificate1173.NumericValid := by decide +kernel
theorem cellsSound1173 : ∀ c∈certificate1173.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4110,MergedCutCells.Batch342.certificate4111], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4110,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4111,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1173 : ∀ c∈certificate1173.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4110,MergedCutCells.Batch342.certificate4111], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4110,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4111,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1173 : ∀ c∈certificate1173.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4110,MergedCutCells.Batch342.certificate4111], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid392,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid392,List.forall_mem_nil _⟩⟩
theorem populationMatches1173 : ∀ c∈certificate1173.cells, c.population=certificate1173.population := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4110,MergedCutCells.Batch342.certificate4111], c.population=PopulationCertificates.Batch039.certificate782
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1173 {x : ℝ} (hx : certificate1173.interval.Contains x) : ∃ c∈certificate1173.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1173 numericValid1173 hx

def certificate1174 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate782,PopulationCertificates.Batch039.certificate782,[MergedCutCells.Batch342.certificate4112,MergedCutCells.Batch342.certificate4113,MergedCutCells.Batch342.certificate4114,MergedCutCells.Batch342.certificate4115],(1093773151/1000000000),none,(1/2),(561682190251218687/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1174 : certificate1174.NumericValid := by decide +kernel
theorem cellsSound1174 : ∀ c∈certificate1174.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4112,MergedCutCells.Batch342.certificate4113,MergedCutCells.Batch342.certificate4114,MergedCutCells.Batch342.certificate4115], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4114,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.sound4115,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1174 : ∀ c∈certificate1174.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4112,MergedCutCells.Batch342.certificate4113,MergedCutCells.Batch342.certificate4114,MergedCutCells.Batch342.certificate4115], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4114,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch342.numericValid4115,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1174 : ∀ c∈certificate1174.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4112,MergedCutCells.Batch342.certificate4113,MergedCutCells.Batch342.certificate4114,MergedCutCells.Batch342.certificate4115], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1174 : ∀ c∈certificate1174.cells, c.population=certificate1174.population := by
  change ∀ c∈[MergedCutCells.Batch342.certificate4112,MergedCutCells.Batch342.certificate4113,MergedCutCells.Batch342.certificate4114,MergedCutCells.Batch342.certificate4115], c.population=PopulationCertificates.Batch039.certificate782
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1174 {x : ℝ} (hx : certificate1174.interval.Contains x) : ∃ c∈certificate1174.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1174 numericValid1174 hx

def certificate1175 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate783,PopulationCertificates.Batch039.certificate783,[MergedCutCells.Batch343.certificate4116,MergedCutCells.Batch343.certificate4117],(2527807769359586691/100000000000000000),none,(1/2),(2361082072429425217/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1175 : certificate1175.NumericValid := by decide +kernel
theorem cellsSound1175 : ∀ c∈certificate1175.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4116,MergedCutCells.Batch343.certificate4117], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4116,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4117,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1175 : ∀ c∈certificate1175.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4116,MergedCutCells.Batch343.certificate4117], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4116,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4117,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1175 : ∀ c∈certificate1175.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4116,MergedCutCells.Batch343.certificate4117], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1175 : ∀ c∈certificate1175.cells, c.population=certificate1175.population := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4116,MergedCutCells.Batch343.certificate4117], c.population=PopulationCertificates.Batch039.certificate783
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1175 {x : ℝ} (hx : certificate1175.interval.Contains x) : ∃ c∈certificate1175.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1175 numericValid1175 hx

end Cycle12.MergedCutGroups.Batch097
