import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch038
import Cycle12.MergedCutCells.Batch335
import Cycle12.MergedCutCells.Batch336
import Cycle12.MergedCutCells.Batch337
import Cycle12.PopulationCertificates.Batch038

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch095

def certificate1140 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate760,PopulationCertificates.Batch038.certificate760,[MergedCutCells.Batch335.certificate4022,MergedCutCells.Batch335.certificate4023],(121877011262149901/200000000000000000),(some (225573437/200000000)),(1/2),(1314808686390827/8000000000000000),(some (17895845359488487/200000000000000000)),(some (4458123103497209/250000000000000000))⟩
theorem numericValid1140 : certificate1140.NumericValid := by decide +kernel
theorem cellsSound1140 : ∀ c∈certificate1140.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4022,MergedCutCells.Batch335.certificate4023], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4022,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4023,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1140 : ∀ c∈certificate1140.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4022,MergedCutCells.Batch335.certificate4023], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4022,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4023,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1140 : ∀ c∈certificate1140.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4022,MergedCutCells.Batch335.certificate4023], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid381,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid381,List.forall_mem_nil _⟩⟩
theorem populationMatches1140 : ∀ c∈certificate1140.cells, c.population=certificate1140.population := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4022,MergedCutCells.Batch335.certificate4023], c.population=PopulationCertificates.Batch038.certificate760
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1140 {x : ℝ} (hx : certificate1140.interval.Contains x) : ∃ c∈certificate1140.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1140 numericValid1140 hx

def certificate1141 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate760,PopulationCertificates.Batch038.certificate760,[MergedCutCells.Batch335.certificate4024,MergedCutCells.Batch335.certificate4025,MergedCutCells.Batch335.certificate4026],(225573437/200000000),none,(1/2),(157070034473264711/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1141 : certificate1141.NumericValid := by decide +kernel
theorem cellsSound1141 : ∀ c∈certificate1141.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4024,MergedCutCells.Batch335.certificate4025,MergedCutCells.Batch335.certificate4026], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4024,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4025,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4026,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1141 : ∀ c∈certificate1141.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4024,MergedCutCells.Batch335.certificate4025,MergedCutCells.Batch335.certificate4026], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4024,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4025,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4026,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1141 : ∀ c∈certificate1141.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4024,MergedCutCells.Batch335.certificate4025,MergedCutCells.Batch335.certificate4026], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1141 : ∀ c∈certificate1141.cells, c.population=certificate1141.population := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4024,MergedCutCells.Batch335.certificate4025,MergedCutCells.Batch335.certificate4026], c.population=PopulationCertificates.Batch038.certificate760
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1141 {x : ℝ} (hx : certificate1141.interval.Contains x) : ∃ c∈certificate1141.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1141 numericValid1141 hx

def certificate1142 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate761,PopulationCertificates.Batch038.certificate761,[MergedCutCells.Batch335.certificate4027,MergedCutCells.Batch335.certificate4028],(24841864931235642567/1000000000000000000),none,(1/2),(7835029418647615059/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1142 : certificate1142.NumericValid := by decide +kernel
theorem cellsSound1142 : ∀ c∈certificate1142.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4027,MergedCutCells.Batch335.certificate4028], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4028,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1142 : ∀ c∈certificate1142.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4027,MergedCutCells.Batch335.certificate4028], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4028,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1142 : ∀ c∈certificate1142.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4027,MergedCutCells.Batch335.certificate4028], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1142 : ∀ c∈certificate1142.cells, c.population=certificate1142.population := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4027,MergedCutCells.Batch335.certificate4028], c.population=PopulationCertificates.Batch038.certificate761
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1142 {x : ℝ} (hx : certificate1142.interval.Contains x) : ∃ c∈certificate1142.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1142 numericValid1142 hx

def certificate1143 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate762,PopulationCertificates.Batch038.certificate762,[MergedCutCells.Batch335.certificate4029,MergedCutCells.Batch335.certificate4030],(154288263399857597/250000000000000000),(some (558081221/500000000)),(1/2),(99551205941050771/500000000000000000),(some (46235509433396019/500000000000000000)),(some (18582764410933997/1000000000000000000))⟩
theorem numericValid1143 : certificate1143.NumericValid := by decide +kernel
theorem cellsSound1143 : ∀ c∈certificate1143.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4029,MergedCutCells.Batch335.certificate4030], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4029,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4030,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1143 : ∀ c∈certificate1143.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4029,MergedCutCells.Batch335.certificate4030], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4029,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4030,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1143 : ∀ c∈certificate1143.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4029,MergedCutCells.Batch335.certificate4030], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid382,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid382,List.forall_mem_nil _⟩⟩
theorem populationMatches1143 : ∀ c∈certificate1143.cells, c.population=certificate1143.population := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4029,MergedCutCells.Batch335.certificate4030], c.population=PopulationCertificates.Batch038.certificate762
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1143 {x : ℝ} (hx : certificate1143.interval.Contains x) : ∃ c∈certificate1143.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1143 numericValid1143 hx

def certificate1144 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate762,PopulationCertificates.Batch038.certificate762,[MergedCutCells.Batch335.certificate4031,MergedCutCells.Batch336.certificate4032,MergedCutCells.Batch336.certificate4033,MergedCutCells.Batch336.certificate4034],(558081221/500000000),none,(1/2),(47807112819517963/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1144 : certificate1144.NumericValid := by decide +kernel
theorem cellsSound1144 : ∀ c∈certificate1144.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4031,MergedCutCells.Batch336.certificate4032,MergedCutCells.Batch336.certificate4033,MergedCutCells.Batch336.certificate4034], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4031,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4032,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4033,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4034,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1144 : ∀ c∈certificate1144.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4031,MergedCutCells.Batch336.certificate4032,MergedCutCells.Batch336.certificate4033,MergedCutCells.Batch336.certificate4034], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4031,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4032,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4033,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4034,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1144 : ∀ c∈certificate1144.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4031,MergedCutCells.Batch336.certificate4032,MergedCutCells.Batch336.certificate4033,MergedCutCells.Batch336.certificate4034], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1144 : ∀ c∈certificate1144.cells, c.population=certificate1144.population := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4031,MergedCutCells.Batch336.certificate4032,MergedCutCells.Batch336.certificate4033,MergedCutCells.Batch336.certificate4034], c.population=PopulationCertificates.Batch038.certificate762
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1144 {x : ℝ} (hx : certificate1144.interval.Contains x) : ∃ c∈certificate1144.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1144 numericValid1144 hx

def certificate1145 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate763,PopulationCertificates.Batch038.certificate763,[MergedCutCells.Batch336.certificate4035,MergedCutCells.Batch336.certificate4036],(6210106206462073057/250000000000000000),none,(1/2),(1596318511432260849/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1145 : certificate1145.NumericValid := by decide +kernel
theorem cellsSound1145 : ∀ c∈certificate1145.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4035,MergedCutCells.Batch336.certificate4036], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4035,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4036,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1145 : ∀ c∈certificate1145.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4035,MergedCutCells.Batch336.certificate4036], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4035,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4036,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1145 : ∀ c∈certificate1145.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4035,MergedCutCells.Batch336.certificate4036], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1145 : ∀ c∈certificate1145.cells, c.population=certificate1145.population := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4035,MergedCutCells.Batch336.certificate4036], c.population=PopulationCertificates.Batch038.certificate763
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1145 {x : ℝ} (hx : certificate1145.interval.Contains x) : ∃ c∈certificate1145.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1145 numericValid1145 hx

def certificate1146 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate764,PopulationCertificates.Batch038.certificate764,[MergedCutCells.Batch336.certificate4037,MergedCutCells.Batch336.certificate4038],(622989418965823317/1000000000000000000),(some (109797593/100000000)),(1/2),(222306651302909779/1000000000000000000),(some (95464899326214177/1000000000000000000)),(some (386828636916971/20000000000000000))⟩
theorem numericValid1146 : certificate1146.NumericValid := by decide +kernel
theorem cellsSound1146 : ∀ c∈certificate1146.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4037,MergedCutCells.Batch336.certificate4038], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4038,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1146 : ∀ c∈certificate1146.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4037,MergedCutCells.Batch336.certificate4038], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4038,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1146 : ∀ c∈certificate1146.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4037,MergedCutCells.Batch336.certificate4038], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid383,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid383,List.forall_mem_nil _⟩⟩
theorem populationMatches1146 : ∀ c∈certificate1146.cells, c.population=certificate1146.population := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4037,MergedCutCells.Batch336.certificate4038], c.population=PopulationCertificates.Batch038.certificate764
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1146 {x : ℝ} (hx : certificate1146.interval.Contains x) : ∃ c∈certificate1146.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1146 numericValid1146 hx

def certificate1147 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate764,PopulationCertificates.Batch038.certificate764,[MergedCutCells.Batch336.certificate4039,MergedCutCells.Batch336.certificate4040,MergedCutCells.Batch336.certificate4041,MergedCutCells.Batch336.certificate4042,MergedCutCells.Batch336.certificate4043],(109797593/100000000),none,(1/2),(212827057804927821/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1147 : certificate1147.NumericValid := by decide +kernel
theorem cellsSound1147 : ∀ c∈certificate1147.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4039,MergedCutCells.Batch336.certificate4040,MergedCutCells.Batch336.certificate4041,MergedCutCells.Batch336.certificate4042,MergedCutCells.Batch336.certificate4043], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4040,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4041,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4042,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.sound4043,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1147 : ∀ c∈certificate1147.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4039,MergedCutCells.Batch336.certificate4040,MergedCutCells.Batch336.certificate4041,MergedCutCells.Batch336.certificate4042,MergedCutCells.Batch336.certificate4043], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4040,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4041,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4042,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch336.numericValid4043,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1147 : ∀ c∈certificate1147.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4039,MergedCutCells.Batch336.certificate4040,MergedCutCells.Batch336.certificate4041,MergedCutCells.Batch336.certificate4042,MergedCutCells.Batch336.certificate4043], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1147 : ∀ c∈certificate1147.cells, c.population=certificate1147.population := by
  change ∀ c∈[MergedCutCells.Batch336.certificate4039,MergedCutCells.Batch336.certificate4040,MergedCutCells.Batch336.certificate4041,MergedCutCells.Batch336.certificate4042,MergedCutCells.Batch336.certificate4043], c.population=PopulationCertificates.Batch038.certificate764
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1147 {x : ℝ} (hx : certificate1147.interval.Contains x) : ∃ c∈certificate1147.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1147 numericValid1147 hx

def certificate1148 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate765,PopulationCertificates.Batch038.certificate765,[MergedCutCells.Batch337.certificate4044,MergedCutCells.Batch337.certificate4045],(24932302261032562341/1000000000000000000),none,(1/2),(8132951123203606509/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1148 : certificate1148.NumericValid := by decide +kernel
theorem cellsSound1148 : ∀ c∈certificate1148.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4044,MergedCutCells.Batch337.certificate4045], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4044,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4045,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1148 : ∀ c∈certificate1148.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4044,MergedCutCells.Batch337.certificate4045], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4044,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4045,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1148 : ∀ c∈certificate1148.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4044,MergedCutCells.Batch337.certificate4045], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1148 : ∀ c∈certificate1148.cells, c.population=certificate1148.population := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4044,MergedCutCells.Batch337.certificate4045], c.population=PopulationCertificates.Batch038.certificate765
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1148 {x : ℝ} (hx : certificate1148.interval.Contains x) : ∃ c∈certificate1148.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1148 numericValid1148 hx

def certificate1149 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate766,PopulationCertificates.Batch038.certificate766,[MergedCutCells.Batch337.certificate4046,MergedCutCells.Batch337.certificate4047],(78788363200920209/125000000000000000),(some (277321657/250000000)),(1/2),(128797700807380391/500000000000000000),(some (98970810884216279/1000000000000000000)),(some (20239774309014273/1000000000000000000))⟩
theorem numericValid1149 : certificate1149.NumericValid := by decide +kernel
theorem cellsSound1149 : ∀ c∈certificate1149.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4046,MergedCutCells.Batch337.certificate4047], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4046,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4047,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1149 : ∀ c∈certificate1149.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4046,MergedCutCells.Batch337.certificate4047], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4046,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4047,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1149 : ∀ c∈certificate1149.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4046,MergedCutCells.Batch337.certificate4047], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid384,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid384,List.forall_mem_nil _⟩⟩
theorem populationMatches1149 : ∀ c∈certificate1149.cells, c.population=certificate1149.population := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4046,MergedCutCells.Batch337.certificate4047], c.population=PopulationCertificates.Batch038.certificate766
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1149 {x : ℝ} (hx : certificate1149.interval.Contains x) : ∃ c∈certificate1149.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1149 numericValid1149 hx

def certificate1150 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate766,PopulationCertificates.Batch038.certificate766,[MergedCutCells.Batch337.certificate4048,MergedCutCells.Batch337.certificate4049,MergedCutCells.Batch337.certificate4050,MergedCutCells.Batch337.certificate4051],(277321657/250000000),none,(1/2),(249075150184393453/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1150 : certificate1150.NumericValid := by decide +kernel
theorem cellsSound1150 : ∀ c∈certificate1150.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4048,MergedCutCells.Batch337.certificate4049,MergedCutCells.Batch337.certificate4050,MergedCutCells.Batch337.certificate4051], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4048,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4050,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4051,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1150 : ∀ c∈certificate1150.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4048,MergedCutCells.Batch337.certificate4049,MergedCutCells.Batch337.certificate4050,MergedCutCells.Batch337.certificate4051], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4048,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4050,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4051,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1150 : ∀ c∈certificate1150.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4048,MergedCutCells.Batch337.certificate4049,MergedCutCells.Batch337.certificate4050,MergedCutCells.Batch337.certificate4051], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1150 : ∀ c∈certificate1150.cells, c.population=certificate1150.population := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4048,MergedCutCells.Batch337.certificate4049,MergedCutCells.Batch337.certificate4050,MergedCutCells.Batch337.certificate4051], c.population=PopulationCertificates.Batch038.certificate766
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1150 {x : ℝ} (hx : certificate1150.interval.Contains x) : ∃ c∈certificate1150.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1150 numericValid1150 hx

def certificate1151 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate767,PopulationCertificates.Batch038.certificate767,[MergedCutCells.Batch337.certificate4052,MergedCutCells.Batch337.certificate4053],(25086596723691509049/1000000000000000000),none,(1/2),(4149602534579760443/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1151 : certificate1151.NumericValid := by decide +kernel
theorem cellsSound1151 : ∀ c∈certificate1151.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4052,MergedCutCells.Batch337.certificate4053], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4052,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4053,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1151 : ∀ c∈certificate1151.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4052,MergedCutCells.Batch337.certificate4053], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4052,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4053,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1151 : ∀ c∈certificate1151.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4052,MergedCutCells.Batch337.certificate4053], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1151 : ∀ c∈certificate1151.cells, c.population=certificate1151.population := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4052,MergedCutCells.Batch337.certificate4053], c.population=PopulationCertificates.Batch038.certificate767
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1151 {x : ℝ} (hx : certificate1151.interval.Contains x) : ∃ c∈certificate1151.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1151 numericValid1151 hx

end Cycle12.MergedCutGroups.Batch095
