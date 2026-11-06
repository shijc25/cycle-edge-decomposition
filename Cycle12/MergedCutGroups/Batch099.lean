import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch039
import Cycle12.MergedCutCells.Batch346
import Cycle12.MergedCutCells.Batch347
import Cycle12.MergedCutCells.Batch348
import Cycle12.PopulationCertificates.Batch039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch099

def certificate1188 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate792,PopulationCertificates.Batch039.certificate792,[MergedCutCells.Batch346.certificate4152,MergedCutCells.Batch346.certificate4153],(45356521315323251/62500000000000000),(some (275686061/250000000)),(1/2),(432424280564185601/500000000000000000),(some (131245515360859209/1000000000000000000)),(some (3624886649159447/125000000000000000))⟩
theorem numericValid1188 : certificate1188.NumericValid := by decide +kernel
theorem cellsSound1188 : ∀ c∈certificate1188.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4152,MergedCutCells.Batch346.certificate4153], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4153,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1188 : ∀ c∈certificate1188.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4152,MergedCutCells.Batch346.certificate4153], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4153,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1188 : ∀ c∈certificate1188.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4152,MergedCutCells.Batch346.certificate4153], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid397,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid397,List.forall_mem_nil _⟩⟩
theorem populationMatches1188 : ∀ c∈certificate1188.cells, c.population=certificate1188.population := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4152,MergedCutCells.Batch346.certificate4153], c.population=PopulationCertificates.Batch039.certificate792
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1188 {x : ℝ} (hx : certificate1188.interval.Contains x) : ∃ c∈certificate1188.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1188 numericValid1188 hx

def certificate1189 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate792,PopulationCertificates.Batch039.certificate792,[MergedCutCells.Batch346.certificate4154,MergedCutCells.Batch346.certificate4155,MergedCutCells.Batch346.certificate4156,MergedCutCells.Batch346.certificate4157],(275686061/250000000),none,(1/2),(426882488631929187/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1189 : certificate1189.NumericValid := by decide +kernel
theorem cellsSound1189 : ∀ c∈certificate1189.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4154,MergedCutCells.Batch346.certificate4155,MergedCutCells.Batch346.certificate4156,MergedCutCells.Batch346.certificate4157], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4154,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4157,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1189 : ∀ c∈certificate1189.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4154,MergedCutCells.Batch346.certificate4155,MergedCutCells.Batch346.certificate4156,MergedCutCells.Batch346.certificate4157], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4154,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4157,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1189 : ∀ c∈certificate1189.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4154,MergedCutCells.Batch346.certificate4155,MergedCutCells.Batch346.certificate4156,MergedCutCells.Batch346.certificate4157], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1189 : ∀ c∈certificate1189.cells, c.population=certificate1189.population := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4154,MergedCutCells.Batch346.certificate4155,MergedCutCells.Batch346.certificate4156,MergedCutCells.Batch346.certificate4157], c.population=PopulationCertificates.Batch039.certificate792
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1189 {x : ℝ} (hx : certificate1189.interval.Contains x) : ∃ c∈certificate1189.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1189 numericValid1189 hx

def certificate1190 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate793,PopulationCertificates.Batch039.certificate793,[MergedCutCells.Batch346.certificate4158,MergedCutCells.Batch346.certificate4159],(24831132594638999937/1000000000000000000),none,(1/2),(10133689561639820417/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1190 : certificate1190.NumericValid := by decide +kernel
theorem cellsSound1190 : ∀ c∈certificate1190.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4158,MergedCutCells.Batch346.certificate4159], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4159,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1190 : ∀ c∈certificate1190.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4158,MergedCutCells.Batch346.certificate4159], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4159,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1190 : ∀ c∈certificate1190.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4158,MergedCutCells.Batch346.certificate4159], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1190 : ∀ c∈certificate1190.cells, c.population=certificate1190.population := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4158,MergedCutCells.Batch346.certificate4159], c.population=PopulationCertificates.Batch039.certificate793
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1190 {x : ℝ} (hx : certificate1190.interval.Contains x) : ∃ c∈certificate1190.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1190 numericValid1190 hx

def certificate1191 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate794,PopulationCertificates.Batch039.certificate794,[MergedCutCells.Batch346.certificate4160,MergedCutCells.Batch346.certificate4161,MergedCutCells.Batch346.certificate4162],(732876725123950387/1000000000000000000),(some (1112620479/1000000000)),(1/2),(921479808123948937/1000000000000000000),(some (133256959779391487/1000000000000000000)),(some (29573639683627821/1000000000000000000))⟩
theorem numericValid1191 : certificate1191.NumericValid := by decide +kernel
theorem cellsSound1191 : ∀ c∈certificate1191.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4160,MergedCutCells.Batch346.certificate4161,MergedCutCells.Batch346.certificate4162], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4162,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1191 : ∀ c∈certificate1191.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4160,MergedCutCells.Batch346.certificate4161,MergedCutCells.Batch346.certificate4162], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4162,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1191 : ∀ c∈certificate1191.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4160,MergedCutCells.Batch346.certificate4161,MergedCutCells.Batch346.certificate4162], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid398,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid398,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid398,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1191 : ∀ c∈certificate1191.cells, c.population=certificate1191.population := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4160,MergedCutCells.Batch346.certificate4161,MergedCutCells.Batch346.certificate4162], c.population=PopulationCertificates.Batch039.certificate794
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1191 {x : ℝ} (hx : certificate1191.interval.Contains x) : ∃ c∈certificate1191.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1191 numericValid1191 hx

def certificate1192 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate794,PopulationCertificates.Batch039.certificate794,[MergedCutCells.Batch346.certificate4163,MergedCutCells.Batch347.certificate4164,MergedCutCells.Batch347.certificate4165,MergedCutCells.Batch347.certificate4166],(1112620479/1000000000),none,(1/2),(909719463146133401/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1192 : certificate1192.NumericValid := by decide +kernel
theorem cellsSound1192 : ∀ c∈certificate1192.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4163,MergedCutCells.Batch347.certificate4164,MergedCutCells.Batch347.certificate4165,MergedCutCells.Batch347.certificate4166], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.sound4163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4164,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4166,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1192 : ∀ c∈certificate1192.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4163,MergedCutCells.Batch347.certificate4164,MergedCutCells.Batch347.certificate4165,MergedCutCells.Batch347.certificate4166], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch346.numericValid4163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4164,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4166,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1192 : ∀ c∈certificate1192.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4163,MergedCutCells.Batch347.certificate4164,MergedCutCells.Batch347.certificate4165,MergedCutCells.Batch347.certificate4166], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1192 : ∀ c∈certificate1192.cells, c.population=certificate1192.population := by
  change ∀ c∈[MergedCutCells.Batch346.certificate4163,MergedCutCells.Batch347.certificate4164,MergedCutCells.Batch347.certificate4165,MergedCutCells.Batch347.certificate4166], c.population=PopulationCertificates.Batch039.certificate794
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1192 {x : ℝ} (hx : certificate1192.interval.Contains x) : ∃ c∈certificate1192.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1192 numericValid1192 hx

def certificate1193 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate795,PopulationCertificates.Batch039.certificate795,[MergedCutCells.Batch347.certificate4167,MergedCutCells.Batch347.certificate4168],(773103615574589829/31250000000000000),none,(1/2),(5119804071501776249/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1193 : certificate1193.NumericValid := by decide +kernel
theorem cellsSound1193 : ∀ c∈certificate1193.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4167,MergedCutCells.Batch347.certificate4168], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4167,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4168,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1193 : ∀ c∈certificate1193.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4167,MergedCutCells.Batch347.certificate4168], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4167,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4168,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1193 : ∀ c∈certificate1193.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4167,MergedCutCells.Batch347.certificate4168], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1193 : ∀ c∈certificate1193.cells, c.population=certificate1193.population := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4167,MergedCutCells.Batch347.certificate4168], c.population=PopulationCertificates.Batch039.certificate795
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1193 {x : ℝ} (hx : certificate1193.interval.Contains x) : ∃ c∈certificate1193.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1193 numericValid1193 hx

def certificate1194 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate796,PopulationCertificates.Batch039.certificate796,[MergedCutCells.Batch347.certificate4169,MergedCutCells.Batch347.certificate4170],(369672128195639823/500000000000000000),(some (43869499/40000000)),(1/2),(979083960449609863/1000000000000000000),(some (33627470723188301/250000000000000000)),(some (29933198514104553/1000000000000000000))⟩
theorem numericValid1194 : certificate1194.NumericValid := by decide +kernel
theorem cellsSound1194 : ∀ c∈certificate1194.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4169,MergedCutCells.Batch347.certificate4170], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4170,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1194 : ∀ c∈certificate1194.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4169,MergedCutCells.Batch347.certificate4170], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4170,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1194 : ∀ c∈certificate1194.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4169,MergedCutCells.Batch347.certificate4170], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid399,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid399,List.forall_mem_nil _⟩⟩
theorem populationMatches1194 : ∀ c∈certificate1194.cells, c.population=certificate1194.population := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4169,MergedCutCells.Batch347.certificate4170], c.population=PopulationCertificates.Batch039.certificate796
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1194 {x : ℝ} (hx : certificate1194.interval.Contains x) : ∃ c∈certificate1194.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1194 numericValid1194 hx

def certificate1195 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate796,PopulationCertificates.Batch039.certificate796,[MergedCutCells.Batch347.certificate4171,MergedCutCells.Batch347.certificate4172,MergedCutCells.Batch347.certificate4173,MergedCutCells.Batch347.certificate4174],(43869499/40000000),none,(1/2),(193432989858094129/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1195 : certificate1195.NumericValid := by decide +kernel
theorem cellsSound1195 : ∀ c∈certificate1195.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4171,MergedCutCells.Batch347.certificate4172,MergedCutCells.Batch347.certificate4173,MergedCutCells.Batch347.certificate4174], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4173,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4174,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1195 : ∀ c∈certificate1195.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4171,MergedCutCells.Batch347.certificate4172,MergedCutCells.Batch347.certificate4173,MergedCutCells.Batch347.certificate4174], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4173,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4174,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1195 : ∀ c∈certificate1195.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4171,MergedCutCells.Batch347.certificate4172,MergedCutCells.Batch347.certificate4173,MergedCutCells.Batch347.certificate4174], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1195 : ∀ c∈certificate1195.cells, c.population=certificate1195.population := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4171,MergedCutCells.Batch347.certificate4172,MergedCutCells.Batch347.certificate4173,MergedCutCells.Batch347.certificate4174], c.population=PopulationCertificates.Batch039.certificate796
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1195 {x : ℝ} (hx : certificate1195.interval.Contains x) : ∃ c∈certificate1195.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1195 numericValid1195 hx

def certificate1196 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate797,PopulationCertificates.Batch039.certificate797,[MergedCutCells.Batch347.certificate4175,MergedCutCells.Batch348.certificate4176],(4929728520984475523/200000000000000000),none,(1/2),(1293396227015708367/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1196 : certificate1196.NumericValid := by decide +kernel
theorem cellsSound1196 : ∀ c∈certificate1196.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4175,MergedCutCells.Batch348.certificate4176], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.sound4175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4176,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1196 : ∀ c∈certificate1196.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4175,MergedCutCells.Batch348.certificate4176], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch347.numericValid4175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4176,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1196 : ∀ c∈certificate1196.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4175,MergedCutCells.Batch348.certificate4176], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1196 : ∀ c∈certificate1196.cells, c.population=certificate1196.population := by
  change ∀ c∈[MergedCutCells.Batch347.certificate4175,MergedCutCells.Batch348.certificate4176], c.population=PopulationCertificates.Batch039.certificate797
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1196 {x : ℝ} (hx : certificate1196.interval.Contains x) : ∃ c∈certificate1196.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1196 numericValid1196 hx

def certificate1197 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate798,PopulationCertificates.Batch039.certificate798,[MergedCutCells.Batch348.certificate4177,MergedCutCells.Batch348.certificate4178],(746189293148217977/1000000000000000000),(some (1105989993/1000000000)),(1/2),(1037861693589105517/1000000000000000000),(some (27306546448218693/200000000000000000)),(some (30516418325573063/1000000000000000000))⟩
theorem numericValid1197 : certificate1197.NumericValid := by decide +kernel
theorem cellsSound1197 : ∀ c∈certificate1197.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4177,MergedCutCells.Batch348.certificate4178], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4178,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1197 : ∀ c∈certificate1197.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4177,MergedCutCells.Batch348.certificate4178], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4178,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1197 : ∀ c∈certificate1197.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4177,MergedCutCells.Batch348.certificate4178], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid400,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid400,List.forall_mem_nil _⟩⟩
theorem populationMatches1197 : ∀ c∈certificate1197.cells, c.population=certificate1197.population := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4177,MergedCutCells.Batch348.certificate4178], c.population=PopulationCertificates.Batch039.certificate798
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1197 {x : ℝ} (hx : certificate1197.interval.Contains x) : ∃ c∈certificate1197.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1197 numericValid1197 hx

def certificate1198 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate798,PopulationCertificates.Batch039.certificate798,[MergedCutCells.Batch348.certificate4179,MergedCutCells.Batch348.certificate4180,MergedCutCells.Batch348.certificate4181,MergedCutCells.Batch348.certificate4182],(1105989993/1000000000),none,(1/2),(1025919951196627343/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1198 : certificate1198.NumericValid := by decide +kernel
theorem cellsSound1198 : ∀ c∈certificate1198.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4179,MergedCutCells.Batch348.certificate4180,MergedCutCells.Batch348.certificate4181,MergedCutCells.Batch348.certificate4182], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4182,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1198 : ∀ c∈certificate1198.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4179,MergedCutCells.Batch348.certificate4180,MergedCutCells.Batch348.certificate4181,MergedCutCells.Batch348.certificate4182], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4182,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1198 : ∀ c∈certificate1198.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4179,MergedCutCells.Batch348.certificate4180,MergedCutCells.Batch348.certificate4181,MergedCutCells.Batch348.certificate4182], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1198 : ∀ c∈certificate1198.cells, c.population=certificate1198.population := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4179,MergedCutCells.Batch348.certificate4180,MergedCutCells.Batch348.certificate4181,MergedCutCells.Batch348.certificate4182], c.population=PopulationCertificates.Batch039.certificate798
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1198 {x : ℝ} (hx : certificate1198.interval.Contains x) : ∃ c∈certificate1198.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1198 numericValid1198 hx

def certificate1199 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate799,PopulationCertificates.Batch039.certificate799,[MergedCutCells.Batch348.certificate4183,MergedCutCells.Batch348.certificate4184],(24558981787317954221/1000000000000000000),none,(1/2),(10456398488760776853/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1199 : certificate1199.NumericValid := by decide +kernel
theorem cellsSound1199 : ∀ c∈certificate1199.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4183,MergedCutCells.Batch348.certificate4184], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4184,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1199 : ∀ c∈certificate1199.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4183,MergedCutCells.Batch348.certificate4184], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4184,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1199 : ∀ c∈certificate1199.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4183,MergedCutCells.Batch348.certificate4184], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1199 : ∀ c∈certificate1199.cells, c.population=certificate1199.population := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4183,MergedCutCells.Batch348.certificate4184], c.population=PopulationCertificates.Batch039.certificate799
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1199 {x : ℝ} (hx : certificate1199.interval.Contains x) : ∃ c∈certificate1199.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1199 numericValid1199 hx

end Cycle12.MergedCutGroups.Batch099
