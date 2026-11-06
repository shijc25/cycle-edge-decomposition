import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch041
import Cycle12.GeometryCertificates.Batch042
import Cycle12.MergedCutCells.Batch359
import Cycle12.MergedCutCells.Batch360
import Cycle12.MergedCutCells.Batch361
import Cycle12.PopulationCertificates.Batch041
import Cycle12.PopulationCertificates.Batch042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch104

def certificate1248 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate832,PopulationCertificates.Batch041.certificate832,[MergedCutCells.Batch359.certificate4314,MergedCutCells.Batch359.certificate4315,MergedCutCells.Batch359.certificate4316],(173383363726678583/250000000000000000),none,(1/40),(208128872732730479/1000000000000000000),none,none⟩
theorem numericValid1248 : certificate1248.NumericValid := by decide +kernel
theorem cellsSound1248 : ∀ c∈certificate1248.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4314,MergedCutCells.Batch359.certificate4315,MergedCutCells.Batch359.certificate4316], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4314,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4315,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4316,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1248 : ∀ c∈certificate1248.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4314,MergedCutCells.Batch359.certificate4315,MergedCutCells.Batch359.certificate4316], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4314,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4315,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4316,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1248 : ∀ c∈certificate1248.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4314,MergedCutCells.Batch359.certificate4315,MergedCutCells.Batch359.certificate4316], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid417,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid418,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid419,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1248 : ∀ c∈certificate1248.cells, c.population=certificate1248.population := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4314,MergedCutCells.Batch359.certificate4315,MergedCutCells.Batch359.certificate4316], c.population=PopulationCertificates.Batch041.certificate832
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1248 {x : ℝ} (hx : certificate1248.interval.Contains x) : ∃ c∈certificate1248.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1248 numericValid1248 hx

def certificate1249 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate833,PopulationCertificates.Batch041.certificate833,[MergedCutCells.Batch359.certificate4317,MergedCutCells.Batch359.certificate4318],(138999654602583193/250000000000000000),(some (256566617/200000000)),(1/2),(65875181490830689/250000000000000000),(some (421917287147083/1000000000000000000)),(some (9430189596691/250000000000000000))⟩
theorem numericValid1249 : certificate1249.NumericValid := by decide +kernel
theorem cellsSound1249 : ∀ c∈certificate1249.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4317,MergedCutCells.Batch359.certificate4318], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4317,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4318,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1249 : ∀ c∈certificate1249.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4317,MergedCutCells.Batch359.certificate4318], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4317,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4318,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1249 : ∀ c∈certificate1249.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4317,MergedCutCells.Batch359.certificate4318], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid420,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid420,List.forall_mem_nil _⟩⟩
theorem populationMatches1249 : ∀ c∈certificate1249.cells, c.population=certificate1249.population := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4317,MergedCutCells.Batch359.certificate4318], c.population=PopulationCertificates.Batch041.certificate833
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1249 {x : ℝ} (hx : certificate1249.interval.Contains x) : ∃ c∈certificate1249.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1249 numericValid1249 hx

def certificate1250 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate833,PopulationCertificates.Batch041.certificate833,[MergedCutCells.Batch359.certificate4319,MergedCutCells.Batch360.certificate4320,MergedCutCells.Batch360.certificate4321],(256566617/200000000),none,(1/2),(64699425982000971/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1250 : certificate1250.NumericValid := by decide +kernel
theorem cellsSound1250 : ∀ c∈certificate1250.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4319,MergedCutCells.Batch360.certificate4320,MergedCutCells.Batch360.certificate4321], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.sound4319,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4320,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4321,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1250 : ∀ c∈certificate1250.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4319,MergedCutCells.Batch360.certificate4320,MergedCutCells.Batch360.certificate4321], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch359.numericValid4319,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4320,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4321,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1250 : ∀ c∈certificate1250.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4319,MergedCutCells.Batch360.certificate4320,MergedCutCells.Batch360.certificate4321], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1250 : ∀ c∈certificate1250.cells, c.population=certificate1250.population := by
  change ∀ c∈[MergedCutCells.Batch359.certificate4319,MergedCutCells.Batch360.certificate4320,MergedCutCells.Batch360.certificate4321], c.population=PopulationCertificates.Batch041.certificate833
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1250 {x : ℝ} (hx : certificate1250.interval.Contains x) : ∃ c∈certificate1250.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1250 numericValid1250 hx

def certificate1251 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate834,PopulationCertificates.Batch041.certificate834,[MergedCutCells.Batch360.certificate4322,MergedCutCells.Batch360.certificate4323],(15055199854349967157/1000000000000000000),none,(1/2),(74723760560611343/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1251 : certificate1251.NumericValid := by decide +kernel
theorem cellsSound1251 : ∀ c∈certificate1251.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4322,MergedCutCells.Batch360.certificate4323], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4323,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1251 : ∀ c∈certificate1251.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4322,MergedCutCells.Batch360.certificate4323], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4323,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1251 : ∀ c∈certificate1251.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4322,MergedCutCells.Batch360.certificate4323], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1251 : ∀ c∈certificate1251.cells, c.population=certificate1251.population := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4322,MergedCutCells.Batch360.certificate4323], c.population=PopulationCertificates.Batch041.certificate834
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1251 {x : ℝ} (hx : certificate1251.interval.Contains x) : ∃ c∈certificate1251.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1251 numericValid1251 hx

def certificate1252 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate835,PopulationCertificates.Batch041.certificate835,[MergedCutCells.Batch360.certificate4324,MergedCutCells.Batch360.certificate4325,MergedCutCells.Batch360.certificate4326],(34804979102042487/50000000000000000),none,(1/40),(215367022813617973/1000000000000000000),none,none⟩
theorem numericValid1252 : certificate1252.NumericValid := by decide +kernel
theorem cellsSound1252 : ∀ c∈certificate1252.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4324,MergedCutCells.Batch360.certificate4325,MergedCutCells.Batch360.certificate4326], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4324,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4325,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4326,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1252 : ∀ c∈certificate1252.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4324,MergedCutCells.Batch360.certificate4325,MergedCutCells.Batch360.certificate4326], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4324,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4325,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4326,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1252 : ∀ c∈certificate1252.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4324,MergedCutCells.Batch360.certificate4325,MergedCutCells.Batch360.certificate4326], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid421,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid422,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid423,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1252 : ∀ c∈certificate1252.cells, c.population=certificate1252.population := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4324,MergedCutCells.Batch360.certificate4325,MergedCutCells.Batch360.certificate4326], c.population=PopulationCertificates.Batch041.certificate835
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1252 {x : ℝ} (hx : certificate1252.interval.Contains x) : ∃ c∈certificate1252.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1252 numericValid1252 hx

def certificate1253 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate836,PopulationCertificates.Batch041.certificate836,[MergedCutCells.Batch360.certificate4327,MergedCutCells.Batch360.certificate4328],(560150658558941171/1000000000000000000),(some (648171963/500000000)),(1/2),(291784888571140469/1000000000000000000),(some (116994055946739/200000000000000000)),(some (54034530924789/1000000000000000000))⟩
theorem numericValid1253 : certificate1253.NumericValid := by decide +kernel
theorem cellsSound1253 : ∀ c∈certificate1253.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4327,MergedCutCells.Batch360.certificate4328], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4327,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4328,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1253 : ∀ c∈certificate1253.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4327,MergedCutCells.Batch360.certificate4328], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4327,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4328,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1253 : ∀ c∈certificate1253.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4327,MergedCutCells.Batch360.certificate4328], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid424,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid424,List.forall_mem_nil _⟩⟩
theorem populationMatches1253 : ∀ c∈certificate1253.cells, c.population=certificate1253.population := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4327,MergedCutCells.Batch360.certificate4328], c.population=PopulationCertificates.Batch041.certificate836
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1253 {x : ℝ} (hx : certificate1253.interval.Contains x) : ∃ c∈certificate1253.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1253 numericValid1253 hx

def certificate1254 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate836,PopulationCertificates.Batch041.certificate836,[MergedCutCells.Batch360.certificate4329,MergedCutCells.Batch360.certificate4330,MergedCutCells.Batch360.certificate4331],(648171963/500000000),none,(1/2),(34392647024070967/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1254 : certificate1254.NumericValid := by decide +kernel
theorem cellsSound1254 : ∀ c∈certificate1254.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4329,MergedCutCells.Batch360.certificate4330,MergedCutCells.Batch360.certificate4331], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4329,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.sound4331,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1254 : ∀ c∈certificate1254.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4329,MergedCutCells.Batch360.certificate4330,MergedCutCells.Batch360.certificate4331], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4329,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch360.numericValid4331,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1254 : ∀ c∈certificate1254.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4329,MergedCutCells.Batch360.certificate4330,MergedCutCells.Batch360.certificate4331], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1254 : ∀ c∈certificate1254.cells, c.population=certificate1254.population := by
  change ∀ c∈[MergedCutCells.Batch360.certificate4329,MergedCutCells.Batch360.certificate4330,MergedCutCells.Batch360.certificate4331], c.population=PopulationCertificates.Batch041.certificate836
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1254 {x : ℝ} (hx : certificate1254.interval.Contains x) : ∃ c∈certificate1254.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1254 numericValid1254 hx

def certificate1255 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate837,PopulationCertificates.Batch041.certificate837,[MergedCutCells.Batch361.certificate4332,MergedCutCells.Batch361.certificate4333],(15215789724397044897/1000000000000000000),none,(1/2),(3811237957999703781/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1255 : certificate1255.NumericValid := by decide +kernel
theorem cellsSound1255 : ∀ c∈certificate1255.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4332,MergedCutCells.Batch361.certificate4333], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4332,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4333,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1255 : ∀ c∈certificate1255.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4332,MergedCutCells.Batch361.certificate4333], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4332,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4333,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1255 : ∀ c∈certificate1255.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4332,MergedCutCells.Batch361.certificate4333], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1255 : ∀ c∈certificate1255.cells, c.population=certificate1255.population := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4332,MergedCutCells.Batch361.certificate4333], c.population=PopulationCertificates.Batch041.certificate837
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1255 {x : ℝ} (hx : certificate1255.interval.Contains x) : ∃ c∈certificate1255.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1255 numericValid1255 hx

def certificate1256 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate838,PopulationCertificates.Batch041.certificate838,[MergedCutCells.Batch361.certificate4334,MergedCutCells.Batch361.certificate4335,MergedCutCells.Batch361.certificate4336],(698218145898700593/1000000000000000000),none,(1/40),(111559978735449181/500000000000000000),none,none⟩
theorem numericValid1256 : certificate1256.NumericValid := by decide +kernel
theorem cellsSound1256 : ∀ c∈certificate1256.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4334,MergedCutCells.Batch361.certificate4335,MergedCutCells.Batch361.certificate4336], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4336,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1256 : ∀ c∈certificate1256.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4334,MergedCutCells.Batch361.certificate4335,MergedCutCells.Batch361.certificate4336], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4336,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1256 : ∀ c∈certificate1256.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4334,MergedCutCells.Batch361.certificate4335,MergedCutCells.Batch361.certificate4336], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid425,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid426,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid427,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1256 : ∀ c∈certificate1256.cells, c.population=certificate1256.population := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4334,MergedCutCells.Batch361.certificate4335,MergedCutCells.Batch361.certificate4336], c.population=PopulationCertificates.Batch041.certificate838
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1256 {x : ℝ} (hx : certificate1256.interval.Contains x) : ∃ c∈certificate1256.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1256 numericValid1256 hx

def certificate1257 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate839,PopulationCertificates.Batch041.certificate839,[MergedCutCells.Batch361.certificate4337,MergedCutCells.Batch361.certificate4338],(282131575882422583/500000000000000000),(some (31810681/25000000)),(1/2),(73348575424402913/250000000000000000),(some (97629692004477/125000000000000000)),(some (18583953996691/250000000000000000))⟩
theorem numericValid1257 : certificate1257.NumericValid := by decide +kernel
theorem cellsSound1257 : ∀ c∈certificate1257.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4337,MergedCutCells.Batch361.certificate4338], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4337,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4338,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1257 : ∀ c∈certificate1257.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4337,MergedCutCells.Batch361.certificate4338], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4337,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4338,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1257 : ∀ c∈certificate1257.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4337,MergedCutCells.Batch361.certificate4338], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid428,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid428,List.forall_mem_nil _⟩⟩
theorem populationMatches1257 : ∀ c∈certificate1257.cells, c.population=certificate1257.population := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4337,MergedCutCells.Batch361.certificate4338], c.population=PopulationCertificates.Batch041.certificate839
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1257 {x : ℝ} (hx : certificate1257.interval.Contains x) : ∃ c∈certificate1257.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1257 numericValid1257 hx

def certificate1258 : RatCutGroup := ⟨GeometryCertificates.Batch041.certificate839,PopulationCertificates.Batch041.certificate839,[MergedCutCells.Batch361.certificate4339,MergedCutCells.Batch361.certificate4340,MergedCutCells.Batch361.certificate4341],(31810681/25000000),none,(1/2),(293410273849277/1000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1258 : certificate1258.NumericValid := by decide +kernel
theorem cellsSound1258 : ∀ c∈certificate1258.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4339,MergedCutCells.Batch361.certificate4340,MergedCutCells.Batch361.certificate4341], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4339,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4341,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1258 : ∀ c∈certificate1258.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4339,MergedCutCells.Batch361.certificate4340,MergedCutCells.Batch361.certificate4341], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4339,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4341,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1258 : ∀ c∈certificate1258.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4339,MergedCutCells.Batch361.certificate4340,MergedCutCells.Batch361.certificate4341], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1258 : ∀ c∈certificate1258.cells, c.population=certificate1258.population := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4339,MergedCutCells.Batch361.certificate4340,MergedCutCells.Batch361.certificate4341], c.population=PopulationCertificates.Batch041.certificate839
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1258 {x : ℝ} (hx : certificate1258.interval.Contains x) : ∃ c∈certificate1258.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1258 numericValid1258 hx

def certificate1259 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate840,PopulationCertificates.Batch042.certificate840,[MergedCutCells.Batch361.certificate4342,MergedCutCells.Batch361.certificate4343],(384483422764000587/25000000000000000),none,(1/2),(776512684499843781/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1259 : certificate1259.NumericValid := by decide +kernel
theorem cellsSound1259 : ∀ c∈certificate1259.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4342,MergedCutCells.Batch361.certificate4343], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4342,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.sound4343,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1259 : ∀ c∈certificate1259.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4342,MergedCutCells.Batch361.certificate4343], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4342,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch361.numericValid4343,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1259 : ∀ c∈certificate1259.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4342,MergedCutCells.Batch361.certificate4343], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1259 : ∀ c∈certificate1259.cells, c.population=certificate1259.population := by
  change ∀ c∈[MergedCutCells.Batch361.certificate4342,MergedCutCells.Batch361.certificate4343], c.population=PopulationCertificates.Batch042.certificate840
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1259 {x : ℝ} (hx : certificate1259.interval.Contains x) : ∃ c∈certificate1259.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1259 numericValid1259 hx

end Cycle12.MergedCutGroups.Batch104
