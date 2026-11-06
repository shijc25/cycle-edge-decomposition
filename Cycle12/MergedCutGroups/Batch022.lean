import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch008
import Cycle12.GeometryCertificates.Batch009
import Cycle12.MergedCutCells.Batch085
import Cycle12.MergedCutCells.Batch086
import Cycle12.MergedCutCells.Batch087
import Cycle12.MergedCutCells.Batch088
import Cycle12.MergedCutCells.Batch089
import Cycle12.PopulationCertificates.Batch008
import Cycle12.PopulationCertificates.Batch009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch022

def certificate264 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate176,PopulationCertificates.Batch008.certificate176,[MergedCutCells.Batch085.certificate1022,MergedCutCells.Batch085.certificate1023,MergedCutCells.Batch085.certificate1024,MergedCutCells.Batch085.certificate1025,MergedCutCells.Batch085.certificate1026,MergedCutCells.Batch085.certificate1027,MergedCutCells.Batch085.certificate1028],(850165604452536769/1000000000000000000),(some 64),(1/2),(422656436955482721/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1423375808236709251/1000000000000000000))⟩
theorem numericValid264 : certificate264.NumericValid := by decide +kernel
theorem cellsSound264 : ∀ c∈certificate264.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1022,MergedCutCells.Batch085.certificate1023,MergedCutCells.Batch085.certificate1024,MergedCutCells.Batch085.certificate1025,MergedCutCells.Batch085.certificate1026,MergedCutCells.Batch085.certificate1027,MergedCutCells.Batch085.certificate1028], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1022,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1023,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1024,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1025,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1026,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1028,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric264 : ∀ c∈certificate264.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1022,MergedCutCells.Batch085.certificate1023,MergedCutCells.Batch085.certificate1024,MergedCutCells.Batch085.certificate1025,MergedCutCells.Batch085.certificate1026,MergedCutCells.Batch085.certificate1027,MergedCutCells.Batch085.certificate1028], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1022,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1023,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1024,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1025,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1026,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1028,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid264 : ∀ c∈certificate264.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1022,MergedCutCells.Batch085.certificate1023,MergedCutCells.Batch085.certificate1024,MergedCutCells.Batch085.certificate1025,MergedCutCells.Batch085.certificate1026,MergedCutCells.Batch085.certificate1027,MergedCutCells.Batch085.certificate1028], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid89,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid89,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid89,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid89,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid89,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid89,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid89,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches264 : ∀ c∈certificate264.cells, c.population=certificate264.population := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1022,MergedCutCells.Batch085.certificate1023,MergedCutCells.Batch085.certificate1024,MergedCutCells.Batch085.certificate1025,MergedCutCells.Batch085.certificate1026,MergedCutCells.Batch085.certificate1027,MergedCutCells.Batch085.certificate1028], c.population=PopulationCertificates.Batch008.certificate176
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers264 {x : ℝ} (hx : certificate264.interval.Contains x) : ∃ c∈certificate264.cells, c.region.interval.Contains x := rat_cut_group_covers certificate264 numericValid264 hx

def certificate265 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate176,PopulationCertificates.Batch008.certificate176,[MergedCutCells.Batch085.certificate1029],64,none,(1/2),(509082404305918883/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid265 : certificate265.NumericValid := by decide +kernel
theorem cellsSound265 : ∀ c∈certificate265.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1029], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1029,List.forall_mem_nil _⟩
theorem cellsNumeric265 : ∀ c∈certificate265.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1029], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1029,List.forall_mem_nil _⟩
theorem cellsEntropyValid265 : ∀ c∈certificate265.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1029], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches265 : ∀ c∈certificate265.cells, c.population=certificate265.population := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1029], c.population=PopulationCertificates.Batch008.certificate176
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers265 {x : ℝ} (hx : certificate265.interval.Contains x) : ∃ c∈certificate265.cells, c.region.interval.Contains x := rat_cut_group_covers certificate265 numericValid265 hx

def certificate266 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate177,PopulationCertificates.Batch008.certificate177,[MergedCutCells.Batch085.certificate1030,MergedCutCells.Batch085.certificate1031,MergedCutCells.Batch086.certificate1032],(3700659408711074843/1000000000000000000),none,(1/2),(145822048624258349/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid266 : certificate266.NumericValid := by decide +kernel
theorem cellsSound266 : ∀ c∈certificate266.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1030,MergedCutCells.Batch085.certificate1031,MergedCutCells.Batch086.certificate1032], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1030,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1031,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1032,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric266 : ∀ c∈certificate266.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1030,MergedCutCells.Batch085.certificate1031,MergedCutCells.Batch086.certificate1032], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1030,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1031,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1032,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid266 : ∀ c∈certificate266.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1030,MergedCutCells.Batch085.certificate1031,MergedCutCells.Batch086.certificate1032], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches266 : ∀ c∈certificate266.cells, c.population=certificate266.population := by
  change ∀ c∈[MergedCutCells.Batch085.certificate1030,MergedCutCells.Batch085.certificate1031,MergedCutCells.Batch086.certificate1032], c.population=PopulationCertificates.Batch008.certificate177
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers266 {x : ℝ} (hx : certificate266.interval.Contains x) : ∃ c∈certificate266.cells, c.region.interval.Contains x := rat_cut_group_covers certificate266 numericValid266 hx

def certificate267 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate178,PopulationCertificates.Batch008.certificate178,[MergedCutCells.Batch086.certificate1033,MergedCutCells.Batch086.certificate1034,MergedCutCells.Batch086.certificate1035,MergedCutCells.Batch086.certificate1036,MergedCutCells.Batch086.certificate1037,MergedCutCells.Batch086.certificate1038,MergedCutCells.Batch086.certificate1039,MergedCutCells.Batch086.certificate1040],(843064961775703581/1000000000000000000),(some 64),(1/2),(108307022005577987/250000000000000000),(some (69314718055994531/100000000000000000)),(some (142459455467631511/100000000000000000))⟩
theorem numericValid267 : certificate267.NumericValid := by decide +kernel
theorem cellsSound267 : ∀ c∈certificate267.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1033,MergedCutCells.Batch086.certificate1034,MergedCutCells.Batch086.certificate1035,MergedCutCells.Batch086.certificate1036,MergedCutCells.Batch086.certificate1037,MergedCutCells.Batch086.certificate1038,MergedCutCells.Batch086.certificate1039,MergedCutCells.Batch086.certificate1040], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1033,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1034,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1035,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1036,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1038,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1040,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric267 : ∀ c∈certificate267.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1033,MergedCutCells.Batch086.certificate1034,MergedCutCells.Batch086.certificate1035,MergedCutCells.Batch086.certificate1036,MergedCutCells.Batch086.certificate1037,MergedCutCells.Batch086.certificate1038,MergedCutCells.Batch086.certificate1039,MergedCutCells.Batch086.certificate1040], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1033,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1034,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1035,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1036,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1038,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1040,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid267 : ∀ c∈certificate267.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1033,MergedCutCells.Batch086.certificate1034,MergedCutCells.Batch086.certificate1035,MergedCutCells.Batch086.certificate1036,MergedCutCells.Batch086.certificate1037,MergedCutCells.Batch086.certificate1038,MergedCutCells.Batch086.certificate1039,MergedCutCells.Batch086.certificate1040], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid90,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid90,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid90,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid90,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid90,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid90,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid90,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid90,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches267 : ∀ c∈certificate267.cells, c.population=certificate267.population := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1033,MergedCutCells.Batch086.certificate1034,MergedCutCells.Batch086.certificate1035,MergedCutCells.Batch086.certificate1036,MergedCutCells.Batch086.certificate1037,MergedCutCells.Batch086.certificate1038,MergedCutCells.Batch086.certificate1039,MergedCutCells.Batch086.certificate1040], c.population=PopulationCertificates.Batch008.certificate178
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers267 {x : ℝ} (hx : certificate267.interval.Contains x) : ∃ c∈certificate267.cells, c.region.interval.Contains x := rat_cut_group_covers certificate267 numericValid267 hx

def certificate268 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate178,PopulationCertificates.Batch008.certificate178,[MergedCutCells.Batch086.certificate1041],64,none,(1/2),(1045064454597233783/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid268 : certificate268.NumericValid := by decide +kernel
theorem cellsSound268 : ∀ c∈certificate268.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1041], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1041,List.forall_mem_nil _⟩
theorem cellsNumeric268 : ∀ c∈certificate268.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1041], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1041,List.forall_mem_nil _⟩
theorem cellsEntropyValid268 : ∀ c∈certificate268.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1041], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches268 : ∀ c∈certificate268.cells, c.population=certificate268.population := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1041], c.population=PopulationCertificates.Batch008.certificate178
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers268 {x : ℝ} (hx : certificate268.interval.Contains x) : ∃ c∈certificate268.cells, c.region.interval.Contains x := rat_cut_group_covers certificate268 numericValid268 hx

def certificate269 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate179,PopulationCertificates.Batch008.certificate179,[MergedCutCells.Batch086.certificate1042,MergedCutCells.Batch086.certificate1043,MergedCutCells.Batch087.certificate1044],(741143783834817013/200000000000000000),none,(1/2),(149099857198249417/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid269 : certificate269.NumericValid := by decide +kernel
theorem cellsSound269 : ∀ c∈certificate269.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1042,MergedCutCells.Batch086.certificate1043,MergedCutCells.Batch087.certificate1044], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1042,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.sound1043,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1044,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric269 : ∀ c∈certificate269.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1042,MergedCutCells.Batch086.certificate1043,MergedCutCells.Batch087.certificate1044], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1042,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch086.numericValid1043,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1044,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid269 : ∀ c∈certificate269.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1042,MergedCutCells.Batch086.certificate1043,MergedCutCells.Batch087.certificate1044], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches269 : ∀ c∈certificate269.cells, c.population=certificate269.population := by
  change ∀ c∈[MergedCutCells.Batch086.certificate1042,MergedCutCells.Batch086.certificate1043,MergedCutCells.Batch087.certificate1044], c.population=PopulationCertificates.Batch008.certificate179
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers269 {x : ℝ} (hx : certificate269.interval.Contains x) : ∃ c∈certificate269.cells, c.region.interval.Contains x := rat_cut_group_covers certificate269 numericValid269 hx

def certificate270 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate180,PopulationCertificates.Batch009.certificate180,[MergedCutCells.Batch087.certificate1045,MergedCutCells.Batch087.certificate1046,MergedCutCells.Batch087.certificate1047,MergedCutCells.Batch087.certificate1048,MergedCutCells.Batch087.certificate1049,MergedCutCells.Batch087.certificate1050,MergedCutCells.Batch087.certificate1051,MergedCutCells.Batch087.certificate1052],(168820309823964043/200000000000000000),(some 64),(1/2),(221230554890604183/500000000000000000),(some (69314718055994531/100000000000000000)),(some (178369137409597021/125000000000000000))⟩
theorem numericValid270 : certificate270.NumericValid := by decide +kernel
theorem cellsSound270 : ∀ c∈certificate270.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1045,MergedCutCells.Batch087.certificate1046,MergedCutCells.Batch087.certificate1047,MergedCutCells.Batch087.certificate1048,MergedCutCells.Batch087.certificate1049,MergedCutCells.Batch087.certificate1050,MergedCutCells.Batch087.certificate1051,MergedCutCells.Batch087.certificate1052], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1045,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1046,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1047,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1048,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1050,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1051,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1052,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric270 : ∀ c∈certificate270.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1045,MergedCutCells.Batch087.certificate1046,MergedCutCells.Batch087.certificate1047,MergedCutCells.Batch087.certificate1048,MergedCutCells.Batch087.certificate1049,MergedCutCells.Batch087.certificate1050,MergedCutCells.Batch087.certificate1051,MergedCutCells.Batch087.certificate1052], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1045,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1046,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1047,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1048,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1050,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1051,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1052,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid270 : ∀ c∈certificate270.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1045,MergedCutCells.Batch087.certificate1046,MergedCutCells.Batch087.certificate1047,MergedCutCells.Batch087.certificate1048,MergedCutCells.Batch087.certificate1049,MergedCutCells.Batch087.certificate1050,MergedCutCells.Batch087.certificate1051,MergedCutCells.Batch087.certificate1052], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid91,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid91,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid91,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid91,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid91,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid91,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid91,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid91,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches270 : ∀ c∈certificate270.cells, c.population=certificate270.population := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1045,MergedCutCells.Batch087.certificate1046,MergedCutCells.Batch087.certificate1047,MergedCutCells.Batch087.certificate1048,MergedCutCells.Batch087.certificate1049,MergedCutCells.Batch087.certificate1050,MergedCutCells.Batch087.certificate1051,MergedCutCells.Batch087.certificate1052], c.population=PopulationCertificates.Batch009.certificate180
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers270 {x : ℝ} (hx : certificate270.interval.Contains x) : ∃ c∈certificate270.cells, c.region.interval.Contains x := rat_cut_group_covers certificate270 numericValid270 hx

def certificate271 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate180,PopulationCertificates.Batch009.certificate180,[MergedCutCells.Batch087.certificate1053],64,none,(1/2),(1059968098317052969/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid271 : certificate271.NumericValid := by decide +kernel
theorem cellsSound271 : ∀ c∈certificate271.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1053], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1053,List.forall_mem_nil _⟩
theorem cellsNumeric271 : ∀ c∈certificate271.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1053], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1053,List.forall_mem_nil _⟩
theorem cellsEntropyValid271 : ∀ c∈certificate271.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1053], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches271 : ∀ c∈certificate271.cells, c.population=certificate271.population := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1053], c.population=PopulationCertificates.Batch009.certificate180
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers271 {x : ℝ} (hx : certificate271.interval.Contains x) : ∃ c∈certificate271.cells, c.region.interval.Contains x := rat_cut_group_covers certificate271 numericValid271 hx

def certificate272 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate181,PopulationCertificates.Batch009.certificate181,[MergedCutCells.Batch087.certificate1054,MergedCutCells.Batch087.certificate1055,MergedCutCells.Batch088.certificate1056,MergedCutCells.Batch088.certificate1057],(1856499538457767883/500000000000000000),none,(1/2),(764416713942283991/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid272 : certificate272.NumericValid := by decide +kernel
theorem cellsSound272 : ∀ c∈certificate272.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1054,MergedCutCells.Batch087.certificate1055,MergedCutCells.Batch088.certificate1056,MergedCutCells.Batch088.certificate1057], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1054,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.sound1055,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1056,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1057,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric272 : ∀ c∈certificate272.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1054,MergedCutCells.Batch087.certificate1055,MergedCutCells.Batch088.certificate1056,MergedCutCells.Batch088.certificate1057], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1054,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch087.numericValid1055,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1056,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1057,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid272 : ∀ c∈certificate272.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1054,MergedCutCells.Batch087.certificate1055,MergedCutCells.Batch088.certificate1056,MergedCutCells.Batch088.certificate1057], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches272 : ∀ c∈certificate272.cells, c.population=certificate272.population := by
  change ∀ c∈[MergedCutCells.Batch087.certificate1054,MergedCutCells.Batch087.certificate1055,MergedCutCells.Batch088.certificate1056,MergedCutCells.Batch088.certificate1057], c.population=PopulationCertificates.Batch009.certificate181
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers272 {x : ℝ} (hx : certificate272.interval.Contains x) : ∃ c∈certificate272.cells, c.region.interval.Contains x := rat_cut_group_covers certificate272 numericValid272 hx

def certificate273 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate182,PopulationCertificates.Batch009.certificate182,[MergedCutCells.Batch088.certificate1058,MergedCutCells.Batch088.certificate1059,MergedCutCells.Batch088.certificate1060,MergedCutCells.Batch088.certificate1061,MergedCutCells.Batch088.certificate1062,MergedCutCells.Batch088.certificate1063,MergedCutCells.Batch088.certificate1064,MergedCutCells.Batch088.certificate1065],(421344150488578603/500000000000000000),(some 64),(1/2),(447124340929754787/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (714013316650841077/500000000000000000))⟩
theorem numericValid273 : certificate273.NumericValid := by decide +kernel
theorem cellsSound273 : ∀ c∈certificate273.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1058,MergedCutCells.Batch088.certificate1059,MergedCutCells.Batch088.certificate1060,MergedCutCells.Batch088.certificate1061,MergedCutCells.Batch088.certificate1062,MergedCutCells.Batch088.certificate1063,MergedCutCells.Batch088.certificate1064,MergedCutCells.Batch088.certificate1065], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1058,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1059,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1060,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1061,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1062,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1063,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1064,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1065,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric273 : ∀ c∈certificate273.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1058,MergedCutCells.Batch088.certificate1059,MergedCutCells.Batch088.certificate1060,MergedCutCells.Batch088.certificate1061,MergedCutCells.Batch088.certificate1062,MergedCutCells.Batch088.certificate1063,MergedCutCells.Batch088.certificate1064,MergedCutCells.Batch088.certificate1065], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1058,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1059,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1060,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1061,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1062,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1063,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1064,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1065,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid273 : ∀ c∈certificate273.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1058,MergedCutCells.Batch088.certificate1059,MergedCutCells.Batch088.certificate1060,MergedCutCells.Batch088.certificate1061,MergedCutCells.Batch088.certificate1062,MergedCutCells.Batch088.certificate1063,MergedCutCells.Batch088.certificate1064,MergedCutCells.Batch088.certificate1065], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid92,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid92,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid92,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid92,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid92,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid92,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid92,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid92,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches273 : ∀ c∈certificate273.cells, c.population=certificate273.population := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1058,MergedCutCells.Batch088.certificate1059,MergedCutCells.Batch088.certificate1060,MergedCutCells.Batch088.certificate1061,MergedCutCells.Batch088.certificate1062,MergedCutCells.Batch088.certificate1063,MergedCutCells.Batch088.certificate1064,MergedCutCells.Batch088.certificate1065], c.population=PopulationCertificates.Batch009.certificate182
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers273 {x : ℝ} (hx : certificate273.interval.Contains x) : ∃ c∈certificate273.cells, c.region.interval.Contains x := rat_cut_group_covers certificate273 numericValid273 hx

def certificate274 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate182,PopulationCertificates.Batch009.certificate182,[MergedCutCells.Batch088.certificate1066],64,none,(1/2),(1084205692325498147/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid274 : certificate274.NumericValid := by decide +kernel
theorem cellsSound274 : ∀ c∈certificate274.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1066], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1066,List.forall_mem_nil _⟩
theorem cellsNumeric274 : ∀ c∈certificate274.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1066], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1066,List.forall_mem_nil _⟩
theorem cellsEntropyValid274 : ∀ c∈certificate274.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1066], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches274 : ∀ c∈certificate274.cells, c.population=certificate274.population := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1066], c.population=PopulationCertificates.Batch009.certificate182
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers274 {x : ℝ} (hx : certificate274.interval.Contains x) : ∃ c∈certificate274.cells, c.region.interval.Contains x := rat_cut_group_covers certificate274 numericValid274 hx

def certificate275 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate183,PopulationCertificates.Batch009.certificate183,[MergedCutCells.Batch088.certificate1067,MergedCutCells.Batch089.certificate1068,MergedCutCells.Batch089.certificate1069,MergedCutCells.Batch089.certificate1070],(929541625710708197/250000000000000000),none,(1/2),(390544655365579343/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid275 : certificate275.NumericValid := by decide +kernel
theorem cellsSound275 : ∀ c∈certificate275.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1067,MergedCutCells.Batch089.certificate1068,MergedCutCells.Batch089.certificate1069,MergedCutCells.Batch089.certificate1070], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.sound1067,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1069,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1070,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric275 : ∀ c∈certificate275.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1067,MergedCutCells.Batch089.certificate1068,MergedCutCells.Batch089.certificate1069,MergedCutCells.Batch089.certificate1070], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch088.numericValid1067,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1069,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1070,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid275 : ∀ c∈certificate275.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1067,MergedCutCells.Batch089.certificate1068,MergedCutCells.Batch089.certificate1069,MergedCutCells.Batch089.certificate1070], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches275 : ∀ c∈certificate275.cells, c.population=certificate275.population := by
  change ∀ c∈[MergedCutCells.Batch088.certificate1067,MergedCutCells.Batch089.certificate1068,MergedCutCells.Batch089.certificate1069,MergedCutCells.Batch089.certificate1070], c.population=PopulationCertificates.Batch009.certificate183
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers275 {x : ℝ} (hx : certificate275.interval.Contains x) : ∃ c∈certificate275.cells, c.region.interval.Contains x := rat_cut_group_covers certificate275 numericValid275 hx

end Cycle12.MergedCutGroups.Batch022
