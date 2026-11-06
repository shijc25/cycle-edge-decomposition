import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch037
import Cycle12.MergedCutCells.Batch332
import Cycle12.MergedCutCells.Batch333
import Cycle12.MergedCutCells.Batch334
import Cycle12.MergedCutCells.Batch335
import Cycle12.PopulationCertificates.Batch037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch094

def certificate1128 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate752,PopulationCertificates.Batch037.certificate752,[MergedCutCells.Batch332.certificate3991,MergedCutCells.Batch332.certificate3992],(588648509928633627/1000000000000000000),(some (1118177893/1000000000)),(1/2),(98392650812666597/1000000000000000000),(some (4784077462461407/62500000000000000)),(some (14681257380391671/1000000000000000000))⟩
theorem numericValid1128 : certificate1128.NumericValid := by decide +kernel
theorem cellsSound1128 : ∀ c∈certificate1128.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3991,MergedCutCells.Batch332.certificate3992], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3991,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3992,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1128 : ∀ c∈certificate1128.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3991,MergedCutCells.Batch332.certificate3992], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3991,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3992,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1128 : ∀ c∈certificate1128.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3991,MergedCutCells.Batch332.certificate3992], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid377,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid377,List.forall_mem_nil _⟩⟩
theorem populationMatches1128 : ∀ c∈certificate1128.cells, c.population=certificate1128.population := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3991,MergedCutCells.Batch332.certificate3992], c.population=PopulationCertificates.Batch037.certificate752
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1128 {x : ℝ} (hx : certificate1128.interval.Contains x) : ∃ c∈certificate1128.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1128 numericValid1128 hx

def certificate1129 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate752,PopulationCertificates.Batch037.certificate752,[MergedCutCells.Batch332.certificate3993,MergedCutCells.Batch332.certificate3994,MergedCutCells.Batch332.certificate3995,MergedCutCells.Batch333.certificate3996],(1118177893/1000000000),none,(1/2),(18458531695441821/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1129 : certificate1129.NumericValid := by decide +kernel
theorem cellsSound1129 : ∀ c∈certificate1129.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3993,MergedCutCells.Batch332.certificate3994,MergedCutCells.Batch332.certificate3995,MergedCutCells.Batch333.certificate3996], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3993,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3994,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3995,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound3996,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1129 : ∀ c∈certificate1129.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3993,MergedCutCells.Batch332.certificate3994,MergedCutCells.Batch332.certificate3995,MergedCutCells.Batch333.certificate3996], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3993,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3994,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3995,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid3996,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1129 : ∀ c∈certificate1129.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3993,MergedCutCells.Batch332.certificate3994,MergedCutCells.Batch332.certificate3995,MergedCutCells.Batch333.certificate3996], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1129 : ∀ c∈certificate1129.cells, c.population=certificate1129.population := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3993,MergedCutCells.Batch332.certificate3994,MergedCutCells.Batch332.certificate3995,MergedCutCells.Batch333.certificate3996], c.population=PopulationCertificates.Batch037.certificate752
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1129 {x : ℝ} (hx : certificate1129.interval.Contains x) : ∃ c∈certificate1129.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1129 numericValid1129 hx

def certificate1130 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate753,PopulationCertificates.Batch037.certificate753,[MergedCutCells.Batch333.certificate3997,MergedCutCells.Batch333.certificate3998],(6016102838994017583/250000000000000000),none,(1/2),(7252998233855357873/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1130 : certificate1130.NumericValid := by decide +kernel
theorem cellsSound1130 : ∀ c∈certificate1130.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch333.certificate3997,MergedCutCells.Batch333.certificate3998], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound3997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound3998,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1130 : ∀ c∈certificate1130.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate3997,MergedCutCells.Batch333.certificate3998], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid3997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid3998,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1130 : ∀ c∈certificate1130.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate3997,MergedCutCells.Batch333.certificate3998], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1130 : ∀ c∈certificate1130.cells, c.population=certificate1130.population := by
  change ∀ c∈[MergedCutCells.Batch333.certificate3997,MergedCutCells.Batch333.certificate3998], c.population=PopulationCertificates.Batch037.certificate753
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1130 {x : ℝ} (hx : certificate1130.interval.Contains x) : ∃ c∈certificate1130.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1130 numericValid1130 hx

def certificate1131 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate754,PopulationCertificates.Batch037.certificate754,[MergedCutCells.Batch333.certificate3999,MergedCutCells.Batch333.certificate4000],(118902240102913679/200000000000000000),(some (1127783993/1000000000)),(1/2),(117250058293989573/1000000000000000000),(some (79808801790651587/1000000000000000000)),(some (15462039086666689/1000000000000000000))⟩
theorem numericValid1131 : certificate1131.NumericValid := by decide +kernel
theorem cellsSound1131 : ∀ c∈certificate1131.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch333.certificate3999,MergedCutCells.Batch333.certificate4000], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound3999,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound4000,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1131 : ∀ c∈certificate1131.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate3999,MergedCutCells.Batch333.certificate4000], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid3999,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid4000,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1131 : ∀ c∈certificate1131.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate3999,MergedCutCells.Batch333.certificate4000], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid378,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid378,List.forall_mem_nil _⟩⟩
theorem populationMatches1131 : ∀ c∈certificate1131.cells, c.population=certificate1131.population := by
  change ∀ c∈[MergedCutCells.Batch333.certificate3999,MergedCutCells.Batch333.certificate4000], c.population=PopulationCertificates.Batch037.certificate754
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1131 {x : ℝ} (hx : certificate1131.interval.Contains x) : ∃ c∈certificate1131.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1131 numericValid1131 hx

def certificate1132 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate754,PopulationCertificates.Batch037.certificate754,[MergedCutCells.Batch333.certificate4001,MergedCutCells.Batch333.certificate4002,MergedCutCells.Batch333.certificate4003],(1127783993/1000000000),none,(1/2),(6933296842987571/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1132 : certificate1132.NumericValid := by decide +kernel
theorem cellsSound1132 : ∀ c∈certificate1132.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4001,MergedCutCells.Batch333.certificate4002,MergedCutCells.Batch333.certificate4003], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound4001,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound4002,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound4003,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1132 : ∀ c∈certificate1132.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4001,MergedCutCells.Batch333.certificate4002,MergedCutCells.Batch333.certificate4003], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid4001,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid4002,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid4003,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1132 : ∀ c∈certificate1132.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4001,MergedCutCells.Batch333.certificate4002,MergedCutCells.Batch333.certificate4003], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1132 : ∀ c∈certificate1132.cells, c.population=certificate1132.population := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4001,MergedCutCells.Batch333.certificate4002,MergedCutCells.Batch333.certificate4003], c.population=PopulationCertificates.Batch037.certificate754
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1132 {x : ℝ} (hx : certificate1132.interval.Contains x) : ∃ c∈certificate1132.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1132 numericValid1132 hx

def certificate1133 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate755,PopulationCertificates.Batch037.certificate755,[MergedCutCells.Batch333.certificate4004,MergedCutCells.Batch333.certificate4005],(12131603791899468429/500000000000000000),none,(1/2),(1848841964470984481/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1133 : certificate1133.NumericValid := by decide +kernel
theorem cellsSound1133 : ∀ c∈certificate1133.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4004,MergedCutCells.Batch333.certificate4005], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound4004,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound4005,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1133 : ∀ c∈certificate1133.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4004,MergedCutCells.Batch333.certificate4005], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid4004,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid4005,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1133 : ∀ c∈certificate1133.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4004,MergedCutCells.Batch333.certificate4005], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1133 : ∀ c∈certificate1133.cells, c.population=certificate1133.population := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4004,MergedCutCells.Batch333.certificate4005], c.population=PopulationCertificates.Batch037.certificate755
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1133 {x : ℝ} (hx : certificate1133.interval.Contains x) : ∃ c∈certificate1133.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1133 numericValid1133 hx

def certificate1134 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate756,PopulationCertificates.Batch037.certificate756,[MergedCutCells.Batch333.certificate4006,MergedCutCells.Batch333.certificate4007],(600571302781162087/1000000000000000000),(some (277521149/250000000)),(1/2),(138038177980149129/1000000000000000000),(some (41334987793089941/500000000000000000)),(some (3230917682053887/200000000000000000))⟩
theorem numericValid1134 : certificate1134.NumericValid := by decide +kernel
theorem cellsSound1134 : ∀ c∈certificate1134.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4006,MergedCutCells.Batch333.certificate4007], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound4006,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.sound4007,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1134 : ∀ c∈certificate1134.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4006,MergedCutCells.Batch333.certificate4007], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid4006,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch333.numericValid4007,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1134 : ∀ c∈certificate1134.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4006,MergedCutCells.Batch333.certificate4007], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid379,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid379,List.forall_mem_nil _⟩⟩
theorem populationMatches1134 : ∀ c∈certificate1134.cells, c.population=certificate1134.population := by
  change ∀ c∈[MergedCutCells.Batch333.certificate4006,MergedCutCells.Batch333.certificate4007], c.population=PopulationCertificates.Batch037.certificate756
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1134 {x : ℝ} (hx : certificate1134.interval.Contains x) : ∃ c∈certificate1134.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1134 numericValid1134 hx

def certificate1135 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate756,PopulationCertificates.Batch037.certificate756,[MergedCutCells.Batch334.certificate4008,MergedCutCells.Batch334.certificate4009,MergedCutCells.Batch334.certificate4010,MergedCutCells.Batch334.certificate4011],(277521149/250000000),none,(1/2),(32524321499109797/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1135 : certificate1135.NumericValid := by decide +kernel
theorem cellsSound1135 : ∀ c∈certificate1135.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4008,MergedCutCells.Batch334.certificate4009,MergedCutCells.Batch334.certificate4010,MergedCutCells.Batch334.certificate4011], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4008,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4009,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4010,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4011,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1135 : ∀ c∈certificate1135.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4008,MergedCutCells.Batch334.certificate4009,MergedCutCells.Batch334.certificate4010,MergedCutCells.Batch334.certificate4011], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4008,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4009,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4010,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4011,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1135 : ∀ c∈certificate1135.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4008,MergedCutCells.Batch334.certificate4009,MergedCutCells.Batch334.certificate4010,MergedCutCells.Batch334.certificate4011], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1135 : ∀ c∈certificate1135.cells, c.population=certificate1135.population := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4008,MergedCutCells.Batch334.certificate4009,MergedCutCells.Batch334.certificate4010,MergedCutCells.Batch334.certificate4011], c.population=PopulationCertificates.Batch037.certificate756
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1135 {x : ℝ} (hx : certificate1135.interval.Contains x) : ∃ c∈certificate1135.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1135 numericValid1135 hx

def certificate1136 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate757,PopulationCertificates.Batch037.certificate757,[MergedCutCells.Batch334.certificate4012,MergedCutCells.Batch334.certificate4013],(12234337433095010959/500000000000000000),none,(1/2),(1885372163474940011/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1136 : certificate1136.NumericValid := by decide +kernel
theorem cellsSound1136 : ∀ c∈certificate1136.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4012,MergedCutCells.Batch334.certificate4013], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4012,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4013,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1136 : ∀ c∈certificate1136.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4012,MergedCutCells.Batch334.certificate4013], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4012,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4013,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1136 : ∀ c∈certificate1136.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4012,MergedCutCells.Batch334.certificate4013], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1136 : ∀ c∈certificate1136.cells, c.population=certificate1136.population := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4012,MergedCutCells.Batch334.certificate4013], c.population=PopulationCertificates.Batch037.certificate757
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1136 {x : ℝ} (hx : certificate1136.interval.Contains x) : ∃ c∈certificate1136.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1136 numericValid1136 hx

def certificate1137 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate758,PopulationCertificates.Batch037.certificate758,[MergedCutCells.Batch334.certificate4014,MergedCutCells.Batch334.certificate4015],(603657816866687331/1000000000000000000),(some (1118663443/1000000000)),(1/2),(143950102410565013/1000000000000000000),(some (86055207127320249/1000000000000000000)),(some (1061472989336639/62500000000000000))⟩
theorem numericValid1137 : certificate1137.NumericValid := by decide +kernel
theorem cellsSound1137 : ∀ c∈certificate1137.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4014,MergedCutCells.Batch334.certificate4015], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4014,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4015,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1137 : ∀ c∈certificate1137.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4014,MergedCutCells.Batch334.certificate4015], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4014,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4015,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1137 : ∀ c∈certificate1137.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4014,MergedCutCells.Batch334.certificate4015], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid380,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid380,List.forall_mem_nil _⟩⟩
theorem populationMatches1137 : ∀ c∈certificate1137.cells, c.population=certificate1137.population := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4014,MergedCutCells.Batch334.certificate4015], c.population=PopulationCertificates.Batch037.certificate758
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1137 {x : ℝ} (hx : certificate1137.interval.Contains x) : ∃ c∈certificate1137.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1137 numericValid1137 hx

def certificate1138 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate758,PopulationCertificates.Batch037.certificate758,[MergedCutCells.Batch334.certificate4016,MergedCutCells.Batch334.certificate4017,MergedCutCells.Batch334.certificate4018,MergedCutCells.Batch334.certificate4019],(1118663443/1000000000),none,(1/2),(68466886878606943/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1138 : certificate1138.NumericValid := by decide +kernel
theorem cellsSound1138 : ∀ c∈certificate1138.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4016,MergedCutCells.Batch334.certificate4017,MergedCutCells.Batch334.certificate4018,MergedCutCells.Batch334.certificate4019], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4016,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4017,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4018,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.sound4019,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1138 : ∀ c∈certificate1138.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4016,MergedCutCells.Batch334.certificate4017,MergedCutCells.Batch334.certificate4018,MergedCutCells.Batch334.certificate4019], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4016,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4017,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4018,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch334.numericValid4019,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1138 : ∀ c∈certificate1138.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4016,MergedCutCells.Batch334.certificate4017,MergedCutCells.Batch334.certificate4018,MergedCutCells.Batch334.certificate4019], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1138 : ∀ c∈certificate1138.cells, c.population=certificate1138.population := by
  change ∀ c∈[MergedCutCells.Batch334.certificate4016,MergedCutCells.Batch334.certificate4017,MergedCutCells.Batch334.certificate4018,MergedCutCells.Batch334.certificate4019], c.population=PopulationCertificates.Batch037.certificate758
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1138 {x : ℝ} (hx : certificate1138.interval.Contains x) : ∃ c∈certificate1138.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1138 numericValid1138 hx

def certificate1139 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate759,PopulationCertificates.Batch037.certificate759,[MergedCutCells.Batch335.certificate4020,MergedCutCells.Batch335.certificate4021],(12310945329504740971/500000000000000000),none,(1/2),(7681035065639197853/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1139 : certificate1139.NumericValid := by decide +kernel
theorem cellsSound1139 : ∀ c∈certificate1139.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4020,MergedCutCells.Batch335.certificate4021], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4020,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.sound4021,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1139 : ∀ c∈certificate1139.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4020,MergedCutCells.Batch335.certificate4021], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4020,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch335.numericValid4021,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1139 : ∀ c∈certificate1139.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4020,MergedCutCells.Batch335.certificate4021], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1139 : ∀ c∈certificate1139.cells, c.population=certificate1139.population := by
  change ∀ c∈[MergedCutCells.Batch335.certificate4020,MergedCutCells.Batch335.certificate4021], c.population=PopulationCertificates.Batch037.certificate759
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1139 {x : ℝ} (hx : certificate1139.interval.Contains x) : ∃ c∈certificate1139.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1139 numericValid1139 hx

end Cycle12.MergedCutGroups.Batch094
