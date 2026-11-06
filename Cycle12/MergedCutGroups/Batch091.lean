import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch036
import Cycle12.MergedCutCells.Batch325
import Cycle12.MergedCutCells.Batch326
import Cycle12.MergedCutCells.Batch327
import Cycle12.PopulationCertificates.Batch036

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch091

def certificate1092 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate728,PopulationCertificates.Batch036.certificate728,[MergedCutCells.Batch325.certificate3905,MergedCutCells.Batch325.certificate3906],(69875365035608587/125000000000000000),(some (1201763439/1000000000)),(1/2),(7769802247206019/100000000000000000),(some (21741319055990409/500000000000000000)),(some (7359941247071931/1000000000000000000))⟩
theorem numericValid1092 : certificate1092.NumericValid := by decide +kernel
theorem cellsSound1092 : ∀ c∈certificate1092.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3905,MergedCutCells.Batch325.certificate3906], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3905,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3906,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1092 : ∀ c∈certificate1092.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3905,MergedCutCells.Batch325.certificate3906], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3905,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3906,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1092 : ∀ c∈certificate1092.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3905,MergedCutCells.Batch325.certificate3906], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid365,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid365,List.forall_mem_nil _⟩⟩
theorem populationMatches1092 : ∀ c∈certificate1092.cells, c.population=certificate1092.population := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3905,MergedCutCells.Batch325.certificate3906], c.population=PopulationCertificates.Batch036.certificate728
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1092 {x : ℝ} (hx : certificate1092.interval.Contains x) : ∃ c∈certificate1092.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1092 numericValid1092 hx

def certificate1093 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate728,PopulationCertificates.Batch036.certificate728,[MergedCutCells.Batch325.certificate3907,MergedCutCells.Batch325.certificate3908,MergedCutCells.Batch325.certificate3909],(1201763439/1000000000),none,(1/2),(37502900882600599/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1093 : certificate1093.NumericValid := by decide +kernel
theorem cellsSound1093 : ∀ c∈certificate1093.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3907,MergedCutCells.Batch325.certificate3908,MergedCutCells.Batch325.certificate3909], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3908,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3909,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1093 : ∀ c∈certificate1093.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3907,MergedCutCells.Batch325.certificate3908,MergedCutCells.Batch325.certificate3909], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3908,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3909,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1093 : ∀ c∈certificate1093.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3907,MergedCutCells.Batch325.certificate3908,MergedCutCells.Batch325.certificate3909], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1093 : ∀ c∈certificate1093.cells, c.population=certificate1093.population := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3907,MergedCutCells.Batch325.certificate3908,MergedCutCells.Batch325.certificate3909], c.population=PopulationCertificates.Batch036.certificate728
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1093 {x : ℝ} (hx : certificate1093.interval.Contains x) : ∃ c∈certificate1093.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1093 numericValid1093 hx

def certificate1094 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate729,PopulationCertificates.Batch036.certificate729,[MergedCutCells.Batch325.certificate3910,MergedCutCells.Batch325.certificate3911],(2133169366800988407/100000000000000000),none,(1/2),(5820062986577606971/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1094 : certificate1094.NumericValid := by decide +kernel
theorem cellsSound1094 : ∀ c∈certificate1094.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3910,MergedCutCells.Batch325.certificate3911], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3910,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3911,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1094 : ∀ c∈certificate1094.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3910,MergedCutCells.Batch325.certificate3911], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3910,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3911,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1094 : ∀ c∈certificate1094.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3910,MergedCutCells.Batch325.certificate3911], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1094 : ∀ c∈certificate1094.cells, c.population=certificate1094.population := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3910,MergedCutCells.Batch325.certificate3911], c.population=PopulationCertificates.Batch036.certificate729
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1094 {x : ℝ} (hx : certificate1094.interval.Contains x) : ∃ c∈certificate1094.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1094 numericValid1094 hx

def certificate1095 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate730,PopulationCertificates.Batch036.certificate730,[MergedCutCells.Batch326.certificate3912,MergedCutCells.Batch326.certificate3913],(559433490908499097/1000000000000000000),(some (73326069/62500000)),(1/2),(71594864258571809/1000000000000000000),(some (22889414020271353/500000000000000000)),(some (783117422571211/100000000000000000))⟩
theorem numericValid1095 : certificate1095.NumericValid := by decide +kernel
theorem cellsSound1095 : ∀ c∈certificate1095.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3912,MergedCutCells.Batch326.certificate3913], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3913,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1095 : ∀ c∈certificate1095.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3912,MergedCutCells.Batch326.certificate3913], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3913,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1095 : ∀ c∈certificate1095.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3912,MergedCutCells.Batch326.certificate3913], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid366,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid366,List.forall_mem_nil _⟩⟩
theorem populationMatches1095 : ∀ c∈certificate1095.cells, c.population=certificate1095.population := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3912,MergedCutCells.Batch326.certificate3913], c.population=PopulationCertificates.Batch036.certificate730
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1095 {x : ℝ} (hx : certificate1095.interval.Contains x) : ∃ c∈certificate1095.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1095 numericValid1095 hx

def certificate1096 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate730,PopulationCertificates.Batch036.certificate730,[MergedCutCells.Batch326.certificate3914,MergedCutCells.Batch326.certificate3915,MergedCutCells.Batch326.certificate3916],(73326069/62500000),none,(1/2),(17172243646614213/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1096 : certificate1096.NumericValid := by decide +kernel
theorem cellsSound1096 : ∀ c∈certificate1096.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3914,MergedCutCells.Batch326.certificate3915,MergedCutCells.Batch326.certificate3916], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3915,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3916,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1096 : ∀ c∈certificate1096.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3914,MergedCutCells.Batch326.certificate3915,MergedCutCells.Batch326.certificate3916], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3915,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3916,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1096 : ∀ c∈certificate1096.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3914,MergedCutCells.Batch326.certificate3915,MergedCutCells.Batch326.certificate3916], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1096 : ∀ c∈certificate1096.cells, c.population=certificate1096.population := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3914,MergedCutCells.Batch326.certificate3915,MergedCutCells.Batch326.certificate3916], c.population=PopulationCertificates.Batch036.certificate730
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1096 {x : ℝ} (hx : certificate1096.interval.Contains x) : ∃ c∈certificate1096.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1096 numericValid1096 hx

def certificate1097 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate731,PopulationCertificates.Batch036.certificate731,[MergedCutCells.Batch326.certificate3917,MergedCutCells.Batch326.certificate3918],(5402923156193151391/250000000000000000),none,(1/2),(5926947016504376309/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1097 : certificate1097.NumericValid := by decide +kernel
theorem cellsSound1097 : ∀ c∈certificate1097.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3917,MergedCutCells.Batch326.certificate3918], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3917,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3918,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1097 : ∀ c∈certificate1097.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3917,MergedCutCells.Batch326.certificate3918], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3917,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3918,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1097 : ∀ c∈certificate1097.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3917,MergedCutCells.Batch326.certificate3918], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1097 : ∀ c∈certificate1097.cells, c.population=certificate1097.population := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3917,MergedCutCells.Batch326.certificate3918], c.population=PopulationCertificates.Batch036.certificate731
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1097 {x : ℝ} (hx : certificate1097.interval.Contains x) : ∃ c∈certificate1097.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1097 numericValid1097 hx

def certificate1098 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate732,PopulationCertificates.Batch036.certificate732,[MergedCutCells.Batch326.certificate3919,MergedCutCells.Batch326.certificate3920],(140697051348513939/250000000000000000),(some (589575201/500000000)),(1/2),(76617561186099771/1000000000000000000),(some (968448573099661/20000000000000000)),(some (8381101019245803/1000000000000000000))⟩
theorem numericValid1098 : certificate1098.NumericValid := by decide +kernel
theorem cellsSound1098 : ∀ c∈certificate1098.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3919,MergedCutCells.Batch326.certificate3920], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3919,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3920,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1098 : ∀ c∈certificate1098.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3919,MergedCutCells.Batch326.certificate3920], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3919,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3920,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1098 : ∀ c∈certificate1098.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3919,MergedCutCells.Batch326.certificate3920], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid367,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid367,List.forall_mem_nil _⟩⟩
theorem populationMatches1098 : ∀ c∈certificate1098.cells, c.population=certificate1098.population := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3919,MergedCutCells.Batch326.certificate3920], c.population=PopulationCertificates.Batch036.certificate732
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1098 {x : ℝ} (hx : certificate1098.interval.Contains x) : ∃ c∈certificate1098.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1098 numericValid1098 hx

def certificate1099 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate732,PopulationCertificates.Batch036.certificate732,[MergedCutCells.Batch326.certificate3921,MergedCutCells.Batch326.certificate3922,MergedCutCells.Batch326.certificate3923],(589575201/500000000),none,(1/2),(18369746657495817/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1099 : certificate1099.NumericValid := by decide +kernel
theorem cellsSound1099 : ∀ c∈certificate1099.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3921,MergedCutCells.Batch326.certificate3922,MergedCutCells.Batch326.certificate3923], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3921,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3922,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.sound3923,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1099 : ∀ c∈certificate1099.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3921,MergedCutCells.Batch326.certificate3922,MergedCutCells.Batch326.certificate3923], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3921,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3922,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch326.numericValid3923,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1099 : ∀ c∈certificate1099.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3921,MergedCutCells.Batch326.certificate3922,MergedCutCells.Batch326.certificate3923], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1099 : ∀ c∈certificate1099.cells, c.population=certificate1099.population := by
  change ∀ c∈[MergedCutCells.Batch326.certificate3921,MergedCutCells.Batch326.certificate3922,MergedCutCells.Batch326.certificate3923], c.population=PopulationCertificates.Batch036.certificate732
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1099 {x : ℝ} (hx : certificate1099.interval.Contains x) : ∃ c∈certificate1099.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1099 numericValid1099 hx

def certificate1100 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate733,PopulationCertificates.Batch036.certificate733,[MergedCutCells.Batch327.certificate3924,MergedCutCells.Batch327.certificate3925],(21819718893898134887/1000000000000000000),none,(1/2),(6035834235729334927/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1100 : certificate1100.NumericValid := by decide +kernel
theorem cellsSound1100 : ∀ c∈certificate1100.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3924,MergedCutCells.Batch327.certificate3925], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3925,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1100 : ∀ c∈certificate1100.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3924,MergedCutCells.Batch327.certificate3925], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3925,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1100 : ∀ c∈certificate1100.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3924,MergedCutCells.Batch327.certificate3925], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1100 : ∀ c∈certificate1100.cells, c.population=certificate1100.population := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3924,MergedCutCells.Batch327.certificate3925], c.population=PopulationCertificates.Batch036.certificate733
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1100 {x : ℝ} (hx : certificate1100.interval.Contains x) : ∃ c∈certificate1100.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1100 numericValid1100 hx

def certificate1101 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate734,PopulationCertificates.Batch036.certificate734,[MergedCutCells.Batch327.certificate3926,MergedCutCells.Batch327.certificate3927],(563468684656265773/1000000000000000000),(some (236070651/200000000)),(1/2),(1409975113438511/20000000000000000),(some (2044870580577147/40000000000000000)),(some (8950600193060389/1000000000000000000))⟩
theorem numericValid1101 : certificate1101.NumericValid := by decide +kernel
theorem cellsSound1101 : ∀ c∈certificate1101.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3926,MergedCutCells.Batch327.certificate3927], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3926,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3927,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1101 : ∀ c∈certificate1101.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3926,MergedCutCells.Batch327.certificate3927], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3926,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3927,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1101 : ∀ c∈certificate1101.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3926,MergedCutCells.Batch327.certificate3927], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid368,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid368,List.forall_mem_nil _⟩⟩
theorem populationMatches1101 : ∀ c∈certificate1101.cells, c.population=certificate1101.population := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3926,MergedCutCells.Batch327.certificate3927], c.population=PopulationCertificates.Batch036.certificate734
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1101 {x : ℝ} (hx : certificate1101.interval.Contains x) : ∃ c∈certificate1101.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1101 numericValid1101 hx

def certificate1102 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate734,PopulationCertificates.Batch036.certificate734,[MergedCutCells.Batch327.certificate3928,MergedCutCells.Batch327.certificate3929,MergedCutCells.Batch327.certificate3930],(236070651/200000000),none,(1/2),(67103254709127631/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1102 : certificate1102.NumericValid := by decide +kernel
theorem cellsSound1102 : ∀ c∈certificate1102.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3928,MergedCutCells.Batch327.certificate3929,MergedCutCells.Batch327.certificate3930], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3928,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3930,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1102 : ∀ c∈certificate1102.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3928,MergedCutCells.Batch327.certificate3929,MergedCutCells.Batch327.certificate3930], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3928,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3930,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1102 : ∀ c∈certificate1102.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3928,MergedCutCells.Batch327.certificate3929,MergedCutCells.Batch327.certificate3930], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1102 : ∀ c∈certificate1102.cells, c.population=certificate1102.population := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3928,MergedCutCells.Batch327.certificate3929,MergedCutCells.Batch327.certificate3930], c.population=PopulationCertificates.Batch036.certificate734
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1102 {x : ℝ} (hx : certificate1102.interval.Contains x) : ∃ c∈certificate1102.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1102 numericValid1102 hx

def certificate1103 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate735,PopulationCertificates.Batch036.certificate735,[MergedCutCells.Batch327.certificate3931,MergedCutCells.Batch327.certificate3932],(22112533556948853429/1000000000000000000),none,(1/2),(6147874413933609771/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1103 : certificate1103.NumericValid := by decide +kernel
theorem cellsSound1103 : ∀ c∈certificate1103.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3931,MergedCutCells.Batch327.certificate3932], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3931,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3932,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1103 : ∀ c∈certificate1103.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3931,MergedCutCells.Batch327.certificate3932], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3931,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3932,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1103 : ∀ c∈certificate1103.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3931,MergedCutCells.Batch327.certificate3932], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1103 : ∀ c∈certificate1103.cells, c.population=certificate1103.population := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3931,MergedCutCells.Batch327.certificate3932], c.population=PopulationCertificates.Batch036.certificate735
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1103 {x : ℝ} (hx : certificate1103.interval.Contains x) : ∃ c∈certificate1103.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1103 numericValid1103 hx

end Cycle12.MergedCutGroups.Batch091
