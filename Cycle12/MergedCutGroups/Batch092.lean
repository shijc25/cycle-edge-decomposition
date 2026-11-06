import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch036
import Cycle12.GeometryCertificates.Batch037
import Cycle12.MergedCutCells.Batch327
import Cycle12.MergedCutCells.Batch328
import Cycle12.MergedCutCells.Batch329
import Cycle12.MergedCutCells.Batch330
import Cycle12.PopulationCertificates.Batch036
import Cycle12.PopulationCertificates.Batch037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch092

def certificate1104 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate736,PopulationCertificates.Batch036.certificate736,[MergedCutCells.Batch327.certificate3933,MergedCutCells.Batch327.certificate3934],(282080585518748411/500000000000000000),(some (1152816283/1000000000)),(1/2),(32256939677739411/500000000000000000),(some (535667149341663/10000000000000000)),(some (9473233561575741/1000000000000000000))⟩
theorem numericValid1104 : certificate1104.NumericValid := by decide +kernel
theorem cellsSound1104 : ∀ c∈certificate1104.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3933,MergedCutCells.Batch327.certificate3934], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3934,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1104 : ∀ c∈certificate1104.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3933,MergedCutCells.Batch327.certificate3934], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3934,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1104 : ∀ c∈certificate1104.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3933,MergedCutCells.Batch327.certificate3934], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid369,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid369,List.forall_mem_nil _⟩⟩
theorem populationMatches1104 : ∀ c∈certificate1104.cells, c.population=certificate1104.population := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3933,MergedCutCells.Batch327.certificate3934], c.population=PopulationCertificates.Batch036.certificate736
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1104 {x : ℝ} (hx : certificate1104.interval.Contains x) : ∃ c∈certificate1104.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1104 numericValid1104 hx

def certificate1105 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate736,PopulationCertificates.Batch036.certificate736,[MergedCutCells.Batch327.certificate3935,MergedCutCells.Batch328.certificate3936,MergedCutCells.Batch328.certificate3937,MergedCutCells.Batch328.certificate3938],(1152816283/1000000000),none,(1/2),(30344174550634803/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1105 : certificate1105.NumericValid := by decide +kernel
theorem cellsSound1105 : ∀ c∈certificate1105.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3935,MergedCutCells.Batch328.certificate3936,MergedCutCells.Batch328.certificate3937,MergedCutCells.Batch328.certificate3938], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.sound3935,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3936,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3937,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3938,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1105 : ∀ c∈certificate1105.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3935,MergedCutCells.Batch328.certificate3936,MergedCutCells.Batch328.certificate3937,MergedCutCells.Batch328.certificate3938], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch327.numericValid3935,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3936,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3937,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3938,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1105 : ∀ c∈certificate1105.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3935,MergedCutCells.Batch328.certificate3936,MergedCutCells.Batch328.certificate3937,MergedCutCells.Batch328.certificate3938], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1105 : ∀ c∈certificate1105.cells, c.population=certificate1105.population := by
  change ∀ c∈[MergedCutCells.Batch327.certificate3935,MergedCutCells.Batch328.certificate3936,MergedCutCells.Batch328.certificate3937,MergedCutCells.Batch328.certificate3938], c.population=PopulationCertificates.Batch036.certificate736
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1105 {x : ℝ} (hx : certificate1105.interval.Contains x) : ∃ c∈certificate1105.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1105 numericValid1105 hx

def certificate1106 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate737,PopulationCertificates.Batch036.certificate737,[MergedCutCells.Batch328.certificate3939,MergedCutCells.Batch328.certificate3940],(11206161808415574559/500000000000000000),none,(1/2),(6262650104195225837/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1106 : certificate1106.NumericValid := by decide +kernel
theorem cellsSound1106 : ∀ c∈certificate1106.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3939,MergedCutCells.Batch328.certificate3940], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3939,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3940,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1106 : ∀ c∈certificate1106.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3939,MergedCutCells.Batch328.certificate3940], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3939,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3940,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1106 : ∀ c∈certificate1106.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3939,MergedCutCells.Batch328.certificate3940], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1106 : ∀ c∈certificate1106.cells, c.population=certificate1106.population := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3939,MergedCutCells.Batch328.certificate3940], c.population=PopulationCertificates.Batch036.certificate737
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1106 {x : ℝ} (hx : certificate1106.interval.Contains x) : ∃ c∈certificate1106.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1106 numericValid1106 hx

def certificate1107 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate738,PopulationCertificates.Batch036.certificate738,[MergedCutCells.Batch328.certificate3941,MergedCutCells.Batch328.certificate3942],(56750577239489553/100000000000000000),(some (1158615823/1000000000)),(1/2),(69466321383449619/1000000000000000000),(some (56368486696811659/1000000000000000000)),(some (2519981749611301/250000000000000000))⟩
theorem numericValid1107 : certificate1107.NumericValid := by decide +kernel
theorem cellsSound1107 : ∀ c∈certificate1107.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3941,MergedCutCells.Batch328.certificate3942], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3941,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3942,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1107 : ∀ c∈certificate1107.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3941,MergedCutCells.Batch328.certificate3942], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3941,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3942,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1107 : ∀ c∈certificate1107.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3941,MergedCutCells.Batch328.certificate3942], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid370,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid370,List.forall_mem_nil _⟩⟩
theorem populationMatches1107 : ∀ c∈certificate1107.cells, c.population=certificate1107.population := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3941,MergedCutCells.Batch328.certificate3942], c.population=PopulationCertificates.Batch036.certificate738
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1107 {x : ℝ} (hx : certificate1107.interval.Contains x) : ∃ c∈certificate1107.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1107 numericValid1107 hx

def certificate1108 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate738,PopulationCertificates.Batch036.certificate738,[MergedCutCells.Batch328.certificate3943,MergedCutCells.Batch328.certificate3944,MergedCutCells.Batch328.certificate3945],(1158615823/1000000000),none,(1/2),(4102711527603551/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1108 : certificate1108.NumericValid := by decide +kernel
theorem cellsSound1108 : ∀ c∈certificate1108.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3943,MergedCutCells.Batch328.certificate3944,MergedCutCells.Batch328.certificate3945], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3943,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3944,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3945,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1108 : ∀ c∈certificate1108.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3943,MergedCutCells.Batch328.certificate3944,MergedCutCells.Batch328.certificate3945], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3943,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3944,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3945,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1108 : ∀ c∈certificate1108.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3943,MergedCutCells.Batch328.certificate3944,MergedCutCells.Batch328.certificate3945], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1108 : ∀ c∈certificate1108.cells, c.population=certificate1108.population := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3943,MergedCutCells.Batch328.certificate3944,MergedCutCells.Batch328.certificate3945], c.population=PopulationCertificates.Batch036.certificate738
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1108 {x : ℝ} (hx : certificate1108.interval.Contains x) : ∃ c∈certificate1108.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1108 numericValid1108 hx

def certificate1109 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate739,PopulationCertificates.Batch036.certificate739,[MergedCutCells.Batch328.certificate3946,MergedCutCells.Batch328.certificate3947],(22496868987899232201/1000000000000000000),none,(1/2),(6368884720337266227/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1109 : certificate1109.NumericValid := by decide +kernel
theorem cellsSound1109 : ∀ c∈certificate1109.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3946,MergedCutCells.Batch328.certificate3947], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3946,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.sound3947,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1109 : ∀ c∈certificate1109.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3946,MergedCutCells.Batch328.certificate3947], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3946,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch328.numericValid3947,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1109 : ∀ c∈certificate1109.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3946,MergedCutCells.Batch328.certificate3947], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1109 : ∀ c∈certificate1109.cells, c.population=certificate1109.population := by
  change ∀ c∈[MergedCutCells.Batch328.certificate3946,MergedCutCells.Batch328.certificate3947], c.population=PopulationCertificates.Batch036.certificate739
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1109 {x : ℝ} (hx : certificate1109.interval.Contains x) : ∃ c∈certificate1109.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1109 numericValid1109 hx

def certificate1110 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate740,PopulationCertificates.Batch037.certificate740,[MergedCutCells.Batch329.certificate3948,MergedCutCells.Batch329.certificate3949],(568290735124224207/1000000000000000000),(some (5799881/5000000)),(1/2),(63291724839041351/1000000000000000000),(some (29620592280045049/500000000000000000)),(some (10710441594864617/1000000000000000000))⟩
theorem numericValid1110 : certificate1110.NumericValid := by decide +kernel
theorem cellsSound1110 : ∀ c∈certificate1110.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3948,MergedCutCells.Batch329.certificate3949], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3948,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3949,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1110 : ∀ c∈certificate1110.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3948,MergedCutCells.Batch329.certificate3949], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3948,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3949,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1110 : ∀ c∈certificate1110.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3948,MergedCutCells.Batch329.certificate3949], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid371,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid371,List.forall_mem_nil _⟩⟩
theorem populationMatches1110 : ∀ c∈certificate1110.cells, c.population=certificate1110.population := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3948,MergedCutCells.Batch329.certificate3949], c.population=PopulationCertificates.Batch037.certificate740
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1110 {x : ℝ} (hx : certificate1110.interval.Contains x) : ∃ c∈certificate1110.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1110 numericValid1110 hx

def certificate1111 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate740,PopulationCertificates.Batch037.certificate740,[MergedCutCells.Batch329.certificate3950,MergedCutCells.Batch329.certificate3951,MergedCutCells.Batch329.certificate3952],(5799881/5000000),none,(1/2),(59175150329264073/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1111 : certificate1111.NumericValid := by decide +kernel
theorem cellsSound1111 : ∀ c∈certificate1111.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3950,MergedCutCells.Batch329.certificate3951,MergedCutCells.Batch329.certificate3952], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3950,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3951,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3952,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1111 : ∀ c∈certificate1111.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3950,MergedCutCells.Batch329.certificate3951,MergedCutCells.Batch329.certificate3952], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3950,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3951,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3952,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1111 : ∀ c∈certificate1111.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3950,MergedCutCells.Batch329.certificate3951,MergedCutCells.Batch329.certificate3952], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1111 : ∀ c∈certificate1111.cells, c.population=certificate1111.population := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3950,MergedCutCells.Batch329.certificate3951,MergedCutCells.Batch329.certificate3952], c.population=PopulationCertificates.Batch037.certificate740
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1111 {x : ℝ} (hx : certificate1111.interval.Contains x) : ∃ c∈certificate1111.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1111 numericValid1111 hx

def certificate1112 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate741,PopulationCertificates.Batch037.certificate741,[MergedCutCells.Batch329.certificate3953,MergedCutCells.Batch329.certificate3954],(22809629885876930449/1000000000000000000),none,(1/2),(1622328389812026193/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1112 : certificate1112.NumericValid := by decide +kernel
theorem cellsSound1112 : ∀ c∈certificate1112.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3953,MergedCutCells.Batch329.certificate3954], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3954,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1112 : ∀ c∈certificate1112.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3953,MergedCutCells.Batch329.certificate3954], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3954,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1112 : ∀ c∈certificate1112.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3953,MergedCutCells.Batch329.certificate3954], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1112 : ∀ c∈certificate1112.cells, c.population=certificate1112.population := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3953,MergedCutCells.Batch329.certificate3954], c.population=PopulationCertificates.Batch037.certificate741
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1112 {x : ℝ} (hx : certificate1112.interval.Contains x) : ∃ c∈certificate1112.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1112 numericValid1112 hx

def certificate1113 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate742,PopulationCertificates.Batch037.certificate742,[MergedCutCells.Batch329.certificate3955,MergedCutCells.Batch329.certificate3956],(285900103369541111/500000000000000000),(some (1166054813/1000000000)),(1/2),(17182730259635953/250000000000000000),(some (15546397183303331/250000000000000000)),(some (284135341019149/25000000000000000))⟩
theorem numericValid1113 : certificate1113.NumericValid := by decide +kernel
theorem cellsSound1113 : ∀ c∈certificate1113.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3955,MergedCutCells.Batch329.certificate3956], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3955,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3956,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1113 : ∀ c∈certificate1113.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3955,MergedCutCells.Batch329.certificate3956], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3955,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3956,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1113 : ∀ c∈certificate1113.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3955,MergedCutCells.Batch329.certificate3956], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid372,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid372,List.forall_mem_nil _⟩⟩
theorem populationMatches1113 : ∀ c∈certificate1113.cells, c.population=certificate1113.population := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3955,MergedCutCells.Batch329.certificate3956], c.population=PopulationCertificates.Batch037.certificate742
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1113 {x : ℝ} (hx : certificate1113.interval.Contains x) : ∃ c∈certificate1113.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1113 numericValid1113 hx

def certificate1114 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate742,PopulationCertificates.Batch037.certificate742,[MergedCutCells.Batch329.certificate3957,MergedCutCells.Batch329.certificate3958,MergedCutCells.Batch329.certificate3959],(1166054813/1000000000),none,(1/2),(64284457861565719/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1114 : certificate1114.NumericValid := by decide +kernel
theorem cellsSound1114 : ∀ c∈certificate1114.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3957,MergedCutCells.Batch329.certificate3958,MergedCutCells.Batch329.certificate3959], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3958,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.sound3959,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1114 : ∀ c∈certificate1114.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3957,MergedCutCells.Batch329.certificate3958,MergedCutCells.Batch329.certificate3959], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3958,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch329.numericValid3959,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1114 : ∀ c∈certificate1114.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3957,MergedCutCells.Batch329.certificate3958,MergedCutCells.Batch329.certificate3959], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1114 : ∀ c∈certificate1114.cells, c.population=certificate1114.population := by
  change ∀ c∈[MergedCutCells.Batch329.certificate3957,MergedCutCells.Batch329.certificate3958,MergedCutCells.Batch329.certificate3959], c.population=PopulationCertificates.Batch037.certificate742
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1114 {x : ℝ} (hx : certificate1114.interval.Contains x) : ∃ c∈certificate1114.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1114 numericValid1114 hx

def certificate1115 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate743,PopulationCertificates.Batch037.certificate743,[MergedCutCells.Batch330.certificate3960,MergedCutCells.Batch330.certificate3961],(23049447370537983081/1000000000000000000),none,(1/2),(6612144679418516553/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1115 : certificate1115.NumericValid := by decide +kernel
theorem cellsSound1115 : ∀ c∈certificate1115.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3960,MergedCutCells.Batch330.certificate3961], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3960,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3961,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1115 : ∀ c∈certificate1115.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3960,MergedCutCells.Batch330.certificate3961], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3960,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3961,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1115 : ∀ c∈certificate1115.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3960,MergedCutCells.Batch330.certificate3961], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1115 : ∀ c∈certificate1115.cells, c.population=certificate1115.population := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3960,MergedCutCells.Batch330.certificate3961], c.population=PopulationCertificates.Batch037.certificate743
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1115 {x : ℝ} (hx : certificate1115.interval.Contains x) : ∃ c∈certificate1115.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1115 numericValid1115 hx

end Cycle12.MergedCutGroups.Batch092
