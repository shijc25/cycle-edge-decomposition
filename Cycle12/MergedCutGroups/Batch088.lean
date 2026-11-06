import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch035
import Cycle12.MergedCutCells.Batch318
import Cycle12.MergedCutCells.Batch319
import Cycle12.MergedCutCells.Batch320
import Cycle12.PopulationCertificates.Batch035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch088

def certificate1056 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate704,PopulationCertificates.Batch035.certificate704,[MergedCutCells.Batch318.certificate3820,MergedCutCells.Batch318.certificate3821],(140010576864476839/250000000000000000),(some (38553521/31250000)),(1/2),(39167710782664459/250000000000000000),(some (5352105663786401/250000000000000000)),(some (1585277991221893/500000000000000000))⟩
theorem numericValid1056 : certificate1056.NumericValid := by decide +kernel
theorem cellsSound1056 : ∀ c∈certificate1056.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3820,MergedCutCells.Batch318.certificate3821], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3820,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3821,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1056 : ∀ c∈certificate1056.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3820,MergedCutCells.Batch318.certificate3821], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3820,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3821,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1056 : ∀ c∈certificate1056.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3820,MergedCutCells.Batch318.certificate3821], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid353,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid353,List.forall_mem_nil _⟩⟩
theorem populationMatches1056 : ∀ c∈certificate1056.cells, c.population=certificate1056.population := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3820,MergedCutCells.Batch318.certificate3821], c.population=PopulationCertificates.Batch035.certificate704
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1056 {x : ℝ} (hx : certificate1056.interval.Contains x) : ∃ c∈certificate1056.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1056 numericValid1056 hx

def certificate1057 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate704,PopulationCertificates.Batch035.certificate704,[MergedCutCells.Batch318.certificate3822,MergedCutCells.Batch318.certificate3823,MergedCutCells.Batch318.certificate3824],(38553521/31250000),none,(1/2),(77775545053438247/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1057 : certificate1057.NumericValid := by decide +kernel
theorem cellsSound1057 : ∀ c∈certificate1057.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3822,MergedCutCells.Batch318.certificate3823,MergedCutCells.Batch318.certificate3824], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3822,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3824,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1057 : ∀ c∈certificate1057.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3822,MergedCutCells.Batch318.certificate3823,MergedCutCells.Batch318.certificate3824], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3822,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3824,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1057 : ∀ c∈certificate1057.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3822,MergedCutCells.Batch318.certificate3823,MergedCutCells.Batch318.certificate3824], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1057 : ∀ c∈certificate1057.cells, c.population=certificate1057.population := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3822,MergedCutCells.Batch318.certificate3823,MergedCutCells.Batch318.certificate3824], c.population=PopulationCertificates.Batch035.certificate704
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1057 {x : ℝ} (hx : certificate1057.interval.Contains x) : ∃ c∈certificate1057.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1057 numericValid1057 hx

def certificate1058 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate705,PopulationCertificates.Batch035.certificate705,[MergedCutCells.Batch318.certificate3825,MergedCutCells.Batch318.certificate3826],(4689831584664203259/250000000000000000),none,(1/2),(1228523253428336573/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1058 : certificate1058.NumericValid := by decide +kernel
theorem cellsSound1058 : ∀ c∈certificate1058.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3825,MergedCutCells.Batch318.certificate3826], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3825,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3826,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1058 : ∀ c∈certificate1058.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3825,MergedCutCells.Batch318.certificate3826], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3825,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3826,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1058 : ∀ c∈certificate1058.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3825,MergedCutCells.Batch318.certificate3826], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1058 : ∀ c∈certificate1058.cells, c.population=certificate1058.population := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3825,MergedCutCells.Batch318.certificate3826], c.population=PopulationCertificates.Batch035.certificate705
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1058 {x : ℝ} (hx : certificate1058.interval.Contains x) : ∃ c∈certificate1058.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1058 numericValid1058 hx

def certificate1059 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate706,PopulationCertificates.Batch035.certificate706,[MergedCutCells.Batch318.certificate3827,MergedCutCells.Batch319.certificate3828],(34855506096673471/62500000000000000),(some (2448729/2000000)),(1/2),(17684532760617521/125000000000000000),(some (466204890951461/20000000000000000)),(some (1752115035114009/500000000000000000))⟩
theorem numericValid1059 : certificate1059.NumericValid := by decide +kernel
theorem cellsSound1059 : ∀ c∈certificate1059.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3827,MergedCutCells.Batch319.certificate3828], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3827,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3828,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1059 : ∀ c∈certificate1059.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3827,MergedCutCells.Batch319.certificate3828], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3827,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3828,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1059 : ∀ c∈certificate1059.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3827,MergedCutCells.Batch319.certificate3828], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid354,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid354,List.forall_mem_nil _⟩⟩
theorem populationMatches1059 : ∀ c∈certificate1059.cells, c.population=certificate1059.population := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3827,MergedCutCells.Batch319.certificate3828], c.population=PopulationCertificates.Batch035.certificate706
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1059 {x : ℝ} (hx : certificate1059.interval.Contains x) : ∃ c∈certificate1059.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1059 numericValid1059 hx

def certificate1060 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate706,PopulationCertificates.Batch035.certificate706,[MergedCutCells.Batch319.certificate3829,MergedCutCells.Batch319.certificate3830,MergedCutCells.Batch319.certificate3831],(2448729/2000000),none,(1/2),(140247867317025423/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1060 : certificate1060.NumericValid := by decide +kernel
theorem cellsSound1060 : ∀ c∈certificate1060.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3829,MergedCutCells.Batch319.certificate3830,MergedCutCells.Batch319.certificate3831], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3829,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3830,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3831,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1060 : ∀ c∈certificate1060.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3829,MergedCutCells.Batch319.certificate3830,MergedCutCells.Batch319.certificate3831], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3829,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3830,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3831,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1060 : ∀ c∈certificate1060.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3829,MergedCutCells.Batch319.certificate3830,MergedCutCells.Batch319.certificate3831], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1060 : ∀ c∈certificate1060.cells, c.population=certificate1060.population := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3829,MergedCutCells.Batch319.certificate3830,MergedCutCells.Batch319.certificate3831], c.population=PopulationCertificates.Batch035.certificate706
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1060 {x : ℝ} (hx : certificate1060.interval.Contains x) : ∃ c∈certificate1060.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1060 numericValid1060 hx

def certificate1061 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate707,PopulationCertificates.Batch035.certificate707,[MergedCutCells.Batch319.certificate3832,MergedCutCells.Batch319.certificate3833],(3773723984721452401/200000000000000000),none,(1/2),(2474820578799054289/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1061 : certificate1061.NumericValid := by decide +kernel
theorem cellsSound1061 : ∀ c∈certificate1061.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3832,MergedCutCells.Batch319.certificate3833], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3832,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3833,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1061 : ∀ c∈certificate1061.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3832,MergedCutCells.Batch319.certificate3833], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3832,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3833,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1061 : ∀ c∈certificate1061.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3832,MergedCutCells.Batch319.certificate3833], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1061 : ∀ c∈certificate1061.cells, c.population=certificate1061.population := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3832,MergedCutCells.Batch319.certificate3833], c.population=PopulationCertificates.Batch035.certificate707
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1061 {x : ℝ} (hx : certificate1061.interval.Contains x) : ∃ c∈certificate1061.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1061 numericValid1061 hx

def certificate1062 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate708,PopulationCertificates.Batch035.certificate708,[MergedCutCells.Batch319.certificate3834,MergedCutCells.Batch319.certificate3835],(558004894263574059/1000000000000000000),(some (61247233/50000000)),(1/2),(135775348097272099/1000000000000000000),(some (1265265667065113/50000000000000000)),(some (3860434472410023/1000000000000000000))⟩
theorem numericValid1062 : certificate1062.NumericValid := by decide +kernel
theorem cellsSound1062 : ∀ c∈certificate1062.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3834,MergedCutCells.Batch319.certificate3835], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3834,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3835,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1062 : ∀ c∈certificate1062.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3834,MergedCutCells.Batch319.certificate3835], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3834,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3835,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1062 : ∀ c∈certificate1062.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3834,MergedCutCells.Batch319.certificate3835], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid355,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid355,List.forall_mem_nil _⟩⟩
theorem populationMatches1062 : ∀ c∈certificate1062.cells, c.population=certificate1062.population := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3834,MergedCutCells.Batch319.certificate3835], c.population=PopulationCertificates.Batch035.certificate708
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1062 {x : ℝ} (hx : certificate1062.interval.Contains x) : ∃ c∈certificate1062.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1062 numericValid1062 hx

def certificate1063 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate708,PopulationCertificates.Batch035.certificate708,[MergedCutCells.Batch319.certificate3836,MergedCutCells.Batch319.certificate3837,MergedCutCells.Batch319.certificate3838],(61247233/50000000),none,(1/2),(26883754464032691/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1063 : certificate1063.NumericValid := by decide +kernel
theorem cellsSound1063 : ∀ c∈certificate1063.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3836,MergedCutCells.Batch319.certificate3837,MergedCutCells.Batch319.certificate3838], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3836,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3837,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3838,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1063 : ∀ c∈certificate1063.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3836,MergedCutCells.Batch319.certificate3837,MergedCutCells.Batch319.certificate3838], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3836,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3837,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3838,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1063 : ∀ c∈certificate1063.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3836,MergedCutCells.Batch319.certificate3837,MergedCutCells.Batch319.certificate3838], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1063 : ∀ c∈certificate1063.cells, c.population=certificate1063.population := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3836,MergedCutCells.Batch319.certificate3837,MergedCutCells.Batch319.certificate3838], c.population=PopulationCertificates.Batch035.certificate708
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1063 {x : ℝ} (hx : certificate1063.interval.Contains x) : ∃ c∈certificate1063.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1063 numericValid1063 hx

def certificate1064 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate709,PopulationCertificates.Batch035.certificate709,[MergedCutCells.Batch319.certificate3839,MergedCutCells.Batch320.certificate3840],(19229017808784097583/1000000000000000000),none,(1/2),(5047335296397691497/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1064 : certificate1064.NumericValid := by decide +kernel
theorem cellsSound1064 : ∀ c∈certificate1064.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3839,MergedCutCells.Batch320.certificate3840], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.sound3839,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3840,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1064 : ∀ c∈certificate1064.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3839,MergedCutCells.Batch320.certificate3840], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch319.numericValid3839,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3840,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1064 : ∀ c∈certificate1064.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3839,MergedCutCells.Batch320.certificate3840], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1064 : ∀ c∈certificate1064.cells, c.population=certificate1064.population := by
  change ∀ c∈[MergedCutCells.Batch319.certificate3839,MergedCutCells.Batch320.certificate3840], c.population=PopulationCertificates.Batch035.certificate709
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1064 {x : ℝ} (hx : certificate1064.interval.Contains x) : ∃ c∈certificate1064.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1064 numericValid1064 hx

def certificate1065 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate710,PopulationCertificates.Batch035.certificate710,[MergedCutCells.Batch320.certificate3841,MergedCutCells.Batch320.certificate3842],(558331313232145533/1000000000000000000),(some (245108477/200000000)),(1/2),(5272905565484791/40000000000000000),(some (26323315916288989/1000000000000000000)),(some (2022268514249651/500000000000000000))⟩
theorem numericValid1065 : certificate1065.NumericValid := by decide +kernel
theorem cellsSound1065 : ∀ c∈certificate1065.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3841,MergedCutCells.Batch320.certificate3842], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3841,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3842,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1065 : ∀ c∈certificate1065.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3841,MergedCutCells.Batch320.certificate3842], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3841,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3842,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1065 : ∀ c∈certificate1065.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3841,MergedCutCells.Batch320.certificate3842], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid356,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid356,List.forall_mem_nil _⟩⟩
theorem populationMatches1065 : ∀ c∈certificate1065.cells, c.population=certificate1065.population := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3841,MergedCutCells.Batch320.certificate3842], c.population=PopulationCertificates.Batch035.certificate710
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1065 {x : ℝ} (hx : certificate1065.interval.Contains x) : ∃ c∈certificate1065.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1065 numericValid1065 hx

def certificate1066 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate710,PopulationCertificates.Batch035.certificate710,[MergedCutCells.Batch320.certificate3843,MergedCutCells.Batch320.certificate3844,MergedCutCells.Batch320.certificate3845],(245108477/200000000),none,(1/2),(130461752476976437/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1066 : certificate1066.NumericValid := by decide +kernel
theorem cellsSound1066 : ∀ c∈certificate1066.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3843,MergedCutCells.Batch320.certificate3844,MergedCutCells.Batch320.certificate3845], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3843,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3844,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3845,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1066 : ∀ c∈certificate1066.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3843,MergedCutCells.Batch320.certificate3844,MergedCutCells.Batch320.certificate3845], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3843,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3844,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3845,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1066 : ∀ c∈certificate1066.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3843,MergedCutCells.Batch320.certificate3844,MergedCutCells.Batch320.certificate3845], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1066 : ∀ c∈certificate1066.cells, c.population=certificate1066.population := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3843,MergedCutCells.Batch320.certificate3844,MergedCutCells.Batch320.certificate3845], c.population=PopulationCertificates.Batch035.certificate710
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1066 {x : ℝ} (hx : certificate1066.interval.Contains x) : ∃ c∈certificate1066.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1066 numericValid1066 hx

def certificate1067 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate711,PopulationCertificates.Batch035.certificate711,[MergedCutCells.Batch320.certificate3846,MergedCutCells.Batch320.certificate3847],(19475255917991226231/1000000000000000000),none,(1/2),(642412558995187309/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1067 : certificate1067.NumericValid := by decide +kernel
theorem cellsSound1067 : ∀ c∈certificate1067.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3846,MergedCutCells.Batch320.certificate3847], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3846,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3847,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1067 : ∀ c∈certificate1067.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3846,MergedCutCells.Batch320.certificate3847], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3846,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3847,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1067 : ∀ c∈certificate1067.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3846,MergedCutCells.Batch320.certificate3847], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1067 : ∀ c∈certificate1067.cells, c.population=certificate1067.population := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3846,MergedCutCells.Batch320.certificate3847], c.population=PopulationCertificates.Batch035.certificate711
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1067 {x : ℝ} (hx : certificate1067.interval.Contains x) : ∃ c∈certificate1067.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1067 numericValid1067 hx

end Cycle12.MergedCutGroups.Batch088
