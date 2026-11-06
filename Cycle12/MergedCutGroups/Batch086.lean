import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch034
import Cycle12.MergedCutCells.Batch313
import Cycle12.MergedCutCells.Batch314
import Cycle12.MergedCutCells.Batch315
import Cycle12.PopulationCertificates.Batch034

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch086

def certificate1032 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate688,PopulationCertificates.Batch034.certificate688,[MergedCutCells.Batch313.certificate3763,MergedCutCells.Batch313.certificate3764],(112764690283851811/200000000000000000),(some (127160607/100000000)),(1/2),(207530884649264069/1000000000000000000),(some (12203063069171889/1000000000000000000)),(some (1647331947207207/1000000000000000000))⟩
theorem numericValid1032 : certificate1032.NumericValid := by decide +kernel
theorem cellsSound1032 : ∀ c∈certificate1032.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3763,MergedCutCells.Batch313.certificate3764], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3763,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3764,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1032 : ∀ c∈certificate1032.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3763,MergedCutCells.Batch313.certificate3764], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3763,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3764,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1032 : ∀ c∈certificate1032.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3763,MergedCutCells.Batch313.certificate3764], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid345,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid345,List.forall_mem_nil _⟩⟩
theorem populationMatches1032 : ∀ c∈certificate1032.cells, c.population=certificate1032.population := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3763,MergedCutCells.Batch313.certificate3764], c.population=PopulationCertificates.Batch034.certificate688
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1032 {x : ℝ} (hx : certificate1032.interval.Contains x) : ∃ c∈certificate1032.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1032 numericValid1032 hx

def certificate1033 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate688,PopulationCertificates.Batch034.certificate688,[MergedCutCells.Batch313.certificate3765,MergedCutCells.Batch313.certificate3766,MergedCutCells.Batch313.certificate3767],(127160607/100000000),none,(1/2),(103488283245953867/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1033 : certificate1033.NumericValid := by decide +kernel
theorem cellsSound1033 : ∀ c∈certificate1033.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3765,MergedCutCells.Batch313.certificate3766,MergedCutCells.Batch313.certificate3767], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3765,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3766,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3767,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1033 : ∀ c∈certificate1033.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3765,MergedCutCells.Batch313.certificate3766,MergedCutCells.Batch313.certificate3767], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3765,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3766,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3767,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1033 : ∀ c∈certificate1033.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3765,MergedCutCells.Batch313.certificate3766,MergedCutCells.Batch313.certificate3767], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1033 : ∀ c∈certificate1033.cells, c.population=certificate1033.population := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3765,MergedCutCells.Batch313.certificate3766,MergedCutCells.Batch313.certificate3767], c.population=PopulationCertificates.Batch034.certificate688
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1033 {x : ℝ} (hx : certificate1033.interval.Contains x) : ∃ c∈certificate1033.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1033 numericValid1033 hx

def certificate1034 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate689,PopulationCertificates.Batch034.certificate689,[MergedCutCells.Batch314.certificate3768,MergedCutCells.Batch314.certificate3769],(8631626716470628079/500000000000000000),none,(1/2),(2227244465131331253/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1034 : certificate1034.NumericValid := by decide +kernel
theorem cellsSound1034 : ∀ c∈certificate1034.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3768,MergedCutCells.Batch314.certificate3769], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3768,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3769,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1034 : ∀ c∈certificate1034.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3768,MergedCutCells.Batch314.certificate3769], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3768,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3769,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1034 : ∀ c∈certificate1034.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3768,MergedCutCells.Batch314.certificate3769], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1034 : ∀ c∈certificate1034.cells, c.population=certificate1034.population := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3768,MergedCutCells.Batch314.certificate3769], c.population=PopulationCertificates.Batch034.certificate689
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1034 {x : ℝ} (hx : certificate1034.interval.Contains x) : ∃ c∈certificate1034.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1034 numericValid1034 hx

def certificate1035 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate690,PopulationCertificates.Batch034.certificate690,[MergedCutCells.Batch314.certificate3770,MergedCutCells.Batch314.certificate3771],(281931728087379919/500000000000000000),(some (1271680787/1000000000)),(1/2),(40960812858172717/200000000000000000),(some (647945522537451/50000000000000000)),(some (70638291553483/40000000000000000))⟩
theorem numericValid1035 : certificate1035.NumericValid := by decide +kernel
theorem cellsSound1035 : ∀ c∈certificate1035.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3770,MergedCutCells.Batch314.certificate3771], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3770,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3771,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1035 : ∀ c∈certificate1035.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3770,MergedCutCells.Batch314.certificate3771], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3770,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3771,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1035 : ∀ c∈certificate1035.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3770,MergedCutCells.Batch314.certificate3771], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid346,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid346,List.forall_mem_nil _⟩⟩
theorem populationMatches1035 : ∀ c∈certificate1035.cells, c.population=certificate1035.population := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3770,MergedCutCells.Batch314.certificate3771], c.population=PopulationCertificates.Batch034.certificate690
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1035 {x : ℝ} (hx : certificate1035.interval.Contains x) : ∃ c∈certificate1035.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1035 numericValid1035 hx

def certificate1036 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate690,PopulationCertificates.Batch034.certificate690,[MergedCutCells.Batch314.certificate3772,MergedCutCells.Batch314.certificate3773,MergedCutCells.Batch314.certificate3774],(1271680787/1000000000),none,(1/2),(204286095743238531/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1036 : certificate1036.NumericValid := by decide +kernel
theorem cellsSound1036 : ∀ c∈certificate1036.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3772,MergedCutCells.Batch314.certificate3773,MergedCutCells.Batch314.certificate3774], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3772,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3773,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3774,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1036 : ∀ c∈certificate1036.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3772,MergedCutCells.Batch314.certificate3773,MergedCutCells.Batch314.certificate3774], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3772,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3773,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3774,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1036 : ∀ c∈certificate1036.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3772,MergedCutCells.Batch314.certificate3773,MergedCutCells.Batch314.certificate3774], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1036 : ∀ c∈certificate1036.cells, c.population=certificate1036.population := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3772,MergedCutCells.Batch314.certificate3773,MergedCutCells.Batch314.certificate3774], c.population=PopulationCertificates.Batch034.certificate690
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1036 {x : ℝ} (hx : certificate1036.interval.Contains x) : ∃ c∈certificate1036.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1036 numericValid1036 hx

def certificate1037 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate691,PopulationCertificates.Batch034.certificate691,[MergedCutCells.Batch314.certificate3775,MergedCutCells.Batch314.certificate3776],(17425155873001604501/1000000000000000000),none,(1/2),(899561702180604889/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1037 : certificate1037.NumericValid := by decide +kernel
theorem cellsSound1037 : ∀ c∈certificate1037.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3775,MergedCutCells.Batch314.certificate3776], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3775,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3776,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1037 : ∀ c∈certificate1037.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3775,MergedCutCells.Batch314.certificate3776], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3775,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3776,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1037 : ∀ c∈certificate1037.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3775,MergedCutCells.Batch314.certificate3776], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1037 : ∀ c∈certificate1037.cells, c.population=certificate1037.population := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3775,MergedCutCells.Batch314.certificate3776], c.population=PopulationCertificates.Batch034.certificate691
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1037 {x : ℝ} (hx : certificate1037.interval.Contains x) : ∃ c∈certificate1037.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1037 numericValid1037 hx

def certificate1038 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate692,PopulationCertificates.Batch034.certificate692,[MergedCutCells.Batch314.certificate3777,MergedCutCells.Batch314.certificate3778],(561505858876437607/1000000000000000000),(some (1267275989/1000000000)),(1/2),(190042908455681841/1000000000000000000),(some (7264600189356259/500000000000000000)),(some (126026671876377/62500000000000000))⟩
theorem numericValid1038 : certificate1038.NumericValid := by decide +kernel
theorem cellsSound1038 : ∀ c∈certificate1038.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3777,MergedCutCells.Batch314.certificate3778], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3777,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3778,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1038 : ∀ c∈certificate1038.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3777,MergedCutCells.Batch314.certificate3778], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3777,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3778,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1038 : ∀ c∈certificate1038.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3777,MergedCutCells.Batch314.certificate3778], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid347,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid347,List.forall_mem_nil _⟩⟩
theorem populationMatches1038 : ∀ c∈certificate1038.cells, c.population=certificate1038.population := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3777,MergedCutCells.Batch314.certificate3778], c.population=PopulationCertificates.Batch034.certificate692
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1038 {x : ℝ} (hx : certificate1038.interval.Contains x) : ∃ c∈certificate1038.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1038 numericValid1038 hx

def certificate1039 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate692,PopulationCertificates.Batch034.certificate692,[MergedCutCells.Batch314.certificate3779,MergedCutCells.Batch315.certificate3780,MergedCutCells.Batch315.certificate3781],(1267275989/1000000000),none,(1/2),(94723263705184059/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1039 : certificate1039.NumericValid := by decide +kernel
theorem cellsSound1039 : ∀ c∈certificate1039.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3779,MergedCutCells.Batch315.certificate3780,MergedCutCells.Batch315.certificate3781], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.sound3779,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3780,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3781,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1039 : ∀ c∈certificate1039.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3779,MergedCutCells.Batch315.certificate3780,MergedCutCells.Batch315.certificate3781], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch314.numericValid3779,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3780,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3781,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1039 : ∀ c∈certificate1039.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3779,MergedCutCells.Batch315.certificate3780,MergedCutCells.Batch315.certificate3781], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1039 : ∀ c∈certificate1039.cells, c.population=certificate1039.population := by
  change ∀ c∈[MergedCutCells.Batch314.certificate3779,MergedCutCells.Batch315.certificate3780,MergedCutCells.Batch315.certificate3781], c.population=PopulationCertificates.Batch034.certificate692
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1039 {x : ℝ} (hx : certificate1039.interval.Contains x) : ∃ c∈certificate1039.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1039 numericValid1039 hx

def certificate1040 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate693,PopulationCertificates.Batch034.certificate693,[MergedCutCells.Batch315.certificate3782,MergedCutCells.Batch315.certificate3783],(17649339354736071723/1000000000000000000),none,(1/2),(454002353178153939/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1040 : certificate1040.NumericValid := by decide +kernel
theorem cellsSound1040 : ∀ c∈certificate1040.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3782,MergedCutCells.Batch315.certificate3783], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3782,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3783,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1040 : ∀ c∈certificate1040.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3782,MergedCutCells.Batch315.certificate3783], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3782,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3783,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1040 : ∀ c∈certificate1040.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3782,MergedCutCells.Batch315.certificate3783], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1040 : ∀ c∈certificate1040.cells, c.population=certificate1040.population := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3782,MergedCutCells.Batch315.certificate3783], c.population=PopulationCertificates.Batch034.certificate693
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1040 {x : ℝ} (hx : certificate1040.interval.Contains x) : ∃ c∈certificate1040.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1040 numericValid1040 hx

def certificate1041 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate694,PopulationCertificates.Batch034.certificate694,[MergedCutCells.Batch315.certificate3784,MergedCutCells.Batch315.certificate3785],(561749627123939413/1000000000000000000),(some (1267731579/1000000000)),(1/2),(23295857184095793/125000000000000000),(some (3834943243813091/250000000000000000)),(some (107387372813781/50000000000000000))⟩
theorem numericValid1041 : certificate1041.NumericValid := by decide +kernel
theorem cellsSound1041 : ∀ c∈certificate1041.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3784,MergedCutCells.Batch315.certificate3785], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3784,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3785,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1041 : ∀ c∈certificate1041.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3784,MergedCutCells.Batch315.certificate3785], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3784,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3785,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1041 : ∀ c∈certificate1041.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3784,MergedCutCells.Batch315.certificate3785], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid348,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid348,List.forall_mem_nil _⟩⟩
theorem populationMatches1041 : ∀ c∈certificate1041.cells, c.population=certificate1041.population := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3784,MergedCutCells.Batch315.certificate3785], c.population=PopulationCertificates.Batch034.certificate694
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1041 {x : ℝ} (hx : certificate1041.interval.Contains x) : ∃ c∈certificate1041.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1041 numericValid1041 hx

def certificate1042 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate694,PopulationCertificates.Batch034.certificate694,[MergedCutCells.Batch315.certificate3786,MergedCutCells.Batch315.certificate3787,MergedCutCells.Batch315.certificate3788],(1267731579/1000000000),none,(1/2),(46414793307930523/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1042 : certificate1042.NumericValid := by decide +kernel
theorem cellsSound1042 : ∀ c∈certificate1042.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3786,MergedCutCells.Batch315.certificate3787,MergedCutCells.Batch315.certificate3788], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3786,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3787,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3788,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1042 : ∀ c∈certificate1042.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3786,MergedCutCells.Batch315.certificate3787,MergedCutCells.Batch315.certificate3788], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3786,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3787,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3788,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1042 : ∀ c∈certificate1042.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3786,MergedCutCells.Batch315.certificate3787,MergedCutCells.Batch315.certificate3788], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1042 : ∀ c∈certificate1042.cells, c.population=certificate1042.population := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3786,MergedCutCells.Batch315.certificate3787,MergedCutCells.Batch315.certificate3788], c.population=PopulationCertificates.Batch034.certificate694
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1042 {x : ℝ} (hx : certificate1042.interval.Contains x) : ∃ c∈certificate1042.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1042 numericValid1042 hx

def certificate1043 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate695,PopulationCertificates.Batch034.certificate695,[MergedCutCells.Batch315.certificate3789,MergedCutCells.Batch315.certificate3790],(3573369315314114979/200000000000000000),none,(1/2),(4620538435509354379/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1043 : certificate1043.NumericValid := by decide +kernel
theorem cellsSound1043 : ∀ c∈certificate1043.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3789,MergedCutCells.Batch315.certificate3790], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3789,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3790,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1043 : ∀ c∈certificate1043.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3789,MergedCutCells.Batch315.certificate3790], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3789,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3790,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1043 : ∀ c∈certificate1043.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3789,MergedCutCells.Batch315.certificate3790], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1043 : ∀ c∈certificate1043.cells, c.population=certificate1043.population := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3789,MergedCutCells.Batch315.certificate3790], c.population=PopulationCertificates.Batch034.certificate695
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1043 {x : ℝ} (hx : certificate1043.interval.Contains x) : ∃ c∈certificate1043.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1043 numericValid1043 hx

end Cycle12.MergedCutGroups.Batch086
