import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch034
import Cycle12.MergedCutCells.Batch311
import Cycle12.MergedCutCells.Batch312
import Cycle12.MergedCutCells.Batch313
import Cycle12.PopulationCertificates.Batch034

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch085

def certificate1020 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate680,PopulationCertificates.Batch034.certificate680,[MergedCutCells.Batch311.certificate3735,MergedCutCells.Batch311.certificate3736],(565785744578021111/1000000000000000000),(some (637634967/500000000)),(1/2),(58171467245995049/250000000000000000),(some (1743309457108391/200000000000000000)),(some (559073975815131/500000000000000000))⟩
theorem numericValid1020 : certificate1020.NumericValid := by decide +kernel
theorem cellsSound1020 : ∀ c∈certificate1020.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3735,MergedCutCells.Batch311.certificate3736], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3735,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3736,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1020 : ∀ c∈certificate1020.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3735,MergedCutCells.Batch311.certificate3736], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3735,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3736,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1020 : ∀ c∈certificate1020.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3735,MergedCutCells.Batch311.certificate3736], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid341,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid341,List.forall_mem_nil _⟩⟩
theorem populationMatches1020 : ∀ c∈certificate1020.cells, c.population=certificate1020.population := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3735,MergedCutCells.Batch311.certificate3736], c.population=PopulationCertificates.Batch034.certificate680
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1020 {x : ℝ} (hx : certificate1020.interval.Contains x) : ∃ c∈certificate1020.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1020 numericValid1020 hx

def certificate1021 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate680,PopulationCertificates.Batch034.certificate680,[MergedCutCells.Batch311.certificate3737,MergedCutCells.Batch311.certificate3738,MergedCutCells.Batch311.certificate3739],(637634967/500000000),none,(1/2),(115846422143237133/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1021 : certificate1021.NumericValid := by decide +kernel
theorem cellsSound1021 : ∀ c∈certificate1021.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3737,MergedCutCells.Batch311.certificate3738,MergedCutCells.Batch311.certificate3739], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3737,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3739,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1021 : ∀ c∈certificate1021.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3737,MergedCutCells.Batch311.certificate3738,MergedCutCells.Batch311.certificate3739], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3737,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3739,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1021 : ∀ c∈certificate1021.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3737,MergedCutCells.Batch311.certificate3738,MergedCutCells.Batch311.certificate3739], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1021 : ∀ c∈certificate1021.cells, c.population=certificate1021.population := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3737,MergedCutCells.Batch311.certificate3738,MergedCutCells.Batch311.certificate3739], c.population=PopulationCertificates.Batch034.certificate680
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1021 {x : ℝ} (hx : certificate1021.interval.Contains x) : ∃ c∈certificate1021.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1021 numericValid1021 hx

def certificate1022 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate681,PopulationCertificates.Batch034.certificate681,[MergedCutCells.Batch311.certificate3740,MergedCutCells.Batch311.certificate3741],(16601584521584192803/1000000000000000000),none,(1/2),(4231423392491740957/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1022 : certificate1022.NumericValid := by decide +kernel
theorem cellsSound1022 : ∀ c∈certificate1022.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3740,MergedCutCells.Batch311.certificate3741], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3740,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3741,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1022 : ∀ c∈certificate1022.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3740,MergedCutCells.Batch311.certificate3741], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3740,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3741,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1022 : ∀ c∈certificate1022.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3740,MergedCutCells.Batch311.certificate3741], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1022 : ∀ c∈certificate1022.cells, c.population=certificate1022.population := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3740,MergedCutCells.Batch311.certificate3741], c.population=PopulationCertificates.Batch034.certificate681
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1022 {x : ℝ} (hx : certificate1022.interval.Contains x) : ∃ c∈certificate1022.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1022 numericValid1022 hx

def certificate1023 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate682,PopulationCertificates.Batch034.certificate682,[MergedCutCells.Batch311.certificate3742,MergedCutCells.Batch311.certificate3743],(70660995820095317/125000000000000000),(some (1274340723/1000000000)),(1/2),(5703923786603057/25000000000000000),(some (9359421425061113/1000000000000000000)),(some (606669548824969/500000000000000000))⟩
theorem numericValid1023 : certificate1023.NumericValid := by decide +kernel
theorem cellsSound1023 : ∀ c∈certificate1023.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3742,MergedCutCells.Batch311.certificate3743], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3743,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1023 : ∀ c∈certificate1023.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3742,MergedCutCells.Batch311.certificate3743], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3743,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1023 : ∀ c∈certificate1023.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3742,MergedCutCells.Batch311.certificate3743], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid342,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid342,List.forall_mem_nil _⟩⟩
theorem populationMatches1023 : ∀ c∈certificate1023.cells, c.population=certificate1023.population := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3742,MergedCutCells.Batch311.certificate3743], c.population=PopulationCertificates.Batch034.certificate682
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1023 {x : ℝ} (hx : certificate1023.interval.Contains x) : ∃ c∈certificate1023.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1023 numericValid1023 hx

def certificate1024 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate682,PopulationCertificates.Batch034.certificate682,[MergedCutCells.Batch312.certificate3744,MergedCutCells.Batch312.certificate3745,MergedCutCells.Batch312.certificate3746],(1274340723/1000000000),none,(1/2),(113981675968458183/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1024 : certificate1024.NumericValid := by decide +kernel
theorem cellsSound1024 : ∀ c∈certificate1024.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3744,MergedCutCells.Batch312.certificate3745,MergedCutCells.Batch312.certificate3746], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3744,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3745,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3746,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1024 : ∀ c∈certificate1024.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3744,MergedCutCells.Batch312.certificate3745,MergedCutCells.Batch312.certificate3746], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3744,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3745,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3746,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1024 : ∀ c∈certificate1024.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3744,MergedCutCells.Batch312.certificate3745,MergedCutCells.Batch312.certificate3746], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1024 : ∀ c∈certificate1024.cells, c.population=certificate1024.population := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3744,MergedCutCells.Batch312.certificate3745,MergedCutCells.Batch312.certificate3746], c.population=PopulationCertificates.Batch034.certificate682
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1024 {x : ℝ} (hx : certificate1024.interval.Contains x) : ∃ c∈certificate1024.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1024 numericValid1024 hx

def certificate1025 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate683,PopulationCertificates.Batch034.certificate683,[MergedCutCells.Batch312.certificate3747,MergedCutCells.Batch312.certificate3748],(4200580660322092803/250000000000000000),none,(1/2),(33634961118478081/7812500000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1025 : certificate1025.NumericValid := by decide +kernel
theorem cellsSound1025 : ∀ c∈certificate1025.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3747,MergedCutCells.Batch312.certificate3748], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3747,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3748,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1025 : ∀ c∈certificate1025.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3747,MergedCutCells.Batch312.certificate3748], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3747,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3748,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1025 : ∀ c∈certificate1025.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3747,MergedCutCells.Batch312.certificate3748], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1025 : ∀ c∈certificate1025.cells, c.population=certificate1025.population := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3747,MergedCutCells.Batch312.certificate3748], c.population=PopulationCertificates.Batch034.certificate683
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1025 {x : ℝ} (hx : certificate1025.interval.Contains x) : ∃ c∈certificate1025.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1025 numericValid1025 hx

def certificate1026 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate684,PopulationCertificates.Batch034.certificate684,[MergedCutCells.Batch312.certificate3749,MergedCutCells.Batch312.certificate3750],(282978072632990137/500000000000000000),(some (159448499/125000000)),(1/2),(225680008727784157/1000000000000000000),(some (628362999346947/62500000000000000)),(some (263484643498311/200000000000000000))⟩
theorem numericValid1026 : certificate1026.NumericValid := by decide +kernel
theorem cellsSound1026 : ∀ c∈certificate1026.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3749,MergedCutCells.Batch312.certificate3750], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3750,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1026 : ∀ c∈certificate1026.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3749,MergedCutCells.Batch312.certificate3750], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3750,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1026 : ∀ c∈certificate1026.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3749,MergedCutCells.Batch312.certificate3750], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid343,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid343,List.forall_mem_nil _⟩⟩
theorem populationMatches1026 : ∀ c∈certificate1026.cells, c.population=certificate1026.population := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3749,MergedCutCells.Batch312.certificate3750], c.population=PopulationCertificates.Batch034.certificate684
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1026 {x : ℝ} (hx : certificate1026.interval.Contains x) : ∃ c∈certificate1026.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1026 numericValid1026 hx

def certificate1027 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate684,PopulationCertificates.Batch034.certificate684,[MergedCutCells.Batch312.certificate3751,MergedCutCells.Batch312.certificate3752,MergedCutCells.Batch312.certificate3753],(159448499/125000000),none,(1/2),(225373034223402639/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1027 : certificate1027.NumericValid := by decide +kernel
theorem cellsSound1027 : ∀ c∈certificate1027.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3751,MergedCutCells.Batch312.certificate3752,MergedCutCells.Batch312.certificate3753], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3751,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3752,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3753,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1027 : ∀ c∈certificate1027.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3751,MergedCutCells.Batch312.certificate3752,MergedCutCells.Batch312.certificate3753], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3751,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3752,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3753,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1027 : ∀ c∈certificate1027.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3751,MergedCutCells.Batch312.certificate3752,MergedCutCells.Batch312.certificate3753], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1027 : ∀ c∈certificate1027.cells, c.population=certificate1027.population := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3751,MergedCutCells.Batch312.certificate3752,MergedCutCells.Batch312.certificate3753], c.population=PopulationCertificates.Batch034.certificate684
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1027 {x : ℝ} (hx : certificate1027.interval.Contains x) : ∃ c∈certificate1027.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1027 numericValid1027 hx

def certificate1028 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate685,PopulationCertificates.Batch034.certificate685,[MergedCutCells.Batch312.certificate3754,MergedCutCells.Batch312.certificate3755],(16837411258889767929/1000000000000000000),none,(1/2),(1084162372388154501/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1028 : certificate1028.NumericValid := by decide +kernel
theorem cellsSound1028 : ∀ c∈certificate1028.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3754,MergedCutCells.Batch312.certificate3755], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.sound3755,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1028 : ∀ c∈certificate1028.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3754,MergedCutCells.Batch312.certificate3755], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch312.numericValid3755,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1028 : ∀ c∈certificate1028.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3754,MergedCutCells.Batch312.certificate3755], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1028 : ∀ c∈certificate1028.cells, c.population=certificate1028.population := by
  change ∀ c∈[MergedCutCells.Batch312.certificate3754,MergedCutCells.Batch312.certificate3755], c.population=PopulationCertificates.Batch034.certificate685
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1028 {x : ℝ} (hx : certificate1028.interval.Contains x) : ∃ c∈certificate1028.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1028 numericValid1028 hx

def certificate1029 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate686,PopulationCertificates.Batch034.certificate686,[MergedCutCells.Batch313.certificate3756,MergedCutCells.Batch313.certificate3757],(70451712189030483/125000000000000000),(some (635607151/500000000)),(1/2),(42230628032021769/200000000000000000),(some (5734422273482183/500000000000000000)),(some (153336576215963/100000000000000000))⟩
theorem numericValid1029 : certificate1029.NumericValid := by decide +kernel
theorem cellsSound1029 : ∀ c∈certificate1029.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3756,MergedCutCells.Batch313.certificate3757], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3757,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1029 : ∀ c∈certificate1029.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3756,MergedCutCells.Batch313.certificate3757], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3757,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1029 : ∀ c∈certificate1029.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3756,MergedCutCells.Batch313.certificate3757], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid344,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid344,List.forall_mem_nil _⟩⟩
theorem populationMatches1029 : ∀ c∈certificate1029.cells, c.population=certificate1029.population := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3756,MergedCutCells.Batch313.certificate3757], c.population=PopulationCertificates.Batch034.certificate686
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1029 {x : ℝ} (hx : certificate1029.interval.Contains x) : ∃ c∈certificate1029.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1029 numericValid1029 hx

def certificate1030 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate686,PopulationCertificates.Batch034.certificate686,[MergedCutCells.Batch313.certificate3758,MergedCutCells.Batch313.certificate3759,MergedCutCells.Batch313.certificate3760],(635607151/500000000),none,(1/2),(26338149798883071/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1030 : certificate1030.NumericValid := by decide +kernel
theorem cellsSound1030 : ∀ c∈certificate1030.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3758,MergedCutCells.Batch313.certificate3759,MergedCutCells.Batch313.certificate3760], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3759,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3760,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1030 : ∀ c∈certificate1030.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3758,MergedCutCells.Batch313.certificate3759,MergedCutCells.Batch313.certificate3760], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3759,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3760,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1030 : ∀ c∈certificate1030.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3758,MergedCutCells.Batch313.certificate3759,MergedCutCells.Batch313.certificate3760], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1030 : ∀ c∈certificate1030.cells, c.population=certificate1030.population := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3758,MergedCutCells.Batch313.certificate3759,MergedCutCells.Batch313.certificate3760], c.population=PopulationCertificates.Batch034.certificate686
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1030 {x : ℝ} (hx : certificate1030.interval.Contains x) : ∃ c∈certificate1030.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1030 numericValid1030 hx

def certificate1031 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate687,PopulationCertificates.Batch034.certificate687,[MergedCutCells.Batch313.certificate3761,MergedCutCells.Batch313.certificate3762],(2131843478987705177/125000000000000000),none,(1/2),(4377417654416081713/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1031 : certificate1031.NumericValid := by decide +kernel
theorem cellsSound1031 : ∀ c∈certificate1031.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3761,MergedCutCells.Batch313.certificate3762], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3761,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.sound3762,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1031 : ∀ c∈certificate1031.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3761,MergedCutCells.Batch313.certificate3762], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3761,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch313.numericValid3762,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1031 : ∀ c∈certificate1031.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3761,MergedCutCells.Batch313.certificate3762], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1031 : ∀ c∈certificate1031.cells, c.population=certificate1031.population := by
  change ∀ c∈[MergedCutCells.Batch313.certificate3761,MergedCutCells.Batch313.certificate3762], c.population=PopulationCertificates.Batch034.certificate687
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1031 {x : ℝ} (hx : certificate1031.interval.Contains x) : ∃ c∈certificate1031.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1031 numericValid1031 hx

end Cycle12.MergedCutGroups.Batch085
