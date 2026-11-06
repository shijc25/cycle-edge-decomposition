import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch030
import Cycle12.MergedCutCells.Batch279
import Cycle12.MergedCutCells.Batch280
import Cycle12.MergedCutCells.Batch281
import Cycle12.MergedCutCells.Batch282
import Cycle12.MergedCutCells.Batch283
import Cycle12.PopulationCertificates.Batch030

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch076

def certificate912 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate608,PopulationCertificates.Batch030.certificate608,[MergedCutCells.Batch279.certificate3355,MergedCutCells.Batch279.certificate3356,MergedCutCells.Batch279.certificate3357],(213697793235496697/250000000000000000),(some (546932877/500000000)),(1/2),(796552139178341539/500000000000000000),(some (66919504920203779/200000000000000000)),(some (104378108535081541/1000000000000000000))⟩
theorem numericValid912 : certificate912.NumericValid := by decide +kernel
theorem cellsSound912 : ∀ c∈certificate912.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3355,MergedCutCells.Batch279.certificate3356,MergedCutCells.Batch279.certificate3357], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3355,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3357,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric912 : ∀ c∈certificate912.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3355,MergedCutCells.Batch279.certificate3356,MergedCutCells.Batch279.certificate3357], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3355,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3357,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid912 : ∀ c∈certificate912.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3355,MergedCutCells.Batch279.certificate3356,MergedCutCells.Batch279.certificate3357], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid305,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid305,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid305,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches912 : ∀ c∈certificate912.cells, c.population=certificate912.population := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3355,MergedCutCells.Batch279.certificate3356,MergedCutCells.Batch279.certificate3357], c.population=PopulationCertificates.Batch030.certificate608
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers912 {x : ℝ} (hx : certificate912.interval.Contains x) : ∃ c∈certificate912.cells, c.region.interval.Contains x := rat_cut_group_covers certificate912 numericValid912 hx

def certificate913 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate608,PopulationCertificates.Batch030.certificate608,[MergedCutCells.Batch279.certificate3358,MergedCutCells.Batch279.certificate3359,MergedCutCells.Batch280.certificate3360,MergedCutCells.Batch280.certificate3361,MergedCutCells.Batch280.certificate3362,MergedCutCells.Batch280.certificate3363],(546932877/500000000),none,(1/2),(311600207604054403/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid913 : certificate913.NumericValid := by decide +kernel
theorem cellsSound913 : ∀ c∈certificate913.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3358,MergedCutCells.Batch279.certificate3359,MergedCutCells.Batch280.certificate3360,MergedCutCells.Batch280.certificate3361,MergedCutCells.Batch280.certificate3362,MergedCutCells.Batch280.certificate3363], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3359,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3360,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3362,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3363,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric913 : ∀ c∈certificate913.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3358,MergedCutCells.Batch279.certificate3359,MergedCutCells.Batch280.certificate3360,MergedCutCells.Batch280.certificate3361,MergedCutCells.Batch280.certificate3362,MergedCutCells.Batch280.certificate3363], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3359,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3360,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3362,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3363,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid913 : ∀ c∈certificate913.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3358,MergedCutCells.Batch279.certificate3359,MergedCutCells.Batch280.certificate3360,MergedCutCells.Batch280.certificate3361,MergedCutCells.Batch280.certificate3362,MergedCutCells.Batch280.certificate3363], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches913 : ∀ c∈certificate913.cells, c.population=certificate913.population := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3358,MergedCutCells.Batch279.certificate3359,MergedCutCells.Batch280.certificate3360,MergedCutCells.Batch280.certificate3361,MergedCutCells.Batch280.certificate3362,MergedCutCells.Batch280.certificate3363], c.population=PopulationCertificates.Batch030.certificate608
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers913 {x : ℝ} (hx : certificate913.interval.Contains x) : ∃ c∈certificate913.cells, c.region.interval.Contains x := rat_cut_group_covers certificate913 numericValid913 hx

def certificate914 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate609,PopulationCertificates.Batch030.certificate609,[MergedCutCells.Batch280.certificate3364,MergedCutCells.Batch280.certificate3365,MergedCutCells.Batch280.certificate3366,MergedCutCells.Batch280.certificate3367],(9538614917269786373/1000000000000000000),none,(1/2),(1789220812281121989/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid914 : certificate914.NumericValid := by decide +kernel
theorem cellsSound914 : ∀ c∈certificate914.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3364,MergedCutCells.Batch280.certificate3365,MergedCutCells.Batch280.certificate3366,MergedCutCells.Batch280.certificate3367], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3365,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3366,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3367,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric914 : ∀ c∈certificate914.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3364,MergedCutCells.Batch280.certificate3365,MergedCutCells.Batch280.certificate3366,MergedCutCells.Batch280.certificate3367], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3365,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3366,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3367,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid914 : ∀ c∈certificate914.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3364,MergedCutCells.Batch280.certificate3365,MergedCutCells.Batch280.certificate3366,MergedCutCells.Batch280.certificate3367], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches914 : ∀ c∈certificate914.cells, c.population=certificate914.population := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3364,MergedCutCells.Batch280.certificate3365,MergedCutCells.Batch280.certificate3366,MergedCutCells.Batch280.certificate3367], c.population=PopulationCertificates.Batch030.certificate609
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers914 {x : ℝ} (hx : certificate914.interval.Contains x) : ∃ c∈certificate914.cells, c.region.interval.Contains x := rat_cut_group_covers certificate914 numericValid914 hx

def certificate915 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate610,PopulationCertificates.Batch030.certificate610,[MergedCutCells.Batch280.certificate3368,MergedCutCells.Batch280.certificate3369,MergedCutCells.Batch280.certificate3370],(430165155086650893/500000000000000000),(some (550273917/500000000)),(1/2),(1655993525093491881/1000000000000000000),(some (84735201208549307/250000000000000000)),(some (106408914181029927/1000000000000000000))⟩
theorem numericValid915 : certificate915.NumericValid := by decide +kernel
theorem cellsSound915 : ∀ c∈certificate915.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3368,MergedCutCells.Batch280.certificate3369,MergedCutCells.Batch280.certificate3370], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3369,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3370,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric915 : ∀ c∈certificate915.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3368,MergedCutCells.Batch280.certificate3369,MergedCutCells.Batch280.certificate3370], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3369,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3370,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid915 : ∀ c∈certificate915.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3368,MergedCutCells.Batch280.certificate3369,MergedCutCells.Batch280.certificate3370], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid306,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid306,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid306,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches915 : ∀ c∈certificate915.cells, c.population=certificate915.population := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3368,MergedCutCells.Batch280.certificate3369,MergedCutCells.Batch280.certificate3370], c.population=PopulationCertificates.Batch030.certificate610
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers915 {x : ℝ} (hx : certificate915.interval.Contains x) : ∃ c∈certificate915.cells, c.region.interval.Contains x := rat_cut_group_covers certificate915 numericValid915 hx

def certificate916 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate610,PopulationCertificates.Batch030.certificate610,[MergedCutCells.Batch280.certificate3371,MergedCutCells.Batch281.certificate3372,MergedCutCells.Batch281.certificate3373,MergedCutCells.Batch281.certificate3374,MergedCutCells.Batch281.certificate3375],(550273917/500000000),none,(1/2),(810630281238802011/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid916 : certificate916.NumericValid := by decide +kernel
theorem cellsSound916 : ∀ c∈certificate916.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3371,MergedCutCells.Batch281.certificate3372,MergedCutCells.Batch281.certificate3373,MergedCutCells.Batch281.certificate3374,MergedCutCells.Batch281.certificate3375], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.sound3371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3372,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3373,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3375,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric916 : ∀ c∈certificate916.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3371,MergedCutCells.Batch281.certificate3372,MergedCutCells.Batch281.certificate3373,MergedCutCells.Batch281.certificate3374,MergedCutCells.Batch281.certificate3375], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch280.numericValid3371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3372,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3373,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3375,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid916 : ∀ c∈certificate916.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3371,MergedCutCells.Batch281.certificate3372,MergedCutCells.Batch281.certificate3373,MergedCutCells.Batch281.certificate3374,MergedCutCells.Batch281.certificate3375], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches916 : ∀ c∈certificate916.cells, c.population=certificate916.population := by
  change ∀ c∈[MergedCutCells.Batch280.certificate3371,MergedCutCells.Batch281.certificate3372,MergedCutCells.Batch281.certificate3373,MergedCutCells.Batch281.certificate3374,MergedCutCells.Batch281.certificate3375], c.population=PopulationCertificates.Batch030.certificate610
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers916 {x : ℝ} (hx : certificate916.interval.Contains x) : ∃ c∈certificate916.cells, c.region.interval.Contains x := rat_cut_group_covers certificate916 numericValid916 hx

def certificate917 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate611,PopulationCertificates.Batch030.certificate611,[MergedCutCells.Batch281.certificate3376,MergedCutCells.Batch281.certificate3377,MergedCutCells.Batch281.certificate3378],(9435637587884634693/1000000000000000000),none,(1/2),(7207170055402056037/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid917 : certificate917.NumericValid := by decide +kernel
theorem cellsSound917 : ∀ c∈certificate917.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3376,MergedCutCells.Batch281.certificate3377,MergedCutCells.Batch281.certificate3378], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3377,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3378,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric917 : ∀ c∈certificate917.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3376,MergedCutCells.Batch281.certificate3377,MergedCutCells.Batch281.certificate3378], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3377,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3378,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid917 : ∀ c∈certificate917.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3376,MergedCutCells.Batch281.certificate3377,MergedCutCells.Batch281.certificate3378], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches917 : ∀ c∈certificate917.cells, c.population=certificate917.population := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3376,MergedCutCells.Batch281.certificate3377,MergedCutCells.Batch281.certificate3378], c.population=PopulationCertificates.Batch030.certificate611
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers917 {x : ℝ} (hx : certificate917.interval.Contains x) : ∃ c∈certificate917.cells, c.region.interval.Contains x := rat_cut_group_covers certificate917 numericValid917 hx

def certificate918 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate612,PopulationCertificates.Batch030.certificate612,[MergedCutCells.Batch281.certificate3379,MergedCutCells.Batch281.certificate3380,MergedCutCells.Batch281.certificate3381],(216055922401772649/250000000000000000),(some (552621551/500000000)),(1/2),(42513623520534891/25000000000000000),(some (85831645070259407/250000000000000000)),(some (54240241553286131/500000000000000000))⟩
theorem numericValid918 : certificate918.NumericValid := by decide +kernel
theorem cellsSound918 : ∀ c∈certificate918.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3379,MergedCutCells.Batch281.certificate3380,MergedCutCells.Batch281.certificate3381], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3379,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3380,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3381,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric918 : ∀ c∈certificate918.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3379,MergedCutCells.Batch281.certificate3380,MergedCutCells.Batch281.certificate3381], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3379,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3380,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3381,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid918 : ∀ c∈certificate918.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3379,MergedCutCells.Batch281.certificate3380,MergedCutCells.Batch281.certificate3381], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid307,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid307,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid307,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches918 : ∀ c∈certificate918.cells, c.population=certificate918.population := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3379,MergedCutCells.Batch281.certificate3380,MergedCutCells.Batch281.certificate3381], c.population=PopulationCertificates.Batch030.certificate612
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers918 {x : ℝ} (hx : certificate918.interval.Contains x) : ∃ c∈certificate918.cells, c.region.interval.Contains x := rat_cut_group_covers certificate918 numericValid918 hx

def certificate919 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate612,PopulationCertificates.Batch030.certificate612,[MergedCutCells.Batch281.certificate3382,MergedCutCells.Batch281.certificate3383,MergedCutCells.Batch282.certificate3384,MergedCutCells.Batch282.certificate3385,MergedCutCells.Batch282.certificate3386],(552621551/500000000),none,(1/2),(20826213489959681/12500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid919 : certificate919.NumericValid := by decide +kernel
theorem cellsSound919 : ∀ c∈certificate919.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3382,MergedCutCells.Batch281.certificate3383,MergedCutCells.Batch282.certificate3384,MergedCutCells.Batch282.certificate3385,MergedCutCells.Batch282.certificate3386], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3382,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.sound3383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3385,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3386,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric919 : ∀ c∈certificate919.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3382,MergedCutCells.Batch281.certificate3383,MergedCutCells.Batch282.certificate3384,MergedCutCells.Batch282.certificate3385,MergedCutCells.Batch282.certificate3386], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3382,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch281.numericValid3383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3385,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3386,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid919 : ∀ c∈certificate919.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3382,MergedCutCells.Batch281.certificate3383,MergedCutCells.Batch282.certificate3384,MergedCutCells.Batch282.certificate3385,MergedCutCells.Batch282.certificate3386], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches919 : ∀ c∈certificate919.cells, c.population=certificate919.population := by
  change ∀ c∈[MergedCutCells.Batch281.certificate3382,MergedCutCells.Batch281.certificate3383,MergedCutCells.Batch282.certificate3384,MergedCutCells.Batch282.certificate3385,MergedCutCells.Batch282.certificate3386], c.population=PopulationCertificates.Batch030.certificate612
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers919 {x : ℝ} (hx : certificate919.interval.Contains x) : ∃ c∈certificate919.cells, c.region.interval.Contains x := rat_cut_group_covers certificate919 numericValid919 hx

def certificate920 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate613,PopulationCertificates.Batch030.certificate613,[MergedCutCells.Batch282.certificate3387,MergedCutCells.Batch282.certificate3388,MergedCutCells.Batch282.certificate3389],(1184105405270456511/125000000000000000),none,(1/2),(3649683495206767013/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid920 : certificate920.NumericValid := by decide +kernel
theorem cellsSound920 : ∀ c∈certificate920.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3387,MergedCutCells.Batch282.certificate3388,MergedCutCells.Batch282.certificate3389], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3387,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3388,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3389,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric920 : ∀ c∈certificate920.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3387,MergedCutCells.Batch282.certificate3388,MergedCutCells.Batch282.certificate3389], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3387,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3388,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3389,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid920 : ∀ c∈certificate920.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3387,MergedCutCells.Batch282.certificate3388,MergedCutCells.Batch282.certificate3389], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches920 : ∀ c∈certificate920.cells, c.population=certificate920.population := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3387,MergedCutCells.Batch282.certificate3388,MergedCutCells.Batch282.certificate3389], c.population=PopulationCertificates.Batch030.certificate613
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers920 {x : ℝ} (hx : certificate920.interval.Contains x) : ∃ c∈certificate920.cells, c.region.interval.Contains x := rat_cut_group_covers certificate920 numericValid920 hx

def certificate921 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate614,PopulationCertificates.Batch030.certificate614,[MergedCutCells.Batch282.certificate3390,MergedCutCells.Batch282.certificate3391,MergedCutCells.Batch282.certificate3392],(434767083932915261/500000000000000000),(some (542335849/500000000)),(1/2),(1769049185416800407/1000000000000000000),(some (345813747764407461/1000000000000000000)),(some (54832352634944713/500000000000000000))⟩
theorem numericValid921 : certificate921.NumericValid := by decide +kernel
theorem cellsSound921 : ∀ c∈certificate921.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3390,MergedCutCells.Batch282.certificate3391,MergedCutCells.Batch282.certificate3392], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3390,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3391,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3392,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric921 : ∀ c∈certificate921.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3390,MergedCutCells.Batch282.certificate3391,MergedCutCells.Batch282.certificate3392], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3390,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3391,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3392,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid921 : ∀ c∈certificate921.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3390,MergedCutCells.Batch282.certificate3391,MergedCutCells.Batch282.certificate3392], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid308,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid308,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid308,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches921 : ∀ c∈certificate921.cells, c.population=certificate921.population := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3390,MergedCutCells.Batch282.certificate3391,MergedCutCells.Batch282.certificate3392], c.population=PopulationCertificates.Batch030.certificate614
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers921 {x : ℝ} (hx : certificate921.interval.Contains x) : ∃ c∈certificate921.cells, c.region.interval.Contains x := rat_cut_group_covers certificate921 numericValid921 hx

def certificate922 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate614,PopulationCertificates.Batch030.certificate614,[MergedCutCells.Batch282.certificate3393,MergedCutCells.Batch282.certificate3394,MergedCutCells.Batch282.certificate3395,MergedCutCells.Batch283.certificate3396,MergedCutCells.Batch283.certificate3397,MergedCutCells.Batch283.certificate3398,MergedCutCells.Batch283.certificate3399],(542335849/500000000),none,(1/2),(865903545136465281/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid922 : certificate922.NumericValid := by decide +kernel
theorem cellsSound922 : ∀ c∈certificate922.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3393,MergedCutCells.Batch282.certificate3394,MergedCutCells.Batch282.certificate3395,MergedCutCells.Batch283.certificate3396,MergedCutCells.Batch283.certificate3397,MergedCutCells.Batch283.certificate3398,MergedCutCells.Batch283.certificate3399], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3393,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3394,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.sound3395,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3397,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3398,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3399,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric922 : ∀ c∈certificate922.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3393,MergedCutCells.Batch282.certificate3394,MergedCutCells.Batch282.certificate3395,MergedCutCells.Batch283.certificate3396,MergedCutCells.Batch283.certificate3397,MergedCutCells.Batch283.certificate3398,MergedCutCells.Batch283.certificate3399], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3393,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3394,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch282.numericValid3395,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3397,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3398,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3399,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid922 : ∀ c∈certificate922.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3393,MergedCutCells.Batch282.certificate3394,MergedCutCells.Batch282.certificate3395,MergedCutCells.Batch283.certificate3396,MergedCutCells.Batch283.certificate3397,MergedCutCells.Batch283.certificate3398,MergedCutCells.Batch283.certificate3399], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches922 : ∀ c∈certificate922.cells, c.population=certificate922.population := by
  change ∀ c∈[MergedCutCells.Batch282.certificate3393,MergedCutCells.Batch282.certificate3394,MergedCutCells.Batch282.certificate3395,MergedCutCells.Batch283.certificate3396,MergedCutCells.Batch283.certificate3397,MergedCutCells.Batch283.certificate3398,MergedCutCells.Batch283.certificate3399], c.population=PopulationCertificates.Batch030.certificate614
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers922 {x : ℝ} (hx : certificate922.interval.Contains x) : ∃ c∈certificate922.cells, c.region.interval.Contains x := rat_cut_group_covers certificate922 numericValid922 hx

def certificate923 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate615,PopulationCertificates.Batch030.certificate615,[MergedCutCells.Batch283.certificate3400,MergedCutCells.Batch283.certificate3401,MergedCutCells.Batch283.certificate3402],(4685730833479817321/500000000000000000),none,(1/2),(7352568155048158293/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid923 : certificate923.NumericValid := by decide +kernel
theorem cellsSound923 : ∀ c∈certificate923.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3400,MergedCutCells.Batch283.certificate3401,MergedCutCells.Batch283.certificate3402], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3400,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3401,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3402,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric923 : ∀ c∈certificate923.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3400,MergedCutCells.Batch283.certificate3401,MergedCutCells.Batch283.certificate3402], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3400,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3401,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3402,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid923 : ∀ c∈certificate923.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3400,MergedCutCells.Batch283.certificate3401,MergedCutCells.Batch283.certificate3402], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches923 : ∀ c∈certificate923.cells, c.population=certificate923.population := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3400,MergedCutCells.Batch283.certificate3401,MergedCutCells.Batch283.certificate3402], c.population=PopulationCertificates.Batch030.certificate615
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers923 {x : ℝ} (hx : certificate923.interval.Contains x) : ∃ c∈certificate923.cells, c.region.interval.Contains x := rat_cut_group_covers certificate923 numericValid923 hx

end Cycle12.MergedCutGroups.Batch076
