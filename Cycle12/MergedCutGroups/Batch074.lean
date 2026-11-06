import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch029
import Cycle12.MergedCutCells.Batch271
import Cycle12.MergedCutCells.Batch272
import Cycle12.MergedCutCells.Batch273
import Cycle12.MergedCutCells.Batch274
import Cycle12.MergedCutCells.Batch275
import Cycle12.PopulationCertificates.Batch029

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch074

def certificate888 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate592,PopulationCertificates.Batch029.certificate592,[MergedCutCells.Batch271.certificate3257,MergedCutCells.Batch271.certificate3258,MergedCutCells.Batch271.certificate3259],(201001214618003199/250000000000000000),(some (1106853147/1000000000)),(1/2),(541966291468964019/500000000000000000),(some (296562303143388921/1000000000000000000)),(some (87434773479867019/1000000000000000000))⟩
theorem numericValid888 : certificate888.NumericValid := by decide +kernel
theorem cellsSound888 : ∀ c∈certificate888.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3257,MergedCutCells.Batch271.certificate3258,MergedCutCells.Batch271.certificate3259], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3258,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3259,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric888 : ∀ c∈certificate888.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3257,MergedCutCells.Batch271.certificate3258,MergedCutCells.Batch271.certificate3259], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3258,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3259,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid888 : ∀ c∈certificate888.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3257,MergedCutCells.Batch271.certificate3258,MergedCutCells.Batch271.certificate3259], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid297,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid297,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid297,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches888 : ∀ c∈certificate888.cells, c.population=certificate888.population := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3257,MergedCutCells.Batch271.certificate3258,MergedCutCells.Batch271.certificate3259], c.population=PopulationCertificates.Batch029.certificate592
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers888 {x : ℝ} (hx : certificate888.interval.Contains x) : ∃ c∈certificate888.cells, c.region.interval.Contains x := rat_cut_group_covers certificate888 numericValid888 hx

def certificate889 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate592,PopulationCertificates.Batch029.certificate592,[MergedCutCells.Batch271.certificate3260,MergedCutCells.Batch271.certificate3261,MergedCutCells.Batch271.certificate3262,MergedCutCells.Batch271.certificate3263,MergedCutCells.Batch272.certificate3264],(1106853147/1000000000),none,(1/2),(105636111510609091/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid889 : certificate889.NumericValid := by decide +kernel
theorem cellsSound889 : ∀ c∈certificate889.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3260,MergedCutCells.Batch271.certificate3261,MergedCutCells.Batch271.certificate3262,MergedCutCells.Batch271.certificate3263,MergedCutCells.Batch272.certificate3264], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3260,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3262,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3263,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3264,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric889 : ∀ c∈certificate889.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3260,MergedCutCells.Batch271.certificate3261,MergedCutCells.Batch271.certificate3262,MergedCutCells.Batch271.certificate3263,MergedCutCells.Batch272.certificate3264], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3260,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3262,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3263,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3264,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid889 : ∀ c∈certificate889.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3260,MergedCutCells.Batch271.certificate3261,MergedCutCells.Batch271.certificate3262,MergedCutCells.Batch271.certificate3263,MergedCutCells.Batch272.certificate3264], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches889 : ∀ c∈certificate889.cells, c.population=certificate889.population := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3260,MergedCutCells.Batch271.certificate3261,MergedCutCells.Batch271.certificate3262,MergedCutCells.Batch271.certificate3263,MergedCutCells.Batch272.certificate3264], c.population=PopulationCertificates.Batch029.certificate592
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers889 {x : ℝ} (hx : certificate889.interval.Contains x) : ∃ c∈certificate889.cells, c.region.interval.Contains x := rat_cut_group_covers certificate889 numericValid889 hx

def certificate890 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate593,PopulationCertificates.Batch029.certificate593,[MergedCutCells.Batch272.certificate3265,MergedCutCells.Batch272.certificate3266,MergedCutCells.Batch272.certificate3267],(1239920520969591451/125000000000000000),none,(1/2),(1287917086306758419/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid890 : certificate890.NumericValid := by decide +kernel
theorem cellsSound890 : ∀ c∈certificate890.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3265,MergedCutCells.Batch272.certificate3266,MergedCutCells.Batch272.certificate3267], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3265,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3266,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3267,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric890 : ∀ c∈certificate890.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3265,MergedCutCells.Batch272.certificate3266,MergedCutCells.Batch272.certificate3267], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3265,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3266,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3267,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid890 : ∀ c∈certificate890.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3265,MergedCutCells.Batch272.certificate3266,MergedCutCells.Batch272.certificate3267], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches890 : ∀ c∈certificate890.cells, c.population=certificate890.population := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3265,MergedCutCells.Batch272.certificate3266,MergedCutCells.Batch272.certificate3267], c.population=PopulationCertificates.Batch029.certificate593
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers890 {x : ℝ} (hx : certificate890.interval.Contains x) : ∃ c∈certificate890.cells, c.region.interval.Contains x := rat_cut_group_covers certificate890 numericValid890 hx

def certificate891 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate594,PopulationCertificates.Batch029.certificate594,[MergedCutCells.Batch272.certificate3268,MergedCutCells.Batch272.certificate3269,MergedCutCells.Batch272.certificate3270],(404599923130934771/500000000000000000),(some (217294741/200000000)),(1/2),(1154388625761478161/1000000000000000000),(some (298735303710475479/1000000000000000000)),(some (22090894744377449/250000000000000000))⟩
theorem numericValid891 : certificate891.NumericValid := by decide +kernel
theorem cellsSound891 : ∀ c∈certificate891.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3268,MergedCutCells.Batch272.certificate3269,MergedCutCells.Batch272.certificate3270], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3268,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3270,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric891 : ∀ c∈certificate891.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3268,MergedCutCells.Batch272.certificate3269,MergedCutCells.Batch272.certificate3270], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3268,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3270,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid891 : ∀ c∈certificate891.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3268,MergedCutCells.Batch272.certificate3269,MergedCutCells.Batch272.certificate3270], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid298,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid298,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid298,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches891 : ∀ c∈certificate891.cells, c.population=certificate891.population := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3268,MergedCutCells.Batch272.certificate3269,MergedCutCells.Batch272.certificate3270], c.population=PopulationCertificates.Batch029.certificate594
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers891 {x : ℝ} (hx : certificate891.interval.Contains x) : ∃ c∈certificate891.cells, c.region.interval.Contains x := rat_cut_group_covers certificate891 numericValid891 hx

def certificate892 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate594,PopulationCertificates.Batch029.certificate594,[MergedCutCells.Batch272.certificate3271,MergedCutCells.Batch272.certificate3272,MergedCutCells.Batch272.certificate3273,MergedCutCells.Batch272.certificate3274,MergedCutCells.Batch272.certificate3275,MergedCutCells.Batch273.certificate3276,MergedCutCells.Batch273.certificate3277,MergedCutCells.Batch273.certificate3278],(217294741/200000000),none,(1/2),(567987563763927753/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid892 : certificate892.NumericValid := by decide +kernel
theorem cellsSound892 : ∀ c∈certificate892.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3271,MergedCutCells.Batch272.certificate3272,MergedCutCells.Batch272.certificate3273,MergedCutCells.Batch272.certificate3274,MergedCutCells.Batch272.certificate3275,MergedCutCells.Batch273.certificate3276,MergedCutCells.Batch273.certificate3277,MergedCutCells.Batch273.certificate3278], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3271,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3272,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3273,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3274,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.sound3275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3276,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3277,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3278,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric892 : ∀ c∈certificate892.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3271,MergedCutCells.Batch272.certificate3272,MergedCutCells.Batch272.certificate3273,MergedCutCells.Batch272.certificate3274,MergedCutCells.Batch272.certificate3275,MergedCutCells.Batch273.certificate3276,MergedCutCells.Batch273.certificate3277,MergedCutCells.Batch273.certificate3278], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3271,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3272,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3273,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3274,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch272.numericValid3275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3276,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3277,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3278,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid892 : ∀ c∈certificate892.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3271,MergedCutCells.Batch272.certificate3272,MergedCutCells.Batch272.certificate3273,MergedCutCells.Batch272.certificate3274,MergedCutCells.Batch272.certificate3275,MergedCutCells.Batch273.certificate3276,MergedCutCells.Batch273.certificate3277,MergedCutCells.Batch273.certificate3278], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches892 : ∀ c∈certificate892.cells, c.population=certificate892.population := by
  change ∀ c∈[MergedCutCells.Batch272.certificate3271,MergedCutCells.Batch272.certificate3272,MergedCutCells.Batch272.certificate3273,MergedCutCells.Batch272.certificate3274,MergedCutCells.Batch272.certificate3275,MergedCutCells.Batch273.certificate3276,MergedCutCells.Batch273.certificate3277,MergedCutCells.Batch273.certificate3278], c.population=PopulationCertificates.Batch029.certificate594
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers892 {x : ℝ} (hx : certificate892.interval.Contains x) : ∃ c∈certificate892.cells, c.region.interval.Contains x := rat_cut_group_covers certificate892 numericValid892 hx

def certificate893 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate595,PopulationCertificates.Batch029.certificate595,[MergedCutCells.Batch273.certificate3279,MergedCutCells.Batch273.certificate3280,MergedCutCells.Batch273.certificate3281],(989175396307718913/100000000000000000),none,(1/2),(6583190308924428201/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid893 : certificate893.NumericValid := by decide +kernel
theorem cellsSound893 : ∀ c∈certificate893.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3279,MergedCutCells.Batch273.certificate3280,MergedCutCells.Batch273.certificate3281], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3279,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3280,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3281,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric893 : ∀ c∈certificate893.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3279,MergedCutCells.Batch273.certificate3280,MergedCutCells.Batch273.certificate3281], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3279,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3280,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3281,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid893 : ∀ c∈certificate893.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3279,MergedCutCells.Batch273.certificate3280,MergedCutCells.Batch273.certificate3281], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches893 : ∀ c∈certificate893.cells, c.population=certificate893.population := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3279,MergedCutCells.Batch273.certificate3280,MergedCutCells.Batch273.certificate3281], c.population=PopulationCertificates.Batch029.certificate595
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers893 {x : ℝ} (hx : certificate893.interval.Contains x) : ∃ c∈certificate893.cells, c.region.interval.Contains x := rat_cut_group_covers certificate893 numericValid893 hx

def certificate894 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate596,PopulationCertificates.Batch029.certificate596,[MergedCutCells.Batch273.certificate3282,MergedCutCells.Batch273.certificate3283,MergedCutCells.Batch273.certificate3284],(203824361674998757/250000000000000000),(some (219185301/200000000)),(1/2),(119700104060914261/100000000000000000),(some (151716453118498079/500000000000000000)),(some (90387268344052403/1000000000000000000))⟩
theorem numericValid894 : certificate894.NumericValid := by decide +kernel
theorem cellsSound894 : ∀ c∈certificate894.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3282,MergedCutCells.Batch273.certificate3283,MergedCutCells.Batch273.certificate3284], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3282,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3283,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3284,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric894 : ∀ c∈certificate894.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3282,MergedCutCells.Batch273.certificate3283,MergedCutCells.Batch273.certificate3284], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3282,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3283,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3284,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid894 : ∀ c∈certificate894.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3282,MergedCutCells.Batch273.certificate3283,MergedCutCells.Batch273.certificate3284], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid299,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid299,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid299,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches894 : ∀ c∈certificate894.cells, c.population=certificate894.population := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3282,MergedCutCells.Batch273.certificate3283,MergedCutCells.Batch273.certificate3284], c.population=PopulationCertificates.Batch029.certificate596
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers894 {x : ℝ} (hx : certificate894.interval.Contains x) : ∃ c∈certificate894.cells, c.region.interval.Contains x := rat_cut_group_covers certificate894 numericValid894 hx

def certificate895 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate596,PopulationCertificates.Batch029.certificate596,[MergedCutCells.Batch273.certificate3285,MergedCutCells.Batch273.certificate3286,MergedCutCells.Batch273.certificate3287,MergedCutCells.Batch274.certificate3288,MergedCutCells.Batch274.certificate3289,MergedCutCells.Batch274.certificate3290],(219185301/200000000),none,(1/2),(1171329804079399069/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid895 : certificate895.NumericValid := by decide +kernel
theorem cellsSound895 : ∀ c∈certificate895.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3285,MergedCutCells.Batch273.certificate3286,MergedCutCells.Batch273.certificate3287,MergedCutCells.Batch274.certificate3288,MergedCutCells.Batch274.certificate3289,MergedCutCells.Batch274.certificate3290], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3286,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.sound3287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3288,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3289,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3290,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric895 : ∀ c∈certificate895.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3285,MergedCutCells.Batch273.certificate3286,MergedCutCells.Batch273.certificate3287,MergedCutCells.Batch274.certificate3288,MergedCutCells.Batch274.certificate3289,MergedCutCells.Batch274.certificate3290], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3286,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch273.numericValid3287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3288,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3289,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3290,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid895 : ∀ c∈certificate895.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3285,MergedCutCells.Batch273.certificate3286,MergedCutCells.Batch273.certificate3287,MergedCutCells.Batch274.certificate3288,MergedCutCells.Batch274.certificate3289,MergedCutCells.Batch274.certificate3290], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches895 : ∀ c∈certificate895.cells, c.population=certificate895.population := by
  change ∀ c∈[MergedCutCells.Batch273.certificate3285,MergedCutCells.Batch273.certificate3286,MergedCutCells.Batch273.certificate3287,MergedCutCells.Batch274.certificate3288,MergedCutCells.Batch274.certificate3289,MergedCutCells.Batch274.certificate3290], c.population=PopulationCertificates.Batch029.certificate596
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers895 {x : ℝ} (hx : certificate895.interval.Contains x) : ∃ c∈certificate895.cells, c.region.interval.Contains x := rat_cut_group_covers certificate895 numericValid895 hx

def certificate896 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate597,PopulationCertificates.Batch029.certificate597,[MergedCutCells.Batch274.certificate3291,MergedCutCells.Batch274.certificate3292,MergedCutCells.Batch274.certificate3293,MergedCutCells.Batch274.certificate3294],(9822105150003026189/1000000000000000000),none,(1/2),(1655915513351576123/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid896 : certificate896.NumericValid := by decide +kernel
theorem cellsSound896 : ∀ c∈certificate896.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3291,MergedCutCells.Batch274.certificate3292,MergedCutCells.Batch274.certificate3293,MergedCutCells.Batch274.certificate3294], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3292,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3294,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric896 : ∀ c∈certificate896.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3291,MergedCutCells.Batch274.certificate3292,MergedCutCells.Batch274.certificate3293,MergedCutCells.Batch274.certificate3294], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3292,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3294,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid896 : ∀ c∈certificate896.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3291,MergedCutCells.Batch274.certificate3292,MergedCutCells.Batch274.certificate3293,MergedCutCells.Batch274.certificate3294], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches896 : ∀ c∈certificate896.cells, c.population=certificate896.population := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3291,MergedCutCells.Batch274.certificate3292,MergedCutCells.Batch274.certificate3293,MergedCutCells.Batch274.certificate3294], c.population=PopulationCertificates.Batch029.certificate597
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers896 {x : ℝ} (hx : certificate896.interval.Contains x) : ∃ c∈certificate896.cells, c.region.interval.Contains x := rat_cut_group_covers certificate896 numericValid896 hx

def certificate897 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate598,PopulationCertificates.Batch029.certificate598,[MergedCutCells.Batch274.certificate3295,MergedCutCells.Batch274.certificate3296,MergedCutCells.Batch274.certificate3297],(102829973833318257/125000000000000000),(some (1105124191/1000000000)),(1/2),(62261951114145579/50000000000000000),(some (156104932369152139/500000000000000000)),(some (47113474562935679/500000000000000000))⟩
theorem numericValid897 : certificate897.NumericValid := by decide +kernel
theorem cellsSound897 : ∀ c∈certificate897.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3295,MergedCutCells.Batch274.certificate3296,MergedCutCells.Batch274.certificate3297], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3296,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3297,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric897 : ∀ c∈certificate897.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3295,MergedCutCells.Batch274.certificate3296,MergedCutCells.Batch274.certificate3297], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3296,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3297,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid897 : ∀ c∈certificate897.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3295,MergedCutCells.Batch274.certificate3296,MergedCutCells.Batch274.certificate3297], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid300,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid300,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid300,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches897 : ∀ c∈certificate897.cells, c.population=certificate897.population := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3295,MergedCutCells.Batch274.certificate3296,MergedCutCells.Batch274.certificate3297], c.population=PopulationCertificates.Batch029.certificate598
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers897 {x : ℝ} (hx : certificate897.interval.Contains x) : ∃ c∈certificate897.cells, c.region.interval.Contains x := rat_cut_group_covers certificate897 numericValid897 hx

def certificate898 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate598,PopulationCertificates.Batch029.certificate598,[MergedCutCells.Batch274.certificate3298,MergedCutCells.Batch274.certificate3299,MergedCutCells.Batch275.certificate3300,MergedCutCells.Batch275.certificate3301,MergedCutCells.Batch275.certificate3302],(1105124191/1000000000),none,(1/2),(1212938491671985129/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid898 : certificate898.NumericValid := by decide +kernel
theorem cellsSound898 : ∀ c∈certificate898.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3298,MergedCutCells.Batch274.certificate3299,MergedCutCells.Batch275.certificate3300,MergedCutCells.Batch275.certificate3301,MergedCutCells.Batch275.certificate3302], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3298,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.sound3299,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3300,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3301,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3302,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric898 : ∀ c∈certificate898.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3298,MergedCutCells.Batch274.certificate3299,MergedCutCells.Batch275.certificate3300,MergedCutCells.Batch275.certificate3301,MergedCutCells.Batch275.certificate3302], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3298,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch274.numericValid3299,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3300,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3301,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3302,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid898 : ∀ c∈certificate898.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3298,MergedCutCells.Batch274.certificate3299,MergedCutCells.Batch275.certificate3300,MergedCutCells.Batch275.certificate3301,MergedCutCells.Batch275.certificate3302], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches898 : ∀ c∈certificate898.cells, c.population=certificate898.population := by
  change ∀ c∈[MergedCutCells.Batch274.certificate3298,MergedCutCells.Batch274.certificate3299,MergedCutCells.Batch275.certificate3300,MergedCutCells.Batch275.certificate3301,MergedCutCells.Batch275.certificate3302], c.population=PopulationCertificates.Batch029.certificate598
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers898 {x : ℝ} (hx : certificate898.interval.Contains x) : ∃ c∈certificate898.cells, c.region.interval.Contains x := rat_cut_group_covers certificate898 numericValid898 hx

def certificate899 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate599,PopulationCertificates.Batch029.certificate599,[MergedCutCells.Batch275.certificate3303,MergedCutCells.Batch275.certificate3304,MergedCutCells.Batch275.certificate3305],(153237813697088227/15625000000000000),none,(1/2),(6680949033426418747/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid899 : certificate899.NumericValid := by decide +kernel
theorem cellsSound899 : ∀ c∈certificate899.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3303,MergedCutCells.Batch275.certificate3304,MergedCutCells.Batch275.certificate3305], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3303,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3304,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3305,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric899 : ∀ c∈certificate899.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3303,MergedCutCells.Batch275.certificate3304,MergedCutCells.Batch275.certificate3305], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3303,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3304,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3305,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid899 : ∀ c∈certificate899.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3303,MergedCutCells.Batch275.certificate3304,MergedCutCells.Batch275.certificate3305], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches899 : ∀ c∈certificate899.cells, c.population=certificate899.population := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3303,MergedCutCells.Batch275.certificate3304,MergedCutCells.Batch275.certificate3305], c.population=PopulationCertificates.Batch029.certificate599
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers899 {x : ℝ} (hx : certificate899.interval.Contains x) : ∃ c∈certificate899.cells, c.region.interval.Contains x := rat_cut_group_covers certificate899 numericValid899 hx

end Cycle12.MergedCutGroups.Batch074
