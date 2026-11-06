import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch034
import Cycle12.GeometryCertificates.Batch035
import Cycle12.MergedCutCells.Batch315
import Cycle12.MergedCutCells.Batch316
import Cycle12.MergedCutCells.Batch317
import Cycle12.MergedCutCells.Batch318
import Cycle12.PopulationCertificates.Batch034
import Cycle12.PopulationCertificates.Batch035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch087

def certificate1044 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate696,PopulationCertificates.Batch034.certificate696,[MergedCutCells.Batch315.certificate3791,MergedCutCells.Batch316.certificate3792],(280915065522790267/500000000000000000),(some (316970507/250000000)),(1/2),(45897733397579341/250000000000000000),(some (8085988998199883/500000000000000000)),(some (456789981949581/200000000000000000))⟩
theorem numericValid1044 : certificate1044.NumericValid := by decide +kernel
theorem cellsSound1044 : ∀ c∈certificate1044.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3791,MergedCutCells.Batch316.certificate3792], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.sound3791,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3792,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1044 : ∀ c∈certificate1044.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3791,MergedCutCells.Batch316.certificate3792], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch315.numericValid3791,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3792,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1044 : ∀ c∈certificate1044.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3791,MergedCutCells.Batch316.certificate3792], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid349,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid349,List.forall_mem_nil _⟩⟩
theorem populationMatches1044 : ∀ c∈certificate1044.cells, c.population=certificate1044.population := by
  change ∀ c∈[MergedCutCells.Batch315.certificate3791,MergedCutCells.Batch316.certificate3792], c.population=PopulationCertificates.Batch034.certificate696
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1044 {x : ℝ} (hx : certificate1044.interval.Contains x) : ∃ c∈certificate1044.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1044 numericValid1044 hx

def certificate1045 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate696,PopulationCertificates.Batch034.certificate696,[MergedCutCells.Batch316.certificate3793,MergedCutCells.Batch316.certificate3794,MergedCutCells.Batch316.certificate3795],(316970507/250000000),none,(1/2),(182909101210473841/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1045 : certificate1045.NumericValid := by decide +kernel
theorem cellsSound1045 : ∀ c∈certificate1045.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3793,MergedCutCells.Batch316.certificate3794,MergedCutCells.Batch316.certificate3795], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3793,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3794,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3795,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1045 : ∀ c∈certificate1045.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3793,MergedCutCells.Batch316.certificate3794,MergedCutCells.Batch316.certificate3795], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3793,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3794,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3795,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1045 : ∀ c∈certificate1045.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3793,MergedCutCells.Batch316.certificate3794,MergedCutCells.Batch316.certificate3795], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1045 : ∀ c∈certificate1045.cells, c.population=certificate1045.population := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3793,MergedCutCells.Batch316.certificate3794,MergedCutCells.Batch316.certificate3795], c.population=PopulationCertificates.Batch034.certificate696
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1045 {x : ℝ} (hx : certificate1045.interval.Contains x) : ∃ c∈certificate1045.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1045 numericValid1045 hx

def certificate1046 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate697,PopulationCertificates.Batch034.certificate697,[MergedCutCells.Batch316.certificate3796,MergedCutCells.Batch316.certificate3797],(1790801840224050961/100000000000000000),none,(1/2),(186204029647913371/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1046 : certificate1046.NumericValid := by decide +kernel
theorem cellsSound1046 : ∀ c∈certificate1046.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3796,MergedCutCells.Batch316.certificate3797], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3796,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3797,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1046 : ∀ c∈certificate1046.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3796,MergedCutCells.Batch316.certificate3797], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3796,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3797,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1046 : ∀ c∈certificate1046.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3796,MergedCutCells.Batch316.certificate3797], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1046 : ∀ c∈certificate1046.cells, c.population=certificate1046.population := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3796,MergedCutCells.Batch316.certificate3797], c.population=PopulationCertificates.Batch034.certificate697
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1046 {x : ℝ} (hx : certificate1046.interval.Contains x) : ∃ c∈certificate1046.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1046 numericValid1046 hx

def certificate1047 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate698,PopulationCertificates.Batch034.certificate698,[MergedCutCells.Batch316.certificate3798,MergedCutCells.Batch316.certificate3799],(559480434020852933/1000000000000000000),(some (1263489263/1000000000)),(1/2),(168797164002577843/1000000000000000000),(some (3578619044246443/200000000000000000)),(some (321235481292493/125000000000000000))⟩
theorem numericValid1047 : certificate1047.NumericValid := by decide +kernel
theorem cellsSound1047 : ∀ c∈certificate1047.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3798,MergedCutCells.Batch316.certificate3799], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3798,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3799,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1047 : ∀ c∈certificate1047.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3798,MergedCutCells.Batch316.certificate3799], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3798,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3799,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1047 : ∀ c∈certificate1047.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3798,MergedCutCells.Batch316.certificate3799], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid350,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid350,List.forall_mem_nil _⟩⟩
theorem populationMatches1047 : ∀ c∈certificate1047.cells, c.population=certificate1047.population := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3798,MergedCutCells.Batch316.certificate3799], c.population=PopulationCertificates.Batch034.certificate698
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1047 {x : ℝ} (hx : certificate1047.interval.Contains x) : ∃ c∈certificate1047.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1047 numericValid1047 hx

def certificate1048 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate698,PopulationCertificates.Batch034.certificate698,[MergedCutCells.Batch316.certificate3800,MergedCutCells.Batch316.certificate3801,MergedCutCells.Batch316.certificate3802],(1263489263/1000000000),none,(1/2),(41972243687180947/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1048 : certificate1048.NumericValid := by decide +kernel
theorem cellsSound1048 : ∀ c∈certificate1048.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3800,MergedCutCells.Batch316.certificate3801,MergedCutCells.Batch316.certificate3802], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3800,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3802,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1048 : ∀ c∈certificate1048.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3800,MergedCutCells.Batch316.certificate3801,MergedCutCells.Batch316.certificate3802], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3800,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3802,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1048 : ∀ c∈certificate1048.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3800,MergedCutCells.Batch316.certificate3801,MergedCutCells.Batch316.certificate3802], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1048 : ∀ c∈certificate1048.cells, c.population=certificate1048.population := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3800,MergedCutCells.Batch316.certificate3801,MergedCutCells.Batch316.certificate3802], c.population=PopulationCertificates.Batch034.certificate698
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1048 {x : ℝ} (hx : certificate1048.interval.Contains x) : ∃ c∈certificate1048.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1048 numericValid1048 hx

def certificate1049 : RatCutGroup := ⟨GeometryCertificates.Batch034.certificate699,PopulationCertificates.Batch034.certificate699,[MergedCutCells.Batch316.certificate3803,MergedCutCells.Batch317.certificate3804],(18137765199184925539/1000000000000000000),none,(1/2),(4698733978723455757/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1049 : certificate1049.NumericValid := by decide +kernel
theorem cellsSound1049 : ∀ c∈certificate1049.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3803,MergedCutCells.Batch317.certificate3804], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.sound3803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3804,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1049 : ∀ c∈certificate1049.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3803,MergedCutCells.Batch317.certificate3804], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch316.numericValid3803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3804,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1049 : ∀ c∈certificate1049.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3803,MergedCutCells.Batch317.certificate3804], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1049 : ∀ c∈certificate1049.cells, c.population=certificate1049.population := by
  change ∀ c∈[MergedCutCells.Batch316.certificate3803,MergedCutCells.Batch317.certificate3804], c.population=PopulationCertificates.Batch034.certificate699
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1049 {x : ℝ} (hx : certificate1049.interval.Contains x) : ∃ c∈certificate1049.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1049 numericValid1049 hx

def certificate1050 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate700,PopulationCertificates.Batch035.certificate700,[MergedCutCells.Batch317.certificate3805,MergedCutCells.Batch317.certificate3806],(559622939069303783/1000000000000000000),(some (308235693/250000000)),(1/2),(163267174333033483/1000000000000000000),(some (19557694745963833/1000000000000000000)),(some (285162471686277/100000000000000000))⟩
theorem numericValid1050 : certificate1050.NumericValid := by decide +kernel
theorem cellsSound1050 : ∀ c∈certificate1050.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3805,MergedCutCells.Batch317.certificate3806], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3806,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1050 : ∀ c∈certificate1050.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3805,MergedCutCells.Batch317.certificate3806], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3806,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1050 : ∀ c∈certificate1050.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3805,MergedCutCells.Batch317.certificate3806], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid351,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid351,List.forall_mem_nil _⟩⟩
theorem populationMatches1050 : ∀ c∈certificate1050.cells, c.population=certificate1050.population := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3805,MergedCutCells.Batch317.certificate3806], c.population=PopulationCertificates.Batch035.certificate700
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1050 {x : ℝ} (hx : certificate1050.interval.Contains x) : ∃ c∈certificate1050.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1050 numericValid1050 hx

def certificate1051 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate700,PopulationCertificates.Batch035.certificate700,[MergedCutCells.Batch317.certificate3807,MergedCutCells.Batch317.certificate3808,MergedCutCells.Batch317.certificate3809,MergedCutCells.Batch317.certificate3810],(308235693/250000000),none,(1/2),(6490338633105999/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1051 : certificate1051.NumericValid := by decide +kernel
theorem cellsSound1051 : ∀ c∈certificate1051.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3807,MergedCutCells.Batch317.certificate3808,MergedCutCells.Batch317.certificate3809,MergedCutCells.Batch317.certificate3810], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3808,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3809,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3810,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1051 : ∀ c∈certificate1051.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3807,MergedCutCells.Batch317.certificate3808,MergedCutCells.Batch317.certificate3809,MergedCutCells.Batch317.certificate3810], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3808,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3809,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3810,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1051 : ∀ c∈certificate1051.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3807,MergedCutCells.Batch317.certificate3808,MergedCutCells.Batch317.certificate3809,MergedCutCells.Batch317.certificate3810], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1051 : ∀ c∈certificate1051.cells, c.population=certificate1051.population := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3807,MergedCutCells.Batch317.certificate3808,MergedCutCells.Batch317.certificate3809,MergedCutCells.Batch317.certificate3810], c.population=PopulationCertificates.Batch035.certificate700
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1051 {x : ℝ} (hx : certificate1051.interval.Contains x) : ∃ c∈certificate1051.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1051 numericValid1051 hx

def certificate1052 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate701,PopulationCertificates.Batch035.certificate701,[MergedCutCells.Batch317.certificate3811,MergedCutCells.Batch317.certificate3812],(9176165193320450901/500000000000000000),none,(1/2),(298774659728884649/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1052 : certificate1052.NumericValid := by decide +kernel
theorem cellsSound1052 : ∀ c∈certificate1052.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3811,MergedCutCells.Batch317.certificate3812], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3811,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3812,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1052 : ∀ c∈certificate1052.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3811,MergedCutCells.Batch317.certificate3812], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3811,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3812,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1052 : ∀ c∈certificate1052.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3811,MergedCutCells.Batch317.certificate3812], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1052 : ∀ c∈certificate1052.cells, c.population=certificate1052.population := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3811,MergedCutCells.Batch317.certificate3812], c.population=PopulationCertificates.Batch035.certificate701
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1052 {x : ℝ} (hx : certificate1052.interval.Contains x) : ∃ c∈certificate1052.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1052 numericValid1052 hx

def certificate1053 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate702,PopulationCertificates.Batch035.certificate702,[MergedCutCells.Batch317.certificate3813,MergedCutCells.Batch317.certificate3814],(55991132586645027/100000000000000000),(some (61673611/50000000)),(1/2),(79695242244781653/500000000000000000),(some (409442039184513/20000000000000000)),(some (1504235989406641/500000000000000000))⟩
theorem numericValid1053 : certificate1053.NumericValid := by decide +kernel
theorem cellsSound1053 : ∀ c∈certificate1053.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3813,MergedCutCells.Batch317.certificate3814], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3813,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3814,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1053 : ∀ c∈certificate1053.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3813,MergedCutCells.Batch317.certificate3814], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3813,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3814,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1053 : ∀ c∈certificate1053.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3813,MergedCutCells.Batch317.certificate3814], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid352,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid352,List.forall_mem_nil _⟩⟩
theorem populationMatches1053 : ∀ c∈certificate1053.cells, c.population=certificate1053.population := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3813,MergedCutCells.Batch317.certificate3814], c.population=PopulationCertificates.Batch035.certificate702
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1053 {x : ℝ} (hx : certificate1053.interval.Contains x) : ∃ c∈certificate1053.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1053 numericValid1053 hx

def certificate1054 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate702,PopulationCertificates.Batch035.certificate702,[MergedCutCells.Batch317.certificate3815,MergedCutCells.Batch318.certificate3816,MergedCutCells.Batch318.certificate3817],(61673611/50000000),none,(1/2),(158393363380380311/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1054 : certificate1054.NumericValid := by decide +kernel
theorem cellsSound1054 : ∀ c∈certificate1054.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3815,MergedCutCells.Batch318.certificate3816,MergedCutCells.Batch318.certificate3817], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.sound3815,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3817,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1054 : ∀ c∈certificate1054.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3815,MergedCutCells.Batch318.certificate3816,MergedCutCells.Batch318.certificate3817], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch317.numericValid3815,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3817,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1054 : ∀ c∈certificate1054.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3815,MergedCutCells.Batch318.certificate3816,MergedCutCells.Batch318.certificate3817], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1054 : ∀ c∈certificate1054.cells, c.population=certificate1054.population := by
  change ∀ c∈[MergedCutCells.Batch317.certificate3815,MergedCutCells.Batch318.certificate3816,MergedCutCells.Batch318.certificate3817], c.population=PopulationCertificates.Batch035.certificate702
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1054 {x : ℝ} (hx : certificate1054.interval.Contains x) : ∃ c∈certificate1054.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1054 numericValid1054 hx

def certificate1055 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate703,PopulationCertificates.Batch035.certificate703,[MergedCutCells.Batch318.certificate3818,MergedCutCells.Batch318.certificate3819],(9291593723557627199/500000000000000000),none,(1/2),(4866396937452254287/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1055 : certificate1055.NumericValid := by decide +kernel
theorem cellsSound1055 : ∀ c∈certificate1055.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3818,MergedCutCells.Batch318.certificate3819], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3818,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.sound3819,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1055 : ∀ c∈certificate1055.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3818,MergedCutCells.Batch318.certificate3819], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3818,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch318.numericValid3819,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1055 : ∀ c∈certificate1055.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3818,MergedCutCells.Batch318.certificate3819], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1055 : ∀ c∈certificate1055.cells, c.population=certificate1055.population := by
  change ∀ c∈[MergedCutCells.Batch318.certificate3818,MergedCutCells.Batch318.certificate3819], c.population=PopulationCertificates.Batch035.certificate703
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1055 {x : ℝ} (hx : certificate1055.interval.Contains x) : ∃ c∈certificate1055.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1055 numericValid1055 hx

end Cycle12.MergedCutGroups.Batch087
