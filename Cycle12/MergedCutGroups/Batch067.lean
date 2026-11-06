import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch026
import Cycle12.GeometryCertificates.Batch027
import Cycle12.MergedCutCells.Batch247
import Cycle12.MergedCutCells.Batch248
import Cycle12.MergedCutCells.Batch249
import Cycle12.MergedCutCells.Batch250
import Cycle12.PopulationCertificates.Batch026
import Cycle12.PopulationCertificates.Batch027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch067

def certificate804 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate536,PopulationCertificates.Batch026.certificate536,[MergedCutCells.Batch247.certificate2969,MergedCutCells.Batch247.certificate2970],(621852645668439883/1000000000000000000),(some (590175151/500000000)),(1/2),(68993064345143027/250000000000000000),(some (570340474749047/5000000000000000)),(some (24228504709270111/1000000000000000000))⟩
theorem numericValid804 : certificate804.NumericValid := by decide +kernel
theorem cellsSound804 : ∀ c∈certificate804.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2969,MergedCutCells.Batch247.certificate2970], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2970,List.forall_mem_nil _⟩⟩
theorem cellsNumeric804 : ∀ c∈certificate804.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2969,MergedCutCells.Batch247.certificate2970], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2970,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid804 : ∀ c∈certificate804.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2969,MergedCutCells.Batch247.certificate2970], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid269,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid269,List.forall_mem_nil _⟩⟩
theorem populationMatches804 : ∀ c∈certificate804.cells, c.population=certificate804.population := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2969,MergedCutCells.Batch247.certificate2970], c.population=PopulationCertificates.Batch026.certificate536
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers804 {x : ℝ} (hx : certificate804.interval.Contains x) : ∃ c∈certificate804.cells, c.region.interval.Contains x := rat_cut_group_covers certificate804 numericValid804 hx

def certificate805 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate536,PopulationCertificates.Batch026.certificate536,[MergedCutCells.Batch247.certificate2971,MergedCutCells.Batch247.certificate2972,MergedCutCells.Batch247.certificate2973,MergedCutCells.Batch247.certificate2974],(590175151/500000000),none,(1/2),(267860992775023081/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid805 : certificate805.NumericValid := by decide +kernel
theorem cellsSound805 : ∀ c∈certificate805.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2971,MergedCutCells.Batch247.certificate2972,MergedCutCells.Batch247.certificate2973,MergedCutCells.Batch247.certificate2974], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2972,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2973,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2974,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric805 : ∀ c∈certificate805.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2971,MergedCutCells.Batch247.certificate2972,MergedCutCells.Batch247.certificate2973,MergedCutCells.Batch247.certificate2974], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2972,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2973,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2974,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid805 : ∀ c∈certificate805.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2971,MergedCutCells.Batch247.certificate2972,MergedCutCells.Batch247.certificate2973,MergedCutCells.Batch247.certificate2974], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches805 : ∀ c∈certificate805.cells, c.population=certificate805.population := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2971,MergedCutCells.Batch247.certificate2972,MergedCutCells.Batch247.certificate2973,MergedCutCells.Batch247.certificate2974], c.population=PopulationCertificates.Batch026.certificate536
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers805 {x : ℝ} (hx : certificate805.interval.Contains x) : ∃ c∈certificate805.cells, c.region.interval.Contains x := rat_cut_group_covers certificate805 numericValid805 hx

def certificate806 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate537,PopulationCertificates.Batch026.certificate537,[MergedCutCells.Batch247.certificate2975,MergedCutCells.Batch248.certificate2976],(9300633999686685519/1000000000000000000),none,(1/2),(4016480673527480549/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid806 : certificate806.NumericValid := by decide +kernel
theorem cellsSound806 : ∀ c∈certificate806.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2975,MergedCutCells.Batch248.certificate2976], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2975,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2976,List.forall_mem_nil _⟩⟩
theorem cellsNumeric806 : ∀ c∈certificate806.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2975,MergedCutCells.Batch248.certificate2976], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2975,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2976,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid806 : ∀ c∈certificate806.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2975,MergedCutCells.Batch248.certificate2976], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches806 : ∀ c∈certificate806.cells, c.population=certificate806.population := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2975,MergedCutCells.Batch248.certificate2976], c.population=PopulationCertificates.Batch026.certificate537
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers806 {x : ℝ} (hx : certificate806.interval.Contains x) : ∃ c∈certificate806.cells, c.region.interval.Contains x := rat_cut_group_covers certificate806 numericValid806 hx

def certificate807 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate538,PopulationCertificates.Batch026.certificate538,[MergedCutCells.Batch248.certificate2977,MergedCutCells.Batch248.certificate2978],(157076960705645127/250000000000000000),(some (1190900959/1000000000)),(1/2),(29302359522207313/100000000000000000),(some (120887352057382339/1000000000000000000)),(some (260931091563677/10000000000000000))⟩
theorem numericValid807 : certificate807.NumericValid := by decide +kernel
theorem cellsSound807 : ∀ c∈certificate807.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2977,MergedCutCells.Batch248.certificate2978], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2977,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2978,List.forall_mem_nil _⟩⟩
theorem cellsNumeric807 : ∀ c∈certificate807.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2977,MergedCutCells.Batch248.certificate2978], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2977,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2978,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid807 : ∀ c∈certificate807.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2977,MergedCutCells.Batch248.certificate2978], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid270,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid270,List.forall_mem_nil _⟩⟩
theorem populationMatches807 : ∀ c∈certificate807.cells, c.population=certificate807.population := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2977,MergedCutCells.Batch248.certificate2978], c.population=PopulationCertificates.Batch026.certificate538
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers807 {x : ℝ} (hx : certificate807.interval.Contains x) : ∃ c∈certificate807.cells, c.region.interval.Contains x := rat_cut_group_covers certificate807 numericValid807 hx

def certificate808 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate538,PopulationCertificates.Batch026.certificate538,[MergedCutCells.Batch248.certificate2979,MergedCutCells.Batch248.certificate2980,MergedCutCells.Batch248.certificate2981,MergedCutCells.Batch248.certificate2982],(1190900959/1000000000),none,(1/2),(284140172789785863/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid808 : certificate808.NumericValid := by decide +kernel
theorem cellsSound808 : ∀ c∈certificate808.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2979,MergedCutCells.Batch248.certificate2980,MergedCutCells.Batch248.certificate2981,MergedCutCells.Batch248.certificate2982], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2979,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2980,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2981,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2982,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric808 : ∀ c∈certificate808.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2979,MergedCutCells.Batch248.certificate2980,MergedCutCells.Batch248.certificate2981,MergedCutCells.Batch248.certificate2982], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2979,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2980,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2981,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2982,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid808 : ∀ c∈certificate808.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2979,MergedCutCells.Batch248.certificate2980,MergedCutCells.Batch248.certificate2981,MergedCutCells.Batch248.certificate2982], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches808 : ∀ c∈certificate808.cells, c.population=certificate808.population := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2979,MergedCutCells.Batch248.certificate2980,MergedCutCells.Batch248.certificate2981,MergedCutCells.Batch248.certificate2982], c.population=PopulationCertificates.Batch026.certificate538
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers808 {x : ℝ} (hx : certificate808.interval.Contains x) : ∃ c∈certificate808.cells, c.region.interval.Contains x := rat_cut_group_covers certificate808 numericValid808 hx

def certificate809 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate539,PopulationCertificates.Batch026.certificate539,[MergedCutCells.Batch248.certificate2983,MergedCutCells.Batch248.certificate2984],(4640707306733617823/500000000000000000),none,(1/2),(4076498333810414503/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid809 : certificate809.NumericValid := by decide +kernel
theorem cellsSound809 : ∀ c∈certificate809.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2983,MergedCutCells.Batch248.certificate2984], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2983,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2984,List.forall_mem_nil _⟩⟩
theorem cellsNumeric809 : ∀ c∈certificate809.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2983,MergedCutCells.Batch248.certificate2984], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2983,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2984,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid809 : ∀ c∈certificate809.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2983,MergedCutCells.Batch248.certificate2984], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches809 : ∀ c∈certificate809.cells, c.population=certificate809.population := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2983,MergedCutCells.Batch248.certificate2984], c.population=PopulationCertificates.Batch026.certificate539
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers809 {x : ℝ} (hx : certificate809.interval.Contains x) : ∃ c∈certificate809.cells, c.region.interval.Contains x := rat_cut_group_covers certificate809 numericValid809 hx

def certificate810 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate540,PopulationCertificates.Batch027.certificate540,[MergedCutCells.Batch248.certificate2985,MergedCutCells.Batch248.certificate2986],(158094780059753739/250000000000000000),(some (1172337659/1000000000)),(1/2),(59583523082547653/200000000000000000),(some (127149077036166199/1000000000000000000)),(some (222714104610229/8000000000000000))⟩
theorem numericValid810 : certificate810.NumericValid := by decide +kernel
theorem cellsSound810 : ∀ c∈certificate810.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2985,MergedCutCells.Batch248.certificate2986], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2985,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2986,List.forall_mem_nil _⟩⟩
theorem cellsNumeric810 : ∀ c∈certificate810.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2985,MergedCutCells.Batch248.certificate2986], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2985,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2986,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid810 : ∀ c∈certificate810.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2985,MergedCutCells.Batch248.certificate2986], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid271,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid271,List.forall_mem_nil _⟩⟩
theorem populationMatches810 : ∀ c∈certificate810.cells, c.population=certificate810.population := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2985,MergedCutCells.Batch248.certificate2986], c.population=PopulationCertificates.Batch027.certificate540
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers810 {x : ℝ} (hx : certificate810.interval.Contains x) : ∃ c∈certificate810.cells, c.region.interval.Contains x := rat_cut_group_covers certificate810 numericValid810 hx

def certificate811 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate540,PopulationCertificates.Batch027.certificate540,[MergedCutCells.Batch248.certificate2987,MergedCutCells.Batch249.certificate2988,MergedCutCells.Batch249.certificate2989,MergedCutCells.Batch249.certificate2990],(1172337659/1000000000),none,(1/2),(288757338525973097/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid811 : certificate811.NumericValid := by decide +kernel
theorem cellsSound811 : ∀ c∈certificate811.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2987,MergedCutCells.Batch249.certificate2988,MergedCutCells.Batch249.certificate2989,MergedCutCells.Batch249.certificate2990], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.sound2987,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2988,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2990,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric811 : ∀ c∈certificate811.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2987,MergedCutCells.Batch249.certificate2988,MergedCutCells.Batch249.certificate2989,MergedCutCells.Batch249.certificate2990], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch248.numericValid2987,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2988,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2990,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid811 : ∀ c∈certificate811.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2987,MergedCutCells.Batch249.certificate2988,MergedCutCells.Batch249.certificate2989,MergedCutCells.Batch249.certificate2990], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches811 : ∀ c∈certificate811.cells, c.population=certificate811.population := by
  change ∀ c∈[MergedCutCells.Batch248.certificate2987,MergedCutCells.Batch249.certificate2988,MergedCutCells.Batch249.certificate2989,MergedCutCells.Batch249.certificate2990], c.population=PopulationCertificates.Batch027.certificate540
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers811 {x : ℝ} (hx : certificate811.interval.Contains x) : ∃ c∈certificate811.cells, c.region.interval.Contains x := rat_cut_group_covers certificate811 numericValid811 hx

def certificate812 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate541,PopulationCertificates.Batch027.certificate541,[MergedCutCells.Batch249.certificate2991,MergedCutCells.Batch249.certificate2992],(376999011924883791/40000000000000000),none,(1/2),(83516938088463303/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid812 : certificate812.NumericValid := by decide +kernel
theorem cellsSound812 : ∀ c∈certificate812.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2991,MergedCutCells.Batch249.certificate2992], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2991,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2992,List.forall_mem_nil _⟩⟩
theorem cellsNumeric812 : ∀ c∈certificate812.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2991,MergedCutCells.Batch249.certificate2992], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2991,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2992,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid812 : ∀ c∈certificate812.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2991,MergedCutCells.Batch249.certificate2992], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches812 : ∀ c∈certificate812.cells, c.population=certificate812.population := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2991,MergedCutCells.Batch249.certificate2992], c.population=PopulationCertificates.Batch027.certificate541
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers812 {x : ℝ} (hx : certificate812.interval.Contains x) : ∃ c∈certificate812.cells, c.region.interval.Contains x := rat_cut_group_covers certificate812 numericValid812 hx

def certificate813 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate542,PopulationCertificates.Batch027.certificate542,[MergedCutCells.Batch249.certificate2993,MergedCutCells.Batch249.certificate2994],(318405970623638049/500000000000000000),(some (1179453493/1000000000)),(1/2),(9479934513560613/31250000000000000),(some (134201295533521851/1000000000000000000)),(some (2984452207860627/100000000000000000))⟩
theorem numericValid813 : certificate813.NumericValid := by decide +kernel
theorem cellsSound813 : ∀ c∈certificate813.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2993,MergedCutCells.Batch249.certificate2994], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2993,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2994,List.forall_mem_nil _⟩⟩
theorem cellsNumeric813 : ∀ c∈certificate813.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2993,MergedCutCells.Batch249.certificate2994], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2993,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2994,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid813 : ∀ c∈certificate813.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2993,MergedCutCells.Batch249.certificate2994], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid272,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid272,List.forall_mem_nil _⟩⟩
theorem populationMatches813 : ∀ c∈certificate813.cells, c.population=certificate813.population := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2993,MergedCutCells.Batch249.certificate2994], c.population=PopulationCertificates.Batch027.certificate542
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers813 {x : ℝ} (hx : certificate813.interval.Contains x) : ∃ c∈certificate813.cells, c.region.interval.Contains x := rat_cut_group_covers certificate813 numericValid813 hx

def certificate814 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate542,PopulationCertificates.Batch027.certificate542,[MergedCutCells.Batch249.certificate2995,MergedCutCells.Batch249.certificate2996,MergedCutCells.Batch249.certificate2997,MergedCutCells.Batch249.certificate2998],(1179453493/1000000000),none,(1/2),(73364322324268003/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid814 : certificate814.NumericValid := by decide +kernel
theorem cellsSound814 : ∀ c∈certificate814.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2995,MergedCutCells.Batch249.certificate2996,MergedCutCells.Batch249.certificate2997,MergedCutCells.Batch249.certificate2998], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2995,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2996,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2998,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric814 : ∀ c∈certificate814.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2995,MergedCutCells.Batch249.certificate2996,MergedCutCells.Batch249.certificate2997,MergedCutCells.Batch249.certificate2998], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2995,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2996,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2998,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid814 : ∀ c∈certificate814.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2995,MergedCutCells.Batch249.certificate2996,MergedCutCells.Batch249.certificate2997,MergedCutCells.Batch249.certificate2998], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches814 : ∀ c∈certificate814.cells, c.population=certificate814.population := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2995,MergedCutCells.Batch249.certificate2996,MergedCutCells.Batch249.certificate2997,MergedCutCells.Batch249.certificate2998], c.population=PopulationCertificates.Batch027.certificate542
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers814 {x : ℝ} (hx : certificate814.interval.Contains x) : ∃ c∈certificate814.cells, c.region.interval.Contains x := rat_cut_group_covers certificate814 numericValid814 hx

def certificate815 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate543,PopulationCertificates.Batch027.certificate543,[MergedCutCells.Batch249.certificate2999,MergedCutCells.Batch250.certificate3000],(1889538406956366239/200000000000000000),none,(1/2),(848026937815156397/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid815 : certificate815.NumericValid := by decide +kernel
theorem cellsSound815 : ∀ c∈certificate815.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2999,MergedCutCells.Batch250.certificate3000], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.sound2999,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3000,List.forall_mem_nil _⟩⟩
theorem cellsNumeric815 : ∀ c∈certificate815.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2999,MergedCutCells.Batch250.certificate3000], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch249.numericValid2999,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3000,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid815 : ∀ c∈certificate815.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2999,MergedCutCells.Batch250.certificate3000], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches815 : ∀ c∈certificate815.cells, c.population=certificate815.population := by
  change ∀ c∈[MergedCutCells.Batch249.certificate2999,MergedCutCells.Batch250.certificate3000], c.population=PopulationCertificates.Batch027.certificate543
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers815 {x : ℝ} (hx : certificate815.interval.Contains x) : ∃ c∈certificate815.cells, c.region.interval.Contains x := rat_cut_group_covers certificate815 numericValid815 hx

end Cycle12.MergedCutGroups.Batch067
