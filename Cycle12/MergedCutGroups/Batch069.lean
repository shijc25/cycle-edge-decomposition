import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch027
import Cycle12.MergedCutCells.Batch253
import Cycle12.MergedCutCells.Batch254
import Cycle12.MergedCutCells.Batch255
import Cycle12.PopulationCertificates.Batch027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch069

def certificate828 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate552,PopulationCertificates.Batch027.certificate552,[MergedCutCells.Batch253.certificate3036,MergedCutCells.Batch253.certificate3037,MergedCutCells.Batch253.certificate3038],(166869430025713171/250000000000000000),(some (574213683/500000000)),(1/2),(38440144289068541/100000000000000000),(some (84249626997742291/500000000000000000)),(some (1004369840473803/25000000000000000))⟩
theorem numericValid828 : certificate828.NumericValid := by decide +kernel
theorem cellsSound828 : ∀ c∈certificate828.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3036,MergedCutCells.Batch253.certificate3037,MergedCutCells.Batch253.certificate3038], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3036,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3038,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric828 : ∀ c∈certificate828.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3036,MergedCutCells.Batch253.certificate3037,MergedCutCells.Batch253.certificate3038], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3036,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3038,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid828 : ∀ c∈certificate828.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3036,MergedCutCells.Batch253.certificate3037,MergedCutCells.Batch253.certificate3038], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid277,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid277,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid277,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches828 : ∀ c∈certificate828.cells, c.population=certificate828.population := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3036,MergedCutCells.Batch253.certificate3037,MergedCutCells.Batch253.certificate3038], c.population=PopulationCertificates.Batch027.certificate552
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers828 {x : ℝ} (hx : certificate828.interval.Contains x) : ∃ c∈certificate828.cells, c.region.interval.Contains x := rat_cut_group_covers certificate828 numericValid828 hx

def certificate829 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate552,PopulationCertificates.Batch027.certificate552,[MergedCutCells.Batch253.certificate3039,MergedCutCells.Batch253.certificate3040,MergedCutCells.Batch253.certificate3041,MergedCutCells.Batch253.certificate3042],(574213683/500000000),none,(1/2),(92807638662893271/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid829 : certificate829.NumericValid := by decide +kernel
theorem cellsSound829 : ∀ c∈certificate829.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3039,MergedCutCells.Batch253.certificate3040,MergedCutCells.Batch253.certificate3041,MergedCutCells.Batch253.certificate3042], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3040,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3041,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3042,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric829 : ∀ c∈certificate829.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3039,MergedCutCells.Batch253.certificate3040,MergedCutCells.Batch253.certificate3041,MergedCutCells.Batch253.certificate3042], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3040,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3041,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3042,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid829 : ∀ c∈certificate829.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3039,MergedCutCells.Batch253.certificate3040,MergedCutCells.Batch253.certificate3041,MergedCutCells.Batch253.certificate3042], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches829 : ∀ c∈certificate829.cells, c.population=certificate829.population := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3039,MergedCutCells.Batch253.certificate3040,MergedCutCells.Batch253.certificate3041,MergedCutCells.Batch253.certificate3042], c.population=PopulationCertificates.Batch027.certificate552
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers829 {x : ℝ} (hx : certificate829.interval.Contains x) : ∃ c∈certificate829.cells, c.region.interval.Contains x := rat_cut_group_covers certificate829 numericValid829 hx

def certificate830 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate553,PopulationCertificates.Batch027.certificate553,[MergedCutCells.Batch253.certificate3043,MergedCutCells.Batch253.certificate3044],(2423166607914452469/250000000000000000),none,(1/2),(1165721684502451031/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid830 : certificate830.NumericValid := by decide +kernel
theorem cellsSound830 : ∀ c∈certificate830.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3043,MergedCutCells.Batch253.certificate3044], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3043,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3044,List.forall_mem_nil _⟩⟩
theorem cellsNumeric830 : ∀ c∈certificate830.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3043,MergedCutCells.Batch253.certificate3044], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3043,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3044,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid830 : ∀ c∈certificate830.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3043,MergedCutCells.Batch253.certificate3044], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches830 : ∀ c∈certificate830.cells, c.population=certificate830.population := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3043,MergedCutCells.Batch253.certificate3044], c.population=PopulationCertificates.Batch027.certificate553
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers830 {x : ℝ} (hx : certificate830.interval.Contains x) : ∃ c∈certificate830.cells, c.region.interval.Contains x := rat_cut_group_covers certificate830 numericValid830 hx

def certificate831 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate554,PopulationCertificates.Batch027.certificate554,[MergedCutCells.Batch253.certificate3045,MergedCutCells.Batch253.certificate3046],(337285899506769633/500000000000000000),(some (1159174811/1000000000)),(1/2),(404422001136504051/1000000000000000000),(some (17617954123707529/100000000000000000)),(some (42618862931454637/1000000000000000000))⟩
theorem numericValid831 : certificate831.NumericValid := by decide +kernel
theorem cellsSound831 : ∀ c∈certificate831.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3045,MergedCutCells.Batch253.certificate3046], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3045,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3046,List.forall_mem_nil _⟩⟩
theorem cellsNumeric831 : ∀ c∈certificate831.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3045,MergedCutCells.Batch253.certificate3046], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3045,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3046,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid831 : ∀ c∈certificate831.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3045,MergedCutCells.Batch253.certificate3046], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid278,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid278,List.forall_mem_nil _⟩⟩
theorem populationMatches831 : ∀ c∈certificate831.cells, c.population=certificate831.population := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3045,MergedCutCells.Batch253.certificate3046], c.population=PopulationCertificates.Batch027.certificate554
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers831 {x : ℝ} (hx : certificate831.interval.Contains x) : ∃ c∈certificate831.cells, c.region.interval.Contains x := rat_cut_group_covers certificate831 numericValid831 hx

def certificate832 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate554,PopulationCertificates.Batch027.certificate554,[MergedCutCells.Batch253.certificate3047,MergedCutCells.Batch254.certificate3048,MergedCutCells.Batch254.certificate3049,MergedCutCells.Batch254.certificate3050],(1159174811/1000000000),none,(1/2),(97649359354733647/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid832 : certificate832.NumericValid := by decide +kernel
theorem cellsSound832 : ∀ c∈certificate832.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3047,MergedCutCells.Batch254.certificate3048,MergedCutCells.Batch254.certificate3049,MergedCutCells.Batch254.certificate3050], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.sound3047,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3048,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3050,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric832 : ∀ c∈certificate832.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3047,MergedCutCells.Batch254.certificate3048,MergedCutCells.Batch254.certificate3049,MergedCutCells.Batch254.certificate3050], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch253.numericValid3047,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3048,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3050,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid832 : ∀ c∈certificate832.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3047,MergedCutCells.Batch254.certificate3048,MergedCutCells.Batch254.certificate3049,MergedCutCells.Batch254.certificate3050], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches832 : ∀ c∈certificate832.cells, c.population=certificate832.population := by
  change ∀ c∈[MergedCutCells.Batch253.certificate3047,MergedCutCells.Batch254.certificate3048,MergedCutCells.Batch254.certificate3049,MergedCutCells.Batch254.certificate3050], c.population=PopulationCertificates.Batch027.certificate554
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers832 {x : ℝ} (hx : certificate832.interval.Contains x) : ∃ c∈certificate832.cells, c.region.interval.Contains x := rat_cut_group_covers certificate832 numericValid832 hx

def certificate833 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate555,PopulationCertificates.Batch027.certificate555,[MergedCutCells.Batch254.certificate3051,MergedCutCells.Batch254.certificate3052],(9814259063221209469/1000000000000000000),none,(1/2),(4776697491326631449/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid833 : certificate833.NumericValid := by decide +kernel
theorem cellsSound833 : ∀ c∈certificate833.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3051,MergedCutCells.Batch254.certificate3052], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3051,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3052,List.forall_mem_nil _⟩⟩
theorem cellsNumeric833 : ∀ c∈certificate833.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3051,MergedCutCells.Batch254.certificate3052], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3051,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3052,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid833 : ∀ c∈certificate833.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3051,MergedCutCells.Batch254.certificate3052], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches833 : ∀ c∈certificate833.cells, c.population=certificate833.population := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3051,MergedCutCells.Batch254.certificate3052], c.population=PopulationCertificates.Batch027.certificate555
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers833 {x : ℝ} (hx : certificate833.interval.Contains x) : ∃ c∈certificate833.cells, c.region.interval.Contains x := rat_cut_group_covers certificate833 numericValid833 hx

def certificate834 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate556,PopulationCertificates.Batch027.certificate556,[MergedCutCells.Batch254.certificate3053,MergedCutCells.Batch254.certificate3054,MergedCutCells.Batch254.certificate3055],(681316102884573961/1000000000000000000),(some (1144217933/1000000000)),(1/2),(424972149168302779/1000000000000000000),(some (182961360701438691/1000000000000000000)),(some (44816898014988791/1000000000000000000))⟩
theorem numericValid834 : certificate834.NumericValid := by decide +kernel
theorem cellsSound834 : ∀ c∈certificate834.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3053,MergedCutCells.Batch254.certificate3054,MergedCutCells.Batch254.certificate3055], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3053,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3054,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3055,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric834 : ∀ c∈certificate834.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3053,MergedCutCells.Batch254.certificate3054,MergedCutCells.Batch254.certificate3055], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3053,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3054,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3055,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid834 : ∀ c∈certificate834.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3053,MergedCutCells.Batch254.certificate3054,MergedCutCells.Batch254.certificate3055], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid279,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid279,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid279,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches834 : ∀ c∈certificate834.cells, c.population=certificate834.population := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3053,MergedCutCells.Batch254.certificate3054,MergedCutCells.Batch254.certificate3055], c.population=PopulationCertificates.Batch027.certificate556
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers834 {x : ℝ} (hx : certificate834.interval.Contains x) : ∃ c∈certificate834.cells, c.region.interval.Contains x := rat_cut_group_covers certificate834 numericValid834 hx

def certificate835 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate556,PopulationCertificates.Batch027.certificate556,[MergedCutCells.Batch254.certificate3056,MergedCutCells.Batch254.certificate3057,MergedCutCells.Batch254.certificate3058,MergedCutCells.Batch254.certificate3059],(1144217933/1000000000),none,(1/2),(410567744634366297/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid835 : certificate835.NumericValid := by decide +kernel
theorem cellsSound835 : ∀ c∈certificate835.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3056,MergedCutCells.Batch254.certificate3057,MergedCutCells.Batch254.certificate3058,MergedCutCells.Batch254.certificate3059], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3056,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3057,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3058,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.sound3059,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric835 : ∀ c∈certificate835.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3056,MergedCutCells.Batch254.certificate3057,MergedCutCells.Batch254.certificate3058,MergedCutCells.Batch254.certificate3059], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3056,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3057,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3058,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch254.numericValid3059,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid835 : ∀ c∈certificate835.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3056,MergedCutCells.Batch254.certificate3057,MergedCutCells.Batch254.certificate3058,MergedCutCells.Batch254.certificate3059], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches835 : ∀ c∈certificate835.cells, c.population=certificate835.population := by
  change ∀ c∈[MergedCutCells.Batch254.certificate3056,MergedCutCells.Batch254.certificate3057,MergedCutCells.Batch254.certificate3058,MergedCutCells.Batch254.certificate3059], c.population=PopulationCertificates.Batch027.certificate556
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers835 {x : ℝ} (hx : certificate835.interval.Contains x) : ∃ c∈certificate835.cells, c.region.interval.Contains x := rat_cut_group_covers certificate835 numericValid835 hx

def certificate836 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate557,PopulationCertificates.Batch027.certificate557,[MergedCutCells.Batch255.certificate3060,MergedCutCells.Batch255.certificate3061],(4908142808574272397/500000000000000000),none,(1/2),(2427294655763537847/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid836 : certificate836.NumericValid := by decide +kernel
theorem cellsSound836 : ∀ c∈certificate836.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3060,MergedCutCells.Batch255.certificate3061], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3060,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3061,List.forall_mem_nil _⟩⟩
theorem cellsNumeric836 : ∀ c∈certificate836.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3060,MergedCutCells.Batch255.certificate3061], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3060,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3061,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid836 : ∀ c∈certificate836.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3060,MergedCutCells.Batch255.certificate3061], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches836 : ∀ c∈certificate836.cells, c.population=certificate836.population := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3060,MergedCutCells.Batch255.certificate3061], c.population=PopulationCertificates.Batch027.certificate557
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers836 {x : ℝ} (hx : certificate836.interval.Contains x) : ∃ c∈certificate836.cells, c.region.interval.Contains x := rat_cut_group_covers certificate836 numericValid836 hx

def certificate837 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate558,PopulationCertificates.Batch027.certificate558,[MergedCutCells.Batch255.certificate3062,MergedCutCells.Batch255.certificate3063,MergedCutCells.Batch255.certificate3064],(344465467716225167/500000000000000000),(some (225485797/200000000)),(1/2),(14010767958326247/31250000000000000),(some (94908921228803561/500000000000000000)),(some (9415455929374787/200000000000000000))⟩
theorem numericValid837 : certificate837.NumericValid := by decide +kernel
theorem cellsSound837 : ∀ c∈certificate837.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3062,MergedCutCells.Batch255.certificate3063,MergedCutCells.Batch255.certificate3064], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3062,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3063,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3064,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric837 : ∀ c∈certificate837.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3062,MergedCutCells.Batch255.certificate3063,MergedCutCells.Batch255.certificate3064], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3062,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3063,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3064,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid837 : ∀ c∈certificate837.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3062,MergedCutCells.Batch255.certificate3063,MergedCutCells.Batch255.certificate3064], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid280,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid280,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid280,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches837 : ∀ c∈certificate837.cells, c.population=certificate837.population := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3062,MergedCutCells.Batch255.certificate3063,MergedCutCells.Batch255.certificate3064], c.population=PopulationCertificates.Batch027.certificate558
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers837 {x : ℝ} (hx : certificate837.interval.Contains x) : ∃ c∈certificate837.cells, c.region.interval.Contains x := rat_cut_group_covers certificate837 numericValid837 hx

def certificate838 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate558,PopulationCertificates.Batch027.certificate558,[MergedCutCells.Batch255.certificate3065,MergedCutCells.Batch255.certificate3066,MergedCutCells.Batch255.certificate3067,MergedCutCells.Batch255.certificate3068,MergedCutCells.Batch255.certificate3069],(225485797/200000000),none,(1/2),(430966296740638861/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid838 : certificate838.NumericValid := by decide +kernel
theorem cellsSound838 : ∀ c∈certificate838.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3065,MergedCutCells.Batch255.certificate3066,MergedCutCells.Batch255.certificate3067,MergedCutCells.Batch255.certificate3068,MergedCutCells.Batch255.certificate3069], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3065,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3066,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3067,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3069,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric838 : ∀ c∈certificate838.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3065,MergedCutCells.Batch255.certificate3066,MergedCutCells.Batch255.certificate3067,MergedCutCells.Batch255.certificate3068,MergedCutCells.Batch255.certificate3069], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3065,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3066,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3067,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3069,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid838 : ∀ c∈certificate838.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3065,MergedCutCells.Batch255.certificate3066,MergedCutCells.Batch255.certificate3067,MergedCutCells.Batch255.certificate3068,MergedCutCells.Batch255.certificate3069], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches838 : ∀ c∈certificate838.cells, c.population=certificate838.population := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3065,MergedCutCells.Batch255.certificate3066,MergedCutCells.Batch255.certificate3067,MergedCutCells.Batch255.certificate3068,MergedCutCells.Batch255.certificate3069], c.population=PopulationCertificates.Batch027.certificate558
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers838 {x : ℝ} (hx : certificate838.interval.Contains x) : ∃ c∈certificate838.cells, c.region.interval.Contains x := rat_cut_group_covers certificate838 numericValid838 hx

def certificate839 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate559,PopulationCertificates.Batch027.certificate559,[MergedCutCells.Batch255.certificate3070,MergedCutCells.Batch255.certificate3071],(9821535649951716947/1000000000000000000),none,(1/2),(2467378868575221529/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid839 : certificate839.NumericValid := by decide +kernel
theorem cellsSound839 : ∀ c∈certificate839.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3070,MergedCutCells.Batch255.certificate3071], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3070,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.sound3071,List.forall_mem_nil _⟩⟩
theorem cellsNumeric839 : ∀ c∈certificate839.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3070,MergedCutCells.Batch255.certificate3071], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3070,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch255.numericValid3071,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid839 : ∀ c∈certificate839.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3070,MergedCutCells.Batch255.certificate3071], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches839 : ∀ c∈certificate839.cells, c.population=certificate839.population := by
  change ∀ c∈[MergedCutCells.Batch255.certificate3070,MergedCutCells.Batch255.certificate3071], c.population=PopulationCertificates.Batch027.certificate559
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers839 {x : ℝ} (hx : certificate839.interval.Contains x) : ∃ c∈certificate839.cells, c.region.interval.Contains x := rat_cut_group_covers certificate839 numericValid839 hx

end Cycle12.MergedCutGroups.Batch069
