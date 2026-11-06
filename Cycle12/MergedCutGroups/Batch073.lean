import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch029
import Cycle12.MergedCutCells.Batch267
import Cycle12.MergedCutCells.Batch268
import Cycle12.MergedCutCells.Batch269
import Cycle12.MergedCutCells.Batch270
import Cycle12.MergedCutCells.Batch271
import Cycle12.PopulationCertificates.Batch029

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch073

def certificate876 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate584,PopulationCertificates.Batch029.certificate584,[MergedCutCells.Batch267.certificate3210,MergedCutCells.Batch267.certificate3211,MergedCutCells.Batch267.certificate3212],(784562232840052909/1000000000000000000),(some (221393211/200000000)),(1/2),(946055837312168661/1000000000000000000),(some (276582024057568209/1000000000000000000)),(some (19776658756296413/250000000000000000))⟩
theorem numericValid876 : certificate876.NumericValid := by decide +kernel
theorem cellsSound876 : ∀ c∈certificate876.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3210,MergedCutCells.Batch267.certificate3211,MergedCutCells.Batch267.certificate3212], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3210,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3211,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3212,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric876 : ∀ c∈certificate876.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3210,MergedCutCells.Batch267.certificate3211,MergedCutCells.Batch267.certificate3212], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3210,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3211,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3212,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid876 : ∀ c∈certificate876.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3210,MergedCutCells.Batch267.certificate3211,MergedCutCells.Batch267.certificate3212], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid293,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid293,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid293,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches876 : ∀ c∈certificate876.cells, c.population=certificate876.population := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3210,MergedCutCells.Batch267.certificate3211,MergedCutCells.Batch267.certificate3212], c.population=PopulationCertificates.Batch029.certificate584
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers876 {x : ℝ} (hx : certificate876.interval.Contains x) : ∃ c∈certificate876.cells, c.region.interval.Contains x := rat_cut_group_covers certificate876 numericValid876 hx

def certificate877 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate584,PopulationCertificates.Batch029.certificate584,[MergedCutCells.Batch267.certificate3213,MergedCutCells.Batch267.certificate3214,MergedCutCells.Batch267.certificate3215,MergedCutCells.Batch268.certificate3216,MergedCutCells.Batch268.certificate3217],(221393211/200000000),none,(1/2),(459933474069587407/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid877 : certificate877.NumericValid := by decide +kernel
theorem cellsSound877 : ∀ c∈certificate877.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3213,MergedCutCells.Batch267.certificate3214,MergedCutCells.Batch267.certificate3215,MergedCutCells.Batch268.certificate3216,MergedCutCells.Batch268.certificate3217], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3214,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3216,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3217,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric877 : ∀ c∈certificate877.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3213,MergedCutCells.Batch267.certificate3214,MergedCutCells.Batch267.certificate3215,MergedCutCells.Batch268.certificate3216,MergedCutCells.Batch268.certificate3217], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3214,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3216,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3217,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid877 : ∀ c∈certificate877.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3213,MergedCutCells.Batch267.certificate3214,MergedCutCells.Batch267.certificate3215,MergedCutCells.Batch268.certificate3216,MergedCutCells.Batch268.certificate3217], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches877 : ∀ c∈certificate877.cells, c.population=certificate877.population := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3213,MergedCutCells.Batch267.certificate3214,MergedCutCells.Batch267.certificate3215,MergedCutCells.Batch268.certificate3216,MergedCutCells.Batch268.certificate3217], c.population=PopulationCertificates.Batch029.certificate584
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers877 {x : ℝ} (hx : certificate877.interval.Contains x) : ∃ c∈certificate877.cells, c.region.interval.Contains x := rat_cut_group_covers certificate877 numericValid877 hx

def certificate878 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate585,PopulationCertificates.Batch029.certificate585,[MergedCutCells.Batch268.certificate3218,MergedCutCells.Batch268.certificate3219,MergedCutCells.Batch268.certificate3220],(993987097368999333/100000000000000000),none,(1/2),(3097473841146015567/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid878 : certificate878.NumericValid := by decide +kernel
theorem cellsSound878 : ∀ c∈certificate878.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3218,MergedCutCells.Batch268.certificate3219,MergedCutCells.Batch268.certificate3220], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3218,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3220,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric878 : ∀ c∈certificate878.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3218,MergedCutCells.Batch268.certificate3219,MergedCutCells.Batch268.certificate3220], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3218,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3220,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid878 : ∀ c∈certificate878.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3218,MergedCutCells.Batch268.certificate3219,MergedCutCells.Batch268.certificate3220], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches878 : ∀ c∈certificate878.cells, c.population=certificate878.population := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3218,MergedCutCells.Batch268.certificate3219,MergedCutCells.Batch268.certificate3220], c.population=PopulationCertificates.Batch029.certificate585
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers878 {x : ℝ} (hx : certificate878.interval.Contains x) : ∃ c∈certificate878.cells, c.region.interval.Contains x := rat_cut_group_covers certificate878 numericValid878 hx

def certificate879 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate586,PopulationCertificates.Batch029.certificate586,[MergedCutCells.Batch268.certificate3221,MergedCutCells.Batch268.certificate3222,MergedCutCells.Batch268.certificate3223],(394731637525717071/500000000000000000),(some (217266791/200000000)),(1/2),(980933563647745053/1000000000000000000),(some (139920845552367003/500000000000000000)),(some (31421714616237/390625000000000))⟩
theorem numericValid879 : certificate879.NumericValid := by decide +kernel
theorem cellsSound879 : ∀ c∈certificate879.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3221,MergedCutCells.Batch268.certificate3222,MergedCutCells.Batch268.certificate3223], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3221,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3222,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3223,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric879 : ∀ c∈certificate879.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3221,MergedCutCells.Batch268.certificate3222,MergedCutCells.Batch268.certificate3223], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3221,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3222,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3223,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid879 : ∀ c∈certificate879.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3221,MergedCutCells.Batch268.certificate3222,MergedCutCells.Batch268.certificate3223], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid294,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid294,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid294,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches879 : ∀ c∈certificate879.cells, c.population=certificate879.population := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3221,MergedCutCells.Batch268.certificate3222,MergedCutCells.Batch268.certificate3223], c.population=PopulationCertificates.Batch029.certificate586
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers879 {x : ℝ} (hx : certificate879.interval.Contains x) : ∃ c∈certificate879.cells, c.region.interval.Contains x := rat_cut_group_covers certificate879 numericValid879 hx

def certificate880 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate586,PopulationCertificates.Batch029.certificate586,[MergedCutCells.Batch268.certificate3224,MergedCutCells.Batch268.certificate3225,MergedCutCells.Batch268.certificate3226,MergedCutCells.Batch268.certificate3227,MergedCutCells.Batch269.certificate3228,MergedCutCells.Batch269.certificate3229],(217266791/200000000),none,(1/2),(190077461631481659/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid880 : certificate880.NumericValid := by decide +kernel
theorem cellsSound880 : ∀ c∈certificate880.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3224,MergedCutCells.Batch268.certificate3225,MergedCutCells.Batch268.certificate3226,MergedCutCells.Batch268.certificate3227,MergedCutCells.Batch269.certificate3228,MergedCutCells.Batch269.certificate3229], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3225,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3226,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.sound3227,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3228,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3229,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric880 : ∀ c∈certificate880.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3224,MergedCutCells.Batch268.certificate3225,MergedCutCells.Batch268.certificate3226,MergedCutCells.Batch268.certificate3227,MergedCutCells.Batch269.certificate3228,MergedCutCells.Batch269.certificate3229], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3225,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3226,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch268.numericValid3227,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3228,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3229,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid880 : ∀ c∈certificate880.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3224,MergedCutCells.Batch268.certificate3225,MergedCutCells.Batch268.certificate3226,MergedCutCells.Batch268.certificate3227,MergedCutCells.Batch269.certificate3228,MergedCutCells.Batch269.certificate3229], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches880 : ∀ c∈certificate880.cells, c.population=certificate880.population := by
  change ∀ c∈[MergedCutCells.Batch268.certificate3224,MergedCutCells.Batch268.certificate3225,MergedCutCells.Batch268.certificate3226,MergedCutCells.Batch268.certificate3227,MergedCutCells.Batch269.certificate3228,MergedCutCells.Batch269.certificate3229], c.population=PopulationCertificates.Batch029.certificate586
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers880 {x : ℝ} (hx : certificate880.interval.Contains x) : ∃ c∈certificate880.cells, c.region.interval.Contains x := rat_cut_group_covers certificate880 numericValid880 hx

def certificate881 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate587,PopulationCertificates.Batch029.certificate587,[MergedCutCells.Batch269.certificate3230,MergedCutCells.Batch269.certificate3231,MergedCutCells.Batch269.certificate3232],(4987111730731111207/500000000000000000),none,(1/2),(391869096531803927/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid881 : certificate881.NumericValid := by decide +kernel
theorem cellsSound881 : ∀ c∈certificate881.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3230,MergedCutCells.Batch269.certificate3231,MergedCutCells.Batch269.certificate3232], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3231,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3232,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric881 : ∀ c∈certificate881.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3230,MergedCutCells.Batch269.certificate3231,MergedCutCells.Batch269.certificate3232], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3231,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3232,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid881 : ∀ c∈certificate881.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3230,MergedCutCells.Batch269.certificate3231,MergedCutCells.Batch269.certificate3232], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches881 : ∀ c∈certificate881.cells, c.population=certificate881.population := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3230,MergedCutCells.Batch269.certificate3231,MergedCutCells.Batch269.certificate3232], c.population=PopulationCertificates.Batch029.certificate587
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers881 {x : ℝ} (hx : certificate881.interval.Contains x) : ∃ c∈certificate881.cells, c.region.interval.Contains x := rat_cut_group_covers certificate881 numericValid881 hx

def certificate882 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate588,PopulationCertificates.Batch029.certificate588,[MergedCutCells.Batch269.certificate3233,MergedCutCells.Batch269.certificate3234,MergedCutCells.Batch269.certificate3235],(792786905386523311/1000000000000000000),(some (546265119/500000000)),(1/2),(1010477363683341167/1000000000000000000),(some (141791170519148209/500000000000000000)),(some (16396294497761351/200000000000000000))⟩
theorem numericValid882 : certificate882.NumericValid := by decide +kernel
theorem cellsSound882 : ∀ c∈certificate882.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3233,MergedCutCells.Batch269.certificate3234,MergedCutCells.Batch269.certificate3235], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3233,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3234,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3235,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric882 : ∀ c∈certificate882.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3233,MergedCutCells.Batch269.certificate3234,MergedCutCells.Batch269.certificate3235], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3233,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3234,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3235,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid882 : ∀ c∈certificate882.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3233,MergedCutCells.Batch269.certificate3234,MergedCutCells.Batch269.certificate3235], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid295,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid295,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid295,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches882 : ∀ c∈certificate882.cells, c.population=certificate882.population := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3233,MergedCutCells.Batch269.certificate3234,MergedCutCells.Batch269.certificate3235], c.population=PopulationCertificates.Batch029.certificate588
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers882 {x : ℝ} (hx : certificate882.interval.Contains x) : ∃ c∈certificate882.cells, c.region.interval.Contains x := rat_cut_group_covers certificate882 numericValid882 hx

def certificate883 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate588,PopulationCertificates.Batch029.certificate588,[MergedCutCells.Batch269.certificate3236,MergedCutCells.Batch269.certificate3237,MergedCutCells.Batch269.certificate3238,MergedCutCells.Batch269.certificate3239,MergedCutCells.Batch270.certificate3240,MergedCutCells.Batch270.certificate3241],(546265119/500000000),none,(1/2),(196490004627802469/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid883 : certificate883.NumericValid := by decide +kernel
theorem cellsSound883 : ∀ c∈certificate883.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3236,MergedCutCells.Batch269.certificate3237,MergedCutCells.Batch269.certificate3238,MergedCutCells.Batch269.certificate3239,MergedCutCells.Batch270.certificate3240,MergedCutCells.Batch270.certificate3241], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3237,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3238,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.sound3239,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3241,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric883 : ∀ c∈certificate883.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3236,MergedCutCells.Batch269.certificate3237,MergedCutCells.Batch269.certificate3238,MergedCutCells.Batch269.certificate3239,MergedCutCells.Batch270.certificate3240,MergedCutCells.Batch270.certificate3241], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3237,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3238,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch269.numericValid3239,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3241,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid883 : ∀ c∈certificate883.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3236,MergedCutCells.Batch269.certificate3237,MergedCutCells.Batch269.certificate3238,MergedCutCells.Batch269.certificate3239,MergedCutCells.Batch270.certificate3240,MergedCutCells.Batch270.certificate3241], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches883 : ∀ c∈certificate883.cells, c.population=certificate883.population := by
  change ∀ c∈[MergedCutCells.Batch269.certificate3236,MergedCutCells.Batch269.certificate3237,MergedCutCells.Batch269.certificate3238,MergedCutCells.Batch269.certificate3239,MergedCutCells.Batch270.certificate3240,MergedCutCells.Batch270.certificate3241], c.population=PopulationCertificates.Batch029.certificate588
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers883 {x : ℝ} (hx : certificate883.interval.Contains x) : ∃ c∈certificate883.cells, c.region.interval.Contains x := rat_cut_group_covers certificate883 numericValid883 hx

def certificate884 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate589,PopulationCertificates.Batch029.certificate589,[MergedCutCells.Batch270.certificate3242,MergedCutCells.Batch270.certificate3243,MergedCutCells.Batch270.certificate3244],(9900004414754382953/1000000000000000000),none,(1/2),(6307435796169749779/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid884 : certificate884.NumericValid := by decide +kernel
theorem cellsSound884 : ∀ c∈certificate884.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3242,MergedCutCells.Batch270.certificate3243,MergedCutCells.Batch270.certificate3244], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3243,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3244,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric884 : ∀ c∈certificate884.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3242,MergedCutCells.Batch270.certificate3243,MergedCutCells.Batch270.certificate3244], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3243,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3244,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid884 : ∀ c∈certificate884.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3242,MergedCutCells.Batch270.certificate3243,MergedCutCells.Batch270.certificate3244], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches884 : ∀ c∈certificate884.cells, c.population=certificate884.population := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3242,MergedCutCells.Batch270.certificate3243,MergedCutCells.Batch270.certificate3244], c.population=PopulationCertificates.Batch029.certificate589
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers884 {x : ℝ} (hx : certificate884.interval.Contains x) : ∃ c∈certificate884.cells, c.region.interval.Contains x := rat_cut_group_covers certificate884 numericValid884 hx

def certificate885 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate590,PopulationCertificates.Batch029.certificate590,[MergedCutCells.Batch270.certificate3245,MergedCutCells.Batch270.certificate3246,MergedCutCells.Batch270.certificate3247],(797069575384194251/1000000000000000000),(some (1098000021/1000000000)),(1/2),(130306673499891077/125000000000000000),(some (57572161551618749/200000000000000000)),(some (10470152176800223/125000000000000000))⟩
theorem numericValid885 : certificate885.NumericValid := by decide +kernel
theorem cellsSound885 : ∀ c∈certificate885.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3245,MergedCutCells.Batch270.certificate3246,MergedCutCells.Batch270.certificate3247], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3245,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3247,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric885 : ∀ c∈certificate885.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3245,MergedCutCells.Batch270.certificate3246,MergedCutCells.Batch270.certificate3247], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3245,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3247,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid885 : ∀ c∈certificate885.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3245,MergedCutCells.Batch270.certificate3246,MergedCutCells.Batch270.certificate3247], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid296,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid296,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid296,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches885 : ∀ c∈certificate885.cells, c.population=certificate885.population := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3245,MergedCutCells.Batch270.certificate3246,MergedCutCells.Batch270.certificate3247], c.population=PopulationCertificates.Batch029.certificate590
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers885 {x : ℝ} (hx : certificate885.interval.Contains x) : ∃ c∈certificate885.cells, c.region.interval.Contains x := rat_cut_group_covers certificate885 numericValid885 hx

def certificate886 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate590,PopulationCertificates.Batch029.certificate590,[MergedCutCells.Batch270.certificate3248,MergedCutCells.Batch270.certificate3249,MergedCutCells.Batch270.certificate3250,MergedCutCells.Batch270.certificate3251,MergedCutCells.Batch271.certificate3252,MergedCutCells.Batch271.certificate3253],(1098000021/1000000000),none,(1/2),(508151365870896057/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid886 : certificate886.NumericValid := by decide +kernel
theorem cellsSound886 : ∀ c∈certificate886.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3248,MergedCutCells.Batch270.certificate3249,MergedCutCells.Batch270.certificate3250,MergedCutCells.Batch270.certificate3251,MergedCutCells.Batch271.certificate3252,MergedCutCells.Batch271.certificate3253], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3248,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3250,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.sound3251,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3252,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3253,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric886 : ∀ c∈certificate886.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3248,MergedCutCells.Batch270.certificate3249,MergedCutCells.Batch270.certificate3250,MergedCutCells.Batch270.certificate3251,MergedCutCells.Batch271.certificate3252,MergedCutCells.Batch271.certificate3253], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3248,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3250,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch270.numericValid3251,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3252,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3253,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid886 : ∀ c∈certificate886.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3248,MergedCutCells.Batch270.certificate3249,MergedCutCells.Batch270.certificate3250,MergedCutCells.Batch270.certificate3251,MergedCutCells.Batch271.certificate3252,MergedCutCells.Batch271.certificate3253], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches886 : ∀ c∈certificate886.cells, c.population=certificate886.population := by
  change ∀ c∈[MergedCutCells.Batch270.certificate3248,MergedCutCells.Batch270.certificate3249,MergedCutCells.Batch270.certificate3250,MergedCutCells.Batch270.certificate3251,MergedCutCells.Batch271.certificate3252,MergedCutCells.Batch271.certificate3253], c.population=PopulationCertificates.Batch029.certificate590
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers886 {x : ℝ} (hx : certificate886.interval.Contains x) : ∃ c∈certificate886.cells, c.region.interval.Contains x := rat_cut_group_covers certificate886 numericValid886 hx

def certificate887 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate591,PopulationCertificates.Batch029.certificate591,[MergedCutCells.Batch271.certificate3254,MergedCutCells.Batch271.certificate3255,MergedCutCells.Batch271.certificate3256],(4967463689661759691/500000000000000000),none,(1/2),(159607493680965661/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid887 : certificate887.NumericValid := by decide +kernel
theorem cellsSound887 : ∀ c∈certificate887.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3254,MergedCutCells.Batch271.certificate3255,MergedCutCells.Batch271.certificate3256], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3254,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3255,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.sound3256,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric887 : ∀ c∈certificate887.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3254,MergedCutCells.Batch271.certificate3255,MergedCutCells.Batch271.certificate3256], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3254,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3255,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch271.numericValid3256,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid887 : ∀ c∈certificate887.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3254,MergedCutCells.Batch271.certificate3255,MergedCutCells.Batch271.certificate3256], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches887 : ∀ c∈certificate887.cells, c.population=certificate887.population := by
  change ∀ c∈[MergedCutCells.Batch271.certificate3254,MergedCutCells.Batch271.certificate3255,MergedCutCells.Batch271.certificate3256], c.population=PopulationCertificates.Batch029.certificate591
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers887 {x : ℝ} (hx : certificate887.interval.Contains x) : ∃ c∈certificate887.cells, c.region.interval.Contains x := rat_cut_group_covers certificate887 numericValid887 hx

end Cycle12.MergedCutGroups.Batch073
