import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch019
import Cycle12.MergedCutCells.Batch182
import Cycle12.MergedCutCells.Batch183
import Cycle12.MergedCutCells.Batch184
import Cycle12.MergedCutCells.Batch185
import Cycle12.MergedCutCells.Batch186
import Cycle12.PopulationCertificates.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch049

def certificate588 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate392,PopulationCertificates.Batch019.certificate392,[MergedCutCells.Batch182.certificate2190,MergedCutCells.Batch182.certificate2191,MergedCutCells.Batch182.certificate2192],(709953848600681293/1000000000000000000),(some (221080411/200000000)),(1/2),(370773505007979931/1000000000000000000),(some (277352032182423581/1000000000000000000)),(some (39710308556658193/500000000000000000))⟩
theorem numericValid588 : certificate588.NumericValid := by decide +kernel
theorem cellsSound588 : ∀ c∈certificate588.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2190,MergedCutCells.Batch182.certificate2191,MergedCutCells.Batch182.certificate2192], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2192,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric588 : ∀ c∈certificate588.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2190,MergedCutCells.Batch182.certificate2191,MergedCutCells.Batch182.certificate2192], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2192,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid588 : ∀ c∈certificate588.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2190,MergedCutCells.Batch182.certificate2191,MergedCutCells.Batch182.certificate2192], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid197,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid197,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid197,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches588 : ∀ c∈certificate588.cells, c.population=certificate588.population := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2190,MergedCutCells.Batch182.certificate2191,MergedCutCells.Batch182.certificate2192], c.population=PopulationCertificates.Batch019.certificate392
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers588 {x : ℝ} (hx : certificate588.interval.Contains x) : ∃ c∈certificate588.cells, c.region.interval.Contains x := rat_cut_group_covers certificate588 numericValid588 hx

def certificate589 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate392,PopulationCertificates.Batch019.certificate392,[MergedCutCells.Batch182.certificate2193,MergedCutCells.Batch182.certificate2194,MergedCutCells.Batch182.certificate2195,MergedCutCells.Batch183.certificate2196,MergedCutCells.Batch183.certificate2197,MergedCutCells.Batch183.certificate2198],(221080411/200000000),none,(1/2),(347220989530477379/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid589 : certificate589.NumericValid := by decide +kernel
theorem cellsSound589 : ∀ c∈certificate589.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2193,MergedCutCells.Batch182.certificate2194,MergedCutCells.Batch182.certificate2195,MergedCutCells.Batch183.certificate2196,MergedCutCells.Batch183.certificate2197,MergedCutCells.Batch183.certificate2198], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2194,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2196,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2198,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric589 : ∀ c∈certificate589.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2193,MergedCutCells.Batch182.certificate2194,MergedCutCells.Batch182.certificate2195,MergedCutCells.Batch183.certificate2196,MergedCutCells.Batch183.certificate2197,MergedCutCells.Batch183.certificate2198], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2194,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2196,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2198,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid589 : ∀ c∈certificate589.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2193,MergedCutCells.Batch182.certificate2194,MergedCutCells.Batch182.certificate2195,MergedCutCells.Batch183.certificate2196,MergedCutCells.Batch183.certificate2197,MergedCutCells.Batch183.certificate2198], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches589 : ∀ c∈certificate589.cells, c.population=certificate589.population := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2193,MergedCutCells.Batch182.certificate2194,MergedCutCells.Batch182.certificate2195,MergedCutCells.Batch183.certificate2196,MergedCutCells.Batch183.certificate2197,MergedCutCells.Batch183.certificate2198], c.population=PopulationCertificates.Batch019.certificate392
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers589 {x : ℝ} (hx : certificate589.interval.Contains x) : ∃ c∈certificate589.cells, c.region.interval.Contains x := rat_cut_group_covers certificate589 numericValid589 hx

def certificate590 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate393,PopulationCertificates.Batch019.certificate393,[MergedCutCells.Batch183.certificate2199,MergedCutCells.Batch183.certificate2200,MergedCutCells.Batch183.certificate2201,MergedCutCells.Batch183.certificate2202],(1106372932670419711/200000000000000000),none,(1/2),(1213859319422571359/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid590 : certificate590.NumericValid := by decide +kernel
theorem cellsSound590 : ∀ c∈certificate590.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2199,MergedCutCells.Batch183.certificate2200,MergedCutCells.Batch183.certificate2201,MergedCutCells.Batch183.certificate2202], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2200,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2202,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric590 : ∀ c∈certificate590.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2199,MergedCutCells.Batch183.certificate2200,MergedCutCells.Batch183.certificate2201,MergedCutCells.Batch183.certificate2202], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2200,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2202,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid590 : ∀ c∈certificate590.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2199,MergedCutCells.Batch183.certificate2200,MergedCutCells.Batch183.certificate2201,MergedCutCells.Batch183.certificate2202], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches590 : ∀ c∈certificate590.cells, c.population=certificate590.population := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2199,MergedCutCells.Batch183.certificate2200,MergedCutCells.Batch183.certificate2201,MergedCutCells.Batch183.certificate2202], c.population=PopulationCertificates.Batch019.certificate393
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers590 {x : ℝ} (hx : certificate590.interval.Contains x) : ∃ c∈certificate590.cells, c.region.interval.Contains x := rat_cut_group_covers certificate590 numericValid590 hx

def certificate591 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate394,PopulationCertificates.Batch019.certificate394,[MergedCutCells.Batch183.certificate2203,MergedCutCells.Batch183.certificate2204,MergedCutCells.Batch183.certificate2205],(179804726978959889/250000000000000000),(some (546903039/500000000)),(1/2),(79297573377528679/200000000000000000),(some (288678771919485961/1000000000000000000)),(some (84103450378641463/1000000000000000000))⟩
theorem numericValid591 : certificate591.NumericValid := by decide +kernel
theorem cellsSound591 : ∀ c∈certificate591.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2203,MergedCutCells.Batch183.certificate2204,MergedCutCells.Batch183.certificate2205], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2203,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2205,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric591 : ∀ c∈certificate591.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2203,MergedCutCells.Batch183.certificate2204,MergedCutCells.Batch183.certificate2205], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2203,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2205,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid591 : ∀ c∈certificate591.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2203,MergedCutCells.Batch183.certificate2204,MergedCutCells.Batch183.certificate2205], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid198,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid198,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid198,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches591 : ∀ c∈certificate591.cells, c.population=certificate591.population := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2203,MergedCutCells.Batch183.certificate2204,MergedCutCells.Batch183.certificate2205], c.population=PopulationCertificates.Batch019.certificate394
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers591 {x : ℝ} (hx : certificate591.interval.Contains x) : ∃ c∈certificate591.cells, c.region.interval.Contains x := rat_cut_group_covers certificate591 numericValid591 hx

def certificate592 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate394,PopulationCertificates.Batch019.certificate394,[MergedCutCells.Batch183.certificate2206,MergedCutCells.Batch183.certificate2207,MergedCutCells.Batch184.certificate2208,MergedCutCells.Batch184.certificate2209,MergedCutCells.Batch184.certificate2210,MergedCutCells.Batch184.certificate2211],(546903039/500000000),none,(1/2),(367643430712388469/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid592 : certificate592.NumericValid := by decide +kernel
theorem cellsSound592 : ∀ c∈certificate592.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2206,MergedCutCells.Batch183.certificate2207,MergedCutCells.Batch184.certificate2208,MergedCutCells.Batch184.certificate2209,MergedCutCells.Batch184.certificate2210,MergedCutCells.Batch184.certificate2211], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2206,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.sound2207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2208,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2209,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2210,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2211,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric592 : ∀ c∈certificate592.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2206,MergedCutCells.Batch183.certificate2207,MergedCutCells.Batch184.certificate2208,MergedCutCells.Batch184.certificate2209,MergedCutCells.Batch184.certificate2210,MergedCutCells.Batch184.certificate2211], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2206,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch183.numericValid2207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2208,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2209,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2210,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2211,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid592 : ∀ c∈certificate592.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2206,MergedCutCells.Batch183.certificate2207,MergedCutCells.Batch184.certificate2208,MergedCutCells.Batch184.certificate2209,MergedCutCells.Batch184.certificate2210,MergedCutCells.Batch184.certificate2211], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches592 : ∀ c∈certificate592.cells, c.population=certificate592.population := by
  change ∀ c∈[MergedCutCells.Batch183.certificate2206,MergedCutCells.Batch183.certificate2207,MergedCutCells.Batch184.certificate2208,MergedCutCells.Batch184.certificate2209,MergedCutCells.Batch184.certificate2210,MergedCutCells.Batch184.certificate2211], c.population=PopulationCertificates.Batch019.certificate394
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers592 {x : ℝ} (hx : certificate592.interval.Contains x) : ∃ c∈certificate592.cells, c.region.interval.Contains x := rat_cut_group_covers certificate592 numericValid592 hx

def certificate593 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate395,PopulationCertificates.Batch019.certificate395,[MergedCutCells.Batch184.certificate2212,MergedCutCells.Batch184.certificate2213,MergedCutCells.Batch184.certificate2214],(5570345173891081219/1000000000000000000),none,(1/2),(2496070173489338957/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid593 : certificate593.NumericValid := by decide +kernel
theorem cellsSound593 : ∀ c∈certificate593.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2212,MergedCutCells.Batch184.certificate2213,MergedCutCells.Batch184.certificate2214], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2212,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2214,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric593 : ∀ c∈certificate593.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2212,MergedCutCells.Batch184.certificate2213,MergedCutCells.Batch184.certificate2214], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2212,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2214,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid593 : ∀ c∈certificate593.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2212,MergedCutCells.Batch184.certificate2213,MergedCutCells.Batch184.certificate2214], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches593 : ∀ c∈certificate593.cells, c.population=certificate593.population := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2212,MergedCutCells.Batch184.certificate2213,MergedCutCells.Batch184.certificate2214], c.population=PopulationCertificates.Batch019.certificate395
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers593 {x : ℝ} (hx : certificate593.interval.Contains x) : ∃ c∈certificate593.cells, c.region.interval.Contains x := rat_cut_group_covers certificate593 numericValid593 hx

def certificate594 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate396,PopulationCertificates.Batch019.certificate396,[MergedCutCells.Batch184.certificate2215,MergedCutCells.Batch184.certificate2216,MergedCutCells.Batch184.certificate2217],(181316337673256881/250000000000000000),(some (1102139467/1000000000)),(1/2),(80892436105359093/200000000000000000),(some (75237018950673119/250000000000000000)),(some (89314123107793603/1000000000000000000))⟩
theorem numericValid594 : certificate594.NumericValid := by decide +kernel
theorem cellsSound594 : ∀ c∈certificate594.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2215,MergedCutCells.Batch184.certificate2216,MergedCutCells.Batch184.certificate2217], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2216,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2217,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric594 : ∀ c∈certificate594.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2215,MergedCutCells.Batch184.certificate2216,MergedCutCells.Batch184.certificate2217], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2216,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2217,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid594 : ∀ c∈certificate594.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2215,MergedCutCells.Batch184.certificate2216,MergedCutCells.Batch184.certificate2217], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid199,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid199,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid199,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches594 : ∀ c∈certificate594.cells, c.population=certificate594.population := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2215,MergedCutCells.Batch184.certificate2216,MergedCutCells.Batch184.certificate2217], c.population=PopulationCertificates.Batch019.certificate396
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers594 {x : ℝ} (hx : certificate594.interval.Contains x) : ∃ c∈certificate594.cells, c.region.interval.Contains x := rat_cut_group_covers certificate594 numericValid594 hx

def certificate595 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate396,PopulationCertificates.Batch019.certificate396,[MergedCutCells.Batch184.certificate2218,MergedCutCells.Batch184.certificate2219,MergedCutCells.Batch185.certificate2220,MergedCutCells.Batch185.certificate2221,MergedCutCells.Batch185.certificate2222],(1102139467/1000000000),none,(1/2),(376787423798761059/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid595 : certificate595.NumericValid := by decide +kernel
theorem cellsSound595 : ∀ c∈certificate595.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2218,MergedCutCells.Batch184.certificate2219,MergedCutCells.Batch185.certificate2220,MergedCutCells.Batch185.certificate2221,MergedCutCells.Batch185.certificate2222], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2218,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.sound2219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2220,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2221,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2222,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric595 : ∀ c∈certificate595.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2218,MergedCutCells.Batch184.certificate2219,MergedCutCells.Batch185.certificate2220,MergedCutCells.Batch185.certificate2221,MergedCutCells.Batch185.certificate2222], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2218,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch184.numericValid2219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2220,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2221,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2222,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid595 : ∀ c∈certificate595.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2218,MergedCutCells.Batch184.certificate2219,MergedCutCells.Batch185.certificate2220,MergedCutCells.Batch185.certificate2221,MergedCutCells.Batch185.certificate2222], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches595 : ∀ c∈certificate595.cells, c.population=certificate595.population := by
  change ∀ c∈[MergedCutCells.Batch184.certificate2218,MergedCutCells.Batch184.certificate2219,MergedCutCells.Batch185.certificate2220,MergedCutCells.Batch185.certificate2221,MergedCutCells.Batch185.certificate2222], c.population=PopulationCertificates.Batch019.certificate396
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers595 {x : ℝ} (hx : certificate595.interval.Contains x) : ∃ c∈certificate595.cells, c.region.interval.Contains x := rat_cut_group_covers certificate595 numericValid595 hx

def certificate596 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate397,PopulationCertificates.Batch019.certificate397,[MergedCutCells.Batch185.certificate2223,MergedCutCells.Batch185.certificate2224,MergedCutCells.Batch185.certificate2225],(2760472614039432963/500000000000000000),none,(1/2),(1242625340363905671/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid596 : certificate596.NumericValid := by decide +kernel
theorem cellsSound596 : ∀ c∈certificate596.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2223,MergedCutCells.Batch185.certificate2224,MergedCutCells.Batch185.certificate2225], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2223,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2225,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric596 : ∀ c∈certificate596.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2223,MergedCutCells.Batch185.certificate2224,MergedCutCells.Batch185.certificate2225], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2223,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2225,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid596 : ∀ c∈certificate596.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2223,MergedCutCells.Batch185.certificate2224,MergedCutCells.Batch185.certificate2225], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches596 : ∀ c∈certificate596.cells, c.population=certificate596.population := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2223,MergedCutCells.Batch185.certificate2224,MergedCutCells.Batch185.certificate2225], c.population=PopulationCertificates.Batch019.certificate397
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers596 {x : ℝ} (hx : certificate596.interval.Contains x) : ∃ c∈certificate596.cells, c.region.interval.Contains x := rat_cut_group_covers certificate596 numericValid596 hx

def certificate597 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate398,PopulationCertificates.Batch019.certificate398,[MergedCutCells.Batch185.certificate2226,MergedCutCells.Batch185.certificate2227,MergedCutCells.Batch185.certificate2228],(182628350596971551/250000000000000000),(some (1082435361/1000000000)),(1/2),(16520903034796389/40000000000000000),(some (311771963675537541/1000000000000000000)),(some (23508387100578811/250000000000000000))⟩
theorem numericValid597 : certificate597.NumericValid := by decide +kernel
theorem cellsSound597 : ∀ c∈certificate597.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2226,MergedCutCells.Batch185.certificate2227,MergedCutCells.Batch185.certificate2228], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2226,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2227,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2228,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric597 : ∀ c∈certificate597.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2226,MergedCutCells.Batch185.certificate2227,MergedCutCells.Batch185.certificate2228], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2226,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2227,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2228,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid597 : ∀ c∈certificate597.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2226,MergedCutCells.Batch185.certificate2227,MergedCutCells.Batch185.certificate2228], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid200,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid200,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid200,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches597 : ∀ c∈certificate597.cells, c.population=certificate597.population := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2226,MergedCutCells.Batch185.certificate2227,MergedCutCells.Batch185.certificate2228], c.population=PopulationCertificates.Batch019.certificate398
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers597 {x : ℝ} (hx : certificate597.interval.Contains x) : ∃ c∈certificate597.cells, c.region.interval.Contains x := rat_cut_group_covers certificate597 numericValid597 hx

def certificate598 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate398,PopulationCertificates.Batch019.certificate398,[MergedCutCells.Batch185.certificate2229,MergedCutCells.Batch185.certificate2230,MergedCutCells.Batch185.certificate2231,MergedCutCells.Batch186.certificate2232,MergedCutCells.Batch186.certificate2233,MergedCutCells.Batch186.certificate2234],(1082435361/1000000000),none,(1/2),(96497795871292411/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid598 : certificate598.NumericValid := by decide +kernel
theorem cellsSound598 : ∀ c∈certificate598.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2229,MergedCutCells.Batch185.certificate2230,MergedCutCells.Batch185.certificate2231,MergedCutCells.Batch186.certificate2232,MergedCutCells.Batch186.certificate2233,MergedCutCells.Batch186.certificate2234], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2229,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.sound2231,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2232,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2233,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2234,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric598 : ∀ c∈certificate598.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2229,MergedCutCells.Batch185.certificate2230,MergedCutCells.Batch185.certificate2231,MergedCutCells.Batch186.certificate2232,MergedCutCells.Batch186.certificate2233,MergedCutCells.Batch186.certificate2234], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2229,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch185.numericValid2231,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2232,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2233,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2234,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid598 : ∀ c∈certificate598.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2229,MergedCutCells.Batch185.certificate2230,MergedCutCells.Batch185.certificate2231,MergedCutCells.Batch186.certificate2232,MergedCutCells.Batch186.certificate2233,MergedCutCells.Batch186.certificate2234], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches598 : ∀ c∈certificate598.cells, c.population=certificate598.population := by
  change ∀ c∈[MergedCutCells.Batch185.certificate2229,MergedCutCells.Batch185.certificate2230,MergedCutCells.Batch185.certificate2231,MergedCutCells.Batch186.certificate2232,MergedCutCells.Batch186.certificate2233,MergedCutCells.Batch186.certificate2234], c.population=PopulationCertificates.Batch019.certificate398
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers598 {x : ℝ} (hx : certificate598.interval.Contains x) : ∃ c∈certificate598.cells, c.region.interval.Contains x := rat_cut_group_covers certificate598 numericValid598 hx

def certificate599 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate399,PopulationCertificates.Batch019.certificate399,[MergedCutCells.Batch186.certificate2235,MergedCutCells.Batch186.certificate2236,MergedCutCells.Batch186.certificate2237,MergedCutCells.Batch186.certificate2238],(5584853422746910891/1000000000000000000),none,(1/2),(63972562835254863/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid599 : certificate599.NumericValid := by decide +kernel
theorem cellsSound599 : ∀ c∈certificate599.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2235,MergedCutCells.Batch186.certificate2236,MergedCutCells.Batch186.certificate2237,MergedCutCells.Batch186.certificate2238], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2235,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2237,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2238,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric599 : ∀ c∈certificate599.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2235,MergedCutCells.Batch186.certificate2236,MergedCutCells.Batch186.certificate2237,MergedCutCells.Batch186.certificate2238], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2235,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2237,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2238,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid599 : ∀ c∈certificate599.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2235,MergedCutCells.Batch186.certificate2236,MergedCutCells.Batch186.certificate2237,MergedCutCells.Batch186.certificate2238], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches599 : ∀ c∈certificate599.cells, c.population=certificate599.population := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2235,MergedCutCells.Batch186.certificate2236,MergedCutCells.Batch186.certificate2237,MergedCutCells.Batch186.certificate2238], c.population=PopulationCertificates.Batch019.certificate399
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers599 {x : ℝ} (hx : certificate599.interval.Contains x) : ∃ c∈certificate599.cells, c.region.interval.Contains x := rat_cut_group_covers certificate599 numericValid599 hx

end Cycle12.MergedCutGroups.Batch049
