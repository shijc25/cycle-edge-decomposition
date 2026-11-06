import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch020
import Cycle12.MergedCutCells.Batch186
import Cycle12.MergedCutCells.Batch187
import Cycle12.MergedCutCells.Batch188
import Cycle12.MergedCutCells.Batch189
import Cycle12.MergedCutCells.Batch190
import Cycle12.PopulationCertificates.Batch020

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch050

def certificate600 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate400,PopulationCertificates.Batch020.certificate400,[MergedCutCells.Batch186.certificate2239,MergedCutCells.Batch186.certificate2240,MergedCutCells.Batch186.certificate2241],(92461593952214569/125000000000000000),(some (1070500521/1000000000)),(1/2),(55240989140262303/125000000000000000),(some (322982900044554667/1000000000000000000)),(some (386900471175293/3906250000000000))⟩
theorem numericValid600 : certificate600.NumericValid := by decide +kernel
theorem cellsSound600 : ∀ c∈certificate600.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2239,MergedCutCells.Batch186.certificate2240,MergedCutCells.Batch186.certificate2241], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2239,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2241,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric600 : ∀ c∈certificate600.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2239,MergedCutCells.Batch186.certificate2240,MergedCutCells.Batch186.certificate2241], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2239,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2241,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid600 : ∀ c∈certificate600.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2239,MergedCutCells.Batch186.certificate2240,MergedCutCells.Batch186.certificate2241], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid201,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid201,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid201,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches600 : ∀ c∈certificate600.cells, c.population=certificate600.population := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2239,MergedCutCells.Batch186.certificate2240,MergedCutCells.Batch186.certificate2241], c.population=PopulationCertificates.Batch020.certificate400
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers600 {x : ℝ} (hx : certificate600.interval.Contains x) : ∃ c∈certificate600.cells, c.region.interval.Contains x := rat_cut_group_covers certificate600 numericValid600 hx

def certificate601 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate400,PopulationCertificates.Batch020.certificate400,[MergedCutCells.Batch186.certificate2242,MergedCutCells.Batch186.certificate2243,MergedCutCells.Batch187.certificate2244,MergedCutCells.Batch187.certificate2245,MergedCutCells.Batch187.certificate2246,MergedCutCells.Batch187.certificate2247,MergedCutCells.Batch187.certificate2248],(1070500521/1000000000),none,(1/2),(102059218024398093/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid601 : certificate601.NumericValid := by decide +kernel
theorem cellsSound601 : ∀ c∈certificate601.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2242,MergedCutCells.Batch186.certificate2243,MergedCutCells.Batch187.certificate2244,MergedCutCells.Batch187.certificate2245,MergedCutCells.Batch187.certificate2246,MergedCutCells.Batch187.certificate2247,MergedCutCells.Batch187.certificate2248], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.sound2243,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2244,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2245,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2247,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2248,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric601 : ∀ c∈certificate601.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2242,MergedCutCells.Batch186.certificate2243,MergedCutCells.Batch187.certificate2244,MergedCutCells.Batch187.certificate2245,MergedCutCells.Batch187.certificate2246,MergedCutCells.Batch187.certificate2247,MergedCutCells.Batch187.certificate2248], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch186.numericValid2243,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2244,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2245,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2247,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2248,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid601 : ∀ c∈certificate601.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2242,MergedCutCells.Batch186.certificate2243,MergedCutCells.Batch187.certificate2244,MergedCutCells.Batch187.certificate2245,MergedCutCells.Batch187.certificate2246,MergedCutCells.Batch187.certificate2247,MergedCutCells.Batch187.certificate2248], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches601 : ∀ c∈certificate601.cells, c.population=certificate601.population := by
  change ∀ c∈[MergedCutCells.Batch186.certificate2242,MergedCutCells.Batch186.certificate2243,MergedCutCells.Batch187.certificate2244,MergedCutCells.Batch187.certificate2245,MergedCutCells.Batch187.certificate2246,MergedCutCells.Batch187.certificate2247,MergedCutCells.Batch187.certificate2248], c.population=PopulationCertificates.Batch020.certificate400
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers601 {x : ℝ} (hx : certificate601.interval.Contains x) : ∃ c∈certificate601.cells, c.region.interval.Contains x := rat_cut_group_covers certificate601 numericValid601 hx

def certificate602 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate401,PopulationCertificates.Batch020.certificate401,[MergedCutCells.Batch187.certificate2249,MergedCutCells.Batch187.certificate2250,MergedCutCells.Batch187.certificate2251],(2758099265466254753/500000000000000000),none,(1/2),(2549446656075021943/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid602 : certificate602.NumericValid := by decide +kernel
theorem cellsSound602 : ∀ c∈certificate602.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2249,MergedCutCells.Batch187.certificate2250,MergedCutCells.Batch187.certificate2251], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2250,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2251,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric602 : ∀ c∈certificate602.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2249,MergedCutCells.Batch187.certificate2250,MergedCutCells.Batch187.certificate2251], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2250,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2251,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid602 : ∀ c∈certificate602.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2249,MergedCutCells.Batch187.certificate2250,MergedCutCells.Batch187.certificate2251], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches602 : ∀ c∈certificate602.cells, c.population=certificate602.population := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2249,MergedCutCells.Batch187.certificate2250,MergedCutCells.Batch187.certificate2251], c.population=PopulationCertificates.Batch020.certificate401
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers602 {x : ℝ} (hx : certificate602.interval.Contains x) : ∃ c∈certificate602.cells, c.region.interval.Contains x := rat_cut_group_covers certificate602 numericValid602 hx

def certificate603 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate402,PopulationCertificates.Batch020.certificate402,[MergedCutCells.Batch187.certificate2252,MergedCutCells.Batch187.certificate2253,MergedCutCells.Batch187.certificate2254],(148964472922620521/200000000000000000),(some (538653521/500000000)),(1/2),(224202336795779119/500000000000000000),(some (67076678082807937/200000000000000000)),(some (104744045682349229/1000000000000000000))⟩
theorem numericValid603 : certificate603.NumericValid := by decide +kernel
theorem cellsSound603 : ∀ c∈certificate603.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2252,MergedCutCells.Batch187.certificate2253,MergedCutCells.Batch187.certificate2254], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2252,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2253,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2254,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric603 : ∀ c∈certificate603.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2252,MergedCutCells.Batch187.certificate2253,MergedCutCells.Batch187.certificate2254], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2252,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2253,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2254,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid603 : ∀ c∈certificate603.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2252,MergedCutCells.Batch187.certificate2253,MergedCutCells.Batch187.certificate2254], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid202,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid202,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid202,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches603 : ∀ c∈certificate603.cells, c.population=certificate603.population := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2252,MergedCutCells.Batch187.certificate2253,MergedCutCells.Batch187.certificate2254], c.population=PopulationCertificates.Batch020.certificate402
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers603 {x : ℝ} (hx : certificate603.interval.Contains x) : ∃ c∈certificate603.cells, c.region.interval.Contains x := rat_cut_group_covers certificate603 numericValid603 hx

def certificate604 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate402,PopulationCertificates.Batch020.certificate402,[MergedCutCells.Batch187.certificate2255,MergedCutCells.Batch188.certificate2256,MergedCutCells.Batch188.certificate2257,MergedCutCells.Batch188.certificate2258,MergedCutCells.Batch188.certificate2259],(538653521/500000000),none,(1/2),(104382028167747477/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid604 : certificate604.NumericValid := by decide +kernel
theorem cellsSound604 : ∀ c∈certificate604.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2255,MergedCutCells.Batch188.certificate2256,MergedCutCells.Batch188.certificate2257,MergedCutCells.Batch188.certificate2258,MergedCutCells.Batch188.certificate2259], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.sound2255,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2256,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2258,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2259,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric604 : ∀ c∈certificate604.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2255,MergedCutCells.Batch188.certificate2256,MergedCutCells.Batch188.certificate2257,MergedCutCells.Batch188.certificate2258,MergedCutCells.Batch188.certificate2259], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch187.numericValid2255,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2256,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2258,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2259,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid604 : ∀ c∈certificate604.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2255,MergedCutCells.Batch188.certificate2256,MergedCutCells.Batch188.certificate2257,MergedCutCells.Batch188.certificate2258,MergedCutCells.Batch188.certificate2259], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches604 : ∀ c∈certificate604.cells, c.population=certificate604.population := by
  change ∀ c∈[MergedCutCells.Batch187.certificate2255,MergedCutCells.Batch188.certificate2256,MergedCutCells.Batch188.certificate2257,MergedCutCells.Batch188.certificate2258,MergedCutCells.Batch188.certificate2259], c.population=PopulationCertificates.Batch020.certificate402
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers604 {x : ℝ} (hx : certificate604.interval.Contains x) : ∃ c∈certificate604.cells, c.region.interval.Contains x := rat_cut_group_covers certificate604 numericValid604 hx

def certificate605 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate403,PopulationCertificates.Batch020.certificate403,[MergedCutCells.Batch188.certificate2260,MergedCutCells.Batch188.certificate2261,MergedCutCells.Batch188.certificate2262,MergedCutCells.Batch188.certificate2263],(1116426337608269407/200000000000000000),none,(1/2),(2626062081015005107/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid605 : certificate605.NumericValid := by decide +kernel
theorem cellsSound605 : ∀ c∈certificate605.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2260,MergedCutCells.Batch188.certificate2261,MergedCutCells.Batch188.certificate2262,MergedCutCells.Batch188.certificate2263], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2260,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2262,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2263,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric605 : ∀ c∈certificate605.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2260,MergedCutCells.Batch188.certificate2261,MergedCutCells.Batch188.certificate2262,MergedCutCells.Batch188.certificate2263], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2260,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2262,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2263,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid605 : ∀ c∈certificate605.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2260,MergedCutCells.Batch188.certificate2261,MergedCutCells.Batch188.certificate2262,MergedCutCells.Batch188.certificate2263], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches605 : ∀ c∈certificate605.cells, c.population=certificate605.population := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2260,MergedCutCells.Batch188.certificate2261,MergedCutCells.Batch188.certificate2262,MergedCutCells.Batch188.certificate2263], c.population=PopulationCertificates.Batch020.certificate403
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers605 {x : ℝ} (hx : certificate605.interval.Contains x) : ∃ c∈certificate605.cells, c.region.interval.Contains x := rat_cut_group_covers certificate605 numericValid605 hx

def certificate606 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate404,PopulationCertificates.Batch020.certificate404,[MergedCutCells.Batch188.certificate2264,MergedCutCells.Batch188.certificate2265,MergedCutCells.Batch188.certificate2266],(751422514635465529/1000000000000000000),(some (1059714431/1000000000)),(1/2),(1884306610631323/4000000000000000),(some (34600057485292531/100000000000000000)),(some (109753937664947501/1000000000000000000))⟩
theorem numericValid606 : certificate606.NumericValid := by decide +kernel
theorem cellsSound606 : ∀ c∈certificate606.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2264,MergedCutCells.Batch188.certificate2265,MergedCutCells.Batch188.certificate2266], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2264,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2265,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2266,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric606 : ∀ c∈certificate606.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2264,MergedCutCells.Batch188.certificate2265,MergedCutCells.Batch188.certificate2266], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2264,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2265,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2266,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid606 : ∀ c∈certificate606.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2264,MergedCutCells.Batch188.certificate2265,MergedCutCells.Batch188.certificate2266], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid203,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid203,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid203,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches606 : ∀ c∈certificate606.cells, c.population=certificate606.population := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2264,MergedCutCells.Batch188.certificate2265,MergedCutCells.Batch188.certificate2266], c.population=PopulationCertificates.Batch020.certificate404
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers606 {x : ℝ} (hx : certificate606.interval.Contains x) : ∃ c∈certificate606.cells, c.region.interval.Contains x := rat_cut_group_covers certificate606 numericValid606 hx

def certificate607 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate404,PopulationCertificates.Batch020.certificate404,[MergedCutCells.Batch188.certificate2267,MergedCutCells.Batch189.certificate2268,MergedCutCells.Batch189.certificate2269,MergedCutCells.Batch189.certificate2270,MergedCutCells.Batch189.certificate2271,MergedCutCells.Batch189.certificate2272,MergedCutCells.Batch189.certificate2273],(1059714431/1000000000),none,(1/2),(220957012723405677/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid607 : certificate607.NumericValid := by decide +kernel
theorem cellsSound607 : ∀ c∈certificate607.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2267,MergedCutCells.Batch189.certificate2268,MergedCutCells.Batch189.certificate2269,MergedCutCells.Batch189.certificate2270,MergedCutCells.Batch189.certificate2271,MergedCutCells.Batch189.certificate2272,MergedCutCells.Batch189.certificate2273], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.sound2267,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2268,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2270,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2271,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2272,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2273,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric607 : ∀ c∈certificate607.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2267,MergedCutCells.Batch189.certificate2268,MergedCutCells.Batch189.certificate2269,MergedCutCells.Batch189.certificate2270,MergedCutCells.Batch189.certificate2271,MergedCutCells.Batch189.certificate2272,MergedCutCells.Batch189.certificate2273], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch188.numericValid2267,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2268,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2270,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2271,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2272,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2273,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid607 : ∀ c∈certificate607.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2267,MergedCutCells.Batch189.certificate2268,MergedCutCells.Batch189.certificate2269,MergedCutCells.Batch189.certificate2270,MergedCutCells.Batch189.certificate2271,MergedCutCells.Batch189.certificate2272,MergedCutCells.Batch189.certificate2273], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches607 : ∀ c∈certificate607.cells, c.population=certificate607.population := by
  change ∀ c∈[MergedCutCells.Batch188.certificate2267,MergedCutCells.Batch189.certificate2268,MergedCutCells.Batch189.certificate2269,MergedCutCells.Batch189.certificate2270,MergedCutCells.Batch189.certificate2271,MergedCutCells.Batch189.certificate2272,MergedCutCells.Batch189.certificate2273], c.population=PopulationCertificates.Batch020.certificate404
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers607 {x : ℝ} (hx : certificate607.interval.Contains x) : ∃ c∈certificate607.cells, c.region.interval.Contains x := rat_cut_group_covers certificate607 numericValid607 hx

def certificate608 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate405,PopulationCertificates.Batch020.certificate405,[MergedCutCells.Batch189.certificate2274,MergedCutCells.Batch189.certificate2275,MergedCutCells.Batch189.certificate2276],(351625034862064007/62500000000000000),none,(1/2),(1351197730122491257/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid608 : certificate608.NumericValid := by decide +kernel
theorem cellsSound608 : ∀ c∈certificate608.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch189.certificate2274,MergedCutCells.Batch189.certificate2275,MergedCutCells.Batch189.certificate2276], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2274,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2276,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric608 : ∀ c∈certificate608.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch189.certificate2274,MergedCutCells.Batch189.certificate2275,MergedCutCells.Batch189.certificate2276], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2274,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2276,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid608 : ∀ c∈certificate608.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch189.certificate2274,MergedCutCells.Batch189.certificate2275,MergedCutCells.Batch189.certificate2276], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches608 : ∀ c∈certificate608.cells, c.population=certificate608.population := by
  change ∀ c∈[MergedCutCells.Batch189.certificate2274,MergedCutCells.Batch189.certificate2275,MergedCutCells.Batch189.certificate2276], c.population=PopulationCertificates.Batch020.certificate405
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers608 {x : ℝ} (hx : certificate608.interval.Contains x) : ∃ c∈certificate608.cells, c.region.interval.Contains x := rat_cut_group_covers certificate608 numericValid608 hx

def certificate609 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate406,PopulationCertificates.Batch020.certificate406,[MergedCutCells.Batch189.certificate2277,MergedCutCells.Batch189.certificate2278,MergedCutCells.Batch189.certificate2279],(759501992279100617/1000000000000000000),(some (1046173503/1000000000)),(1/2),(492033411609834187/1000000000000000000),(some (71449279241700871/200000000000000000)),(some (57598882409397597/500000000000000000))⟩
theorem numericValid609 : certificate609.NumericValid := by decide +kernel
theorem cellsSound609 : ∀ c∈certificate609.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch189.certificate2277,MergedCutCells.Batch189.certificate2278,MergedCutCells.Batch189.certificate2279], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2277,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2278,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.sound2279,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric609 : ∀ c∈certificate609.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch189.certificate2277,MergedCutCells.Batch189.certificate2278,MergedCutCells.Batch189.certificate2279], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2277,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2278,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch189.numericValid2279,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid609 : ∀ c∈certificate609.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch189.certificate2277,MergedCutCells.Batch189.certificate2278,MergedCutCells.Batch189.certificate2279], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid204,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid204,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid204,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches609 : ∀ c∈certificate609.cells, c.population=certificate609.population := by
  change ∀ c∈[MergedCutCells.Batch189.certificate2277,MergedCutCells.Batch189.certificate2278,MergedCutCells.Batch189.certificate2279], c.population=PopulationCertificates.Batch020.certificate406
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers609 {x : ℝ} (hx : certificate609.interval.Contains x) : ∃ c∈certificate609.cells, c.region.interval.Contains x := rat_cut_group_covers certificate609 numericValid609 hx

def certificate610 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate406,PopulationCertificates.Batch020.certificate406,[MergedCutCells.Batch190.certificate2280,MergedCutCells.Batch190.certificate2281,MergedCutCells.Batch190.certificate2282,MergedCutCells.Batch190.certificate2283,MergedCutCells.Batch190.certificate2284,MergedCutCells.Batch190.certificate2285,MergedCutCells.Batch190.certificate2286],(1046173503/1000000000),none,(1/2),(450405859520945233/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid610 : certificate610.NumericValid := by decide +kernel
theorem cellsSound610 : ∀ c∈certificate610.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2280,MergedCutCells.Batch190.certificate2281,MergedCutCells.Batch190.certificate2282,MergedCutCells.Batch190.certificate2283,MergedCutCells.Batch190.certificate2284,MergedCutCells.Batch190.certificate2285,MergedCutCells.Batch190.certificate2286], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2280,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2281,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2282,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2283,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2284,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2286,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric610 : ∀ c∈certificate610.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2280,MergedCutCells.Batch190.certificate2281,MergedCutCells.Batch190.certificate2282,MergedCutCells.Batch190.certificate2283,MergedCutCells.Batch190.certificate2284,MergedCutCells.Batch190.certificate2285,MergedCutCells.Batch190.certificate2286], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2280,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2281,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2282,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2283,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2284,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2286,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid610 : ∀ c∈certificate610.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2280,MergedCutCells.Batch190.certificate2281,MergedCutCells.Batch190.certificate2282,MergedCutCells.Batch190.certificate2283,MergedCutCells.Batch190.certificate2284,MergedCutCells.Batch190.certificate2285,MergedCutCells.Batch190.certificate2286], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches610 : ∀ c∈certificate610.cells, c.population=certificate610.population := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2280,MergedCutCells.Batch190.certificate2281,MergedCutCells.Batch190.certificate2282,MergedCutCells.Batch190.certificate2283,MergedCutCells.Batch190.certificate2284,MergedCutCells.Batch190.certificate2285,MergedCutCells.Batch190.certificate2286], c.population=PopulationCertificates.Batch020.certificate406
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers610 {x : ℝ} (hx : certificate610.interval.Contains x) : ∃ c∈certificate610.cells, c.region.interval.Contains x := rat_cut_group_covers certificate610 numericValid610 hx

def certificate611 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate407,PopulationCertificates.Batch020.certificate407,[MergedCutCells.Batch190.certificate2287,MergedCutCells.Batch190.certificate2288,MergedCutCells.Batch190.certificate2289],(1117147137904386749/200000000000000000),none,(1/2),(1349355795660451619/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid611 : certificate611.NumericValid := by decide +kernel
theorem cellsSound611 : ∀ c∈certificate611.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2287,MergedCutCells.Batch190.certificate2288,MergedCutCells.Batch190.certificate2289], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2288,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2289,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric611 : ∀ c∈certificate611.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2287,MergedCutCells.Batch190.certificate2288,MergedCutCells.Batch190.certificate2289], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2288,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2289,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid611 : ∀ c∈certificate611.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2287,MergedCutCells.Batch190.certificate2288,MergedCutCells.Batch190.certificate2289], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches611 : ∀ c∈certificate611.cells, c.population=certificate611.population := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2287,MergedCutCells.Batch190.certificate2288,MergedCutCells.Batch190.certificate2289], c.population=PopulationCertificates.Batch020.certificate407
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers611 {x : ℝ} (hx : certificate611.interval.Contains x) : ∃ c∈certificate611.cells, c.region.interval.Contains x := rat_cut_group_covers certificate611 numericValid611 hx

end Cycle12.MergedCutGroups.Batch050
