import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch018
import Cycle12.GeometryCertificates.Batch019
import Cycle12.MergedCutCells.Batch174
import Cycle12.MergedCutCells.Batch175
import Cycle12.MergedCutCells.Batch176
import Cycle12.MergedCutCells.Batch177
import Cycle12.MergedCutCells.Batch178
import Cycle12.PopulationCertificates.Batch018
import Cycle12.PopulationCertificates.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch047

def certificate564 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate376,PopulationCertificates.Batch018.certificate376,[MergedCutCells.Batch174.certificate2099,MergedCutCells.Batch175.certificate2100,MergedCutCells.Batch175.certificate2101],(654339282277167051/1000000000000000000),(some (591011367/500000000)),(1/2),(302721247639154277/1000000000000000000),(some (11738041118832793/62500000000000000)),(some (23205464231252837/500000000000000000))⟩
theorem numericValid564 : certificate564.NumericValid := by decide +kernel
theorem cellsSound564 : ∀ c∈certificate564.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2099,MergedCutCells.Batch175.certificate2100,MergedCutCells.Batch175.certificate2101], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2099,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2101,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric564 : ∀ c∈certificate564.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2099,MergedCutCells.Batch175.certificate2100,MergedCutCells.Batch175.certificate2101], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2099,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2101,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid564 : ∀ c∈certificate564.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2099,MergedCutCells.Batch175.certificate2100,MergedCutCells.Batch175.certificate2101], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid189,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid189,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid189,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches564 : ∀ c∈certificate564.cells, c.population=certificate564.population := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2099,MergedCutCells.Batch175.certificate2100,MergedCutCells.Batch175.certificate2101], c.population=PopulationCertificates.Batch018.certificate376
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers564 {x : ℝ} (hx : certificate564.interval.Contains x) : ∃ c∈certificate564.cells, c.region.interval.Contains x := rat_cut_group_covers certificate564 numericValid564 hx

def certificate565 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate376,PopulationCertificates.Batch018.certificate376,[MergedCutCells.Batch175.certificate2102,MergedCutCells.Batch175.certificate2103,MergedCutCells.Batch175.certificate2104,MergedCutCells.Batch175.certificate2105],(591011367/500000000),none,(1/2),(144535728625082709/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid565 : certificate565.NumericValid := by decide +kernel
theorem cellsSound565 : ∀ c∈certificate565.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2102,MergedCutCells.Batch175.certificate2103,MergedCutCells.Batch175.certificate2104,MergedCutCells.Batch175.certificate2105], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2102,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2103,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2104,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2105,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric565 : ∀ c∈certificate565.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2102,MergedCutCells.Batch175.certificate2103,MergedCutCells.Batch175.certificate2104,MergedCutCells.Batch175.certificate2105], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2102,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2103,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2104,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2105,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid565 : ∀ c∈certificate565.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2102,MergedCutCells.Batch175.certificate2103,MergedCutCells.Batch175.certificate2104,MergedCutCells.Batch175.certificate2105], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches565 : ∀ c∈certificate565.cells, c.population=certificate565.population := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2102,MergedCutCells.Batch175.certificate2103,MergedCutCells.Batch175.certificate2104,MergedCutCells.Batch175.certificate2105], c.population=PopulationCertificates.Batch018.certificate376
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers565 {x : ℝ} (hx : certificate565.interval.Contains x) : ∃ c∈certificate565.cells, c.region.interval.Contains x := rat_cut_group_covers certificate565 numericValid565 hx

def certificate566 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate377,PopulationCertificates.Batch018.certificate377,[MergedCutCells.Batch175.certificate2106,MergedCutCells.Batch175.certificate2107],(5264479815843020311/1000000000000000000),none,(1/2),(2060113860874920171/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid566 : certificate566.NumericValid := by decide +kernel
theorem cellsSound566 : ∀ c∈certificate566.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2106,MergedCutCells.Batch175.certificate2107], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2107,List.forall_mem_nil _⟩⟩
theorem cellsNumeric566 : ∀ c∈certificate566.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2106,MergedCutCells.Batch175.certificate2107], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2107,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid566 : ∀ c∈certificate566.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2106,MergedCutCells.Batch175.certificate2107], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches566 : ∀ c∈certificate566.cells, c.population=certificate566.population := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2106,MergedCutCells.Batch175.certificate2107], c.population=PopulationCertificates.Batch018.certificate377
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers566 {x : ℝ} (hx : certificate566.interval.Contains x) : ∃ c∈certificate566.cells, c.region.interval.Contains x := rat_cut_group_covers certificate566 numericValid566 hx

def certificate567 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate378,PopulationCertificates.Batch018.certificate378,[MergedCutCells.Batch175.certificate2108,MergedCutCells.Batch175.certificate2109],(132461980496036479/200000000000000000),(some (582777697/500000000)),(1/2),(15799988964764117/50000000000000000),(some (49601519009939791/250000000000000000)),(some (9992585831274823/200000000000000000))⟩
theorem numericValid567 : certificate567.NumericValid := by decide +kernel
theorem cellsSound567 : ∀ c∈certificate567.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2108,MergedCutCells.Batch175.certificate2109], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2109,List.forall_mem_nil _⟩⟩
theorem cellsNumeric567 : ∀ c∈certificate567.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2108,MergedCutCells.Batch175.certificate2109], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2109,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid567 : ∀ c∈certificate567.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2108,MergedCutCells.Batch175.certificate2109], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid190,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid190,List.forall_mem_nil _⟩⟩
theorem populationMatches567 : ∀ c∈certificate567.cells, c.population=certificate567.population := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2108,MergedCutCells.Batch175.certificate2109], c.population=PopulationCertificates.Batch018.certificate378
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers567 {x : ℝ} (hx : certificate567.interval.Contains x) : ∃ c∈certificate567.cells, c.region.interval.Contains x := rat_cut_group_covers certificate567 numericValid567 hx

def certificate568 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate378,PopulationCertificates.Batch018.certificate378,[MergedCutCells.Batch175.certificate2110,MergedCutCells.Batch175.certificate2111,MergedCutCells.Batch176.certificate2112,MergedCutCells.Batch176.certificate2113,MergedCutCells.Batch176.certificate2114],(582777697/500000000),none,(1/2),(75396907248519747/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid568 : certificate568.NumericValid := by decide +kernel
theorem cellsSound568 : ∀ c∈certificate568.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2110,MergedCutCells.Batch175.certificate2111,MergedCutCells.Batch176.certificate2112,MergedCutCells.Batch176.certificate2113,MergedCutCells.Batch176.certificate2114], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2110,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.sound2111,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2114,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric568 : ∀ c∈certificate568.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2110,MergedCutCells.Batch175.certificate2111,MergedCutCells.Batch176.certificate2112,MergedCutCells.Batch176.certificate2113,MergedCutCells.Batch176.certificate2114], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2110,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch175.numericValid2111,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2114,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid568 : ∀ c∈certificate568.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2110,MergedCutCells.Batch175.certificate2111,MergedCutCells.Batch176.certificate2112,MergedCutCells.Batch176.certificate2113,MergedCutCells.Batch176.certificate2114], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches568 : ∀ c∈certificate568.cells, c.population=certificate568.population := by
  change ∀ c∈[MergedCutCells.Batch175.certificate2110,MergedCutCells.Batch175.certificate2111,MergedCutCells.Batch176.certificate2112,MergedCutCells.Batch176.certificate2113,MergedCutCells.Batch176.certificate2114], c.population=PopulationCertificates.Batch018.certificate378
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers568 {x : ℝ} (hx : certificate568.interval.Contains x) : ∃ c∈certificate568.cells, c.region.interval.Contains x := rat_cut_group_covers certificate568 numericValid568 hx

def certificate569 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate379,PopulationCertificates.Batch018.certificate379,[MergedCutCells.Batch176.certificate2115,MergedCutCells.Batch176.certificate2116],(5316065545981350163/1000000000000000000),none,(1/2),(1061976940717695947/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid569 : certificate569.NumericValid := by decide +kernel
theorem cellsSound569 : ∀ c∈certificate569.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2115,MergedCutCells.Batch176.certificate2116], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2115,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2116,List.forall_mem_nil _⟩⟩
theorem cellsNumeric569 : ∀ c∈certificate569.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2115,MergedCutCells.Batch176.certificate2116], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2115,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2116,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid569 : ∀ c∈certificate569.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2115,MergedCutCells.Batch176.certificate2116], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches569 : ∀ c∈certificate569.cells, c.population=certificate569.population := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2115,MergedCutCells.Batch176.certificate2116], c.population=PopulationCertificates.Batch018.certificate379
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers569 {x : ℝ} (hx : certificate569.interval.Contains x) : ∃ c∈certificate569.cells, c.region.interval.Contains x := rat_cut_group_covers certificate569 numericValid569 hx

def certificate570 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate380,PopulationCertificates.Batch019.certificate380,[MergedCutCells.Batch176.certificate2117,MergedCutCells.Batch176.certificate2118,MergedCutCells.Batch176.certificate2119],(669857839769253171/1000000000000000000),(some (46081389/40000000)),(1/2),(321623980159204659/1000000000000000000),(some (209544572995488657/1000000000000000000)),(some (13449036219553173/250000000000000000))⟩
theorem numericValid570 : certificate570.NumericValid := by decide +kernel
theorem cellsSound570 : ∀ c∈certificate570.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2117,MergedCutCells.Batch176.certificate2118,MergedCutCells.Batch176.certificate2119], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2117,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2119,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric570 : ∀ c∈certificate570.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2117,MergedCutCells.Batch176.certificate2118,MergedCutCells.Batch176.certificate2119], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2117,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2119,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid570 : ∀ c∈certificate570.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2117,MergedCutCells.Batch176.certificate2118,MergedCutCells.Batch176.certificate2119], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid191,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid191,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid191,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches570 : ∀ c∈certificate570.cells, c.population=certificate570.population := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2117,MergedCutCells.Batch176.certificate2118,MergedCutCells.Batch176.certificate2119], c.population=PopulationCertificates.Batch019.certificate380
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers570 {x : ℝ} (hx : certificate570.interval.Contains x) : ∃ c∈certificate570.cells, c.region.interval.Contains x := rat_cut_group_covers certificate570 numericValid570 hx

def certificate571 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate380,PopulationCertificates.Batch019.certificate380,[MergedCutCells.Batch176.certificate2120,MergedCutCells.Batch176.certificate2121,MergedCutCells.Batch176.certificate2122,MergedCutCells.Batch176.certificate2123,MergedCutCells.Batch177.certificate2124],(46081389/40000000),none,(1/2),(302075743649292669/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid571 : certificate571.NumericValid := by decide +kernel
theorem cellsSound571 : ∀ c∈certificate571.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2120,MergedCutCells.Batch176.certificate2121,MergedCutCells.Batch176.certificate2122,MergedCutCells.Batch176.certificate2123,MergedCutCells.Batch177.certificate2124], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2120,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.sound2123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2124,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric571 : ∀ c∈certificate571.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2120,MergedCutCells.Batch176.certificate2121,MergedCutCells.Batch176.certificate2122,MergedCutCells.Batch176.certificate2123,MergedCutCells.Batch177.certificate2124], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2120,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch176.numericValid2123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2124,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid571 : ∀ c∈certificate571.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2120,MergedCutCells.Batch176.certificate2121,MergedCutCells.Batch176.certificate2122,MergedCutCells.Batch176.certificate2123,MergedCutCells.Batch177.certificate2124], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches571 : ∀ c∈certificate571.cells, c.population=certificate571.population := by
  change ∀ c∈[MergedCutCells.Batch176.certificate2120,MergedCutCells.Batch176.certificate2121,MergedCutCells.Batch176.certificate2122,MergedCutCells.Batch176.certificate2123,MergedCutCells.Batch177.certificate2124], c.population=PopulationCertificates.Batch019.certificate380
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers571 {x : ℝ} (hx : certificate571.interval.Contains x) : ∃ c∈certificate571.cells, c.region.interval.Contains x := rat_cut_group_covers certificate571 numericValid571 hx

def certificate572 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate381,PopulationCertificates.Batch019.certificate381,[MergedCutCells.Batch177.certificate2125,MergedCutCells.Batch177.certificate2126,MergedCutCells.Batch177.certificate2127],(5391842453161152089/1000000000000000000),none,(1/2),(438042109166102621/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid572 : certificate572.NumericValid := by decide +kernel
theorem cellsSound572 : ∀ c∈certificate572.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2125,MergedCutCells.Batch177.certificate2126,MergedCutCells.Batch177.certificate2127], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2126,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2127,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric572 : ∀ c∈certificate572.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2125,MergedCutCells.Batch177.certificate2126,MergedCutCells.Batch177.certificate2127], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2126,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2127,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid572 : ∀ c∈certificate572.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2125,MergedCutCells.Batch177.certificate2126,MergedCutCells.Batch177.certificate2127], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches572 : ∀ c∈certificate572.cells, c.population=certificate572.population := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2125,MergedCutCells.Batch177.certificate2126,MergedCutCells.Batch177.certificate2127], c.population=PopulationCertificates.Batch019.certificate381
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers572 {x : ℝ} (hx : certificate572.interval.Contains x) : ∃ c∈certificate572.cells, c.region.interval.Contains x := rat_cut_group_covers certificate572 numericValid572 hx

def certificate573 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate382,PopulationCertificates.Batch019.certificate382,[MergedCutCells.Batch177.certificate2128,MergedCutCells.Batch177.certificate2129,MergedCutCells.Batch177.certificate2130],(42326612213363823/62500000000000000),(some (1163192121/1000000000)),(1/2),(82823342630928999/250000000000000000),(some (55315605467640221/250000000000000000)),(some (57940391888539363/1000000000000000000))⟩
theorem numericValid573 : certificate573.NumericValid := by decide +kernel
theorem cellsSound573 : ∀ c∈certificate573.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2128,MergedCutCells.Batch177.certificate2129,MergedCutCells.Batch177.certificate2130], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2128,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2130,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric573 : ∀ c∈certificate573.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2128,MergedCutCells.Batch177.certificate2129,MergedCutCells.Batch177.certificate2130], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2128,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2130,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid573 : ∀ c∈certificate573.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2128,MergedCutCells.Batch177.certificate2129,MergedCutCells.Batch177.certificate2130], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid192,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid192,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid192,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches573 : ∀ c∈certificate573.cells, c.population=certificate573.population := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2128,MergedCutCells.Batch177.certificate2129,MergedCutCells.Batch177.certificate2130], c.population=PopulationCertificates.Batch019.certificate382
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers573 {x : ℝ} (hx : certificate573.interval.Contains x) : ∃ c∈certificate573.cells, c.region.interval.Contains x := rat_cut_group_covers certificate573 numericValid573 hx

def certificate574 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate382,PopulationCertificates.Batch019.certificate382,[MergedCutCells.Batch177.certificate2131,MergedCutCells.Batch177.certificate2132,MergedCutCells.Batch177.certificate2133,MergedCutCells.Batch177.certificate2134,MergedCutCells.Batch177.certificate2135],(1163192121/1000000000),none,(1/2),(7877351336713979/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid574 : certificate574.NumericValid := by decide +kernel
theorem cellsSound574 : ∀ c∈certificate574.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2131,MergedCutCells.Batch177.certificate2132,MergedCutCells.Batch177.certificate2133,MergedCutCells.Batch177.certificate2134,MergedCutCells.Batch177.certificate2135], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2132,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2134,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.sound2135,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric574 : ∀ c∈certificate574.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2131,MergedCutCells.Batch177.certificate2132,MergedCutCells.Batch177.certificate2133,MergedCutCells.Batch177.certificate2134,MergedCutCells.Batch177.certificate2135], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2132,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2134,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch177.numericValid2135,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid574 : ∀ c∈certificate574.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2131,MergedCutCells.Batch177.certificate2132,MergedCutCells.Batch177.certificate2133,MergedCutCells.Batch177.certificate2134,MergedCutCells.Batch177.certificate2135], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches574 : ∀ c∈certificate574.cells, c.population=certificate574.population := by
  change ∀ c∈[MergedCutCells.Batch177.certificate2131,MergedCutCells.Batch177.certificate2132,MergedCutCells.Batch177.certificate2133,MergedCutCells.Batch177.certificate2134,MergedCutCells.Batch177.certificate2135], c.population=PopulationCertificates.Batch019.certificate382
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers574 {x : ℝ} (hx : certificate574.interval.Contains x) : ∃ c∈certificate574.cells, c.region.interval.Contains x := rat_cut_group_covers certificate574 numericValid574 hx

def certificate575 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate383,PopulationCertificates.Batch019.certificate383,[MergedCutCells.Batch178.certificate2136,MergedCutCells.Batch178.certificate2137,MergedCutCells.Batch178.certificate2138],(1089304490191547407/200000000000000000),none,(1/2),(2257449253986682091/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid575 : certificate575.NumericValid := by decide +kernel
theorem cellsSound575 : ∀ c∈certificate575.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2136,MergedCutCells.Batch178.certificate2137,MergedCutCells.Batch178.certificate2138], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2137,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2138,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric575 : ∀ c∈certificate575.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2136,MergedCutCells.Batch178.certificate2137,MergedCutCells.Batch178.certificate2138], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2137,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2138,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid575 : ∀ c∈certificate575.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2136,MergedCutCells.Batch178.certificate2137,MergedCutCells.Batch178.certificate2138], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches575 : ∀ c∈certificate575.cells, c.population=certificate575.population := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2136,MergedCutCells.Batch178.certificate2137,MergedCutCells.Batch178.certificate2138], c.population=PopulationCertificates.Batch019.certificate383
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers575 {x : ℝ} (hx : certificate575.interval.Contains x) : ∃ c∈certificate575.cells, c.region.interval.Contains x := rat_cut_group_covers certificate575 numericValid575 hx

end Cycle12.MergedCutGroups.Batch047
