import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch020
import Cycle12.MergedCutCells.Batch190
import Cycle12.MergedCutCells.Batch191
import Cycle12.MergedCutCells.Batch192
import Cycle12.MergedCutCells.Batch193
import Cycle12.MergedCutCells.Batch194
import Cycle12.MergedCutCells.Batch195
import Cycle12.PopulationCertificates.Batch020

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch051

def certificate612 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate408,PopulationCertificates.Batch020.certificate408,[MergedCutCells.Batch190.certificate2290,MergedCutCells.Batch190.certificate2291,MergedCutCells.Batch191.certificate2292],(153070837271590469/200000000000000000),(some (1053650323/1000000000)),(1/2),(102191659800776571/200000000000000000),(some (36950991143273887/100000000000000000)),(some (24260276544067903/200000000000000000))⟩
theorem numericValid612 : certificate612.NumericValid := by decide +kernel
theorem cellsSound612 : ∀ c∈certificate612.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2290,MergedCutCells.Batch190.certificate2291,MergedCutCells.Batch191.certificate2292], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2290,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.sound2291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2292,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric612 : ∀ c∈certificate612.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2290,MergedCutCells.Batch190.certificate2291,MergedCutCells.Batch191.certificate2292], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2290,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch190.numericValid2291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2292,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid612 : ∀ c∈certificate612.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2290,MergedCutCells.Batch190.certificate2291,MergedCutCells.Batch191.certificate2292], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid205,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid205,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid205,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches612 : ∀ c∈certificate612.cells, c.population=certificate612.population := by
  change ∀ c∈[MergedCutCells.Batch190.certificate2290,MergedCutCells.Batch190.certificate2291,MergedCutCells.Batch191.certificate2292], c.population=PopulationCertificates.Batch020.certificate408
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers612 {x : ℝ} (hx : certificate612.interval.Contains x) : ∃ c∈certificate612.cells, c.region.interval.Contains x := rat_cut_group_covers certificate612 numericValid612 hx

def certificate613 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate408,PopulationCertificates.Batch020.certificate408,[MergedCutCells.Batch191.certificate2293,MergedCutCells.Batch191.certificate2294,MergedCutCells.Batch191.certificate2295,MergedCutCells.Batch191.certificate2296,MergedCutCells.Batch191.certificate2297,MergedCutCells.Batch191.certificate2298],(1053650323/1000000000),none,(1/2),(476562933188121043/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid613 : certificate613.NumericValid := by decide +kernel
theorem cellsSound613 : ∀ c∈certificate613.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2293,MergedCutCells.Batch191.certificate2294,MergedCutCells.Batch191.certificate2295,MergedCutCells.Batch191.certificate2296,MergedCutCells.Batch191.certificate2297,MergedCutCells.Batch191.certificate2298], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2294,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2296,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2297,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2298,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric613 : ∀ c∈certificate613.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2293,MergedCutCells.Batch191.certificate2294,MergedCutCells.Batch191.certificate2295,MergedCutCells.Batch191.certificate2296,MergedCutCells.Batch191.certificate2297,MergedCutCells.Batch191.certificate2298], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2294,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2296,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2297,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2298,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid613 : ∀ c∈certificate613.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2293,MergedCutCells.Batch191.certificate2294,MergedCutCells.Batch191.certificate2295,MergedCutCells.Batch191.certificate2296,MergedCutCells.Batch191.certificate2297,MergedCutCells.Batch191.certificate2298], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches613 : ∀ c∈certificate613.cells, c.population=certificate613.population := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2293,MergedCutCells.Batch191.certificate2294,MergedCutCells.Batch191.certificate2295,MergedCutCells.Batch191.certificate2296,MergedCutCells.Batch191.certificate2297,MergedCutCells.Batch191.certificate2298], c.population=PopulationCertificates.Batch020.certificate408
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers613 {x : ℝ} (hx : certificate613.interval.Contains x) : ∃ c∈certificate613.cells, c.region.interval.Contains x := rat_cut_group_covers certificate613 numericValid613 hx

def certificate614 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate409,PopulationCertificates.Batch020.certificate409,[MergedCutCells.Batch191.certificate2299,MergedCutCells.Batch191.certificate2300,MergedCutCells.Batch191.certificate2301],(1407927789106081393/250000000000000000),none,(1/2),(278059290666667273/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid614 : certificate614.NumericValid := by decide +kernel
theorem cellsSound614 : ∀ c∈certificate614.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2299,MergedCutCells.Batch191.certificate2300,MergedCutCells.Batch191.certificate2301], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2299,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2300,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2301,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric614 : ∀ c∈certificate614.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2299,MergedCutCells.Batch191.certificate2300,MergedCutCells.Batch191.certificate2301], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2299,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2300,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2301,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid614 : ∀ c∈certificate614.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2299,MergedCutCells.Batch191.certificate2300,MergedCutCells.Batch191.certificate2301], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches614 : ∀ c∈certificate614.cells, c.population=certificate614.population := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2299,MergedCutCells.Batch191.certificate2300,MergedCutCells.Batch191.certificate2301], c.population=PopulationCertificates.Batch020.certificate409
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers614 {x : ℝ} (hx : certificate614.interval.Contains x) : ∃ c∈certificate614.cells, c.region.interval.Contains x := rat_cut_group_covers certificate614 numericValid614 hx

def certificate615 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate410,PopulationCertificates.Batch020.certificate410,[MergedCutCells.Batch191.certificate2302,MergedCutCells.Batch191.certificate2303,MergedCutCells.Batch192.certificate2304],(770208068648220333/1000000000000000000),(some (1034140447/1000000000)),(1/2),(528587344282309713/1000000000000000000),(some (380447964172287121/1000000000000000000)),(some (6344922364993061/50000000000000000))⟩
theorem numericValid615 : certificate615.NumericValid := by decide +kernel
theorem cellsSound615 : ∀ c∈certificate615.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2302,MergedCutCells.Batch191.certificate2303,MergedCutCells.Batch192.certificate2304], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2302,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.sound2303,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2304,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric615 : ∀ c∈certificate615.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2302,MergedCutCells.Batch191.certificate2303,MergedCutCells.Batch192.certificate2304], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2302,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch191.numericValid2303,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2304,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid615 : ∀ c∈certificate615.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2302,MergedCutCells.Batch191.certificate2303,MergedCutCells.Batch192.certificate2304], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid206,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid206,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid206,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches615 : ∀ c∈certificate615.cells, c.population=certificate615.population := by
  change ∀ c∈[MergedCutCells.Batch191.certificate2302,MergedCutCells.Batch191.certificate2303,MergedCutCells.Batch192.certificate2304], c.population=PopulationCertificates.Batch020.certificate410
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers615 {x : ℝ} (hx : certificate615.interval.Contains x) : ∃ c∈certificate615.cells, c.region.interval.Contains x := rat_cut_group_covers certificate615 numericValid615 hx

def certificate616 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate410,PopulationCertificates.Batch020.certificate410,[MergedCutCells.Batch192.certificate2305,MergedCutCells.Batch192.certificate2306,MergedCutCells.Batch192.certificate2307,MergedCutCells.Batch192.certificate2308,MergedCutCells.Batch192.certificate2309,MergedCutCells.Batch192.certificate2310,MergedCutCells.Batch192.certificate2311,MergedCutCells.Batch192.certificate2312],(1034140447/1000000000),none,(1/2),(249365602370099487/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid616 : certificate616.NumericValid := by decide +kernel
theorem cellsSound616 : ∀ c∈certificate616.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch192.certificate2305,MergedCutCells.Batch192.certificate2306,MergedCutCells.Batch192.certificate2307,MergedCutCells.Batch192.certificate2308,MergedCutCells.Batch192.certificate2309,MergedCutCells.Batch192.certificate2310,MergedCutCells.Batch192.certificate2311,MergedCutCells.Batch192.certificate2312], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2305,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2306,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2307,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2308,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2311,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2312,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric616 : ∀ c∈certificate616.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch192.certificate2305,MergedCutCells.Batch192.certificate2306,MergedCutCells.Batch192.certificate2307,MergedCutCells.Batch192.certificate2308,MergedCutCells.Batch192.certificate2309,MergedCutCells.Batch192.certificate2310,MergedCutCells.Batch192.certificate2311,MergedCutCells.Batch192.certificate2312], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2305,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2306,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2307,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2308,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2311,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2312,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid616 : ∀ c∈certificate616.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch192.certificate2305,MergedCutCells.Batch192.certificate2306,MergedCutCells.Batch192.certificate2307,MergedCutCells.Batch192.certificate2308,MergedCutCells.Batch192.certificate2309,MergedCutCells.Batch192.certificate2310,MergedCutCells.Batch192.certificate2311,MergedCutCells.Batch192.certificate2312], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches616 : ∀ c∈certificate616.cells, c.population=certificate616.population := by
  change ∀ c∈[MergedCutCells.Batch192.certificate2305,MergedCutCells.Batch192.certificate2306,MergedCutCells.Batch192.certificate2307,MergedCutCells.Batch192.certificate2308,MergedCutCells.Batch192.certificate2309,MergedCutCells.Batch192.certificate2310,MergedCutCells.Batch192.certificate2311,MergedCutCells.Batch192.certificate2312], c.population=PopulationCertificates.Batch020.certificate410
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers616 {x : ℝ} (hx : certificate616.interval.Contains x) : ∃ c∈certificate616.cells, c.region.interval.Contains x := rat_cut_group_covers certificate616 numericValid616 hx

def certificate617 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate411,PopulationCertificates.Batch020.certificate411,[MergedCutCells.Batch192.certificate2313,MergedCutCells.Batch192.certificate2314,MergedCutCells.Batch192.certificate2315,MergedCutCells.Batch193.certificate2316],(2785883101206189837/500000000000000000),none,(1/2),(2780744898977033981/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid617 : certificate617.NumericValid := by decide +kernel
theorem cellsSound617 : ∀ c∈certificate617.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch192.certificate2313,MergedCutCells.Batch192.certificate2314,MergedCutCells.Batch192.certificate2315,MergedCutCells.Batch193.certificate2316], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2313,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2314,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.sound2315,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2316,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric617 : ∀ c∈certificate617.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch192.certificate2313,MergedCutCells.Batch192.certificate2314,MergedCutCells.Batch192.certificate2315,MergedCutCells.Batch193.certificate2316], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2313,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2314,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch192.numericValid2315,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2316,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid617 : ∀ c∈certificate617.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch192.certificate2313,MergedCutCells.Batch192.certificate2314,MergedCutCells.Batch192.certificate2315,MergedCutCells.Batch193.certificate2316], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches617 : ∀ c∈certificate617.cells, c.population=certificate617.population := by
  change ∀ c∈[MergedCutCells.Batch192.certificate2313,MergedCutCells.Batch192.certificate2314,MergedCutCells.Batch192.certificate2315,MergedCutCells.Batch193.certificate2316], c.population=PopulationCertificates.Batch020.certificate411
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers617 {x : ℝ} (hx : certificate617.interval.Contains x) : ∃ c∈certificate617.cells, c.region.interval.Contains x := rat_cut_group_covers certificate617 numericValid617 hx

def certificate618 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate412,PopulationCertificates.Batch020.certificate412,[MergedCutCells.Batch193.certificate2317,MergedCutCells.Batch193.certificate2318,MergedCutCells.Batch193.certificate2319],(780388804089132259/1000000000000000000),(some (262153163/250000000)),(1/2),(283635812534284607/500000000000000000),(some (196353806889960899/500000000000000000)),(some (26670208484247813/200000000000000000))⟩
theorem numericValid618 : certificate618.NumericValid := by decide +kernel
theorem cellsSound618 : ∀ c∈certificate618.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2317,MergedCutCells.Batch193.certificate2318,MergedCutCells.Batch193.certificate2319], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2317,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2318,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2319,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric618 : ∀ c∈certificate618.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2317,MergedCutCells.Batch193.certificate2318,MergedCutCells.Batch193.certificate2319], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2317,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2318,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2319,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid618 : ∀ c∈certificate618.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2317,MergedCutCells.Batch193.certificate2318,MergedCutCells.Batch193.certificate2319], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid207,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid207,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid207,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches618 : ∀ c∈certificate618.cells, c.population=certificate618.population := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2317,MergedCutCells.Batch193.certificate2318,MergedCutCells.Batch193.certificate2319], c.population=PopulationCertificates.Batch020.certificate412
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers618 {x : ℝ} (hx : certificate618.interval.Contains x) : ∃ c∈certificate618.cells, c.region.interval.Contains x := rat_cut_group_covers certificate618 numericValid618 hx

def certificate619 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate412,PopulationCertificates.Batch020.certificate412,[MergedCutCells.Batch193.certificate2320,MergedCutCells.Batch193.certificate2321,MergedCutCells.Batch193.certificate2322,MergedCutCells.Batch193.certificate2323,MergedCutCells.Batch193.certificate2324,MergedCutCells.Batch193.certificate2325],(262153163/250000000),none,(1/2),(262992408569623467/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid619 : certificate619.NumericValid := by decide +kernel
theorem cellsSound619 : ∀ c∈certificate619.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2320,MergedCutCells.Batch193.certificate2321,MergedCutCells.Batch193.certificate2322,MergedCutCells.Batch193.certificate2323,MergedCutCells.Batch193.certificate2324,MergedCutCells.Batch193.certificate2325], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2320,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2321,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2323,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2324,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2325,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric619 : ∀ c∈certificate619.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2320,MergedCutCells.Batch193.certificate2321,MergedCutCells.Batch193.certificate2322,MergedCutCells.Batch193.certificate2323,MergedCutCells.Batch193.certificate2324,MergedCutCells.Batch193.certificate2325], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2320,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2321,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2323,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2324,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2325,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid619 : ∀ c∈certificate619.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2320,MergedCutCells.Batch193.certificate2321,MergedCutCells.Batch193.certificate2322,MergedCutCells.Batch193.certificate2323,MergedCutCells.Batch193.certificate2324,MergedCutCells.Batch193.certificate2325], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches619 : ∀ c∈certificate619.cells, c.population=certificate619.population := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2320,MergedCutCells.Batch193.certificate2321,MergedCutCells.Batch193.certificate2322,MergedCutCells.Batch193.certificate2323,MergedCutCells.Batch193.certificate2324,MergedCutCells.Batch193.certificate2325], c.population=PopulationCertificates.Batch020.certificate412
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers619 {x : ℝ} (hx : certificate619.interval.Contains x) : ∃ c∈certificate619.cells, c.region.interval.Contains x := rat_cut_group_covers certificate619 numericValid619 hx

def certificate620 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate413,PopulationCertificates.Batch020.certificate413,[MergedCutCells.Batch193.certificate2326,MergedCutCells.Batch193.certificate2327,MergedCutCells.Batch194.certificate2328,MergedCutCells.Batch194.certificate2329],(561967092213826061/100000000000000000),none,(1/2),(89555098408300087/31250000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid620 : certificate620.NumericValid := by decide +kernel
theorem cellsSound620 : ∀ c∈certificate620.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2326,MergedCutCells.Batch193.certificate2327,MergedCutCells.Batch194.certificate2328,MergedCutCells.Batch194.certificate2329], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2326,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.sound2327,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2328,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2329,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric620 : ∀ c∈certificate620.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2326,MergedCutCells.Batch193.certificate2327,MergedCutCells.Batch194.certificate2328,MergedCutCells.Batch194.certificate2329], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2326,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch193.numericValid2327,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2328,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2329,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid620 : ∀ c∈certificate620.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2326,MergedCutCells.Batch193.certificate2327,MergedCutCells.Batch194.certificate2328,MergedCutCells.Batch194.certificate2329], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches620 : ∀ c∈certificate620.cells, c.population=certificate620.population := by
  change ∀ c∈[MergedCutCells.Batch193.certificate2326,MergedCutCells.Batch193.certificate2327,MergedCutCells.Batch194.certificate2328,MergedCutCells.Batch194.certificate2329], c.population=PopulationCertificates.Batch020.certificate413
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers620 {x : ℝ} (hx : certificate620.interval.Contains x) : ∃ c∈certificate620.cells, c.region.interval.Contains x := rat_cut_group_covers certificate620 numericValid620 hx

def certificate621 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate414,PopulationCertificates.Batch020.certificate414,[MergedCutCells.Batch194.certificate2330,MergedCutCells.Batch194.certificate2331,MergedCutCells.Batch194.certificate2332],(394223754678797283/500000000000000000),(some (206604917/200000000)),(1/2),(610136807688657759/1000000000000000000),(some (403016207660701809/1000000000000000000)),(some (34732479115612933/250000000000000000))⟩
theorem numericValid621 : certificate621.NumericValid := by decide +kernel
theorem cellsSound621 : ∀ c∈certificate621.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2330,MergedCutCells.Batch194.certificate2331,MergedCutCells.Batch194.certificate2332], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2331,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2332,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric621 : ∀ c∈certificate621.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2330,MergedCutCells.Batch194.certificate2331,MergedCutCells.Batch194.certificate2332], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2331,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2332,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid621 : ∀ c∈certificate621.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2330,MergedCutCells.Batch194.certificate2331,MergedCutCells.Batch194.certificate2332], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid208,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid208,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid208,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches621 : ∀ c∈certificate621.cells, c.population=certificate621.population := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2330,MergedCutCells.Batch194.certificate2331,MergedCutCells.Batch194.certificate2332], c.population=PopulationCertificates.Batch020.certificate414
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers621 {x : ℝ} (hx : certificate621.interval.Contains x) : ∃ c∈certificate621.cells, c.region.interval.Contains x := rat_cut_group_covers certificate621 numericValid621 hx

def certificate622 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate414,PopulationCertificates.Batch020.certificate414,[MergedCutCells.Batch194.certificate2333,MergedCutCells.Batch194.certificate2334,MergedCutCells.Batch194.certificate2335,MergedCutCells.Batch194.certificate2336,MergedCutCells.Batch194.certificate2337,MergedCutCells.Batch194.certificate2338],(206604917/200000000),none,(1/2),(567985307559341157/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid622 : certificate622.NumericValid := by decide +kernel
theorem cellsSound622 : ∀ c∈certificate622.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2333,MergedCutCells.Batch194.certificate2334,MergedCutCells.Batch194.certificate2335,MergedCutCells.Batch194.certificate2336,MergedCutCells.Batch194.certificate2337,MergedCutCells.Batch194.certificate2338], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2333,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2336,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2337,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2338,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric622 : ∀ c∈certificate622.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2333,MergedCutCells.Batch194.certificate2334,MergedCutCells.Batch194.certificate2335,MergedCutCells.Batch194.certificate2336,MergedCutCells.Batch194.certificate2337,MergedCutCells.Batch194.certificate2338], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2333,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2336,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2337,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2338,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid622 : ∀ c∈certificate622.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2333,MergedCutCells.Batch194.certificate2334,MergedCutCells.Batch194.certificate2335,MergedCutCells.Batch194.certificate2336,MergedCutCells.Batch194.certificate2337,MergedCutCells.Batch194.certificate2338], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches622 : ∀ c∈certificate622.cells, c.population=certificate622.population := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2333,MergedCutCells.Batch194.certificate2334,MergedCutCells.Batch194.certificate2335,MergedCutCells.Batch194.certificate2336,MergedCutCells.Batch194.certificate2337,MergedCutCells.Batch194.certificate2338], c.population=PopulationCertificates.Batch020.certificate414
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers622 {x : ℝ} (hx : certificate622.interval.Contains x) : ∃ c∈certificate622.cells, c.region.interval.Contains x := rat_cut_group_covers certificate622 numericValid622 hx

def certificate623 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate415,PopulationCertificates.Batch020.certificate415,[MergedCutCells.Batch194.certificate2339,MergedCutCells.Batch195.certificate2340,MergedCutCells.Batch195.certificate2341,MergedCutCells.Batch195.certificate2342],(1107951475107982289/200000000000000000),none,(1/2),(2867527912068430973/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid623 : certificate623.NumericValid := by decide +kernel
theorem cellsSound623 : ∀ c∈certificate623.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2339,MergedCutCells.Batch195.certificate2340,MergedCutCells.Batch195.certificate2341,MergedCutCells.Batch195.certificate2342], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.sound2339,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2341,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2342,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric623 : ∀ c∈certificate623.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2339,MergedCutCells.Batch195.certificate2340,MergedCutCells.Batch195.certificate2341,MergedCutCells.Batch195.certificate2342], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch194.numericValid2339,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2341,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2342,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid623 : ∀ c∈certificate623.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2339,MergedCutCells.Batch195.certificate2340,MergedCutCells.Batch195.certificate2341,MergedCutCells.Batch195.certificate2342], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches623 : ∀ c∈certificate623.cells, c.population=certificate623.population := by
  change ∀ c∈[MergedCutCells.Batch194.certificate2339,MergedCutCells.Batch195.certificate2340,MergedCutCells.Batch195.certificate2341,MergedCutCells.Batch195.certificate2342], c.population=PopulationCertificates.Batch020.certificate415
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers623 {x : ℝ} (hx : certificate623.interval.Contains x) : ∃ c∈certificate623.cells, c.region.interval.Contains x := rat_cut_group_covers certificate623 numericValid623 hx

end Cycle12.MergedCutGroups.Batch051
