import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch020
import Cycle12.GeometryCertificates.Batch021
import Cycle12.MergedCutCells.Batch195
import Cycle12.MergedCutCells.Batch196
import Cycle12.MergedCutCells.Batch197
import Cycle12.MergedCutCells.Batch198
import Cycle12.MergedCutCells.Batch199
import Cycle12.PopulationCertificates.Batch020
import Cycle12.PopulationCertificates.Batch021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch052

def certificate624 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate416,PopulationCertificates.Batch020.certificate416,[MergedCutCells.Batch195.certificate2343,MergedCutCells.Batch195.certificate2344,MergedCutCells.Batch195.certificate2345],(397513938790896387/500000000000000000),(some (1017301393/1000000000)),(1/2),(80152268293525309/125000000000000000),(some (206705525986824533/500000000000000000)),(some (72351855915117119/500000000000000000))⟩
theorem numericValid624 : certificate624.NumericValid := by decide +kernel
theorem cellsSound624 : ∀ c∈certificate624.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch195.certificate2343,MergedCutCells.Batch195.certificate2344,MergedCutCells.Batch195.certificate2345], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2343,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2344,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2345,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric624 : ∀ c∈certificate624.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch195.certificate2343,MergedCutCells.Batch195.certificate2344,MergedCutCells.Batch195.certificate2345], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2343,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2344,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2345,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid624 : ∀ c∈certificate624.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch195.certificate2343,MergedCutCells.Batch195.certificate2344,MergedCutCells.Batch195.certificate2345], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid209,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid209,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid209,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches624 : ∀ c∈certificate624.cells, c.population=certificate624.population := by
  change ∀ c∈[MergedCutCells.Batch195.certificate2343,MergedCutCells.Batch195.certificate2344,MergedCutCells.Batch195.certificate2345], c.population=PopulationCertificates.Batch020.certificate416
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers624 {x : ℝ} (hx : certificate624.interval.Contains x) : ∃ c∈certificate624.cells, c.region.interval.Contains x := rat_cut_group_covers certificate624 numericValid624 hx

def certificate625 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate416,PopulationCertificates.Batch020.certificate416,[MergedCutCells.Batch195.certificate2346,MergedCutCells.Batch195.certificate2347,MergedCutCells.Batch195.certificate2348,MergedCutCells.Batch195.certificate2349,MergedCutCells.Batch195.certificate2350,MergedCutCells.Batch195.certificate2351,MergedCutCells.Batch196.certificate2352,MergedCutCells.Batch196.certificate2353],(1017301393/1000000000),none,(1/2),(119087097475840291/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid625 : certificate625.NumericValid := by decide +kernel
theorem cellsSound625 : ∀ c∈certificate625.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch195.certificate2346,MergedCutCells.Batch195.certificate2347,MergedCutCells.Batch195.certificate2348,MergedCutCells.Batch195.certificate2349,MergedCutCells.Batch195.certificate2350,MergedCutCells.Batch195.certificate2351,MergedCutCells.Batch196.certificate2352,MergedCutCells.Batch196.certificate2353], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2346,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2348,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2349,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2350,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.sound2351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2352,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2353,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric625 : ∀ c∈certificate625.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch195.certificate2346,MergedCutCells.Batch195.certificate2347,MergedCutCells.Batch195.certificate2348,MergedCutCells.Batch195.certificate2349,MergedCutCells.Batch195.certificate2350,MergedCutCells.Batch195.certificate2351,MergedCutCells.Batch196.certificate2352,MergedCutCells.Batch196.certificate2353], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2346,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2348,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2349,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2350,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch195.numericValid2351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2352,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2353,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid625 : ∀ c∈certificate625.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch195.certificate2346,MergedCutCells.Batch195.certificate2347,MergedCutCells.Batch195.certificate2348,MergedCutCells.Batch195.certificate2349,MergedCutCells.Batch195.certificate2350,MergedCutCells.Batch195.certificate2351,MergedCutCells.Batch196.certificate2352,MergedCutCells.Batch196.certificate2353], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches625 : ∀ c∈certificate625.cells, c.population=certificate625.population := by
  change ∀ c∈[MergedCutCells.Batch195.certificate2346,MergedCutCells.Batch195.certificate2347,MergedCutCells.Batch195.certificate2348,MergedCutCells.Batch195.certificate2349,MergedCutCells.Batch195.certificate2350,MergedCutCells.Batch195.certificate2351,MergedCutCells.Batch196.certificate2352,MergedCutCells.Batch196.certificate2353], c.population=PopulationCertificates.Batch020.certificate416
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers625 {x : ℝ} (hx : certificate625.interval.Contains x) : ∃ c∈certificate625.cells, c.region.interval.Contains x := rat_cut_group_covers certificate625 numericValid625 hx

def certificate626 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate417,PopulationCertificates.Batch020.certificate417,[MergedCutCells.Batch196.certificate2354,MergedCutCells.Batch196.certificate2355,MergedCutCells.Batch196.certificate2356,MergedCutCells.Batch196.certificate2357],(1117877481817023177/200000000000000000),none,(1/2),(1478290695713516327/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid626 : certificate626.NumericValid := by decide +kernel
theorem cellsSound626 : ∀ c∈certificate626.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2354,MergedCutCells.Batch196.certificate2355,MergedCutCells.Batch196.certificate2356,MergedCutCells.Batch196.certificate2357], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2354,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2355,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2357,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric626 : ∀ c∈certificate626.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2354,MergedCutCells.Batch196.certificate2355,MergedCutCells.Batch196.certificate2356,MergedCutCells.Batch196.certificate2357], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2354,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2355,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2357,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid626 : ∀ c∈certificate626.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2354,MergedCutCells.Batch196.certificate2355,MergedCutCells.Batch196.certificate2356,MergedCutCells.Batch196.certificate2357], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches626 : ∀ c∈certificate626.cells, c.population=certificate626.population := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2354,MergedCutCells.Batch196.certificate2355,MergedCutCells.Batch196.certificate2356,MergedCutCells.Batch196.certificate2357], c.population=PopulationCertificates.Batch020.certificate417
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers626 {x : ℝ} (hx : certificate626.interval.Contains x) : ∃ c∈certificate626.cells, c.region.interval.Contains x := rat_cut_group_covers certificate626 numericValid626 hx

def certificate627 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate418,PopulationCertificates.Batch020.certificate418,[MergedCutCells.Batch196.certificate2358,MergedCutCells.Batch196.certificate2359,MergedCutCells.Batch196.certificate2360],(802444746282693249/1000000000000000000),(some (1026256353/1000000000)),(1/2),(672137226876717639/1000000000000000000),(some (425753508610422941/1000000000000000000)),(some (30352422058615323/200000000000000000))⟩
theorem numericValid627 : certificate627.NumericValid := by decide +kernel
theorem cellsSound627 : ∀ c∈certificate627.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2358,MergedCutCells.Batch196.certificate2359,MergedCutCells.Batch196.certificate2360], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2359,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2360,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric627 : ∀ c∈certificate627.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2358,MergedCutCells.Batch196.certificate2359,MergedCutCells.Batch196.certificate2360], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2359,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2360,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid627 : ∀ c∈certificate627.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2358,MergedCutCells.Batch196.certificate2359,MergedCutCells.Batch196.certificate2360], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid210,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid210,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid210,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches627 : ∀ c∈certificate627.cells, c.population=certificate627.population := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2358,MergedCutCells.Batch196.certificate2359,MergedCutCells.Batch196.certificate2360], c.population=PopulationCertificates.Batch020.certificate418
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers627 {x : ℝ} (hx : certificate627.interval.Contains x) : ∃ c∈certificate627.cells, c.region.interval.Contains x := rat_cut_group_covers certificate627 numericValid627 hx

def certificate628 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate418,PopulationCertificates.Batch020.certificate418,[MergedCutCells.Batch196.certificate2361,MergedCutCells.Batch196.certificate2362,MergedCutCells.Batch196.certificate2363,MergedCutCells.Batch197.certificate2364,MergedCutCells.Batch197.certificate2365,MergedCutCells.Batch197.certificate2366],(1026256353/1000000000),none,(1/2),(622964545557865691/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid628 : certificate628.NumericValid := by decide +kernel
theorem cellsSound628 : ∀ c∈certificate628.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2361,MergedCutCells.Batch196.certificate2362,MergedCutCells.Batch196.certificate2363,MergedCutCells.Batch197.certificate2364,MergedCutCells.Batch197.certificate2365,MergedCutCells.Batch197.certificate2366], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2362,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.sound2363,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2365,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2366,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric628 : ∀ c∈certificate628.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2361,MergedCutCells.Batch196.certificate2362,MergedCutCells.Batch196.certificate2363,MergedCutCells.Batch197.certificate2364,MergedCutCells.Batch197.certificate2365,MergedCutCells.Batch197.certificate2366], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2362,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch196.numericValid2363,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2365,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2366,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid628 : ∀ c∈certificate628.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2361,MergedCutCells.Batch196.certificate2362,MergedCutCells.Batch196.certificate2363,MergedCutCells.Batch197.certificate2364,MergedCutCells.Batch197.certificate2365,MergedCutCells.Batch197.certificate2366], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches628 : ∀ c∈certificate628.cells, c.population=certificate628.population := by
  change ∀ c∈[MergedCutCells.Batch196.certificate2361,MergedCutCells.Batch196.certificate2362,MergedCutCells.Batch196.certificate2363,MergedCutCells.Batch197.certificate2364,MergedCutCells.Batch197.certificate2365,MergedCutCells.Batch197.certificate2366], c.population=PopulationCertificates.Batch020.certificate418
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers628 {x : ℝ} (hx : certificate628.interval.Contains x) : ∃ c∈certificate628.cells, c.region.interval.Contains x := rat_cut_group_covers certificate628 numericValid628 hx

def certificate629 : RatCutGroup := ⟨GeometryCertificates.Batch020.certificate419,PopulationCertificates.Batch020.certificate419,[MergedCutCells.Batch197.certificate2367,MergedCutCells.Batch197.certificate2368,MergedCutCells.Batch197.certificate2369,MergedCutCells.Batch197.certificate2370],(5537769948008627787/1000000000000000000),none,(1/2),(2964112457531571429/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid629 : certificate629.NumericValid := by decide +kernel
theorem cellsSound629 : ∀ c∈certificate629.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2367,MergedCutCells.Batch197.certificate2368,MergedCutCells.Batch197.certificate2369,MergedCutCells.Batch197.certificate2370], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2367,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2369,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2370,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric629 : ∀ c∈certificate629.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2367,MergedCutCells.Batch197.certificate2368,MergedCutCells.Batch197.certificate2369,MergedCutCells.Batch197.certificate2370], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2367,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2369,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2370,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid629 : ∀ c∈certificate629.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2367,MergedCutCells.Batch197.certificate2368,MergedCutCells.Batch197.certificate2369,MergedCutCells.Batch197.certificate2370], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches629 : ∀ c∈certificate629.cells, c.population=certificate629.population := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2367,MergedCutCells.Batch197.certificate2368,MergedCutCells.Batch197.certificate2369,MergedCutCells.Batch197.certificate2370], c.population=PopulationCertificates.Batch020.certificate419
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers629 {x : ℝ} (hx : certificate629.interval.Contains x) : ∃ c∈certificate629.cells, c.region.interval.Contains x := rat_cut_group_covers certificate629 numericValid629 hx

def certificate630 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate420,PopulationCertificates.Batch021.certificate420,[MergedCutCells.Batch197.certificate2371,MergedCutCells.Batch197.certificate2372,MergedCutCells.Batch197.certificate2373],(32367994437852441/40000000000000000),(some (504659409/500000000)),(1/2),(4470162064330371/6250000000000000),(some (217853634710852371/500000000000000000)),(some (78811530700179971/500000000000000000))⟩
theorem numericValid630 : certificate630.NumericValid := by decide +kernel
theorem cellsSound630 : ∀ c∈certificate630.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2371,MergedCutCells.Batch197.certificate2372,MergedCutCells.Batch197.certificate2373], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2372,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2373,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric630 : ∀ c∈certificate630.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2371,MergedCutCells.Batch197.certificate2372,MergedCutCells.Batch197.certificate2373], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2372,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2373,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid630 : ∀ c∈certificate630.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2371,MergedCutCells.Batch197.certificate2372,MergedCutCells.Batch197.certificate2373], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid211,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid211,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid211,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches630 : ∀ c∈certificate630.cells, c.population=certificate630.population := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2371,MergedCutCells.Batch197.certificate2372,MergedCutCells.Batch197.certificate2373], c.population=PopulationCertificates.Batch021.certificate420
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers630 {x : ℝ} (hx : certificate630.interval.Contains x) : ∃ c∈certificate630.cells, c.region.interval.Contains x := rat_cut_group_covers certificate630 numericValid630 hx

def certificate631 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate420,PopulationCertificates.Batch021.certificate420,[MergedCutCells.Batch197.certificate2374,MergedCutCells.Batch197.certificate2375,MergedCutCells.Batch198.certificate2376,MergedCutCells.Batch198.certificate2377,MergedCutCells.Batch198.certificate2378,MergedCutCells.Batch198.certificate2379],(504659409/500000000),none,(1/2),(166871031623155189/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid631 : certificate631.NumericValid := by decide +kernel
theorem cellsSound631 : ∀ c∈certificate631.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2374,MergedCutCells.Batch197.certificate2375,MergedCutCells.Batch198.certificate2376,MergedCutCells.Batch198.certificate2377,MergedCutCells.Batch198.certificate2378,MergedCutCells.Batch198.certificate2379], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.sound2375,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2377,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2378,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2379,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric631 : ∀ c∈certificate631.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2374,MergedCutCells.Batch197.certificate2375,MergedCutCells.Batch198.certificate2376,MergedCutCells.Batch198.certificate2377,MergedCutCells.Batch198.certificate2378,MergedCutCells.Batch198.certificate2379], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch197.numericValid2375,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2377,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2378,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2379,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid631 : ∀ c∈certificate631.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2374,MergedCutCells.Batch197.certificate2375,MergedCutCells.Batch198.certificate2376,MergedCutCells.Batch198.certificate2377,MergedCutCells.Batch198.certificate2378,MergedCutCells.Batch198.certificate2379], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches631 : ∀ c∈certificate631.cells, c.population=certificate631.population := by
  change ∀ c∈[MergedCutCells.Batch197.certificate2374,MergedCutCells.Batch197.certificate2375,MergedCutCells.Batch198.certificate2376,MergedCutCells.Batch198.certificate2377,MergedCutCells.Batch198.certificate2378,MergedCutCells.Batch198.certificate2379], c.population=PopulationCertificates.Batch021.certificate420
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers631 {x : ℝ} (hx : certificate631.interval.Contains x) : ∃ c∈certificate631.cells, c.region.interval.Contains x := rat_cut_group_covers certificate631 numericValid631 hx

def certificate632 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate421,PopulationCertificates.Batch021.certificate421,[MergedCutCells.Batch198.certificate2380,MergedCutCells.Batch198.certificate2381,MergedCutCells.Batch198.certificate2382],(278246456235761879/50000000000000000),none,(1/2),(3055220192669898713/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid632 : certificate632.NumericValid := by decide +kernel
theorem cellsSound632 : ∀ c∈certificate632.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2380,MergedCutCells.Batch198.certificate2381,MergedCutCells.Batch198.certificate2382], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2380,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2381,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2382,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric632 : ∀ c∈certificate632.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2380,MergedCutCells.Batch198.certificate2381,MergedCutCells.Batch198.certificate2382], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2380,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2381,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2382,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid632 : ∀ c∈certificate632.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2380,MergedCutCells.Batch198.certificate2381,MergedCutCells.Batch198.certificate2382], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches632 : ∀ c∈certificate632.cells, c.population=certificate632.population := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2380,MergedCutCells.Batch198.certificate2381,MergedCutCells.Batch198.certificate2382], c.population=PopulationCertificates.Batch021.certificate421
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers632 {x : ℝ} (hx : certificate632.interval.Contains x) : ∃ c∈certificate632.cells, c.region.interval.Contains x := rat_cut_group_covers certificate632 numericValid632 hx

def certificate633 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate422,PopulationCertificates.Batch021.certificate422,[MergedCutCells.Batch198.certificate2383,MergedCutCells.Batch198.certificate2384,MergedCutCells.Batch198.certificate2385],(818143504102595113/1000000000000000000),(some (63823639/62500000)),(1/2),(765195504277738549/1000000000000000000),(some (28000231808706841/62500000000000000)),(some (165083225210530431/1000000000000000000))⟩
theorem numericValid633 : certificate633.NumericValid := by decide +kernel
theorem cellsSound633 : ∀ c∈certificate633.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2383,MergedCutCells.Batch198.certificate2384,MergedCutCells.Batch198.certificate2385], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2385,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric633 : ∀ c∈certificate633.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2383,MergedCutCells.Batch198.certificate2384,MergedCutCells.Batch198.certificate2385], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2385,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid633 : ∀ c∈certificate633.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2383,MergedCutCells.Batch198.certificate2384,MergedCutCells.Batch198.certificate2385], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid212,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid212,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid212,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches633 : ∀ c∈certificate633.cells, c.population=certificate633.population := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2383,MergedCutCells.Batch198.certificate2384,MergedCutCells.Batch198.certificate2385], c.population=PopulationCertificates.Batch021.certificate422
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers633 {x : ℝ} (hx : certificate633.interval.Contains x) : ∃ c∈certificate633.cells, c.region.interval.Contains x := rat_cut_group_covers certificate633 numericValid633 hx

def certificate634 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate422,PopulationCertificates.Batch021.certificate422,[MergedCutCells.Batch198.certificate2386,MergedCutCells.Batch198.certificate2387,MergedCutCells.Batch199.certificate2388,MergedCutCells.Batch199.certificate2389,MergedCutCells.Batch199.certificate2390,MergedCutCells.Batch199.certificate2391],(63823639/62500000),none,(1/2),(178403964381548009/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid634 : certificate634.NumericValid := by decide +kernel
theorem cellsSound634 : ∀ c∈certificate634.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2386,MergedCutCells.Batch198.certificate2387,MergedCutCells.Batch199.certificate2388,MergedCutCells.Batch199.certificate2389,MergedCutCells.Batch199.certificate2390,MergedCutCells.Batch199.certificate2391], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2386,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.sound2387,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2388,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2389,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2390,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2391,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric634 : ∀ c∈certificate634.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2386,MergedCutCells.Batch198.certificate2387,MergedCutCells.Batch199.certificate2388,MergedCutCells.Batch199.certificate2389,MergedCutCells.Batch199.certificate2390,MergedCutCells.Batch199.certificate2391], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2386,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch198.numericValid2387,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2388,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2389,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2390,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2391,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid634 : ∀ c∈certificate634.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2386,MergedCutCells.Batch198.certificate2387,MergedCutCells.Batch199.certificate2388,MergedCutCells.Batch199.certificate2389,MergedCutCells.Batch199.certificate2390,MergedCutCells.Batch199.certificate2391], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches634 : ∀ c∈certificate634.cells, c.population=certificate634.population := by
  change ∀ c∈[MergedCutCells.Batch198.certificate2386,MergedCutCells.Batch198.certificate2387,MergedCutCells.Batch199.certificate2388,MergedCutCells.Batch199.certificate2389,MergedCutCells.Batch199.certificate2390,MergedCutCells.Batch199.certificate2391], c.population=PopulationCertificates.Batch021.certificate422
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers634 {x : ℝ} (hx : certificate634.interval.Contains x) : ∃ c∈certificate634.cells, c.region.interval.Contains x := rat_cut_group_covers certificate634 numericValid634 hx

def certificate635 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate423,PopulationCertificates.Batch021.certificate423,[MergedCutCells.Batch199.certificate2392,MergedCutCells.Batch199.certificate2393,MergedCutCells.Batch199.certificate2394],(549286896534432847/100000000000000000),none,(1/2),(3067828519458614351/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid635 : certificate635.NumericValid := by decide +kernel
theorem cellsSound635 : ∀ c∈certificate635.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2392,MergedCutCells.Batch199.certificate2393,MergedCutCells.Batch199.certificate2394], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2392,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2393,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2394,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric635 : ∀ c∈certificate635.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2392,MergedCutCells.Batch199.certificate2393,MergedCutCells.Batch199.certificate2394], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2392,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2393,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2394,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid635 : ∀ c∈certificate635.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2392,MergedCutCells.Batch199.certificate2393,MergedCutCells.Batch199.certificate2394], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches635 : ∀ c∈certificate635.cells, c.population=certificate635.population := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2392,MergedCutCells.Batch199.certificate2393,MergedCutCells.Batch199.certificate2394], c.population=PopulationCertificates.Batch021.certificate423
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers635 {x : ℝ} (hx : certificate635.interval.Contains x) : ∃ c∈certificate635.cells, c.region.interval.Contains x := rat_cut_group_covers certificate635 numericValid635 hx

end Cycle12.MergedCutGroups.Batch052
