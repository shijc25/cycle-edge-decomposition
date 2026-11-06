import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch021
import Cycle12.MergedCutCells.Batch204
import Cycle12.MergedCutCells.Batch205
import Cycle12.MergedCutCells.Batch206
import Cycle12.MergedCutCells.Batch207
import Cycle12.MergedCutCells.Batch208
import Cycle12.PopulationCertificates.Batch021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch054

def certificate648 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate432,PopulationCertificates.Batch021.certificate432,[MergedCutCells.Batch204.certificate2448,MergedCutCells.Batch204.certificate2449,MergedCutCells.Batch204.certificate2450],(856014240633528317/1000000000000000000),(some (992480763/1000000000)),(1/2),(259510693205422683/250000000000000000),(some (500243995285298407/1000000000000000000)),(some (199885747602405631/1000000000000000000))⟩
theorem numericValid648 : certificate648.NumericValid := by decide +kernel
theorem cellsSound648 : ∀ c∈certificate648.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2448,MergedCutCells.Batch204.certificate2449,MergedCutCells.Batch204.certificate2450], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2448,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2449,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2450,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric648 : ∀ c∈certificate648.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2448,MergedCutCells.Batch204.certificate2449,MergedCutCells.Batch204.certificate2450], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2448,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2449,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2450,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid648 : ∀ c∈certificate648.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2448,MergedCutCells.Batch204.certificate2449,MergedCutCells.Batch204.certificate2450], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid217,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid217,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid217,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches648 : ∀ c∈certificate648.cells, c.population=certificate648.population := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2448,MergedCutCells.Batch204.certificate2449,MergedCutCells.Batch204.certificate2450], c.population=PopulationCertificates.Batch021.certificate432
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers648 {x : ℝ} (hx : certificate648.interval.Contains x) : ∃ c∈certificate648.cells, c.region.interval.Contains x := rat_cut_group_covers certificate648 numericValid648 hx

def certificate649 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate432,PopulationCertificates.Batch021.certificate432,[MergedCutCells.Batch204.certificate2451,MergedCutCells.Batch204.certificate2452,MergedCutCells.Batch204.certificate2453,MergedCutCells.Batch204.certificate2454,MergedCutCells.Batch204.certificate2455,MergedCutCells.Batch204.certificate2456],(992480763/1000000000),none,(1/2),(485840094871718879/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid649 : certificate649.NumericValid := by decide +kernel
theorem cellsSound649 : ∀ c∈certificate649.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2451,MergedCutCells.Batch204.certificate2452,MergedCutCells.Batch204.certificate2453,MergedCutCells.Batch204.certificate2454,MergedCutCells.Batch204.certificate2455,MergedCutCells.Batch204.certificate2456], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2451,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2452,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2454,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2455,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2456,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric649 : ∀ c∈certificate649.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2451,MergedCutCells.Batch204.certificate2452,MergedCutCells.Batch204.certificate2453,MergedCutCells.Batch204.certificate2454,MergedCutCells.Batch204.certificate2455,MergedCutCells.Batch204.certificate2456], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2451,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2452,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2454,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2455,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2456,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid649 : ∀ c∈certificate649.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2451,MergedCutCells.Batch204.certificate2452,MergedCutCells.Batch204.certificate2453,MergedCutCells.Batch204.certificate2454,MergedCutCells.Batch204.certificate2455,MergedCutCells.Batch204.certificate2456], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches649 : ∀ c∈certificate649.cells, c.population=certificate649.population := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2451,MergedCutCells.Batch204.certificate2452,MergedCutCells.Batch204.certificate2453,MergedCutCells.Batch204.certificate2454,MergedCutCells.Batch204.certificate2455,MergedCutCells.Batch204.certificate2456], c.population=PopulationCertificates.Batch021.certificate432
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers649 {x : ℝ} (hx : certificate649.interval.Contains x) : ∃ c∈certificate649.cells, c.region.interval.Contains x := rat_cut_group_covers certificate649 numericValid649 hx

def certificate650 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate433,PopulationCertificates.Batch021.certificate433,[MergedCutCells.Batch204.certificate2457,MergedCutCells.Batch204.certificate2458,MergedCutCells.Batch204.certificate2459,MergedCutCells.Batch205.certificate2460],(544967856026133419/100000000000000000),none,(1/2),(682828270792474867/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid650 : certificate650.NumericValid := by decide +kernel
theorem cellsSound650 : ∀ c∈certificate650.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2457,MergedCutCells.Batch204.certificate2458,MergedCutCells.Batch204.certificate2459,MergedCutCells.Batch205.certificate2460], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2457,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.sound2459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2460,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric650 : ∀ c∈certificate650.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2457,MergedCutCells.Batch204.certificate2458,MergedCutCells.Batch204.certificate2459,MergedCutCells.Batch205.certificate2460], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2457,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch204.numericValid2459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2460,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid650 : ∀ c∈certificate650.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2457,MergedCutCells.Batch204.certificate2458,MergedCutCells.Batch204.certificate2459,MergedCutCells.Batch205.certificate2460], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches650 : ∀ c∈certificate650.cells, c.population=certificate650.population := by
  change ∀ c∈[MergedCutCells.Batch204.certificate2457,MergedCutCells.Batch204.certificate2458,MergedCutCells.Batch204.certificate2459,MergedCutCells.Batch205.certificate2460], c.population=PopulationCertificates.Batch021.certificate433
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers650 {x : ℝ} (hx : certificate650.interval.Contains x) : ∃ c∈certificate650.cells, c.region.interval.Contains x := rat_cut_group_covers certificate650 numericValid650 hx

def certificate651 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate434,PopulationCertificates.Batch021.certificate434,[MergedCutCells.Batch205.certificate2461,MergedCutCells.Batch205.certificate2462],(432220566365185521/500000000000000000),(some (122196323/125000000)),(1/2),(11071413283244131/10000000000000000),(some (7961322430146917/15625000000000000)),(some (103340024888769731/500000000000000000))⟩
theorem numericValid651 : certificate651.NumericValid := by decide +kernel
theorem cellsSound651 : ∀ c∈certificate651.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2461,MergedCutCells.Batch205.certificate2462], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2461,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2462,List.forall_mem_nil _⟩⟩
theorem cellsNumeric651 : ∀ c∈certificate651.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2461,MergedCutCells.Batch205.certificate2462], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2461,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2462,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid651 : ∀ c∈certificate651.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2461,MergedCutCells.Batch205.certificate2462], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid218,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid218,List.forall_mem_nil _⟩⟩
theorem populationMatches651 : ∀ c∈certificate651.cells, c.population=certificate651.population := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2461,MergedCutCells.Batch205.certificate2462], c.population=PopulationCertificates.Batch021.certificate434
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers651 {x : ℝ} (hx : certificate651.interval.Contains x) : ∃ c∈certificate651.cells, c.region.interval.Contains x := rat_cut_group_covers certificate651 numericValid651 hx

def certificate652 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate434,PopulationCertificates.Batch021.certificate434,[MergedCutCells.Batch205.certificate2463,MergedCutCells.Batch205.certificate2464,MergedCutCells.Batch205.certificate2465,MergedCutCells.Batch205.certificate2466,MergedCutCells.Batch205.certificate2467,MergedCutCells.Batch205.certificate2468,MergedCutCells.Batch205.certificate2469,MergedCutCells.Batch205.certificate2470],(122196323/125000000),none,(1/2),(514043523312970957/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid652 : certificate652.NumericValid := by decide +kernel
theorem cellsSound652 : ∀ c∈certificate652.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2463,MergedCutCells.Batch205.certificate2464,MergedCutCells.Batch205.certificate2465,MergedCutCells.Batch205.certificate2466,MergedCutCells.Batch205.certificate2467,MergedCutCells.Batch205.certificate2468,MergedCutCells.Batch205.certificate2469,MergedCutCells.Batch205.certificate2470], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2463,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2464,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2466,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2467,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2468,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2469,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2470,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric652 : ∀ c∈certificate652.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2463,MergedCutCells.Batch205.certificate2464,MergedCutCells.Batch205.certificate2465,MergedCutCells.Batch205.certificate2466,MergedCutCells.Batch205.certificate2467,MergedCutCells.Batch205.certificate2468,MergedCutCells.Batch205.certificate2469,MergedCutCells.Batch205.certificate2470], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2463,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2464,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2466,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2467,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2468,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2469,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2470,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid652 : ∀ c∈certificate652.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2463,MergedCutCells.Batch205.certificate2464,MergedCutCells.Batch205.certificate2465,MergedCutCells.Batch205.certificate2466,MergedCutCells.Batch205.certificate2467,MergedCutCells.Batch205.certificate2468,MergedCutCells.Batch205.certificate2469,MergedCutCells.Batch205.certificate2470], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches652 : ∀ c∈certificate652.cells, c.population=certificate652.population := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2463,MergedCutCells.Batch205.certificate2464,MergedCutCells.Batch205.certificate2465,MergedCutCells.Batch205.certificate2466,MergedCutCells.Batch205.certificate2467,MergedCutCells.Batch205.certificate2468,MergedCutCells.Batch205.certificate2469,MergedCutCells.Batch205.certificate2470], c.population=PopulationCertificates.Batch021.certificate434
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers652 {x : ℝ} (hx : certificate652.interval.Contains x) : ∃ c∈certificate652.cells, c.region.interval.Contains x := rat_cut_group_covers certificate652 numericValid652 hx

def certificate653 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate435,PopulationCertificates.Batch021.certificate435,[MergedCutCells.Batch205.certificate2471,MergedCutCells.Batch206.certificate2472,MergedCutCells.Batch206.certificate2473,MergedCutCells.Batch206.certificate2474],(2694363738654067187/500000000000000000),none,(1/2),(3442164086336961591/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid653 : certificate653.NumericValid := by decide +kernel
theorem cellsSound653 : ∀ c∈certificate653.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2471,MergedCutCells.Batch206.certificate2472,MergedCutCells.Batch206.certificate2473,MergedCutCells.Batch206.certificate2474], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.sound2471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2472,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2474,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric653 : ∀ c∈certificate653.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2471,MergedCutCells.Batch206.certificate2472,MergedCutCells.Batch206.certificate2473,MergedCutCells.Batch206.certificate2474], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch205.numericValid2471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2472,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2474,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid653 : ∀ c∈certificate653.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2471,MergedCutCells.Batch206.certificate2472,MergedCutCells.Batch206.certificate2473,MergedCutCells.Batch206.certificate2474], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches653 : ∀ c∈certificate653.cells, c.population=certificate653.population := by
  change ∀ c∈[MergedCutCells.Batch205.certificate2471,MergedCutCells.Batch206.certificate2472,MergedCutCells.Batch206.certificate2473,MergedCutCells.Batch206.certificate2474], c.population=PopulationCertificates.Batch021.certificate435
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers653 {x : ℝ} (hx : certificate653.interval.Contains x) : ∃ c∈certificate653.cells, c.region.interval.Contains x := rat_cut_group_covers certificate653 numericValid653 hx

def certificate654 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate436,PopulationCertificates.Batch021.certificate436,[MergedCutCells.Batch206.certificate2475,MergedCutCells.Batch206.certificate2476],(87199479606932351/100000000000000000),(some (246640843/250000000)),(1/2),(590654045424226473/500000000000000000),(some (260250168533535089/500000000000000000)),(some (214995330401175471/1000000000000000000))⟩
theorem numericValid654 : certificate654.NumericValid := by decide +kernel
theorem cellsSound654 : ∀ c∈certificate654.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch206.certificate2475,MergedCutCells.Batch206.certificate2476], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2475,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2476,List.forall_mem_nil _⟩⟩
theorem cellsNumeric654 : ∀ c∈certificate654.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch206.certificate2475,MergedCutCells.Batch206.certificate2476], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2475,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2476,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid654 : ∀ c∈certificate654.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch206.certificate2475,MergedCutCells.Batch206.certificate2476], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid219,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid219,List.forall_mem_nil _⟩⟩
theorem populationMatches654 : ∀ c∈certificate654.cells, c.population=certificate654.population := by
  change ∀ c∈[MergedCutCells.Batch206.certificate2475,MergedCutCells.Batch206.certificate2476], c.population=PopulationCertificates.Batch021.certificate436
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers654 {x : ℝ} (hx : certificate654.interval.Contains x) : ∃ c∈certificate654.cells, c.region.interval.Contains x := rat_cut_group_covers certificate654 numericValid654 hx

def certificate655 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate436,PopulationCertificates.Batch021.certificate436,[MergedCutCells.Batch206.certificate2477,MergedCutCells.Batch206.certificate2478,MergedCutCells.Batch206.certificate2479,MergedCutCells.Batch206.certificate2480,MergedCutCells.Batch206.certificate2481,MergedCutCells.Batch206.certificate2482,MergedCutCells.Batch206.certificate2483],(246640843/250000000),none,(1/2),(44149811636606179/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid655 : certificate655.NumericValid := by decide +kernel
theorem cellsSound655 : ∀ c∈certificate655.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch206.certificate2477,MergedCutCells.Batch206.certificate2478,MergedCutCells.Batch206.certificate2479,MergedCutCells.Batch206.certificate2480,MergedCutCells.Batch206.certificate2481,MergedCutCells.Batch206.certificate2482,MergedCutCells.Batch206.certificate2483], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2477,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2478,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2479,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2481,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2482,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.sound2483,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric655 : ∀ c∈certificate655.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch206.certificate2477,MergedCutCells.Batch206.certificate2478,MergedCutCells.Batch206.certificate2479,MergedCutCells.Batch206.certificate2480,MergedCutCells.Batch206.certificate2481,MergedCutCells.Batch206.certificate2482,MergedCutCells.Batch206.certificate2483], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2477,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2478,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2479,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2481,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2482,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch206.numericValid2483,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid655 : ∀ c∈certificate655.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch206.certificate2477,MergedCutCells.Batch206.certificate2478,MergedCutCells.Batch206.certificate2479,MergedCutCells.Batch206.certificate2480,MergedCutCells.Batch206.certificate2481,MergedCutCells.Batch206.certificate2482,MergedCutCells.Batch206.certificate2483], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches655 : ∀ c∈certificate655.cells, c.population=certificate655.population := by
  change ∀ c∈[MergedCutCells.Batch206.certificate2477,MergedCutCells.Batch206.certificate2478,MergedCutCells.Batch206.certificate2479,MergedCutCells.Batch206.certificate2480,MergedCutCells.Batch206.certificate2481,MergedCutCells.Batch206.certificate2482,MergedCutCells.Batch206.certificate2483], c.population=PopulationCertificates.Batch021.certificate436
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers655 {x : ℝ} (hx : certificate655.interval.Contains x) : ∃ c∈certificate655.cells, c.region.interval.Contains x := rat_cut_group_covers certificate655 numericValid655 hx

def certificate656 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate437,PopulationCertificates.Batch021.certificate437,[MergedCutCells.Batch207.certificate2484,MergedCutCells.Batch207.certificate2485,MergedCutCells.Batch207.certificate2486],(1348902944002520283/250000000000000000),none,(1/2),(222086840763585161/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid656 : certificate656.NumericValid := by decide +kernel
theorem cellsSound656 : ∀ c∈certificate656.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2484,MergedCutCells.Batch207.certificate2485,MergedCutCells.Batch207.certificate2486], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2485,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2486,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric656 : ∀ c∈certificate656.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2484,MergedCutCells.Batch207.certificate2485,MergedCutCells.Batch207.certificate2486], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2485,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2486,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid656 : ∀ c∈certificate656.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2484,MergedCutCells.Batch207.certificate2485,MergedCutCells.Batch207.certificate2486], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches656 : ∀ c∈certificate656.cells, c.population=certificate656.population := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2484,MergedCutCells.Batch207.certificate2485,MergedCutCells.Batch207.certificate2486], c.population=PopulationCertificates.Batch021.certificate437
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers656 {x : ℝ} (hx : certificate656.interval.Contains x) : ∃ c∈certificate656.cells, c.region.interval.Contains x := rat_cut_group_covers certificate656 numericValid656 hx

def certificate657 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate438,PopulationCertificates.Batch021.certificate438,[MergedCutCells.Batch207.certificate2487,MergedCutCells.Batch207.certificate2488,MergedCutCells.Batch207.certificate2489],(439163561598209157/500000000000000000),(some (15523767/15625000)),(1/2),(631121707281981631/500000000000000000),(some (525843287540188911/1000000000000000000)),(some (219160427910609281/1000000000000000000))⟩
theorem numericValid657 : certificate657.NumericValid := by decide +kernel
theorem cellsSound657 : ∀ c∈certificate657.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2487,MergedCutCells.Batch207.certificate2488,MergedCutCells.Batch207.certificate2489], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2487,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2488,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2489,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric657 : ∀ c∈certificate657.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2487,MergedCutCells.Batch207.certificate2488,MergedCutCells.Batch207.certificate2489], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2487,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2488,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2489,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid657 : ∀ c∈certificate657.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2487,MergedCutCells.Batch207.certificate2488,MergedCutCells.Batch207.certificate2489], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid220,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid220,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid220,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches657 : ∀ c∈certificate657.cells, c.population=certificate657.population := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2487,MergedCutCells.Batch207.certificate2488,MergedCutCells.Batch207.certificate2489], c.population=PopulationCertificates.Batch021.certificate438
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers657 {x : ℝ} (hx : certificate657.interval.Contains x) : ∃ c∈certificate657.cells, c.region.interval.Contains x := rat_cut_group_covers certificate657 numericValid657 hx

def certificate658 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate438,PopulationCertificates.Batch021.certificate438,[MergedCutCells.Batch207.certificate2490,MergedCutCells.Batch207.certificate2491,MergedCutCells.Batch207.certificate2492,MergedCutCells.Batch207.certificate2493,MergedCutCells.Batch207.certificate2494,MergedCutCells.Batch207.certificate2495,MergedCutCells.Batch208.certificate2496],(15523767/15625000),none,(1/2),(18543367608680967/15625000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid658 : certificate658.NumericValid := by decide +kernel
theorem cellsSound658 : ∀ c∈certificate658.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2490,MergedCutCells.Batch207.certificate2491,MergedCutCells.Batch207.certificate2492,MergedCutCells.Batch207.certificate2493,MergedCutCells.Batch207.certificate2494,MergedCutCells.Batch207.certificate2495,MergedCutCells.Batch208.certificate2496], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2490,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2491,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2492,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2494,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.sound2495,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2496,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric658 : ∀ c∈certificate658.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2490,MergedCutCells.Batch207.certificate2491,MergedCutCells.Batch207.certificate2492,MergedCutCells.Batch207.certificate2493,MergedCutCells.Batch207.certificate2494,MergedCutCells.Batch207.certificate2495,MergedCutCells.Batch208.certificate2496], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2490,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2491,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2492,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2494,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch207.numericValid2495,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2496,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid658 : ∀ c∈certificate658.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2490,MergedCutCells.Batch207.certificate2491,MergedCutCells.Batch207.certificate2492,MergedCutCells.Batch207.certificate2493,MergedCutCells.Batch207.certificate2494,MergedCutCells.Batch207.certificate2495,MergedCutCells.Batch208.certificate2496], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches658 : ∀ c∈certificate658.cells, c.population=certificate658.population := by
  change ∀ c∈[MergedCutCells.Batch207.certificate2490,MergedCutCells.Batch207.certificate2491,MergedCutCells.Batch207.certificate2492,MergedCutCells.Batch207.certificate2493,MergedCutCells.Batch207.certificate2494,MergedCutCells.Batch207.certificate2495,MergedCutCells.Batch208.certificate2496], c.population=PopulationCertificates.Batch021.certificate438
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers658 {x : ℝ} (hx : certificate658.interval.Contains x) : ∃ c∈certificate658.cells, c.region.interval.Contains x := rat_cut_group_covers certificate658 numericValid658 hx

def certificate659 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate439,PopulationCertificates.Batch021.certificate439,[MergedCutCells.Batch208.certificate2497,MergedCutCells.Batch208.certificate2498,MergedCutCells.Batch208.certificate2499],(2672414285588011631/500000000000000000),none,(1/2),(906223740319681613/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid659 : certificate659.NumericValid := by decide +kernel
theorem cellsSound659 : ∀ c∈certificate659.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2497,MergedCutCells.Batch208.certificate2498,MergedCutCells.Batch208.certificate2499], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2497,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2499,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric659 : ∀ c∈certificate659.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2497,MergedCutCells.Batch208.certificate2498,MergedCutCells.Batch208.certificate2499], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2497,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2499,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid659 : ∀ c∈certificate659.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2497,MergedCutCells.Batch208.certificate2498,MergedCutCells.Batch208.certificate2499], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches659 : ∀ c∈certificate659.cells, c.population=certificate659.population := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2497,MergedCutCells.Batch208.certificate2498,MergedCutCells.Batch208.certificate2499], c.population=PopulationCertificates.Batch021.certificate439
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers659 {x : ℝ} (hx : certificate659.interval.Contains x) : ∃ c∈certificate659.cells, c.region.interval.Contains x := rat_cut_group_covers certificate659 numericValid659 hx

end Cycle12.MergedCutGroups.Batch054
