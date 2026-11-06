import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch023
import Cycle12.MergedCutCells.Batch225
import Cycle12.MergedCutCells.Batch226
import Cycle12.MergedCutCells.Batch227
import Cycle12.MergedCutCells.Batch228
import Cycle12.MergedCutCells.Batch229
import Cycle12.PopulationCertificates.Batch023

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch059

def certificate708 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate472,PopulationCertificates.Batch023.certificate472,[MergedCutCells.Batch225.certificate2702,MergedCutCells.Batch225.certificate2703],(190227548076614199/200000000000000000),(some (999131817/1000000000)),(1/2),(460188458275131157/200000000000000000),(some (154662962876542187/250000000000000000)),(some (61887996807147177/200000000000000000))⟩
theorem numericValid708 : certificate708.NumericValid := by decide +kernel
theorem cellsSound708 : ∀ c∈certificate708.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2702,MergedCutCells.Batch225.certificate2703], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2702,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2703,List.forall_mem_nil _⟩⟩
theorem cellsNumeric708 : ∀ c∈certificate708.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2702,MergedCutCells.Batch225.certificate2703], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2702,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2703,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid708 : ∀ c∈certificate708.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2702,MergedCutCells.Batch225.certificate2703], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid237,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid237,List.forall_mem_nil _⟩⟩
theorem populationMatches708 : ∀ c∈certificate708.cells, c.population=certificate708.population := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2702,MergedCutCells.Batch225.certificate2703], c.population=PopulationCertificates.Batch023.certificate472
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers708 {x : ℝ} (hx : certificate708.interval.Contains x) : ∃ c∈certificate708.cells, c.region.interval.Contains x := rat_cut_group_covers certificate708 numericValid708 hx

def certificate709 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate472,PopulationCertificates.Batch023.certificate472,[MergedCutCells.Batch225.certificate2704,MergedCutCells.Batch225.certificate2705,MergedCutCells.Batch225.certificate2706,MergedCutCells.Batch225.certificate2707,MergedCutCells.Batch225.certificate2708,MergedCutCells.Batch225.certificate2709],(999131817/1000000000),none,(1/2),(552590849835901809/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid709 : certificate709.NumericValid := by decide +kernel
theorem cellsSound709 : ∀ c∈certificate709.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2704,MergedCutCells.Batch225.certificate2705,MergedCutCells.Batch225.certificate2706,MergedCutCells.Batch225.certificate2707,MergedCutCells.Batch225.certificate2708,MergedCutCells.Batch225.certificate2709], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2704,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2705,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2706,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2707,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2708,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2709,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric709 : ∀ c∈certificate709.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2704,MergedCutCells.Batch225.certificate2705,MergedCutCells.Batch225.certificate2706,MergedCutCells.Batch225.certificate2707,MergedCutCells.Batch225.certificate2708,MergedCutCells.Batch225.certificate2709], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2704,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2705,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2706,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2707,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2708,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2709,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid709 : ∀ c∈certificate709.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2704,MergedCutCells.Batch225.certificate2705,MergedCutCells.Batch225.certificate2706,MergedCutCells.Batch225.certificate2707,MergedCutCells.Batch225.certificate2708,MergedCutCells.Batch225.certificate2709], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches709 : ∀ c∈certificate709.cells, c.population=certificate709.population := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2704,MergedCutCells.Batch225.certificate2705,MergedCutCells.Batch225.certificate2706,MergedCutCells.Batch225.certificate2707,MergedCutCells.Batch225.certificate2708,MergedCutCells.Batch225.certificate2709], c.population=PopulationCertificates.Batch023.certificate472
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers709 {x : ℝ} (hx : certificate709.interval.Contains x) : ∃ c∈certificate709.cells, c.region.interval.Contains x := rat_cut_group_covers certificate709 numericValid709 hx

def certificate710 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate473,PopulationCertificates.Batch023.certificate473,[MergedCutCells.Batch225.certificate2710,MergedCutCells.Batch225.certificate2711,MergedCutCells.Batch226.certificate2712,MergedCutCells.Batch226.certificate2713],(4786389565516300381/1000000000000000000),none,(1/2),(2166368847862272079/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid710 : certificate710.NumericValid := by decide +kernel
theorem cellsSound710 : ∀ c∈certificate710.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2710,MergedCutCells.Batch225.certificate2711,MergedCutCells.Batch226.certificate2712,MergedCutCells.Batch226.certificate2713], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2711,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2713,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric710 : ∀ c∈certificate710.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2710,MergedCutCells.Batch225.certificate2711,MergedCutCells.Batch226.certificate2712,MergedCutCells.Batch226.certificate2713], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2711,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2713,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid710 : ∀ c∈certificate710.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2710,MergedCutCells.Batch225.certificate2711,MergedCutCells.Batch226.certificate2712,MergedCutCells.Batch226.certificate2713], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches710 : ∀ c∈certificate710.cells, c.population=certificate710.population := by
  change ∀ c∈[MergedCutCells.Batch225.certificate2710,MergedCutCells.Batch225.certificate2711,MergedCutCells.Batch226.certificate2712,MergedCutCells.Batch226.certificate2713], c.population=PopulationCertificates.Batch023.certificate473
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers710 {x : ℝ} (hx : certificate710.interval.Contains x) : ∃ c∈certificate710.cells, c.region.interval.Contains x := rat_cut_group_covers certificate710 numericValid710 hx

def certificate711 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate474,PopulationCertificates.Batch023.certificate474,[MergedCutCells.Batch226.certificate2714,MergedCutCells.Batch226.certificate2715],(957944417812057023/1000000000000000000),(some (490887409/500000000)),(1/2),(1199249628928695731/500000000000000000),(some (155141955079999319/250000000000000000)),(some (311843590259886733/1000000000000000000))⟩
theorem numericValid711 : certificate711.NumericValid := by decide +kernel
theorem cellsSound711 : ∀ c∈certificate711.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch226.certificate2714,MergedCutCells.Batch226.certificate2715], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2715,List.forall_mem_nil _⟩⟩
theorem cellsNumeric711 : ∀ c∈certificate711.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch226.certificate2714,MergedCutCells.Batch226.certificate2715], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2715,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid711 : ∀ c∈certificate711.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch226.certificate2714,MergedCutCells.Batch226.certificate2715], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid238,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid238,List.forall_mem_nil _⟩⟩
theorem populationMatches711 : ∀ c∈certificate711.cells, c.population=certificate711.population := by
  change ∀ c∈[MergedCutCells.Batch226.certificate2714,MergedCutCells.Batch226.certificate2715], c.population=PopulationCertificates.Batch023.certificate474
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers711 {x : ℝ} (hx : certificate711.interval.Contains x) : ∃ c∈certificate711.cells, c.region.interval.Contains x := rat_cut_group_covers certificate711 numericValid711 hx

def certificate712 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate474,PopulationCertificates.Batch023.certificate474,[MergedCutCells.Batch226.certificate2716,MergedCutCells.Batch226.certificate2717,MergedCutCells.Batch226.certificate2718,MergedCutCells.Batch226.certificate2719,MergedCutCells.Batch226.certificate2720,MergedCutCells.Batch226.certificate2721,MergedCutCells.Batch226.certificate2722,MergedCutCells.Batch226.certificate2723],(490887409/500000000),none,(1/2),(2290657872943670001/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid712 : certificate712.NumericValid := by decide +kernel
theorem cellsSound712 : ∀ c∈certificate712.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch226.certificate2716,MergedCutCells.Batch226.certificate2717,MergedCutCells.Batch226.certificate2718,MergedCutCells.Batch226.certificate2719,MergedCutCells.Batch226.certificate2720,MergedCutCells.Batch226.certificate2721,MergedCutCells.Batch226.certificate2722,MergedCutCells.Batch226.certificate2723], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2716,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2717,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2718,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2719,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2720,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2721,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2722,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.sound2723,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric712 : ∀ c∈certificate712.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch226.certificate2716,MergedCutCells.Batch226.certificate2717,MergedCutCells.Batch226.certificate2718,MergedCutCells.Batch226.certificate2719,MergedCutCells.Batch226.certificate2720,MergedCutCells.Batch226.certificate2721,MergedCutCells.Batch226.certificate2722,MergedCutCells.Batch226.certificate2723], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2716,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2717,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2718,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2719,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2720,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2721,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2722,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch226.numericValid2723,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid712 : ∀ c∈certificate712.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch226.certificate2716,MergedCutCells.Batch226.certificate2717,MergedCutCells.Batch226.certificate2718,MergedCutCells.Batch226.certificate2719,MergedCutCells.Batch226.certificate2720,MergedCutCells.Batch226.certificate2721,MergedCutCells.Batch226.certificate2722,MergedCutCells.Batch226.certificate2723], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches712 : ∀ c∈certificate712.cells, c.population=certificate712.population := by
  change ∀ c∈[MergedCutCells.Batch226.certificate2716,MergedCutCells.Batch226.certificate2717,MergedCutCells.Batch226.certificate2718,MergedCutCells.Batch226.certificate2719,MergedCutCells.Batch226.certificate2720,MergedCutCells.Batch226.certificate2721,MergedCutCells.Batch226.certificate2722,MergedCutCells.Batch226.certificate2723], c.population=PopulationCertificates.Batch023.certificate474
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers712 {x : ℝ} (hx : certificate712.interval.Contains x) : ∃ c∈certificate712.cells, c.region.interval.Contains x := rat_cut_group_covers certificate712 numericValid712 hx

def certificate713 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate475,PopulationCertificates.Batch023.certificate475,[MergedCutCells.Batch227.certificate2724,MergedCutCells.Batch227.certificate2725,MergedCutCells.Batch227.certificate2726,MergedCutCells.Batch227.certificate2727],(2388297365046084279/500000000000000000),none,(1/2),(2205247317649369677/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid713 : certificate713.NumericValid := by decide +kernel
theorem cellsSound713 : ∀ c∈certificate713.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2724,MergedCutCells.Batch227.certificate2725,MergedCutCells.Batch227.certificate2726,MergedCutCells.Batch227.certificate2727], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2724,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2725,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2726,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2727,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric713 : ∀ c∈certificate713.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2724,MergedCutCells.Batch227.certificate2725,MergedCutCells.Batch227.certificate2726,MergedCutCells.Batch227.certificate2727], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2724,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2725,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2726,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2727,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid713 : ∀ c∈certificate713.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2724,MergedCutCells.Batch227.certificate2725,MergedCutCells.Batch227.certificate2726,MergedCutCells.Batch227.certificate2727], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches713 : ∀ c∈certificate713.cells, c.population=certificate713.population := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2724,MergedCutCells.Batch227.certificate2725,MergedCutCells.Batch227.certificate2726,MergedCutCells.Batch227.certificate2727], c.population=PopulationCertificates.Batch023.certificate475
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers713 {x : ℝ} (hx : certificate713.interval.Contains x) : ∃ c∈certificate713.cells, c.region.interval.Contains x := rat_cut_group_covers certificate713 numericValid713 hx

def certificate714 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate476,PopulationCertificates.Batch023.certificate476,[MergedCutCells.Batch227.certificate2728,MergedCutCells.Batch227.certificate2729],(961884347204903967/1000000000000000000),(some (123223637/125000000)),(1/2),(2477820024144844477/1000000000000000000),(some (156176914513982013/250000000000000000)),(some (317156706968692181/1000000000000000000))⟩
theorem numericValid714 : certificate714.NumericValid := by decide +kernel
theorem cellsSound714 : ∀ c∈certificate714.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2728,MergedCutCells.Batch227.certificate2729], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2728,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2729,List.forall_mem_nil _⟩⟩
theorem cellsNumeric714 : ∀ c∈certificate714.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2728,MergedCutCells.Batch227.certificate2729], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2728,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2729,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid714 : ∀ c∈certificate714.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2728,MergedCutCells.Batch227.certificate2729], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid239,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid239,List.forall_mem_nil _⟩⟩
theorem populationMatches714 : ∀ c∈certificate714.cells, c.population=certificate714.population := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2728,MergedCutCells.Batch227.certificate2729], c.population=PopulationCertificates.Batch023.certificate476
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers714 {x : ℝ} (hx : certificate714.interval.Contains x) : ∃ c∈certificate714.cells, c.region.interval.Contains x := rat_cut_group_covers certificate714 numericValid714 hx

def certificate715 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate476,PopulationCertificates.Batch023.certificate476,[MergedCutCells.Batch227.certificate2730,MergedCutCells.Batch227.certificate2731,MergedCutCells.Batch227.certificate2732,MergedCutCells.Batch227.certificate2733,MergedCutCells.Batch227.certificate2734,MergedCutCells.Batch227.certificate2735],(123223637/125000000),none,(1/2),(591009925741917501/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid715 : certificate715.NumericValid := by decide +kernel
theorem cellsSound715 : ∀ c∈certificate715.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2730,MergedCutCells.Batch227.certificate2731,MergedCutCells.Batch227.certificate2732,MergedCutCells.Batch227.certificate2733,MergedCutCells.Batch227.certificate2734,MergedCutCells.Batch227.certificate2735], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2730,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2732,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2733,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2734,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.sound2735,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric715 : ∀ c∈certificate715.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2730,MergedCutCells.Batch227.certificate2731,MergedCutCells.Batch227.certificate2732,MergedCutCells.Batch227.certificate2733,MergedCutCells.Batch227.certificate2734,MergedCutCells.Batch227.certificate2735], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2730,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2732,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2733,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2734,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch227.numericValid2735,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid715 : ∀ c∈certificate715.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2730,MergedCutCells.Batch227.certificate2731,MergedCutCells.Batch227.certificate2732,MergedCutCells.Batch227.certificate2733,MergedCutCells.Batch227.certificate2734,MergedCutCells.Batch227.certificate2735], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches715 : ∀ c∈certificate715.cells, c.population=certificate715.population := by
  change ∀ c∈[MergedCutCells.Batch227.certificate2730,MergedCutCells.Batch227.certificate2731,MergedCutCells.Batch227.certificate2732,MergedCutCells.Batch227.certificate2733,MergedCutCells.Batch227.certificate2734,MergedCutCells.Batch227.certificate2735], c.population=PopulationCertificates.Batch023.certificate476
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers715 {x : ℝ} (hx : certificate715.interval.Contains x) : ∃ c∈certificate715.cells, c.region.interval.Contains x := rat_cut_group_covers certificate715 numericValid715 hx

def certificate716 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate477,PopulationCertificates.Batch023.certificate477,[MergedCutCells.Batch228.certificate2736,MergedCutCells.Batch228.certificate2737,MergedCutCells.Batch228.certificate2738,MergedCutCells.Batch228.certificate2739],(2383255279212662603/500000000000000000),none,(1/2),(897892617136286399/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid716 : certificate716.NumericValid := by decide +kernel
theorem cellsSound716 : ∀ c∈certificate716.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2736,MergedCutCells.Batch228.certificate2737,MergedCutCells.Batch228.certificate2738,MergedCutCells.Batch228.certificate2739], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2736,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2737,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2739,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric716 : ∀ c∈certificate716.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2736,MergedCutCells.Batch228.certificate2737,MergedCutCells.Batch228.certificate2738,MergedCutCells.Batch228.certificate2739], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2736,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2737,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2739,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid716 : ∀ c∈certificate716.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2736,MergedCutCells.Batch228.certificate2737,MergedCutCells.Batch228.certificate2738,MergedCutCells.Batch228.certificate2739], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches716 : ∀ c∈certificate716.cells, c.population=certificate716.population := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2736,MergedCutCells.Batch228.certificate2737,MergedCutCells.Batch228.certificate2738,MergedCutCells.Batch228.certificate2739], c.population=PopulationCertificates.Batch023.certificate477
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers716 {x : ℝ} (hx : certificate716.interval.Contains x) : ∃ c∈certificate716.cells, c.region.interval.Contains x := rat_cut_group_covers certificate716 numericValid716 hx

def certificate717 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate478,PopulationCertificates.Batch023.certificate478,[MergedCutCells.Batch228.certificate2740,MergedCutCells.Batch228.certificate2741],(481247217439104619/500000000000000000),(some (246638279/250000000)),(1/2),(2519292521246861101/1000000000000000000),(some (314457492643087649/500000000000000000)),(some (64547303303188991/200000000000000000))⟩
theorem numericValid717 : certificate717.NumericValid := by decide +kernel
theorem cellsSound717 : ∀ c∈certificate717.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2740,MergedCutCells.Batch228.certificate2741], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2740,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2741,List.forall_mem_nil _⟩⟩
theorem cellsNumeric717 : ∀ c∈certificate717.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2740,MergedCutCells.Batch228.certificate2741], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2740,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2741,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid717 : ∀ c∈certificate717.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2740,MergedCutCells.Batch228.certificate2741], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid240,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid240,List.forall_mem_nil _⟩⟩
theorem populationMatches717 : ∀ c∈certificate717.cells, c.population=certificate717.population := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2740,MergedCutCells.Batch228.certificate2741], c.population=PopulationCertificates.Batch023.certificate478
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers717 {x : ℝ} (hx : certificate717.interval.Contains x) : ∃ c∈certificate717.cells, c.region.interval.Contains x := rat_cut_group_covers certificate717 numericValid717 hx

def certificate718 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate478,PopulationCertificates.Batch023.certificate478,[MergedCutCells.Batch228.certificate2742,MergedCutCells.Batch228.certificate2743,MergedCutCells.Batch228.certificate2744,MergedCutCells.Batch228.certificate2745,MergedCutCells.Batch228.certificate2746,MergedCutCells.Batch228.certificate2747],(246638279/250000000),none,(1/2),(2416065478716146511/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid718 : certificate718.NumericValid := by decide +kernel
theorem cellsSound718 : ∀ c∈certificate718.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2742,MergedCutCells.Batch228.certificate2743,MergedCutCells.Batch228.certificate2744,MergedCutCells.Batch228.certificate2745,MergedCutCells.Batch228.certificate2746,MergedCutCells.Batch228.certificate2747], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2743,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2744,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2745,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2746,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.sound2747,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric718 : ∀ c∈certificate718.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2742,MergedCutCells.Batch228.certificate2743,MergedCutCells.Batch228.certificate2744,MergedCutCells.Batch228.certificate2745,MergedCutCells.Batch228.certificate2746,MergedCutCells.Batch228.certificate2747], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2743,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2744,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2745,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2746,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch228.numericValid2747,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid718 : ∀ c∈certificate718.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2742,MergedCutCells.Batch228.certificate2743,MergedCutCells.Batch228.certificate2744,MergedCutCells.Batch228.certificate2745,MergedCutCells.Batch228.certificate2746,MergedCutCells.Batch228.certificate2747], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches718 : ∀ c∈certificate718.cells, c.population=certificate718.population := by
  change ∀ c∈[MergedCutCells.Batch228.certificate2742,MergedCutCells.Batch228.certificate2743,MergedCutCells.Batch228.certificate2744,MergedCutCells.Batch228.certificate2745,MergedCutCells.Batch228.certificate2746,MergedCutCells.Batch228.certificate2747], c.population=PopulationCertificates.Batch023.certificate478
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers718 {x : ℝ} (hx : certificate718.interval.Contains x) : ∃ c∈certificate718.cells, c.region.interval.Contains x := rat_cut_group_covers certificate718 numericValid718 hx

def certificate719 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate479,PopulationCertificates.Batch023.certificate479,[MergedCutCells.Batch229.certificate2748,MergedCutCells.Batch229.certificate2749,MergedCutCells.Batch229.certificate2750,MergedCutCells.Batch229.certificate2751],(4714334374534769691/1000000000000000000),none,(1/2),(4493724857033487989/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid719 : certificate719.NumericValid := by decide +kernel
theorem cellsSound719 : ∀ c∈certificate719.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch229.certificate2748,MergedCutCells.Batch229.certificate2749,MergedCutCells.Batch229.certificate2750,MergedCutCells.Batch229.certificate2751], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2748,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2750,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2751,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric719 : ∀ c∈certificate719.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch229.certificate2748,MergedCutCells.Batch229.certificate2749,MergedCutCells.Batch229.certificate2750,MergedCutCells.Batch229.certificate2751], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2748,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2750,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2751,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid719 : ∀ c∈certificate719.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch229.certificate2748,MergedCutCells.Batch229.certificate2749,MergedCutCells.Batch229.certificate2750,MergedCutCells.Batch229.certificate2751], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches719 : ∀ c∈certificate719.cells, c.population=certificate719.population := by
  change ∀ c∈[MergedCutCells.Batch229.certificate2748,MergedCutCells.Batch229.certificate2749,MergedCutCells.Batch229.certificate2750,MergedCutCells.Batch229.certificate2751], c.population=PopulationCertificates.Batch023.certificate479
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers719 {x : ℝ} (hx : certificate719.interval.Contains x) : ∃ c∈certificate719.cells, c.region.interval.Contains x := rat_cut_group_covers certificate719 numericValid719 hx

end Cycle12.MergedCutGroups.Batch059
