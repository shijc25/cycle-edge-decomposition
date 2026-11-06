import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch022
import Cycle12.GeometryCertificates.Batch023
import Cycle12.MergedCutCells.Batch216
import Cycle12.MergedCutCells.Batch217
import Cycle12.MergedCutCells.Batch218
import Cycle12.MergedCutCells.Batch219
import Cycle12.MergedCutCells.Batch220
import Cycle12.PopulationCertificates.Batch022
import Cycle12.PopulationCertificates.Batch023

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch057

def certificate684 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate456,PopulationCertificates.Batch022.certificate456,[MergedCutCells.Batch216.certificate2601,MergedCutCells.Batch216.certificate2602],(46208459765130961/50000000000000000),(some (60678081/62500000)),(1/2),(182608019364002177/100000000000000000),(some (36372255173165371/62500000000000000)),(some (268694550271329367/1000000000000000000))⟩
theorem numericValid684 : certificate684.NumericValid := by decide +kernel
theorem cellsSound684 : ∀ c∈certificate684.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2601,MergedCutCells.Batch216.certificate2602], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2601,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2602,List.forall_mem_nil _⟩⟩
theorem cellsNumeric684 : ∀ c∈certificate684.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2601,MergedCutCells.Batch216.certificate2602], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2601,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2602,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid684 : ∀ c∈certificate684.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2601,MergedCutCells.Batch216.certificate2602], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid229,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid229,List.forall_mem_nil _⟩⟩
theorem populationMatches684 : ∀ c∈certificate684.cells, c.population=certificate684.population := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2601,MergedCutCells.Batch216.certificate2602], c.population=PopulationCertificates.Batch022.certificate456
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers684 {x : ℝ} (hx : certificate684.interval.Contains x) : ∃ c∈certificate684.cells, c.region.interval.Contains x := rat_cut_group_covers certificate684 numericValid684 hx

def certificate685 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate456,PopulationCertificates.Batch022.certificate456,[MergedCutCells.Batch216.certificate2603,MergedCutCells.Batch217.certificate2604,MergedCutCells.Batch217.certificate2605,MergedCutCells.Batch217.certificate2606,MergedCutCells.Batch217.certificate2607,MergedCutCells.Batch217.certificate2608,MergedCutCells.Batch217.certificate2609],(60678081/62500000),none,(1/2),(861242912426325399/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid685 : certificate685.NumericValid := by decide +kernel
theorem cellsSound685 : ∀ c∈certificate685.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2603,MergedCutCells.Batch217.certificate2604,MergedCutCells.Batch217.certificate2605,MergedCutCells.Batch217.certificate2606,MergedCutCells.Batch217.certificate2607,MergedCutCells.Batch217.certificate2608,MergedCutCells.Batch217.certificate2609], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2605,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2606,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2608,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2609,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric685 : ∀ c∈certificate685.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2603,MergedCutCells.Batch217.certificate2604,MergedCutCells.Batch217.certificate2605,MergedCutCells.Batch217.certificate2606,MergedCutCells.Batch217.certificate2607,MergedCutCells.Batch217.certificate2608,MergedCutCells.Batch217.certificate2609], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2605,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2606,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2608,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2609,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid685 : ∀ c∈certificate685.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2603,MergedCutCells.Batch217.certificate2604,MergedCutCells.Batch217.certificate2605,MergedCutCells.Batch217.certificate2606,MergedCutCells.Batch217.certificate2607,MergedCutCells.Batch217.certificate2608,MergedCutCells.Batch217.certificate2609], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches685 : ∀ c∈certificate685.cells, c.population=certificate685.population := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2603,MergedCutCells.Batch217.certificate2604,MergedCutCells.Batch217.certificate2605,MergedCutCells.Batch217.certificate2606,MergedCutCells.Batch217.certificate2607,MergedCutCells.Batch217.certificate2608,MergedCutCells.Batch217.certificate2609], c.population=PopulationCertificates.Batch022.certificate456
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers685 {x : ℝ} (hx : certificate685.interval.Contains x) : ∃ c∈certificate685.cells, c.region.interval.Contains x := rat_cut_group_covers certificate685 numericValid685 hx

def certificate686 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate457,PopulationCertificates.Batch022.certificate457,[MergedCutCells.Batch217.certificate2610,MergedCutCells.Batch217.certificate2611,MergedCutCells.Batch217.certificate2612,MergedCutCells.Batch217.certificate2613],(5081330861966520487/1000000000000000000),none,(1/2),(254214210563157573/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid686 : certificate686.NumericValid := by decide +kernel
theorem cellsSound686 : ∀ c∈certificate686.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch217.certificate2610,MergedCutCells.Batch217.certificate2611,MergedCutCells.Batch217.certificate2612,MergedCutCells.Batch217.certificate2613], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2610,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2611,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2612,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2613,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric686 : ∀ c∈certificate686.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch217.certificate2610,MergedCutCells.Batch217.certificate2611,MergedCutCells.Batch217.certificate2612,MergedCutCells.Batch217.certificate2613], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2610,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2611,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2612,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2613,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid686 : ∀ c∈certificate686.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch217.certificate2610,MergedCutCells.Batch217.certificate2611,MergedCutCells.Batch217.certificate2612,MergedCutCells.Batch217.certificate2613], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches686 : ∀ c∈certificate686.cells, c.population=certificate686.population := by
  change ∀ c∈[MergedCutCells.Batch217.certificate2610,MergedCutCells.Batch217.certificate2611,MergedCutCells.Batch217.certificate2612,MergedCutCells.Batch217.certificate2613], c.population=PopulationCertificates.Batch022.certificate457
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers686 {x : ℝ} (hx : certificate686.interval.Contains x) : ∃ c∈certificate686.cells, c.region.interval.Contains x := rat_cut_group_covers certificate686 numericValid686 hx

def certificate687 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate458,PopulationCertificates.Batch022.certificate458,[MergedCutCells.Batch217.certificate2614,MergedCutCells.Batch217.certificate2615],(926968675977638391/1000000000000000000),(some (973755931/1000000000)),(1/2),(188409232521193067/100000000000000000),(some (293337175014011967/500000000000000000)),(some (273464507125149633/1000000000000000000))⟩
theorem numericValid687 : certificate687.NumericValid := by decide +kernel
theorem cellsSound687 : ∀ c∈certificate687.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch217.certificate2614,MergedCutCells.Batch217.certificate2615], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2614,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.sound2615,List.forall_mem_nil _⟩⟩
theorem cellsNumeric687 : ∀ c∈certificate687.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch217.certificate2614,MergedCutCells.Batch217.certificate2615], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2614,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch217.numericValid2615,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid687 : ∀ c∈certificate687.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch217.certificate2614,MergedCutCells.Batch217.certificate2615], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid230,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid230,List.forall_mem_nil _⟩⟩
theorem populationMatches687 : ∀ c∈certificate687.cells, c.population=certificate687.population := by
  change ∀ c∈[MergedCutCells.Batch217.certificate2614,MergedCutCells.Batch217.certificate2615], c.population=PopulationCertificates.Batch022.certificate458
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers687 {x : ℝ} (hx : certificate687.interval.Contains x) : ∃ c∈certificate687.cells, c.region.interval.Contains x := rat_cut_group_covers certificate687 numericValid687 hx

def certificate688 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate458,PopulationCertificates.Batch022.certificate458,[MergedCutCells.Batch218.certificate2616,MergedCutCells.Batch218.certificate2617,MergedCutCells.Batch218.certificate2618,MergedCutCells.Batch218.certificate2619,MergedCutCells.Batch218.certificate2620,MergedCutCells.Batch218.certificate2621,MergedCutCells.Batch218.certificate2622],(973755931/1000000000),none,(1/2),(1790825864064947551/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid688 : certificate688.NumericValid := by decide +kernel
theorem cellsSound688 : ∀ c∈certificate688.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2616,MergedCutCells.Batch218.certificate2617,MergedCutCells.Batch218.certificate2618,MergedCutCells.Batch218.certificate2619,MergedCutCells.Batch218.certificate2620,MergedCutCells.Batch218.certificate2621,MergedCutCells.Batch218.certificate2622], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2616,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2617,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2619,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2620,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2622,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric688 : ∀ c∈certificate688.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2616,MergedCutCells.Batch218.certificate2617,MergedCutCells.Batch218.certificate2618,MergedCutCells.Batch218.certificate2619,MergedCutCells.Batch218.certificate2620,MergedCutCells.Batch218.certificate2621,MergedCutCells.Batch218.certificate2622], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2616,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2617,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2619,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2620,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2622,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid688 : ∀ c∈certificate688.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2616,MergedCutCells.Batch218.certificate2617,MergedCutCells.Batch218.certificate2618,MergedCutCells.Batch218.certificate2619,MergedCutCells.Batch218.certificate2620,MergedCutCells.Batch218.certificate2621,MergedCutCells.Batch218.certificate2622], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches688 : ∀ c∈certificate688.cells, c.population=certificate688.population := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2616,MergedCutCells.Batch218.certificate2617,MergedCutCells.Batch218.certificate2618,MergedCutCells.Batch218.certificate2619,MergedCutCells.Batch218.certificate2620,MergedCutCells.Batch218.certificate2621,MergedCutCells.Batch218.certificate2622], c.population=PopulationCertificates.Batch022.certificate458
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers688 {x : ℝ} (hx : certificate688.interval.Contains x) : ∃ c∈certificate688.cells, c.region.interval.Contains x := rat_cut_group_covers certificate688 numericValid688 hx

def certificate689 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate459,PopulationCertificates.Batch022.certificate459,[MergedCutCells.Batch218.certificate2623,MergedCutCells.Batch218.certificate2624,MergedCutCells.Batch218.certificate2625,MergedCutCells.Batch218.certificate2626],(1248421938625348219/250000000000000000),none,(1/2),(4054934382274095421/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid689 : certificate689.NumericValid := by decide +kernel
theorem cellsSound689 : ∀ c∈certificate689.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2623,MergedCutCells.Batch218.certificate2624,MergedCutCells.Batch218.certificate2625,MergedCutCells.Batch218.certificate2626], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2623,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2624,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2626,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric689 : ∀ c∈certificate689.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2623,MergedCutCells.Batch218.certificate2624,MergedCutCells.Batch218.certificate2625,MergedCutCells.Batch218.certificate2626], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2623,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2624,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2626,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid689 : ∀ c∈certificate689.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2623,MergedCutCells.Batch218.certificate2624,MergedCutCells.Batch218.certificate2625,MergedCutCells.Batch218.certificate2626], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches689 : ∀ c∈certificate689.cells, c.population=certificate689.population := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2623,MergedCutCells.Batch218.certificate2624,MergedCutCells.Batch218.certificate2625,MergedCutCells.Batch218.certificate2626], c.population=PopulationCertificates.Batch022.certificate459
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers689 {x : ℝ} (hx : certificate689.interval.Contains x) : ∃ c∈certificate689.cells, c.region.interval.Contains x := rat_cut_group_covers certificate689 numericValid689 hx

def certificate690 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate460,PopulationCertificates.Batch023.certificate460,[MergedCutCells.Batch218.certificate2627,MergedCutCells.Batch219.certificate2628],(465018820794804907/500000000000000000),(some (976942249/1000000000)),(1/2),(120534124671935223/62500000000000000),(some (591481792838814181/1000000000000000000)),(some (55689654726456393/200000000000000000))⟩
theorem numericValid690 : certificate690.NumericValid := by decide +kernel
theorem cellsSound690 : ∀ c∈certificate690.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2627,MergedCutCells.Batch219.certificate2628], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.sound2627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2628,List.forall_mem_nil _⟩⟩
theorem cellsNumeric690 : ∀ c∈certificate690.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2627,MergedCutCells.Batch219.certificate2628], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch218.numericValid2627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2628,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid690 : ∀ c∈certificate690.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2627,MergedCutCells.Batch219.certificate2628], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid231,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid231,List.forall_mem_nil _⟩⟩
theorem populationMatches690 : ∀ c∈certificate690.cells, c.population=certificate690.population := by
  change ∀ c∈[MergedCutCells.Batch218.certificate2627,MergedCutCells.Batch219.certificate2628], c.population=PopulationCertificates.Batch023.certificate460
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers690 {x : ℝ} (hx : certificate690.interval.Contains x) : ∃ c∈certificate690.cells, c.region.interval.Contains x := rat_cut_group_covers certificate690 numericValid690 hx

def certificate691 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate460,PopulationCertificates.Batch023.certificate460,[MergedCutCells.Batch219.certificate2629,MergedCutCells.Batch219.certificate2630,MergedCutCells.Batch219.certificate2631,MergedCutCells.Batch219.certificate2632,MergedCutCells.Batch219.certificate2633,MergedCutCells.Batch219.certificate2634,MergedCutCells.Batch219.certificate2635],(976942249/1000000000),none,(1/2),(917901230774563209/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid691 : certificate691.NumericValid := by decide +kernel
theorem cellsSound691 : ∀ c∈certificate691.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch219.certificate2629,MergedCutCells.Batch219.certificate2630,MergedCutCells.Batch219.certificate2631,MergedCutCells.Batch219.certificate2632,MergedCutCells.Batch219.certificate2633,MergedCutCells.Batch219.certificate2634,MergedCutCells.Batch219.certificate2635], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2630,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2631,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2632,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2634,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2635,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric691 : ∀ c∈certificate691.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch219.certificate2629,MergedCutCells.Batch219.certificate2630,MergedCutCells.Batch219.certificate2631,MergedCutCells.Batch219.certificate2632,MergedCutCells.Batch219.certificate2633,MergedCutCells.Batch219.certificate2634,MergedCutCells.Batch219.certificate2635], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2630,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2631,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2632,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2634,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2635,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid691 : ∀ c∈certificate691.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch219.certificate2629,MergedCutCells.Batch219.certificate2630,MergedCutCells.Batch219.certificate2631,MergedCutCells.Batch219.certificate2632,MergedCutCells.Batch219.certificate2633,MergedCutCells.Batch219.certificate2634,MergedCutCells.Batch219.certificate2635], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches691 : ∀ c∈certificate691.cells, c.population=certificate691.population := by
  change ∀ c∈[MergedCutCells.Batch219.certificate2629,MergedCutCells.Batch219.certificate2630,MergedCutCells.Batch219.certificate2631,MergedCutCells.Batch219.certificate2632,MergedCutCells.Batch219.certificate2633,MergedCutCells.Batch219.certificate2634,MergedCutCells.Batch219.certificate2635], c.population=PopulationCertificates.Batch023.certificate460
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers691 {x : ℝ} (hx : certificate691.interval.Contains x) : ∃ c∈certificate691.cells, c.region.interval.Contains x := rat_cut_group_covers certificate691 numericValid691 hx

def certificate692 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate461,PopulationCertificates.Batch023.certificate461,[MergedCutCells.Batch219.certificate2636,MergedCutCells.Batch219.certificate2637,MergedCutCells.Batch219.certificate2638,MergedCutCells.Batch219.certificate2639],(5011154568274861473/1000000000000000000),none,(1/2),(412346465711465109/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid692 : certificate692.NumericValid := by decide +kernel
theorem cellsSound692 : ∀ c∈certificate692.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch219.certificate2636,MergedCutCells.Batch219.certificate2637,MergedCutCells.Batch219.certificate2638,MergedCutCells.Batch219.certificate2639], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2636,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2637,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2638,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.sound2639,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric692 : ∀ c∈certificate692.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch219.certificate2636,MergedCutCells.Batch219.certificate2637,MergedCutCells.Batch219.certificate2638,MergedCutCells.Batch219.certificate2639], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2636,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2637,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2638,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch219.numericValid2639,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid692 : ∀ c∈certificate692.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch219.certificate2636,MergedCutCells.Batch219.certificate2637,MergedCutCells.Batch219.certificate2638,MergedCutCells.Batch219.certificate2639], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches692 : ∀ c∈certificate692.cells, c.population=certificate692.population := by
  change ∀ c∈[MergedCutCells.Batch219.certificate2636,MergedCutCells.Batch219.certificate2637,MergedCutCells.Batch219.certificate2638,MergedCutCells.Batch219.certificate2639], c.population=PopulationCertificates.Batch023.certificate461
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers692 {x : ℝ} (hx : certificate692.interval.Contains x) : ∃ c∈certificate692.cells, c.region.interval.Contains x := rat_cut_group_covers certificate692 numericValid692 hx

def certificate693 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate462,PopulationCertificates.Batch023.certificate462,[MergedCutCells.Batch220.certificate2640,MergedCutCells.Batch220.certificate2641],(938423753571246267/1000000000000000000),(some (15405179/15625000)),(1/2),(1009336120442374431/500000000000000000),(some (596157739250991033/1000000000000000000)),(some (283423558185177187/1000000000000000000))⟩
theorem numericValid693 : certificate693.NumericValid := by decide +kernel
theorem cellsSound693 : ∀ c∈certificate693.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2640,MergedCutCells.Batch220.certificate2641], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2640,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2641,List.forall_mem_nil _⟩⟩
theorem cellsNumeric693 : ∀ c∈certificate693.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2640,MergedCutCells.Batch220.certificate2641], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2640,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2641,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid693 : ∀ c∈certificate693.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2640,MergedCutCells.Batch220.certificate2641], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid232,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid232,List.forall_mem_nil _⟩⟩
theorem populationMatches693 : ∀ c∈certificate693.cells, c.population=certificate693.population := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2640,MergedCutCells.Batch220.certificate2641], c.population=PopulationCertificates.Batch023.certificate462
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers693 {x : ℝ} (hx : certificate693.interval.Contains x) : ∃ c∈certificate693.cells, c.region.interval.Contains x := rat_cut_group_covers certificate693 numericValid693 hx

def certificate694 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate462,PopulationCertificates.Batch023.certificate462,[MergedCutCells.Batch220.certificate2642,MergedCutCells.Batch220.certificate2643,MergedCutCells.Batch220.certificate2644,MergedCutCells.Batch220.certificate2645,MergedCutCells.Batch220.certificate2646,MergedCutCells.Batch220.certificate2647],(15405179/15625000),none,(1/2),(75936557385295749/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid694 : certificate694.NumericValid := by decide +kernel
theorem cellsSound694 : ∀ c∈certificate694.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2642,MergedCutCells.Batch220.certificate2643,MergedCutCells.Batch220.certificate2644,MergedCutCells.Batch220.certificate2645,MergedCutCells.Batch220.certificate2646,MergedCutCells.Batch220.certificate2647], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2642,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2643,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2644,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2645,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2646,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2647,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric694 : ∀ c∈certificate694.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2642,MergedCutCells.Batch220.certificate2643,MergedCutCells.Batch220.certificate2644,MergedCutCells.Batch220.certificate2645,MergedCutCells.Batch220.certificate2646,MergedCutCells.Batch220.certificate2647], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2642,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2643,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2644,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2645,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2646,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2647,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid694 : ∀ c∈certificate694.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2642,MergedCutCells.Batch220.certificate2643,MergedCutCells.Batch220.certificate2644,MergedCutCells.Batch220.certificate2645,MergedCutCells.Batch220.certificate2646,MergedCutCells.Batch220.certificate2647], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches694 : ∀ c∈certificate694.cells, c.population=certificate694.population := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2642,MergedCutCells.Batch220.certificate2643,MergedCutCells.Batch220.certificate2644,MergedCutCells.Batch220.certificate2645,MergedCutCells.Batch220.certificate2646,MergedCutCells.Batch220.certificate2647], c.population=PopulationCertificates.Batch023.certificate462
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers694 {x : ℝ} (hx : certificate694.interval.Contains x) : ∃ c∈certificate694.cells, c.region.interval.Contains x := rat_cut_group_covers certificate694 numericValid694 hx

def certificate695 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate463,PopulationCertificates.Batch023.certificate463,[MergedCutCells.Batch220.certificate2648,MergedCutCells.Batch220.certificate2649,MergedCutCells.Batch220.certificate2650],(246285946343669653/50000000000000000),none,(1/2),(164561999410668013/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid695 : certificate695.NumericValid := by decide +kernel
theorem cellsSound695 : ∀ c∈certificate695.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2648,MergedCutCells.Batch220.certificate2649,MergedCutCells.Batch220.certificate2650], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2648,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2650,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric695 : ∀ c∈certificate695.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2648,MergedCutCells.Batch220.certificate2649,MergedCutCells.Batch220.certificate2650], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2648,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2650,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid695 : ∀ c∈certificate695.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2648,MergedCutCells.Batch220.certificate2649,MergedCutCells.Batch220.certificate2650], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches695 : ∀ c∈certificate695.cells, c.population=certificate695.population := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2648,MergedCutCells.Batch220.certificate2649,MergedCutCells.Batch220.certificate2650], c.population=PopulationCertificates.Batch023.certificate463
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers695 {x : ℝ} (hx : certificate695.interval.Contains x) : ∃ c∈certificate695.cells, c.region.interval.Contains x := rat_cut_group_covers certificate695 numericValid695 hx

end Cycle12.MergedCutGroups.Batch057
