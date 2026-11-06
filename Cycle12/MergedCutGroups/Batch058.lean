import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch023
import Cycle12.MergedCutCells.Batch220
import Cycle12.MergedCutCells.Batch221
import Cycle12.MergedCutCells.Batch222
import Cycle12.MergedCutCells.Batch223
import Cycle12.MergedCutCells.Batch224
import Cycle12.MergedCutCells.Batch225
import Cycle12.PopulationCertificates.Batch023

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch058

def certificate696 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate464,PopulationCertificates.Batch023.certificate464,[MergedCutCells.Batch220.certificate2651,MergedCutCells.Batch221.certificate2652],(465065309481134747/500000000000000000),(some (977038781/1000000000)),(1/2),(399593315782519381/200000000000000000),(some (601965319114221827/1000000000000000000)),(some (289791979338231029/1000000000000000000))⟩
theorem numericValid696 : certificate696.NumericValid := by decide +kernel
theorem cellsSound696 : ∀ c∈certificate696.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2651,MergedCutCells.Batch221.certificate2652], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.sound2651,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2652,List.forall_mem_nil _⟩⟩
theorem cellsNumeric696 : ∀ c∈certificate696.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2651,MergedCutCells.Batch221.certificate2652], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch220.numericValid2651,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2652,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid696 : ∀ c∈certificate696.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2651,MergedCutCells.Batch221.certificate2652], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid233,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid233,List.forall_mem_nil _⟩⟩
theorem populationMatches696 : ∀ c∈certificate696.cells, c.population=certificate696.population := by
  change ∀ c∈[MergedCutCells.Batch220.certificate2651,MergedCutCells.Batch221.certificate2652], c.population=PopulationCertificates.Batch023.certificate464
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers696 {x : ℝ} (hx : certificate696.interval.Contains x) : ∃ c∈certificate696.cells, c.region.interval.Contains x := rat_cut_group_covers certificate696 numericValid696 hx

def certificate697 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate464,PopulationCertificates.Batch023.certificate464,[MergedCutCells.Batch221.certificate2653,MergedCutCells.Batch221.certificate2654,MergedCutCells.Batch221.certificate2655,MergedCutCells.Batch221.certificate2656,MergedCutCells.Batch221.certificate2657,MergedCutCells.Batch221.certificate2658,MergedCutCells.Batch221.certificate2659],(977038781/1000000000),none,(1/2),(243141158934212979/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid697 : certificate697.NumericValid := by decide +kernel
theorem cellsSound697 : ∀ c∈certificate697.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch221.certificate2653,MergedCutCells.Batch221.certificate2654,MergedCutCells.Batch221.certificate2655,MergedCutCells.Batch221.certificate2656,MergedCutCells.Batch221.certificate2657,MergedCutCells.Batch221.certificate2658,MergedCutCells.Batch221.certificate2659], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2653,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2654,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2655,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2656,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2657,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2658,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2659,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric697 : ∀ c∈certificate697.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch221.certificate2653,MergedCutCells.Batch221.certificate2654,MergedCutCells.Batch221.certificate2655,MergedCutCells.Batch221.certificate2656,MergedCutCells.Batch221.certificate2657,MergedCutCells.Batch221.certificate2658,MergedCutCells.Batch221.certificate2659], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2653,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2654,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2655,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2656,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2657,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2658,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2659,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid697 : ∀ c∈certificate697.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch221.certificate2653,MergedCutCells.Batch221.certificate2654,MergedCutCells.Batch221.certificate2655,MergedCutCells.Batch221.certificate2656,MergedCutCells.Batch221.certificate2657,MergedCutCells.Batch221.certificate2658,MergedCutCells.Batch221.certificate2659], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches697 : ∀ c∈certificate697.cells, c.population=certificate697.population := by
  change ∀ c∈[MergedCutCells.Batch221.certificate2653,MergedCutCells.Batch221.certificate2654,MergedCutCells.Batch221.certificate2655,MergedCutCells.Batch221.certificate2656,MergedCutCells.Batch221.certificate2657,MergedCutCells.Batch221.certificate2658,MergedCutCells.Batch221.certificate2659], c.population=PopulationCertificates.Batch023.certificate464
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers697 {x : ℝ} (hx : certificate697.interval.Contains x) : ∃ c∈certificate697.cells, c.region.interval.Contains x := rat_cut_group_covers certificate697 numericValid697 hx

def certificate698 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate465,PopulationCertificates.Batch023.certificate465,[MergedCutCells.Batch221.certificate2660,MergedCutCells.Batch221.certificate2661,MergedCutCells.Batch221.certificate2662,MergedCutCells.Batch221.certificate2663],(2471602881882526267/500000000000000000),none,(1/2),(2094777195983844229/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid698 : certificate698.NumericValid := by decide +kernel
theorem cellsSound698 : ∀ c∈certificate698.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch221.certificate2660,MergedCutCells.Batch221.certificate2661,MergedCutCells.Batch221.certificate2662,MergedCutCells.Batch221.certificate2663], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2660,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2662,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.sound2663,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric698 : ∀ c∈certificate698.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch221.certificate2660,MergedCutCells.Batch221.certificate2661,MergedCutCells.Batch221.certificate2662,MergedCutCells.Batch221.certificate2663], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2660,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2662,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch221.numericValid2663,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid698 : ∀ c∈certificate698.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch221.certificate2660,MergedCutCells.Batch221.certificate2661,MergedCutCells.Batch221.certificate2662,MergedCutCells.Batch221.certificate2663], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches698 : ∀ c∈certificate698.cells, c.population=certificate698.population := by
  change ∀ c∈[MergedCutCells.Batch221.certificate2660,MergedCutCells.Batch221.certificate2661,MergedCutCells.Batch221.certificate2662,MergedCutCells.Batch221.certificate2663], c.population=PopulationCertificates.Batch023.certificate465
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers698 {x : ℝ} (hx : certificate698.interval.Contains x) : ∃ c∈certificate698.cells, c.region.interval.Contains x := rat_cut_group_covers certificate698 numericValid698 hx

def certificate699 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate466,PopulationCertificates.Batch023.certificate466,[MergedCutCells.Batch222.certificate2664,MergedCutCells.Batch222.certificate2665],(234605938420448259/250000000000000000),(some (246412103/250000000)),(1/2),(418950167531625771/200000000000000000),(some (605449512712511133/1000000000000000000)),(some (146860297374126651/500000000000000000))⟩
theorem numericValid699 : certificate699.NumericValid := by decide +kernel
theorem cellsSound699 : ∀ c∈certificate699.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2664,MergedCutCells.Batch222.certificate2665], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2664,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2665,List.forall_mem_nil _⟩⟩
theorem cellsNumeric699 : ∀ c∈certificate699.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2664,MergedCutCells.Batch222.certificate2665], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2664,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2665,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid699 : ∀ c∈certificate699.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2664,MergedCutCells.Batch222.certificate2665], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid234,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid234,List.forall_mem_nil _⟩⟩
theorem populationMatches699 : ∀ c∈certificate699.cells, c.population=certificate699.population := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2664,MergedCutCells.Batch222.certificate2665], c.population=PopulationCertificates.Batch023.certificate466
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers699 {x : ℝ} (hx : certificate699.interval.Contains x) : ∃ c∈certificate699.cells, c.region.interval.Contains x := rat_cut_group_covers certificate699 numericValid699 hx

def certificate700 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate466,PopulationCertificates.Batch023.certificate466,[MergedCutCells.Batch222.certificate2666,MergedCutCells.Batch222.certificate2667,MergedCutCells.Batch222.certificate2668,MergedCutCells.Batch222.certificate2669,MergedCutCells.Batch222.certificate2670,MergedCutCells.Batch222.certificate2671,MergedCutCells.Batch222.certificate2672],(246412103/250000000),none,(1/2),(2016494098988323903/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid700 : certificate700.NumericValid := by decide +kernel
theorem cellsSound700 : ∀ c∈certificate700.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2666,MergedCutCells.Batch222.certificate2667,MergedCutCells.Batch222.certificate2668,MergedCutCells.Batch222.certificate2669,MergedCutCells.Batch222.certificate2670,MergedCutCells.Batch222.certificate2671,MergedCutCells.Batch222.certificate2672], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2666,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2667,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2668,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2669,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2671,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2672,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric700 : ∀ c∈certificate700.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2666,MergedCutCells.Batch222.certificate2667,MergedCutCells.Batch222.certificate2668,MergedCutCells.Batch222.certificate2669,MergedCutCells.Batch222.certificate2670,MergedCutCells.Batch222.certificate2671,MergedCutCells.Batch222.certificate2672], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2666,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2667,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2668,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2669,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2671,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2672,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid700 : ∀ c∈certificate700.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2666,MergedCutCells.Batch222.certificate2667,MergedCutCells.Batch222.certificate2668,MergedCutCells.Batch222.certificate2669,MergedCutCells.Batch222.certificate2670,MergedCutCells.Batch222.certificate2671,MergedCutCells.Batch222.certificate2672], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches700 : ∀ c∈certificate700.cells, c.population=certificate700.population := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2666,MergedCutCells.Batch222.certificate2667,MergedCutCells.Batch222.certificate2668,MergedCutCells.Batch222.certificate2669,MergedCutCells.Batch222.certificate2670,MergedCutCells.Batch222.certificate2671,MergedCutCells.Batch222.certificate2672], c.population=PopulationCertificates.Batch023.certificate466
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers700 {x : ℝ} (hx : certificate700.interval.Contains x) : ∃ c∈certificate700.cells, c.region.interval.Contains x := rat_cut_group_covers certificate700 numericValid700 hx

def certificate701 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate467,PopulationCertificates.Batch023.certificate467,[MergedCutCells.Batch222.certificate2673,MergedCutCells.Batch222.certificate2674,MergedCutCells.Batch222.certificate2675],(986764932678296411/200000000000000000),none,(1/2),(852626341504678291/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid701 : certificate701.NumericValid := by decide +kernel
theorem cellsSound701 : ∀ c∈certificate701.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2673,MergedCutCells.Batch222.certificate2674,MergedCutCells.Batch222.certificate2675], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2673,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.sound2675,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric701 : ∀ c∈certificate701.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2673,MergedCutCells.Batch222.certificate2674,MergedCutCells.Batch222.certificate2675], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2673,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch222.numericValid2675,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid701 : ∀ c∈certificate701.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2673,MergedCutCells.Batch222.certificate2674,MergedCutCells.Batch222.certificate2675], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches701 : ∀ c∈certificate701.cells, c.population=certificate701.population := by
  change ∀ c∈[MergedCutCells.Batch222.certificate2673,MergedCutCells.Batch222.certificate2674,MergedCutCells.Batch222.certificate2675], c.population=PopulationCertificates.Batch023.certificate467
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers701 {x : ℝ} (hx : certificate701.interval.Contains x) : ∃ c∈certificate701.cells, c.region.interval.Contains x := rat_cut_group_covers certificate701 numericValid701 hx

def certificate702 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate468,PopulationCertificates.Batch023.certificate468,[MergedCutCells.Batch223.certificate2676,MergedCutCells.Batch223.certificate2677],(236891698438400437/250000000000000000),(some (485600447/500000000)),(1/2),(1100681998141205879/500000000000000000),(some (121528502312434639/200000000000000000)),(some (74059361890696991/250000000000000000))⟩
theorem numericValid702 : certificate702.NumericValid := by decide +kernel
theorem cellsSound702 : ∀ c∈certificate702.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2676,MergedCutCells.Batch223.certificate2677], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2676,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2677,List.forall_mem_nil _⟩⟩
theorem cellsNumeric702 : ∀ c∈certificate702.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2676,MergedCutCells.Batch223.certificate2677], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2676,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2677,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid702 : ∀ c∈certificate702.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2676,MergedCutCells.Batch223.certificate2677], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid235,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid235,List.forall_mem_nil _⟩⟩
theorem populationMatches702 : ∀ c∈certificate702.cells, c.population=certificate702.population := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2676,MergedCutCells.Batch223.certificate2677], c.population=PopulationCertificates.Batch023.certificate468
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers702 {x : ℝ} (hx : certificate702.interval.Contains x) : ∃ c∈certificate702.cells, c.region.interval.Contains x := rat_cut_group_covers certificate702 numericValid702 hx

def certificate703 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate468,PopulationCertificates.Batch023.certificate468,[MergedCutCells.Batch223.certificate2678,MergedCutCells.Batch223.certificate2679,MergedCutCells.Batch223.certificate2680,MergedCutCells.Batch223.certificate2681,MergedCutCells.Batch223.certificate2682,MergedCutCells.Batch223.certificate2683,MergedCutCells.Batch223.certificate2684,MergedCutCells.Batch223.certificate2685],(485600447/500000000),none,(1/2),(130390709178554199/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid703 : certificate703.NumericValid := by decide +kernel
theorem cellsSound703 : ∀ c∈certificate703.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2678,MergedCutCells.Batch223.certificate2679,MergedCutCells.Batch223.certificate2680,MergedCutCells.Batch223.certificate2681,MergedCutCells.Batch223.certificate2682,MergedCutCells.Batch223.certificate2683,MergedCutCells.Batch223.certificate2684,MergedCutCells.Batch223.certificate2685], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2678,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2680,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2681,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2683,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2684,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2685,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric703 : ∀ c∈certificate703.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2678,MergedCutCells.Batch223.certificate2679,MergedCutCells.Batch223.certificate2680,MergedCutCells.Batch223.certificate2681,MergedCutCells.Batch223.certificate2682,MergedCutCells.Batch223.certificate2683,MergedCutCells.Batch223.certificate2684,MergedCutCells.Batch223.certificate2685], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2678,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2680,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2681,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2683,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2684,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2685,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid703 : ∀ c∈certificate703.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2678,MergedCutCells.Batch223.certificate2679,MergedCutCells.Batch223.certificate2680,MergedCutCells.Batch223.certificate2681,MergedCutCells.Batch223.certificate2682,MergedCutCells.Batch223.certificate2683,MergedCutCells.Batch223.certificate2684,MergedCutCells.Batch223.certificate2685], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches703 : ∀ c∈certificate703.cells, c.population=certificate703.population := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2678,MergedCutCells.Batch223.certificate2679,MergedCutCells.Batch223.certificate2680,MergedCutCells.Batch223.certificate2681,MergedCutCells.Batch223.certificate2682,MergedCutCells.Batch223.certificate2683,MergedCutCells.Batch223.certificate2684,MergedCutCells.Batch223.certificate2685], c.population=PopulationCertificates.Batch023.certificate468
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers703 {x : ℝ} (hx : certificate703.interval.Contains x) : ∃ c∈certificate703.cells, c.region.interval.Contains x := rat_cut_group_covers certificate703 numericValid703 hx

def certificate704 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate469,PopulationCertificates.Batch023.certificate469,[MergedCutCells.Batch223.certificate2686,MergedCutCells.Batch223.certificate2687,MergedCutCells.Batch224.certificate2688],(2425190680841736369/500000000000000000),none,(1/2),(4256193740970769467/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid704 : certificate704.NumericValid := by decide +kernel
theorem cellsSound704 : ∀ c∈certificate704.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2686,MergedCutCells.Batch223.certificate2687,MergedCutCells.Batch224.certificate2688], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2686,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.sound2687,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2688,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric704 : ∀ c∈certificate704.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2686,MergedCutCells.Batch223.certificate2687,MergedCutCells.Batch224.certificate2688], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2686,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch223.numericValid2687,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2688,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid704 : ∀ c∈certificate704.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2686,MergedCutCells.Batch223.certificate2687,MergedCutCells.Batch224.certificate2688], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches704 : ∀ c∈certificate704.cells, c.population=certificate704.population := by
  change ∀ c∈[MergedCutCells.Batch223.certificate2686,MergedCutCells.Batch223.certificate2687,MergedCutCells.Batch224.certificate2688], c.population=PopulationCertificates.Batch023.certificate469
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers704 {x : ℝ} (hx : certificate704.interval.Contains x) : ∃ c∈certificate704.cells, c.region.interval.Contains x := rat_cut_group_covers certificate704 numericValid704 hx

def certificate705 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate470,PopulationCertificates.Batch023.certificate470,[MergedCutCells.Batch224.certificate2689,MergedCutCells.Batch224.certificate2690],(938423752688354811/1000000000000000000),(some (15405179/15625000)),(1/2),(2174809072759341133/1000000000000000000),(some (615637709450304737/1000000000000000000)),(some (305725468467787949/1000000000000000000))⟩
theorem numericValid705 : certificate705.NumericValid := by decide +kernel
theorem cellsSound705 : ∀ c∈certificate705.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2689,MergedCutCells.Batch224.certificate2690], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2689,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2690,List.forall_mem_nil _⟩⟩
theorem cellsNumeric705 : ∀ c∈certificate705.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2689,MergedCutCells.Batch224.certificate2690], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2689,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2690,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid705 : ∀ c∈certificate705.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2689,MergedCutCells.Batch224.certificate2690], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid236,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid236,List.forall_mem_nil _⟩⟩
theorem populationMatches705 : ∀ c∈certificate705.cells, c.population=certificate705.population := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2689,MergedCutCells.Batch224.certificate2690], c.population=PopulationCertificates.Batch023.certificate470
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers705 {x : ℝ} (hx : certificate705.interval.Contains x) : ∃ c∈certificate705.cells, c.region.interval.Contains x := rat_cut_group_covers certificate705 numericValid705 hx

def certificate706 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate470,PopulationCertificates.Batch023.certificate470,[MergedCutCells.Batch224.certificate2691,MergedCutCells.Batch224.certificate2692,MergedCutCells.Batch224.certificate2693,MergedCutCells.Batch224.certificate2694,MergedCutCells.Batch224.certificate2695,MergedCutCells.Batch224.certificate2696,MergedCutCells.Batch224.certificate2697],(15405179/15625000),none,(1/2),(133497134908085687/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid706 : certificate706.NumericValid := by decide +kernel
theorem cellsSound706 : ∀ c∈certificate706.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2691,MergedCutCells.Batch224.certificate2692,MergedCutCells.Batch224.certificate2693,MergedCutCells.Batch224.certificate2694,MergedCutCells.Batch224.certificate2695,MergedCutCells.Batch224.certificate2696,MergedCutCells.Batch224.certificate2697], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2691,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2692,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2693,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2694,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2695,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2697,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric706 : ∀ c∈certificate706.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2691,MergedCutCells.Batch224.certificate2692,MergedCutCells.Batch224.certificate2693,MergedCutCells.Batch224.certificate2694,MergedCutCells.Batch224.certificate2695,MergedCutCells.Batch224.certificate2696,MergedCutCells.Batch224.certificate2697], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2691,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2692,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2693,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2694,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2695,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2697,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid706 : ∀ c∈certificate706.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2691,MergedCutCells.Batch224.certificate2692,MergedCutCells.Batch224.certificate2693,MergedCutCells.Batch224.certificate2694,MergedCutCells.Batch224.certificate2695,MergedCutCells.Batch224.certificate2696,MergedCutCells.Batch224.certificate2697], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches706 : ∀ c∈certificate706.cells, c.population=certificate706.population := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2691,MergedCutCells.Batch224.certificate2692,MergedCutCells.Batch224.certificate2693,MergedCutCells.Batch224.certificate2694,MergedCutCells.Batch224.certificate2695,MergedCutCells.Batch224.certificate2696,MergedCutCells.Batch224.certificate2697], c.population=PopulationCertificates.Batch023.certificate470
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers706 {x : ℝ} (hx : certificate706.interval.Contains x) : ∃ c∈certificate706.cells, c.region.interval.Contains x := rat_cut_group_covers certificate706 numericValid706 hx

def certificate707 : RatCutGroup := ⟨GeometryCertificates.Batch023.certificate471,PopulationCertificates.Batch023.certificate471,[MergedCutCells.Batch224.certificate2698,MergedCutCells.Batch224.certificate2699,MergedCutCells.Batch225.certificate2700,MergedCutCells.Batch225.certificate2701],(1216966159540410207/250000000000000000),none,(1/2),(216855135019935663/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid707 : certificate707.NumericValid := by decide +kernel
theorem cellsSound707 : ∀ c∈certificate707.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2698,MergedCutCells.Batch224.certificate2699,MergedCutCells.Batch225.certificate2700,MergedCutCells.Batch225.certificate2701], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.sound2699,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2700,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.sound2701,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric707 : ∀ c∈certificate707.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2698,MergedCutCells.Batch224.certificate2699,MergedCutCells.Batch225.certificate2700,MergedCutCells.Batch225.certificate2701], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch224.numericValid2699,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2700,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch225.numericValid2701,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid707 : ∀ c∈certificate707.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2698,MergedCutCells.Batch224.certificate2699,MergedCutCells.Batch225.certificate2700,MergedCutCells.Batch225.certificate2701], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches707 : ∀ c∈certificate707.cells, c.population=certificate707.population := by
  change ∀ c∈[MergedCutCells.Batch224.certificate2698,MergedCutCells.Batch224.certificate2699,MergedCutCells.Batch225.certificate2700,MergedCutCells.Batch225.certificate2701], c.population=PopulationCertificates.Batch023.certificate471
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers707 {x : ℝ} (hx : certificate707.interval.Contains x) : ∃ c∈certificate707.cells, c.region.interval.Contains x := rat_cut_group_covers certificate707 numericValid707 hx

end Cycle12.MergedCutGroups.Batch058
