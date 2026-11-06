import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch026
import Cycle12.MergedCutCells.Batch244
import Cycle12.MergedCutCells.Batch245
import Cycle12.MergedCutCells.Batch246
import Cycle12.MergedCutCells.Batch247
import Cycle12.PopulationCertificates.Batch026

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch066

def certificate792 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate528,PopulationCertificates.Batch026.certificate528,[MergedCutCells.Batch244.certificate2938,MergedCutCells.Batch244.certificate2939],(193922055436933/320000000000000),(some (1208606823/1000000000)),(1/2),(257503189316098399/1000000000000000000),(some (89340598177105929/1000000000000000000)),(some (8898959667178359/500000000000000000))⟩
theorem numericValid792 : certificate792.NumericValid := by decide +kernel
theorem cellsSound792 : ∀ c∈certificate792.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2938,MergedCutCells.Batch244.certificate2939], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2938,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2939,List.forall_mem_nil _⟩⟩
theorem cellsNumeric792 : ∀ c∈certificate792.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2938,MergedCutCells.Batch244.certificate2939], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2938,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2939,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid792 : ∀ c∈certificate792.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2938,MergedCutCells.Batch244.certificate2939], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid265,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid265,List.forall_mem_nil _⟩⟩
theorem populationMatches792 : ∀ c∈certificate792.cells, c.population=certificate792.population := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2938,MergedCutCells.Batch244.certificate2939], c.population=PopulationCertificates.Batch026.certificate528
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers792 {x : ℝ} (hx : certificate792.interval.Contains x) : ∃ c∈certificate792.cells, c.region.interval.Contains x := rat_cut_group_covers certificate792 numericValid792 hx

def certificate793 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate528,PopulationCertificates.Batch026.certificate528,[MergedCutCells.Batch245.certificate2940,MergedCutCells.Batch245.certificate2941,MergedCutCells.Batch245.certificate2942,MergedCutCells.Batch245.certificate2943],(1208606823/1000000000),none,(1/2),(62928813024087421/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid793 : certificate793.NumericValid := by decide +kernel
theorem cellsSound793 : ∀ c∈certificate793.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2940,MergedCutCells.Batch245.certificate2941,MergedCutCells.Batch245.certificate2942,MergedCutCells.Batch245.certificate2943], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2940,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2941,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2942,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2943,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric793 : ∀ c∈certificate793.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2940,MergedCutCells.Batch245.certificate2941,MergedCutCells.Batch245.certificate2942,MergedCutCells.Batch245.certificate2943], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2940,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2941,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2942,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2943,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid793 : ∀ c∈certificate793.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2940,MergedCutCells.Batch245.certificate2941,MergedCutCells.Batch245.certificate2942,MergedCutCells.Batch245.certificate2943], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches793 : ∀ c∈certificate793.cells, c.population=certificate793.population := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2940,MergedCutCells.Batch245.certificate2941,MergedCutCells.Batch245.certificate2942,MergedCutCells.Batch245.certificate2943], c.population=PopulationCertificates.Batch026.certificate528
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers793 {x : ℝ} (hx : certificate793.interval.Contains x) : ∃ c∈certificate793.cells, c.region.interval.Contains x := rat_cut_group_covers certificate793 numericValid793 hx

def certificate794 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate529,PopulationCertificates.Batch026.certificate529,[MergedCutCells.Batch245.certificate2944,MergedCutCells.Batch245.certificate2945],(9004043892792520339/1000000000000000000),none,(1/2),(3717481723262553233/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid794 : certificate794.NumericValid := by decide +kernel
theorem cellsSound794 : ∀ c∈certificate794.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2944,MergedCutCells.Batch245.certificate2945], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2944,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2945,List.forall_mem_nil _⟩⟩
theorem cellsNumeric794 : ∀ c∈certificate794.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2944,MergedCutCells.Batch245.certificate2945], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2944,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2945,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid794 : ∀ c∈certificate794.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2944,MergedCutCells.Batch245.certificate2945], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches794 : ∀ c∈certificate794.cells, c.population=certificate794.population := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2944,MergedCutCells.Batch245.certificate2945], c.population=PopulationCertificates.Batch026.certificate529
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers794 {x : ℝ} (hx : certificate794.interval.Contains x) : ∃ c∈certificate794.cells, c.region.interval.Contains x := rat_cut_group_covers certificate794 numericValid794 hx

def certificate795 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate530,PopulationCertificates.Batch026.certificate530,[MergedCutCells.Batch245.certificate2946,MergedCutCells.Batch245.certificate2947],(122019474562668023/200000000000000000),(some (243110707/200000000)),(1/2),(262118291059016739/1000000000000000000),(some (47816566927120087/500000000000000000)),(some (9692147915489623/500000000000000000))⟩
theorem numericValid795 : certificate795.NumericValid := by decide +kernel
theorem cellsSound795 : ∀ c∈certificate795.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2946,MergedCutCells.Batch245.certificate2947], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2946,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2947,List.forall_mem_nil _⟩⟩
theorem cellsNumeric795 : ∀ c∈certificate795.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2946,MergedCutCells.Batch245.certificate2947], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2946,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2947,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid795 : ∀ c∈certificate795.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2946,MergedCutCells.Batch245.certificate2947], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid266,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid266,List.forall_mem_nil _⟩⟩
theorem populationMatches795 : ∀ c∈certificate795.cells, c.population=certificate795.population := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2946,MergedCutCells.Batch245.certificate2947], c.population=PopulationCertificates.Batch026.certificate530
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers795 {x : ℝ} (hx : certificate795.interval.Contains x) : ∃ c∈certificate795.cells, c.region.interval.Contains x := rat_cut_group_covers certificate795 numericValid795 hx

def certificate796 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate530,PopulationCertificates.Batch026.certificate530,[MergedCutCells.Batch245.certificate2948,MergedCutCells.Batch245.certificate2949,MergedCutCells.Batch245.certificate2950],(243110707/200000000),none,(1/2),(255531882700348283/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid796 : certificate796.NumericValid := by decide +kernel
theorem cellsSound796 : ∀ c∈certificate796.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2948,MergedCutCells.Batch245.certificate2949,MergedCutCells.Batch245.certificate2950], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2948,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2949,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2950,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric796 : ∀ c∈certificate796.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2948,MergedCutCells.Batch245.certificate2949,MergedCutCells.Batch245.certificate2950], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2948,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2949,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2950,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid796 : ∀ c∈certificate796.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2948,MergedCutCells.Batch245.certificate2949,MergedCutCells.Batch245.certificate2950], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches796 : ∀ c∈certificate796.cells, c.population=certificate796.population := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2948,MergedCutCells.Batch245.certificate2949,MergedCutCells.Batch245.certificate2950], c.population=PopulationCertificates.Batch026.certificate530
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers796 {x : ℝ} (hx : certificate796.interval.Contains x) : ∃ c∈certificate796.cells, c.region.interval.Contains x := rat_cut_group_covers certificate796 numericValid796 hx

def certificate797 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate531,PopulationCertificates.Batch026.certificate531,[MergedCutCells.Batch245.certificate2951,MergedCutCells.Batch246.certificate2952],(9013517942874777859/1000000000000000000),none,(1/2),(1885810330681385907/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid797 : certificate797.NumericValid := by decide +kernel
theorem cellsSound797 : ∀ c∈certificate797.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2951,MergedCutCells.Batch246.certificate2952], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.sound2951,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2952,List.forall_mem_nil _⟩⟩
theorem cellsNumeric797 : ∀ c∈certificate797.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2951,MergedCutCells.Batch246.certificate2952], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch245.numericValid2951,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2952,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid797 : ∀ c∈certificate797.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2951,MergedCutCells.Batch246.certificate2952], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches797 : ∀ c∈certificate797.cells, c.population=certificate797.population := by
  change ∀ c∈[MergedCutCells.Batch245.certificate2951,MergedCutCells.Batch246.certificate2952], c.population=PopulationCertificates.Batch026.certificate531
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers797 {x : ℝ} (hx : certificate797.interval.Contains x) : ∃ c∈certificate797.cells, c.region.interval.Contains x := rat_cut_group_covers certificate797 numericValid797 hx

def certificate798 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate532,PopulationCertificates.Batch026.certificate532,[MergedCutCells.Batch246.certificate2953,MergedCutCells.Batch246.certificate2954],(306943252720822777/500000000000000000),(some (596151899/500000000)),(1/2),(16663924396677237/62500000000000000),(some (101433299096755923/1000000000000000000)),(some (40775596252183/1953125000000000))⟩
theorem numericValid798 : certificate798.NumericValid := by decide +kernel
theorem cellsSound798 : ∀ c∈certificate798.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2953,MergedCutCells.Batch246.certificate2954], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2954,List.forall_mem_nil _⟩⟩
theorem cellsNumeric798 : ∀ c∈certificate798.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2953,MergedCutCells.Batch246.certificate2954], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2954,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid798 : ∀ c∈certificate798.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2953,MergedCutCells.Batch246.certificate2954], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid267,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid267,List.forall_mem_nil _⟩⟩
theorem populationMatches798 : ∀ c∈certificate798.cells, c.population=certificate798.population := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2953,MergedCutCells.Batch246.certificate2954], c.population=PopulationCertificates.Batch026.certificate532
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers798 {x : ℝ} (hx : certificate798.interval.Contains x) : ∃ c∈certificate798.cells, c.region.interval.Contains x := rat_cut_group_covers certificate798 numericValid798 hx

def certificate799 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate532,PopulationCertificates.Batch026.certificate532,[MergedCutCells.Batch246.certificate2955,MergedCutCells.Batch246.certificate2956,MergedCutCells.Batch246.certificate2957,MergedCutCells.Batch246.certificate2958],(596151899/500000000),none,(1/2),(64883716365255443/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid799 : certificate799.NumericValid := by decide +kernel
theorem cellsSound799 : ∀ c∈certificate799.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2955,MergedCutCells.Batch246.certificate2956,MergedCutCells.Batch246.certificate2957,MergedCutCells.Batch246.certificate2958], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2955,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2956,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2958,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric799 : ∀ c∈certificate799.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2955,MergedCutCells.Batch246.certificate2956,MergedCutCells.Batch246.certificate2957,MergedCutCells.Batch246.certificate2958], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2955,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2956,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2958,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid799 : ∀ c∈certificate799.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2955,MergedCutCells.Batch246.certificate2956,MergedCutCells.Batch246.certificate2957,MergedCutCells.Batch246.certificate2958], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches799 : ∀ c∈certificate799.cells, c.population=certificate799.population := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2955,MergedCutCells.Batch246.certificate2956,MergedCutCells.Batch246.certificate2957,MergedCutCells.Batch246.certificate2958], c.population=PopulationCertificates.Batch026.certificate532
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers799 {x : ℝ} (hx : certificate799.interval.Contains x) : ∃ c∈certificate799.cells, c.region.interval.Contains x := rat_cut_group_covers certificate799 numericValid799 hx

def certificate800 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate533,PopulationCertificates.Batch026.certificate533,[MergedCutCells.Batch246.certificate2959,MergedCutCells.Batch246.certificate2960],(914788242912512049/100000000000000000),none,(1/2),(96589650060790311/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid800 : certificate800.NumericValid := by decide +kernel
theorem cellsSound800 : ∀ c∈certificate800.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2959,MergedCutCells.Batch246.certificate2960], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2959,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2960,List.forall_mem_nil _⟩⟩
theorem cellsNumeric800 : ∀ c∈certificate800.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2959,MergedCutCells.Batch246.certificate2960], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2959,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2960,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid800 : ∀ c∈certificate800.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2959,MergedCutCells.Batch246.certificate2960], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches800 : ∀ c∈certificate800.cells, c.population=certificate800.population := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2959,MergedCutCells.Batch246.certificate2960], c.population=PopulationCertificates.Batch026.certificate533
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers800 {x : ℝ} (hx : certificate800.interval.Contains x) : ∃ c∈certificate800.cells, c.region.interval.Contains x := rat_cut_group_covers certificate800 numericValid800 hx

def certificate801 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate534,PopulationCertificates.Batch026.certificate534,[MergedCutCells.Batch246.certificate2961,MergedCutCells.Batch246.certificate2962],(618079479967919877/1000000000000000000),(some (240703331/200000000)),(1/2),(54246081505065581/200000000000000000),(some (21617904612593361/200000000000000000)),(some (11312910010429673/500000000000000000))⟩
theorem numericValid801 : certificate801.NumericValid := by decide +kernel
theorem cellsSound801 : ∀ c∈certificate801.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2961,MergedCutCells.Batch246.certificate2962], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2961,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2962,List.forall_mem_nil _⟩⟩
theorem cellsNumeric801 : ∀ c∈certificate801.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2961,MergedCutCells.Batch246.certificate2962], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2961,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2962,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid801 : ∀ c∈certificate801.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2961,MergedCutCells.Batch246.certificate2962], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid268,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid268,List.forall_mem_nil _⟩⟩
theorem populationMatches801 : ∀ c∈certificate801.cells, c.population=certificate801.population := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2961,MergedCutCells.Batch246.certificate2962], c.population=PopulationCertificates.Batch026.certificate534
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers801 {x : ℝ} (hx : certificate801.interval.Contains x) : ∃ c∈certificate801.cells, c.region.interval.Contains x := rat_cut_group_covers certificate801 numericValid801 hx

def certificate802 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate534,PopulationCertificates.Batch026.certificate534,[MergedCutCells.Batch246.certificate2963,MergedCutCells.Batch247.certificate2964,MergedCutCells.Batch247.certificate2965,MergedCutCells.Batch247.certificate2966],(240703331/200000000),none,(1/2),(32949967066585839/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid802 : certificate802.NumericValid := by decide +kernel
theorem cellsSound802 : ∀ c∈certificate802.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2963,MergedCutCells.Batch247.certificate2964,MergedCutCells.Batch247.certificate2965,MergedCutCells.Batch247.certificate2966], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.sound2963,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2965,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2966,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric802 : ∀ c∈certificate802.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2963,MergedCutCells.Batch247.certificate2964,MergedCutCells.Batch247.certificate2965,MergedCutCells.Batch247.certificate2966], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch246.numericValid2963,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2965,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2966,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid802 : ∀ c∈certificate802.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2963,MergedCutCells.Batch247.certificate2964,MergedCutCells.Batch247.certificate2965,MergedCutCells.Batch247.certificate2966], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches802 : ∀ c∈certificate802.cells, c.population=certificate802.population := by
  change ∀ c∈[MergedCutCells.Batch246.certificate2963,MergedCutCells.Batch247.certificate2964,MergedCutCells.Batch247.certificate2965,MergedCutCells.Batch247.certificate2966], c.population=PopulationCertificates.Batch026.certificate534
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers802 {x : ℝ} (hx : certificate802.interval.Contains x) : ∃ c∈certificate802.cells, c.region.interval.Contains x := rat_cut_group_covers certificate802 numericValid802 hx

def certificate803 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate535,PopulationCertificates.Batch026.certificate535,[MergedCutCells.Batch247.certificate2967,MergedCutCells.Batch247.certificate2968],(71575128691361747/7812500000000000),none,(1/2),(1960458575693069829/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid803 : certificate803.NumericValid := by decide +kernel
theorem cellsSound803 : ∀ c∈certificate803.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2967,MergedCutCells.Batch247.certificate2968], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2967,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.sound2968,List.forall_mem_nil _⟩⟩
theorem cellsNumeric803 : ∀ c∈certificate803.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2967,MergedCutCells.Batch247.certificate2968], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2967,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch247.numericValid2968,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid803 : ∀ c∈certificate803.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2967,MergedCutCells.Batch247.certificate2968], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches803 : ∀ c∈certificate803.cells, c.population=certificate803.population := by
  change ∀ c∈[MergedCutCells.Batch247.certificate2967,MergedCutCells.Batch247.certificate2968], c.population=PopulationCertificates.Batch026.certificate535
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers803 {x : ℝ} (hx : certificate803.interval.Contains x) : ∃ c∈certificate803.cells, c.region.interval.Contains x := rat_cut_group_covers certificate803 numericValid803 hx

end Cycle12.MergedCutGroups.Batch066
