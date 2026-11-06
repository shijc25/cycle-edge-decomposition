import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch024
import Cycle12.GeometryCertificates.Batch025
import Cycle12.MergedCutCells.Batch235
import Cycle12.MergedCutCells.Batch236
import Cycle12.MergedCutCells.Batch237
import Cycle12.PopulationCertificates.Batch024
import Cycle12.PopulationCertificates.Batch025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch062

def certificate744 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate496,PopulationCertificates.Batch024.certificate496,[MergedCutCells.Batch235.certificate2821,MergedCutCells.Batch235.certificate2822],(28763099350521389/50000000000000000),(some (51937059/40000000)),(1/2),(287895499841572011/1000000000000000000),(some (8670008587465423/500000000000000000)),(some (2477389439905857/1000000000000000000))⟩
theorem numericValid744 : certificate744.NumericValid := by decide +kernel
theorem cellsSound744 : ∀ c∈certificate744.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2821,MergedCutCells.Batch235.certificate2822], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2821,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2822,List.forall_mem_nil _⟩⟩
theorem cellsNumeric744 : ∀ c∈certificate744.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2821,MergedCutCells.Batch235.certificate2822], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2821,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2822,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid744 : ∀ c∈certificate744.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2821,MergedCutCells.Batch235.certificate2822], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid249,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid249,List.forall_mem_nil _⟩⟩
theorem populationMatches744 : ∀ c∈certificate744.cells, c.population=certificate744.population := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2821,MergedCutCells.Batch235.certificate2822], c.population=PopulationCertificates.Batch024.certificate496
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers744 {x : ℝ} (hx : certificate744.interval.Contains x) : ∃ c∈certificate744.cells, c.region.interval.Contains x := rat_cut_group_covers certificate744 numericValid744 hx

def certificate745 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate496,PopulationCertificates.Batch024.certificate496,[MergedCutCells.Batch235.certificate2823,MergedCutCells.Batch235.certificate2824,MergedCutCells.Batch235.certificate2825],(51937059/40000000),none,(1/2),(143606755777799739/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid745 : certificate745.NumericValid := by decide +kernel
theorem cellsSound745 : ∀ c∈certificate745.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2823,MergedCutCells.Batch235.certificate2824,MergedCutCells.Batch235.certificate2825], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2824,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2825,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric745 : ∀ c∈certificate745.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2823,MergedCutCells.Batch235.certificate2824,MergedCutCells.Batch235.certificate2825], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2824,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2825,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid745 : ∀ c∈certificate745.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2823,MergedCutCells.Batch235.certificate2824,MergedCutCells.Batch235.certificate2825], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches745 : ∀ c∈certificate745.cells, c.population=certificate745.population := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2823,MergedCutCells.Batch235.certificate2824,MergedCutCells.Batch235.certificate2825], c.population=PopulationCertificates.Batch024.certificate496
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers745 {x : ℝ} (hx : certificate745.interval.Contains x) : ∃ c∈certificate745.cells, c.region.interval.Contains x := rat_cut_group_covers certificate745 numericValid745 hx

def certificate746 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate497,PopulationCertificates.Batch024.certificate497,[MergedCutCells.Batch235.certificate2826,MergedCutCells.Batch235.certificate2827],(7712526219056567007/1000000000000000000),none,(1/2),(2747431751299337683/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid746 : certificate746.NumericValid := by decide +kernel
theorem cellsSound746 : ∀ c∈certificate746.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2826,MergedCutCells.Batch235.certificate2827], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2826,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2827,List.forall_mem_nil _⟩⟩
theorem cellsNumeric746 : ∀ c∈certificate746.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2826,MergedCutCells.Batch235.certificate2827], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2826,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2827,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid746 : ∀ c∈certificate746.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2826,MergedCutCells.Batch235.certificate2827], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches746 : ∀ c∈certificate746.cells, c.population=certificate746.population := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2826,MergedCutCells.Batch235.certificate2827], c.population=PopulationCertificates.Batch024.certificate497
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers746 {x : ℝ} (hx : certificate746.interval.Contains x) : ∃ c∈certificate746.cells, c.region.interval.Contains x := rat_cut_group_covers certificate746 numericValid746 hx

def certificate747 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate498,PopulationCertificates.Batch024.certificate498,[MergedCutCells.Batch235.certificate2828,MergedCutCells.Batch235.certificate2829],(575515969679582439/1000000000000000000),(some (51956027/40000000)),(1/2),(35095742082190889/125000000000000000),(some (5202102780610333/250000000000000000)),(some (766629854754553/250000000000000000))⟩
theorem numericValid747 : certificate747.NumericValid := by decide +kernel
theorem cellsSound747 : ∀ c∈certificate747.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2828,MergedCutCells.Batch235.certificate2829], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2828,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2829,List.forall_mem_nil _⟩⟩
theorem cellsNumeric747 : ∀ c∈certificate747.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2828,MergedCutCells.Batch235.certificate2829], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2828,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2829,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid747 : ∀ c∈certificate747.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2828,MergedCutCells.Batch235.certificate2829], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid250,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid250,List.forall_mem_nil _⟩⟩
theorem populationMatches747 : ∀ c∈certificate747.cells, c.population=certificate747.population := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2828,MergedCutCells.Batch235.certificate2829], c.population=PopulationCertificates.Batch024.certificate498
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers747 {x : ℝ} (hx : certificate747.interval.Contains x) : ∃ c∈certificate747.cells, c.region.interval.Contains x := rat_cut_group_covers certificate747 numericValid747 hx

def certificate748 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate498,PopulationCertificates.Batch024.certificate498,[MergedCutCells.Batch235.certificate2830,MergedCutCells.Batch235.certificate2831,MergedCutCells.Batch236.certificate2832],(51956027/40000000),none,(1/2),(139947729391034551/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid748 : certificate748.NumericValid := by decide +kernel
theorem cellsSound748 : ∀ c∈certificate748.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2830,MergedCutCells.Batch235.certificate2831,MergedCutCells.Batch236.certificate2832], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2830,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2831,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2832,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric748 : ∀ c∈certificate748.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2830,MergedCutCells.Batch235.certificate2831,MergedCutCells.Batch236.certificate2832], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2830,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2831,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2832,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid748 : ∀ c∈certificate748.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2830,MergedCutCells.Batch235.certificate2831,MergedCutCells.Batch236.certificate2832], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches748 : ∀ c∈certificate748.cells, c.population=certificate748.population := by
  change ∀ c∈[MergedCutCells.Batch235.certificate2830,MergedCutCells.Batch235.certificate2831,MergedCutCells.Batch236.certificate2832], c.population=PopulationCertificates.Batch024.certificate498
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers748 {x : ℝ} (hx : certificate748.interval.Contains x) : ∃ c∈certificate748.cells, c.region.interval.Contains x := rat_cut_group_covers certificate748 numericValid748 hx

def certificate749 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate499,PopulationCertificates.Batch024.certificate499,[MergedCutCells.Batch236.certificate2833,MergedCutCells.Batch236.certificate2834],(7732962793596426583/1000000000000000000),none,(1/2),(556612118276822741/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid749 : certificate749.NumericValid := by decide +kernel
theorem cellsSound749 : ∀ c∈certificate749.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2833,MergedCutCells.Batch236.certificate2834], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2833,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2834,List.forall_mem_nil _⟩⟩
theorem cellsNumeric749 : ∀ c∈certificate749.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2833,MergedCutCells.Batch236.certificate2834], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2833,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2834,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid749 : ∀ c∈certificate749.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2833,MergedCutCells.Batch236.certificate2834], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches749 : ∀ c∈certificate749.cells, c.population=certificate749.population := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2833,MergedCutCells.Batch236.certificate2834], c.population=PopulationCertificates.Batch024.certificate499
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers749 {x : ℝ} (hx : certificate749.interval.Contains x) : ∃ c∈certificate749.cells, c.region.interval.Contains x := rat_cut_group_covers certificate749 numericValid749 hx

def certificate750 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate500,PopulationCertificates.Batch025.certificate500,[MergedCutCells.Batch236.certificate2835,MergedCutCells.Batch236.certificate2836],(71990651625078479/125000000000000000),(some (1299664681/1000000000)),(1/2),(54722975445572003/200000000000000000),(some (24525784843268453/1000000000000000000)),(some (58133147710997/15625000000000000))⟩
theorem numericValid750 : certificate750.NumericValid := by decide +kernel
theorem cellsSound750 : ∀ c∈certificate750.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2835,MergedCutCells.Batch236.certificate2836], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2835,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2836,List.forall_mem_nil _⟩⟩
theorem cellsNumeric750 : ∀ c∈certificate750.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2835,MergedCutCells.Batch236.certificate2836], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2835,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2836,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid750 : ∀ c∈certificate750.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2835,MergedCutCells.Batch236.certificate2836], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid251,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid251,List.forall_mem_nil _⟩⟩
theorem populationMatches750 : ∀ c∈certificate750.cells, c.population=certificate750.population := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2835,MergedCutCells.Batch236.certificate2836], c.population=PopulationCertificates.Batch025.certificate500
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers750 {x : ℝ} (hx : certificate750.interval.Contains x) : ∃ c∈certificate750.cells, c.region.interval.Contains x := rat_cut_group_covers certificate750 numericValid750 hx

def certificate751 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate500,PopulationCertificates.Batch025.certificate500,[MergedCutCells.Batch236.certificate2837,MergedCutCells.Batch236.certificate2838,MergedCutCells.Batch236.certificate2839],(1299664681/1000000000),none,(1/2),(272538023289321739/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid751 : certificate751.NumericValid := by decide +kernel
theorem cellsSound751 : ∀ c∈certificate751.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2837,MergedCutCells.Batch236.certificate2838,MergedCutCells.Batch236.certificate2839], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2837,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2838,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2839,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric751 : ∀ c∈certificate751.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2837,MergedCutCells.Batch236.certificate2838,MergedCutCells.Batch236.certificate2839], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2837,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2838,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2839,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid751 : ∀ c∈certificate751.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2837,MergedCutCells.Batch236.certificate2838,MergedCutCells.Batch236.certificate2839], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches751 : ∀ c∈certificate751.cells, c.population=certificate751.population := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2837,MergedCutCells.Batch236.certificate2838,MergedCutCells.Batch236.certificate2839], c.population=PopulationCertificates.Batch025.certificate500
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers751 {x : ℝ} (hx : certificate751.interval.Contains x) : ∃ c∈certificate751.cells, c.region.interval.Contains x := rat_cut_group_covers certificate751 numericValid751 hx

def certificate752 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate501,PopulationCertificates.Batch025.certificate501,[MergedCutCells.Batch236.certificate2840,MergedCutCells.Batch236.certificate2841],(196741146112402689/25000000000000000),none,(1/2),(713487340665915393/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid752 : certificate752.NumericValid := by decide +kernel
theorem cellsSound752 : ∀ c∈certificate752.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2840,MergedCutCells.Batch236.certificate2841], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2840,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2841,List.forall_mem_nil _⟩⟩
theorem cellsNumeric752 : ∀ c∈certificate752.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2840,MergedCutCells.Batch236.certificate2841], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2840,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2841,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid752 : ∀ c∈certificate752.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2840,MergedCutCells.Batch236.certificate2841], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches752 : ∀ c∈certificate752.cells, c.population=certificate752.population := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2840,MergedCutCells.Batch236.certificate2841], c.population=PopulationCertificates.Batch025.certificate501
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers752 {x : ℝ} (hx : certificate752.interval.Contains x) : ∃ c∈certificate752.cells, c.region.interval.Contains x := rat_cut_group_covers certificate752 numericValid752 hx

def certificate753 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate502,PopulationCertificates.Batch025.certificate502,[MergedCutCells.Batch236.certificate2842,MergedCutCells.Batch236.certificate2843],(144581116767101131/250000000000000000),(some (31809969/25000000)),(1/2),(55956006803724521/200000000000000000),(some (26294543733054641/1000000000000000000)),(some (4039312357072789/1000000000000000000))⟩
theorem numericValid753 : certificate753.NumericValid := by decide +kernel
theorem cellsSound753 : ∀ c∈certificate753.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2842,MergedCutCells.Batch236.certificate2843], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2842,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.sound2843,List.forall_mem_nil _⟩⟩
theorem cellsNumeric753 : ∀ c∈certificate753.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2842,MergedCutCells.Batch236.certificate2843], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2842,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch236.numericValid2843,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid753 : ∀ c∈certificate753.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2842,MergedCutCells.Batch236.certificate2843], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid252,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid252,List.forall_mem_nil _⟩⟩
theorem populationMatches753 : ∀ c∈certificate753.cells, c.population=certificate753.population := by
  change ∀ c∈[MergedCutCells.Batch236.certificate2842,MergedCutCells.Batch236.certificate2843], c.population=PopulationCertificates.Batch025.certificate502
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers753 {x : ℝ} (hx : certificate753.interval.Contains x) : ∃ c∈certificate753.cells, c.region.interval.Contains x := rat_cut_group_covers certificate753 numericValid753 hx

def certificate754 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate502,PopulationCertificates.Batch025.certificate502,[MergedCutCells.Batch237.certificate2844,MergedCutCells.Batch237.certificate2845,MergedCutCells.Batch237.certificate2846],(31809969/25000000),none,(1/2),(278539729455472331/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid754 : certificate754.NumericValid := by decide +kernel
theorem cellsSound754 : ∀ c∈certificate754.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2844,MergedCutCells.Batch237.certificate2845,MergedCutCells.Batch237.certificate2846], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2844,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2845,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2846,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric754 : ∀ c∈certificate754.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2844,MergedCutCells.Batch237.certificate2845,MergedCutCells.Batch237.certificate2846], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2844,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2845,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2846,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid754 : ∀ c∈certificate754.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2844,MergedCutCells.Batch237.certificate2845,MergedCutCells.Batch237.certificate2846], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches754 : ∀ c∈certificate754.cells, c.population=certificate754.population := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2844,MergedCutCells.Batch237.certificate2845,MergedCutCells.Batch237.certificate2846], c.population=PopulationCertificates.Batch025.certificate502
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers754 {x : ℝ} (hx : certificate754.interval.Contains x) : ∃ c∈certificate754.cells, c.region.interval.Contains x := rat_cut_group_covers certificate754 numericValid754 hx

def certificate755 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate503,PopulationCertificates.Batch025.certificate503,[MergedCutCells.Batch237.certificate2847,MergedCutCells.Batch237.certificate2848],(79847643337581981/10000000000000000),none,(1/2),(732459116546208171/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid755 : certificate755.NumericValid := by decide +kernel
theorem cellsSound755 : ∀ c∈certificate755.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2847,MergedCutCells.Batch237.certificate2848], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2847,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2848,List.forall_mem_nil _⟩⟩
theorem cellsNumeric755 : ∀ c∈certificate755.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2847,MergedCutCells.Batch237.certificate2848], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2847,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2848,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid755 : ∀ c∈certificate755.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2847,MergedCutCells.Batch237.certificate2848], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches755 : ∀ c∈certificate755.cells, c.population=certificate755.population := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2847,MergedCutCells.Batch237.certificate2848], c.population=PopulationCertificates.Batch025.certificate503
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers755 {x : ℝ} (hx : certificate755.interval.Contains x) : ∃ c∈certificate755.cells, c.region.interval.Contains x := rat_cut_group_covers certificate755 numericValid755 hx

end Cycle12.MergedCutGroups.Batch062
