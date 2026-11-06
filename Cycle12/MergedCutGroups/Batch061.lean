import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch024
import Cycle12.MergedCutCells.Batch232
import Cycle12.MergedCutCells.Batch233
import Cycle12.MergedCutCells.Batch234
import Cycle12.MergedCutCells.Batch235
import Cycle12.PopulationCertificates.Batch024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch061

def certificate732 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate488,PopulationCertificates.Batch024.certificate488,[MergedCutCells.Batch232.certificate2792,MergedCutCells.Batch232.certificate2793],(573725434029482697/1000000000000000000),(some (663966629/500000000)),(1/2),(149368509566735681/500000000000000000),(some (4304136058376497/500000000000000000)),(some (1102230101737683/1000000000000000000))⟩
theorem numericValid732 : certificate732.NumericValid := by decide +kernel
theorem cellsSound732 : ∀ c∈certificate732.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2792,MergedCutCells.Batch232.certificate2793], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2792,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2793,List.forall_mem_nil _⟩⟩
theorem cellsNumeric732 : ∀ c∈certificate732.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2792,MergedCutCells.Batch232.certificate2793], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2792,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2793,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid732 : ∀ c∈certificate732.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2792,MergedCutCells.Batch232.certificate2793], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid245,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid245,List.forall_mem_nil _⟩⟩
theorem populationMatches732 : ∀ c∈certificate732.cells, c.population=certificate732.population := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2792,MergedCutCells.Batch232.certificate2793], c.population=PopulationCertificates.Batch024.certificate488
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers732 {x : ℝ} (hx : certificate732.interval.Contains x) : ∃ c∈certificate732.cells, c.region.interval.Contains x := rat_cut_group_covers certificate732 numericValid732 hx

def certificate733 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate488,PopulationCertificates.Batch024.certificate488,[MergedCutCells.Batch232.certificate2794,MergedCutCells.Batch232.certificate2795,MergedCutCells.Batch233.certificate2796],(663966629/500000000),none,(1/2),(298733516827897969/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid733 : certificate733.NumericValid := by decide +kernel
theorem cellsSound733 : ∀ c∈certificate733.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2794,MergedCutCells.Batch232.certificate2795,MergedCutCells.Batch233.certificate2796], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2794,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2795,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2796,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric733 : ∀ c∈certificate733.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2794,MergedCutCells.Batch232.certificate2795,MergedCutCells.Batch233.certificate2796], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2794,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2795,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2796,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid733 : ∀ c∈certificate733.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2794,MergedCutCells.Batch232.certificate2795,MergedCutCells.Batch233.certificate2796], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches733 : ∀ c∈certificate733.cells, c.population=certificate733.population := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2794,MergedCutCells.Batch232.certificate2795,MergedCutCells.Batch233.certificate2796], c.population=PopulationCertificates.Batch024.certificate488
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers733 {x : ℝ} (hx : certificate733.interval.Contains x) : ∃ c∈certificate733.cells, c.region.interval.Contains x := rat_cut_group_covers certificate733 numericValid733 hx

def certificate734 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate489,PopulationCertificates.Batch024.certificate489,[MergedCutCells.Batch233.certificate2797,MergedCutCells.Batch233.certificate2798],(373364398994646671/50000000000000000),none,(1/2),(2579491872692688099/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid734 : certificate734.NumericValid := by decide +kernel
theorem cellsSound734 : ∀ c∈certificate734.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2797,MergedCutCells.Batch233.certificate2798], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2797,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2798,List.forall_mem_nil _⟩⟩
theorem cellsNumeric734 : ∀ c∈certificate734.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2797,MergedCutCells.Batch233.certificate2798], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2797,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2798,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid734 : ∀ c∈certificate734.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2797,MergedCutCells.Batch233.certificate2798], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches734 : ∀ c∈certificate734.cells, c.population=certificate734.population := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2797,MergedCutCells.Batch233.certificate2798], c.population=PopulationCertificates.Batch024.certificate489
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers734 {x : ℝ} (hx : certificate734.interval.Contains x) : ∃ c∈certificate734.cells, c.region.interval.Contains x := rat_cut_group_covers certificate734 numericValid734 hx

def certificate735 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate490,PopulationCertificates.Batch024.certificate490,[MergedCutCells.Batch233.certificate2799,MergedCutCells.Batch233.certificate2800],(7166373756065163/12500000000000000),(some (1294780597/1000000000)),(1/2),(36478463624042289/125000000000000000),(some (2798754646131327/250000000000000000)),(some (23299860089729/15625000000000000))⟩
theorem numericValid735 : certificate735.NumericValid := by decide +kernel
theorem cellsSound735 : ∀ c∈certificate735.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2799,MergedCutCells.Batch233.certificate2800], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2799,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2800,List.forall_mem_nil _⟩⟩
theorem cellsNumeric735 : ∀ c∈certificate735.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2799,MergedCutCells.Batch233.certificate2800], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2799,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2800,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid735 : ∀ c∈certificate735.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2799,MergedCutCells.Batch233.certificate2800], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid246,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid246,List.forall_mem_nil _⟩⟩
theorem populationMatches735 : ∀ c∈certificate735.cells, c.population=certificate735.population := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2799,MergedCutCells.Batch233.certificate2800], c.population=PopulationCertificates.Batch024.certificate490
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers735 {x : ℝ} (hx : certificate735.interval.Contains x) : ∃ c∈certificate735.cells, c.region.interval.Contains x := rat_cut_group_covers certificate735 numericValid735 hx

def certificate736 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate490,PopulationCertificates.Batch024.certificate490,[MergedCutCells.Batch233.certificate2801,MergedCutCells.Batch233.certificate2802,MergedCutCells.Batch233.certificate2803,MergedCutCells.Batch233.certificate2804],(1294780597/1000000000),none,(1/2),(145723436689641261/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid736 : certificate736.NumericValid := by decide +kernel
theorem cellsSound736 : ∀ c∈certificate736.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2801,MergedCutCells.Batch233.certificate2802,MergedCutCells.Batch233.certificate2803,MergedCutCells.Batch233.certificate2804], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2802,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2804,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric736 : ∀ c∈certificate736.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2801,MergedCutCells.Batch233.certificate2802,MergedCutCells.Batch233.certificate2803,MergedCutCells.Batch233.certificate2804], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2802,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2804,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid736 : ∀ c∈certificate736.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2801,MergedCutCells.Batch233.certificate2802,MergedCutCells.Batch233.certificate2803,MergedCutCells.Batch233.certificate2804], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches736 : ∀ c∈certificate736.cells, c.population=certificate736.population := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2801,MergedCutCells.Batch233.certificate2802,MergedCutCells.Batch233.certificate2803,MergedCutCells.Batch233.certificate2804], c.population=PopulationCertificates.Batch024.certificate490
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers736 {x : ℝ} (hx : certificate736.interval.Contains x) : ∃ c∈certificate736.cells, c.region.interval.Contains x := rat_cut_group_covers certificate736 numericValid736 hx

def certificate737 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate491,PopulationCertificates.Batch024.certificate491,[MergedCutCells.Batch233.certificate2805,MergedCutCells.Batch233.certificate2806],(7483537804844551507/1000000000000000000),none,(1/2),(2612211328663004351/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid737 : certificate737.NumericValid := by decide +kernel
theorem cellsSound737 : ∀ c∈certificate737.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2805,MergedCutCells.Batch233.certificate2806], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2806,List.forall_mem_nil _⟩⟩
theorem cellsNumeric737 : ∀ c∈certificate737.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2805,MergedCutCells.Batch233.certificate2806], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2806,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid737 : ∀ c∈certificate737.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2805,MergedCutCells.Batch233.certificate2806], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches737 : ∀ c∈certificate737.cells, c.population=certificate737.population := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2805,MergedCutCells.Batch233.certificate2806], c.population=PopulationCertificates.Batch024.certificate491
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers737 {x : ℝ} (hx : certificate737.interval.Contains x) : ∃ c∈certificate737.cells, c.region.interval.Contains x := rat_cut_group_covers certificate737 numericValid737 hx

def certificate738 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate492,PopulationCertificates.Batch024.certificate492,[MergedCutCells.Batch233.certificate2807,MergedCutCells.Batch234.certificate2808],(575442095817284289/1000000000000000000),(some (1298762753/1000000000)),(1/2),(297622172703322237/1000000000000000000),(some (6313610528208579/500000000000000000)),(some (171374126462503/100000000000000000))⟩
theorem numericValid738 : certificate738.NumericValid := by decide +kernel
theorem cellsSound738 : ∀ c∈certificate738.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2807,MergedCutCells.Batch234.certificate2808], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.sound2807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2808,List.forall_mem_nil _⟩⟩
theorem cellsNumeric738 : ∀ c∈certificate738.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2807,MergedCutCells.Batch234.certificate2808], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch233.numericValid2807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2808,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid738 : ∀ c∈certificate738.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2807,MergedCutCells.Batch234.certificate2808], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid247,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid247,List.forall_mem_nil _⟩⟩
theorem populationMatches738 : ∀ c∈certificate738.cells, c.population=certificate738.population := by
  change ∀ c∈[MergedCutCells.Batch233.certificate2807,MergedCutCells.Batch234.certificate2808], c.population=PopulationCertificates.Batch024.certificate492
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers738 {x : ℝ} (hx : certificate738.interval.Contains x) : ∃ c∈certificate738.cells, c.region.interval.Contains x := rat_cut_group_covers certificate738 numericValid738 hx

def certificate739 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate492,PopulationCertificates.Batch024.certificate492,[MergedCutCells.Batch234.certificate2809,MergedCutCells.Batch234.certificate2810,MergedCutCells.Batch234.certificate2811],(1298762753/1000000000),none,(1/2),(297175142266111937/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid739 : certificate739.NumericValid := by decide +kernel
theorem cellsSound739 : ∀ c∈certificate739.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2809,MergedCutCells.Batch234.certificate2810,MergedCutCells.Batch234.certificate2811], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2809,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2810,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2811,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric739 : ∀ c∈certificate739.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2809,MergedCutCells.Batch234.certificate2810,MergedCutCells.Batch234.certificate2811], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2809,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2810,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2811,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid739 : ∀ c∈certificate739.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2809,MergedCutCells.Batch234.certificate2810,MergedCutCells.Batch234.certificate2811], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches739 : ∀ c∈certificate739.cells, c.population=certificate739.population := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2809,MergedCutCells.Batch234.certificate2810,MergedCutCells.Batch234.certificate2811], c.population=PopulationCertificates.Batch024.certificate492
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers739 {x : ℝ} (hx : certificate739.interval.Contains x) : ∃ c∈certificate739.cells, c.region.interval.Contains x := rat_cut_group_covers certificate739 numericValid739 hx

def certificate740 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate493,PopulationCertificates.Batch024.certificate493,[MergedCutCells.Batch234.certificate2812,MergedCutCells.Batch234.certificate2813],(1897604479449345967/250000000000000000),none,(1/2),(2682510283208377117/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid740 : certificate740.NumericValid := by decide +kernel
theorem cellsSound740 : ∀ c∈certificate740.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2812,MergedCutCells.Batch234.certificate2813], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2812,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2813,List.forall_mem_nil _⟩⟩
theorem cellsNumeric740 : ∀ c∈certificate740.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2812,MergedCutCells.Batch234.certificate2813], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2812,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2813,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid740 : ∀ c∈certificate740.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2812,MergedCutCells.Batch234.certificate2813], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches740 : ∀ c∈certificate740.cells, c.population=certificate740.population := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2812,MergedCutCells.Batch234.certificate2813], c.population=PopulationCertificates.Batch024.certificate493
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers740 {x : ℝ} (hx : certificate740.interval.Contains x) : ∃ c∈certificate740.cells, c.region.interval.Contains x := rat_cut_group_covers certificate740 numericValid740 hx

def certificate741 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate494,PopulationCertificates.Batch024.certificate494,[MergedCutCells.Batch234.certificate2814,MergedCutCells.Batch234.certificate2815],(143852649322824329/250000000000000000),(some (1298703943/1000000000)),(1/2),(294066626780795307/1000000000000000000),(some (3532453067359681/250000000000000000)),(some (488055489124853/250000000000000000))⟩
theorem numericValid741 : certificate741.NumericValid := by decide +kernel
theorem cellsSound741 : ∀ c∈certificate741.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2814,MergedCutCells.Batch234.certificate2815], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2814,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2815,List.forall_mem_nil _⟩⟩
theorem cellsNumeric741 : ∀ c∈certificate741.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2814,MergedCutCells.Batch234.certificate2815], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2814,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2815,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid741 : ∀ c∈certificate741.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2814,MergedCutCells.Batch234.certificate2815], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid248,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid248,List.forall_mem_nil _⟩⟩
theorem populationMatches741 : ∀ c∈certificate741.cells, c.population=certificate741.population := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2814,MergedCutCells.Batch234.certificate2815], c.population=PopulationCertificates.Batch024.certificate494
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers741 {x : ℝ} (hx : certificate741.interval.Contains x) : ∃ c∈certificate741.cells, c.region.interval.Contains x := rat_cut_group_covers certificate741 numericValid741 hx

def certificate742 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate494,PopulationCertificates.Batch024.certificate494,[MergedCutCells.Batch234.certificate2816,MergedCutCells.Batch234.certificate2817,MergedCutCells.Batch234.certificate2818],(1298703943/1000000000),none,(1/2),(293546872694401229/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid742 : certificate742.NumericValid := by decide +kernel
theorem cellsSound742 : ∀ c∈certificate742.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2816,MergedCutCells.Batch234.certificate2817,MergedCutCells.Batch234.certificate2818], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2817,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2818,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric742 : ∀ c∈certificate742.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2816,MergedCutCells.Batch234.certificate2817,MergedCutCells.Batch234.certificate2818], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2817,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2818,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid742 : ∀ c∈certificate742.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2816,MergedCutCells.Batch234.certificate2817,MergedCutCells.Batch234.certificate2818], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches742 : ∀ c∈certificate742.cells, c.population=certificate742.population := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2816,MergedCutCells.Batch234.certificate2817,MergedCutCells.Batch234.certificate2818], c.population=PopulationCertificates.Batch024.certificate494
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers742 {x : ℝ} (hx : certificate742.interval.Contains x) : ∃ c∈certificate742.cells, c.region.interval.Contains x := rat_cut_group_covers certificate742 numericValid742 hx

def certificate743 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate495,PopulationCertificates.Batch024.certificate495,[MergedCutCells.Batch234.certificate2819,MergedCutCells.Batch235.certificate2820],(7656546719584410081/1000000000000000000),none,(1/2),(2716757898335872933/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid743 : certificate743.NumericValid := by decide +kernel
theorem cellsSound743 : ∀ c∈certificate743.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2819,MergedCutCells.Batch235.certificate2820], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.sound2819,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.sound2820,List.forall_mem_nil _⟩⟩
theorem cellsNumeric743 : ∀ c∈certificate743.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2819,MergedCutCells.Batch235.certificate2820], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch234.numericValid2819,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch235.numericValid2820,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid743 : ∀ c∈certificate743.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2819,MergedCutCells.Batch235.certificate2820], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches743 : ∀ c∈certificate743.cells, c.population=certificate743.population := by
  change ∀ c∈[MergedCutCells.Batch234.certificate2819,MergedCutCells.Batch235.certificate2820], c.population=PopulationCertificates.Batch024.certificate495
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers743 {x : ℝ} (hx : certificate743.interval.Contains x) : ∃ c∈certificate743.cells, c.region.interval.Contains x := rat_cut_group_covers certificate743 numericValid743 hx

end Cycle12.MergedCutGroups.Batch061
