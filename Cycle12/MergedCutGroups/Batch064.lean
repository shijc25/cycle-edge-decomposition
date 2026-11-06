import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch025
import Cycle12.MergedCutCells.Batch239
import Cycle12.MergedCutCells.Batch240
import Cycle12.MergedCutCells.Batch241
import Cycle12.MergedCutCells.Batch242
import Cycle12.PopulationCertificates.Batch025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch064

def certificate768 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate512,PopulationCertificates.Batch025.certificate512,[MergedCutCells.Batch239.certificate2878,MergedCutCells.Batch239.certificate2879],(291992074339249059/500000000000000000),(some (1251597399/1000000000)),(1/2),(51845140602084911/200000000000000000),(some (4593600505567587/100000000000000000)),(some (786365087049287/100000000000000000))⟩
theorem numericValid768 : certificate768.NumericValid := by decide +kernel
theorem cellsSound768 : ∀ c∈certificate768.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2878,MergedCutCells.Batch239.certificate2879], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2879,List.forall_mem_nil _⟩⟩
theorem cellsNumeric768 : ∀ c∈certificate768.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2878,MergedCutCells.Batch239.certificate2879], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2879,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid768 : ∀ c∈certificate768.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2878,MergedCutCells.Batch239.certificate2879], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid257,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid257,List.forall_mem_nil _⟩⟩
theorem populationMatches768 : ∀ c∈certificate768.cells, c.population=certificate768.population := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2878,MergedCutCells.Batch239.certificate2879], c.population=PopulationCertificates.Batch025.certificate512
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers768 {x : ℝ} (hx : certificate768.interval.Contains x) : ∃ c∈certificate768.cells, c.region.interval.Contains x := rat_cut_group_covers certificate768 numericValid768 hx

def certificate769 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate512,PopulationCertificates.Batch025.certificate512,[MergedCutCells.Batch240.certificate2880,MergedCutCells.Batch240.certificate2881,MergedCutCells.Batch240.certificate2882],(1251597399/1000000000),none,(1/2),(5133829568641977/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid769 : certificate769.NumericValid := by decide +kernel
theorem cellsSound769 : ∀ c∈certificate769.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2880,MergedCutCells.Batch240.certificate2881,MergedCutCells.Batch240.certificate2882], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2880,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2881,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2882,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric769 : ∀ c∈certificate769.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2880,MergedCutCells.Batch240.certificate2881,MergedCutCells.Batch240.certificate2882], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2880,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2881,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2882,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid769 : ∀ c∈certificate769.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2880,MergedCutCells.Batch240.certificate2881,MergedCutCells.Batch240.certificate2882], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches769 : ∀ c∈certificate769.cells, c.population=certificate769.population := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2880,MergedCutCells.Batch240.certificate2881,MergedCutCells.Batch240.certificate2882], c.population=PopulationCertificates.Batch025.certificate512
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers769 {x : ℝ} (hx : certificate769.interval.Contains x) : ∃ c∈certificate769.cells, c.region.interval.Contains x := rat_cut_group_covers certificate769 numericValid769 hx

def certificate770 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate513,PopulationCertificates.Batch025.certificate513,[MergedCutCells.Batch240.certificate2883,MergedCutCells.Batch240.certificate2884],(1656375908311522161/200000000000000000),none,(1/2),(789184652161371487/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid770 : certificate770.NumericValid := by decide +kernel
theorem cellsSound770 : ∀ c∈certificate770.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2883,MergedCutCells.Batch240.certificate2884], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2883,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2884,List.forall_mem_nil _⟩⟩
theorem cellsNumeric770 : ∀ c∈certificate770.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2883,MergedCutCells.Batch240.certificate2884], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2883,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2884,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid770 : ∀ c∈certificate770.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2883,MergedCutCells.Batch240.certificate2884], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches770 : ∀ c∈certificate770.cells, c.population=certificate770.population := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2883,MergedCutCells.Batch240.certificate2884], c.population=PopulationCertificates.Batch025.certificate513
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers770 {x : ℝ} (hx : certificate770.interval.Contains x) : ∃ c∈certificate770.cells, c.region.interval.Contains x := rat_cut_group_covers certificate770 numericValid770 hx

def certificate771 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate514,PopulationCertificates.Batch025.certificate514,[MergedCutCells.Batch240.certificate2885,MergedCutCells.Batch240.certificate2886],(293613949261896943/500000000000000000),(some (315616883/250000000)),(1/2),(262971684547043031/1000000000000000000),(some (25483749500422581/500000000000000000)),(some (1783567945548239/200000000000000000))⟩
theorem numericValid771 : certificate771.NumericValid := by decide +kernel
theorem cellsSound771 : ∀ c∈certificate771.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2885,MergedCutCells.Batch240.certificate2886], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2885,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2886,List.forall_mem_nil _⟩⟩
theorem cellsNumeric771 : ∀ c∈certificate771.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2885,MergedCutCells.Batch240.certificate2886], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2885,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2886,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid771 : ∀ c∈certificate771.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2885,MergedCutCells.Batch240.certificate2886], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid258,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid258,List.forall_mem_nil _⟩⟩
theorem populationMatches771 : ∀ c∈certificate771.cells, c.population=certificate771.population := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2885,MergedCutCells.Batch240.certificate2886], c.population=PopulationCertificates.Batch025.certificate514
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers771 {x : ℝ} (hx : certificate771.interval.Contains x) : ∃ c∈certificate771.cells, c.region.interval.Contains x := rat_cut_group_covers certificate771 numericValid771 hx

def certificate772 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate514,PopulationCertificates.Batch025.certificate514,[MergedCutCells.Batch240.certificate2887,MergedCutCells.Batch240.certificate2888,MergedCutCells.Batch240.certificate2889],(315616883/250000000),none,(1/2),(130016644552240409/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid772 : certificate772.NumericValid := by decide +kernel
theorem cellsSound772 : ∀ c∈certificate772.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2887,MergedCutCells.Batch240.certificate2888,MergedCutCells.Batch240.certificate2889], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2887,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2888,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2889,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric772 : ∀ c∈certificate772.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2887,MergedCutCells.Batch240.certificate2888,MergedCutCells.Batch240.certificate2889], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2887,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2888,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2889,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid772 : ∀ c∈certificate772.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2887,MergedCutCells.Batch240.certificate2888,MergedCutCells.Batch240.certificate2889], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches772 : ∀ c∈certificate772.cells, c.population=certificate772.population := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2887,MergedCutCells.Batch240.certificate2888,MergedCutCells.Batch240.certificate2889], c.population=PopulationCertificates.Batch025.certificate514
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers772 {x : ℝ} (hx : certificate772.interval.Contains x) : ∃ c∈certificate772.cells, c.region.interval.Contains x := rat_cut_group_covers certificate772 numericValid772 hx

def certificate773 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate515,PopulationCertificates.Batch025.certificate515,[MergedCutCells.Batch240.certificate2890,MergedCutCells.Batch240.certificate2891],(2099091381246000543/250000000000000000),none,(1/2),(3234550582181912773/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid773 : certificate773.NumericValid := by decide +kernel
theorem cellsSound773 : ∀ c∈certificate773.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2890,MergedCutCells.Batch240.certificate2891], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2890,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.sound2891,List.forall_mem_nil _⟩⟩
theorem cellsNumeric773 : ∀ c∈certificate773.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2890,MergedCutCells.Batch240.certificate2891], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2890,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch240.numericValid2891,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid773 : ∀ c∈certificate773.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2890,MergedCutCells.Batch240.certificate2891], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches773 : ∀ c∈certificate773.cells, c.population=certificate773.population := by
  change ∀ c∈[MergedCutCells.Batch240.certificate2890,MergedCutCells.Batch240.certificate2891], c.population=PopulationCertificates.Batch025.certificate515
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers773 {x : ℝ} (hx : certificate773.interval.Contains x) : ∃ c∈certificate773.cells, c.region.interval.Contains x := rat_cut_group_covers certificate773 numericValid773 hx

def certificate774 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate516,PopulationCertificates.Batch025.certificate516,[MergedCutCells.Batch241.certificate2892,MergedCutCells.Batch241.certificate2893],(588365246464177023/1000000000000000000),(some (6168433/5000000)),(1/2),(127952275477654363/500000000000000000),(some (55773351758585531/1000000000000000000)),(some (9950369523272171/1000000000000000000))⟩
theorem numericValid774 : certificate774.NumericValid := by decide +kernel
theorem cellsSound774 : ∀ c∈certificate774.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2892,MergedCutCells.Batch241.certificate2893], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2892,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2893,List.forall_mem_nil _⟩⟩
theorem cellsNumeric774 : ∀ c∈certificate774.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2892,MergedCutCells.Batch241.certificate2893], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2892,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2893,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid774 : ∀ c∈certificate774.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2892,MergedCutCells.Batch241.certificate2893], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid259,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid259,List.forall_mem_nil _⟩⟩
theorem populationMatches774 : ∀ c∈certificate774.cells, c.population=certificate774.population := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2892,MergedCutCells.Batch241.certificate2893], c.population=PopulationCertificates.Batch025.certificate516
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers774 {x : ℝ} (hx : certificate774.interval.Contains x) : ∃ c∈certificate774.cells, c.region.interval.Contains x := rat_cut_group_covers certificate774 numericValid774 hx

def certificate775 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate516,PopulationCertificates.Batch025.certificate516,[MergedCutCells.Batch241.certificate2894,MergedCutCells.Batch241.certificate2895,MergedCutCells.Batch241.certificate2896,MergedCutCells.Batch241.certificate2897],(6168433/5000000),none,(1/2),(50507214321379067/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid775 : certificate775.NumericValid := by decide +kernel
theorem cellsSound775 : ∀ c∈certificate775.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2894,MergedCutCells.Batch241.certificate2895,MergedCutCells.Batch241.certificate2896,MergedCutCells.Batch241.certificate2897], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2894,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2895,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2896,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2897,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric775 : ∀ c∈certificate775.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2894,MergedCutCells.Batch241.certificate2895,MergedCutCells.Batch241.certificate2896,MergedCutCells.Batch241.certificate2897], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2894,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2895,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2896,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2897,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid775 : ∀ c∈certificate775.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2894,MergedCutCells.Batch241.certificate2895,MergedCutCells.Batch241.certificate2896,MergedCutCells.Batch241.certificate2897], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches775 : ∀ c∈certificate775.cells, c.population=certificate775.population := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2894,MergedCutCells.Batch241.certificate2895,MergedCutCells.Batch241.certificate2896,MergedCutCells.Batch241.certificate2897], c.population=PopulationCertificates.Batch025.certificate516
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers775 {x : ℝ} (hx : certificate775.interval.Contains x) : ∃ c∈certificate775.cells, c.region.interval.Contains x := rat_cut_group_covers certificate775 numericValid775 hx

def certificate776 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate517,PopulationCertificates.Batch025.certificate517,[MergedCutCells.Batch241.certificate2898,MergedCutCells.Batch241.certificate2899],(8429140451159841159/1000000000000000000),none,(1/2),(3279661609313394163/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid776 : certificate776.NumericValid := by decide +kernel
theorem cellsSound776 : ∀ c∈certificate776.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2898,MergedCutCells.Batch241.certificate2899], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2898,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2899,List.forall_mem_nil _⟩⟩
theorem cellsNumeric776 : ∀ c∈certificate776.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2898,MergedCutCells.Batch241.certificate2899], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2898,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2899,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid776 : ∀ c∈certificate776.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2898,MergedCutCells.Batch241.certificate2899], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches776 : ∀ c∈certificate776.cells, c.population=certificate776.population := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2898,MergedCutCells.Batch241.certificate2899], c.population=PopulationCertificates.Batch025.certificate517
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers776 {x : ℝ} (hx : certificate776.interval.Contains x) : ∃ c∈certificate776.cells, c.region.interval.Contains x := rat_cut_group_covers certificate776 numericValid776 hx

def certificate777 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate518,PopulationCertificates.Batch025.certificate518,[MergedCutCells.Batch241.certificate2900,MergedCutCells.Batch241.certificate2901],(2311727380970401/3906250000000000),(some (247950511/200000000)),(1/2),(8113568436741559/31250000000000000),(some (61102893579637021/1000000000000000000)),(some (5561778223314971/500000000000000000))⟩
theorem numericValid777 : certificate777.NumericValid := by decide +kernel
theorem cellsSound777 : ∀ c∈certificate777.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2900,MergedCutCells.Batch241.certificate2901], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2901,List.forall_mem_nil _⟩⟩
theorem cellsNumeric777 : ∀ c∈certificate777.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2900,MergedCutCells.Batch241.certificate2901], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2901,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid777 : ∀ c∈certificate777.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2900,MergedCutCells.Batch241.certificate2901], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid260,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid260,List.forall_mem_nil _⟩⟩
theorem populationMatches777 : ∀ c∈certificate777.cells, c.population=certificate777.population := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2900,MergedCutCells.Batch241.certificate2901], c.population=PopulationCertificates.Batch025.certificate518
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers777 {x : ℝ} (hx : certificate777.interval.Contains x) : ∃ c∈certificate777.cells, c.region.interval.Contains x := rat_cut_group_covers certificate777 numericValid777 hx

def certificate778 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate518,PopulationCertificates.Batch025.certificate518,[MergedCutCells.Batch241.certificate2902,MergedCutCells.Batch241.certificate2903,MergedCutCells.Batch242.certificate2904],(247950511/200000000),none,(1/2),(63992442671530149/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid778 : certificate778.NumericValid := by decide +kernel
theorem cellsSound778 : ∀ c∈certificate778.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2902,MergedCutCells.Batch241.certificate2903,MergedCutCells.Batch242.certificate2904], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2902,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.sound2903,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2904,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric778 : ∀ c∈certificate778.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2902,MergedCutCells.Batch241.certificate2903,MergedCutCells.Batch242.certificate2904], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2902,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch241.numericValid2903,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2904,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid778 : ∀ c∈certificate778.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2902,MergedCutCells.Batch241.certificate2903,MergedCutCells.Batch242.certificate2904], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches778 : ∀ c∈certificate778.cells, c.population=certificate778.population := by
  change ∀ c∈[MergedCutCells.Batch241.certificate2902,MergedCutCells.Batch241.certificate2903,MergedCutCells.Batch242.certificate2904], c.population=PopulationCertificates.Batch025.certificate518
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers778 {x : ℝ} (hx : certificate778.interval.Contains x) : ∃ c∈certificate778.cells, c.region.interval.Contains x := rat_cut_group_covers certificate778 numericValid778 hx

def certificate779 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate519,PopulationCertificates.Batch025.certificate519,[MergedCutCells.Batch242.certificate2905,MergedCutCells.Batch242.certificate2906],(8547582761192461613/1000000000000000000),none,(1/2),(672087488626479623/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid779 : certificate779.NumericValid := by decide +kernel
theorem cellsSound779 : ∀ c∈certificate779.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2905,MergedCutCells.Batch242.certificate2906], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2905,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2906,List.forall_mem_nil _⟩⟩
theorem cellsNumeric779 : ∀ c∈certificate779.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2905,MergedCutCells.Batch242.certificate2906], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2905,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2906,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid779 : ∀ c∈certificate779.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2905,MergedCutCells.Batch242.certificate2906], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches779 : ∀ c∈certificate779.cells, c.population=certificate779.population := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2905,MergedCutCells.Batch242.certificate2906], c.population=PopulationCertificates.Batch025.certificate519
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers779 {x : ℝ} (hx : certificate779.interval.Contains x) : ∃ c∈certificate779.cells, c.region.interval.Contains x := rat_cut_group_covers certificate779 numericValid779 hx

end Cycle12.MergedCutGroups.Batch064
