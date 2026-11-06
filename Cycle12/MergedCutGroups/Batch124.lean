import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch050
import Cycle12.GeometryCertificates.Batch051
import Cycle12.MergedCutCells.Batch414
import Cycle12.MergedCutCells.Batch415
import Cycle12.MergedCutCells.Batch416
import Cycle12.MergedCutCells.Batch417
import Cycle12.PopulationCertificates.Batch050
import Cycle12.PopulationCertificates.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch124

def certificate1488 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1012,PopulationCertificates.Batch050.certificate1012,[MergedCutCells.Batch414.certificate4976,MergedCutCells.Batch414.certificate4977,MergedCutCells.Batch414.certificate4978,MergedCutCells.Batch414.certificate4979,MergedCutCells.Batch415.certificate4980],(711228629152005069/1000000000000000000),none,(1/40),(21190898640003187/500000000000000000),none,none⟩
theorem numericValid1488 : certificate1488.NumericValid := by decide +kernel
theorem cellsSound1488 : ∀ c∈certificate1488.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4976,MergedCutCells.Batch414.certificate4977,MergedCutCells.Batch414.certificate4978,MergedCutCells.Batch414.certificate4979,MergedCutCells.Batch415.certificate4980], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4976,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4977,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4978,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.sound4979,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4980,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1488 : ∀ c∈certificate1488.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4976,MergedCutCells.Batch414.certificate4977,MergedCutCells.Batch414.certificate4978,MergedCutCells.Batch414.certificate4979,MergedCutCells.Batch415.certificate4980], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4976,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4977,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4978,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch414.numericValid4979,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4980,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1488 : ∀ c∈certificate1488.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4976,MergedCutCells.Batch414.certificate4977,MergedCutCells.Batch414.certificate4978,MergedCutCells.Batch414.certificate4979,MergedCutCells.Batch415.certificate4980], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid716,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid717,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid718,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy035.valid719,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid720,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1488 : ∀ c∈certificate1488.cells, c.population=certificate1488.population := by
  change ∀ c∈[MergedCutCells.Batch414.certificate4976,MergedCutCells.Batch414.certificate4977,MergedCutCells.Batch414.certificate4978,MergedCutCells.Batch414.certificate4979,MergedCutCells.Batch415.certificate4980], c.population=PopulationCertificates.Batch050.certificate1012
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1488 {x : ℝ} (hx : certificate1488.interval.Contains x) : ∃ c∈certificate1488.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1488 numericValid1488 hx

def certificate1489 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1013,PopulationCertificates.Batch050.certificate1013,[MergedCutCells.Batch415.certificate4981,MergedCutCells.Batch415.certificate4982],(615056611883816811/1000000000000000000),(some (277342049/250000000)),(1/2),(325754121988866973/1000000000000000000),(some (14376784155629519/500000000000000000)),(some (449021492845891/100000000000000000))⟩
theorem numericValid1489 : certificate1489.NumericValid := by decide +kernel
theorem cellsSound1489 : ∀ c∈certificate1489.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4981,MergedCutCells.Batch415.certificate4982], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4981,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4982,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1489 : ∀ c∈certificate1489.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4981,MergedCutCells.Batch415.certificate4982], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4981,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4982,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1489 : ∀ c∈certificate1489.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4981,MergedCutCells.Batch415.certificate4982], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid721,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid721,List.forall_mem_nil _⟩⟩
theorem populationMatches1489 : ∀ c∈certificate1489.cells, c.population=certificate1489.population := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4981,MergedCutCells.Batch415.certificate4982], c.population=PopulationCertificates.Batch050.certificate1013
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1489 {x : ℝ} (hx : certificate1489.interval.Contains x) : ∃ c∈certificate1489.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1489 numericValid1489 hx

def certificate1490 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1013,PopulationCertificates.Batch050.certificate1013,[MergedCutCells.Batch415.certificate4983,MergedCutCells.Batch415.certificate4984,MergedCutCells.Batch415.certificate4985],(277342049/250000000),none,(1/2),(62242574582001013/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1490 : certificate1490.NumericValid := by decide +kernel
theorem cellsSound1490 : ∀ c∈certificate1490.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4983,MergedCutCells.Batch415.certificate4984,MergedCutCells.Batch415.certificate4985], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4983,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4984,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4985,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1490 : ∀ c∈certificate1490.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4983,MergedCutCells.Batch415.certificate4984,MergedCutCells.Batch415.certificate4985], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4983,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4984,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4985,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1490 : ∀ c∈certificate1490.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4983,MergedCutCells.Batch415.certificate4984,MergedCutCells.Batch415.certificate4985], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1490 : ∀ c∈certificate1490.cells, c.population=certificate1490.population := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4983,MergedCutCells.Batch415.certificate4984,MergedCutCells.Batch415.certificate4985], c.population=PopulationCertificates.Batch050.certificate1013
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1490 {x : ℝ} (hx : certificate1490.interval.Contains x) : ∃ c∈certificate1490.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1490 numericValid1490 hx

def certificate1491 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1014,PopulationCertificates.Batch050.certificate1014,[MergedCutCells.Batch415.certificate4986,MergedCutCells.Batch415.certificate4987],(36742461105914029177/1000000000000000000),none,(1/2),(4659944824946356631/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1491 : certificate1491.NumericValid := by decide +kernel
theorem cellsSound1491 : ∀ c∈certificate1491.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4986,MergedCutCells.Batch415.certificate4987], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4986,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4987,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1491 : ∀ c∈certificate1491.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4986,MergedCutCells.Batch415.certificate4987], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4986,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4987,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1491 : ∀ c∈certificate1491.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4986,MergedCutCells.Batch415.certificate4987], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1491 : ∀ c∈certificate1491.cells, c.population=certificate1491.population := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4986,MergedCutCells.Batch415.certificate4987], c.population=PopulationCertificates.Batch050.certificate1014
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1491 {x : ℝ} (hx : certificate1491.interval.Contains x) : ∃ c∈certificate1491.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1491 numericValid1491 hx

def certificate1492 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1015,PopulationCertificates.Batch050.certificate1015,[MergedCutCells.Batch415.certificate4988,MergedCutCells.Batch415.certificate4989,MergedCutCells.Batch415.certificate4990,MergedCutCells.Batch415.certificate4991,MergedCutCells.Batch416.certificate4992],(143027595071529363/200000000000000000),none,(1/40),(49083605770552581/1000000000000000000),none,none⟩
theorem numericValid1492 : certificate1492.NumericValid := by decide +kernel
theorem cellsSound1492 : ∀ c∈certificate1492.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4988,MergedCutCells.Batch415.certificate4989,MergedCutCells.Batch415.certificate4990,MergedCutCells.Batch415.certificate4991,MergedCutCells.Batch416.certificate4992], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4988,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4990,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.sound4991,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound4992,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1492 : ∀ c∈certificate1492.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4988,MergedCutCells.Batch415.certificate4989,MergedCutCells.Batch415.certificate4990,MergedCutCells.Batch415.certificate4991,MergedCutCells.Batch416.certificate4992], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4988,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4990,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch415.numericValid4991,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid4992,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1492 : ∀ c∈certificate1492.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4988,MergedCutCells.Batch415.certificate4989,MergedCutCells.Batch415.certificate4990,MergedCutCells.Batch415.certificate4991,MergedCutCells.Batch416.certificate4992], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid722,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid723,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid724,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid725,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid726,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1492 : ∀ c∈certificate1492.cells, c.population=certificate1492.population := by
  change ∀ c∈[MergedCutCells.Batch415.certificate4988,MergedCutCells.Batch415.certificate4989,MergedCutCells.Batch415.certificate4990,MergedCutCells.Batch415.certificate4991,MergedCutCells.Batch416.certificate4992], c.population=PopulationCertificates.Batch050.certificate1015
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1492 {x : ℝ} (hx : certificate1492.interval.Contains x) : ∃ c∈certificate1492.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1492 numericValid1492 hx

def certificate1493 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1016,PopulationCertificates.Batch050.certificate1016,[MergedCutCells.Batch416.certificate4993,MergedCutCells.Batch416.certificate4994],(75375326139114467/125000000000000000),(some (136295453/125000000)),(1/2),(251955082007310891/1000000000000000000),(some (14887111788581413/500000000000000000)),(some (4679912748204081/1000000000000000000))⟩
theorem numericValid1493 : certificate1493.NumericValid := by decide +kernel
theorem cellsSound1493 : ∀ c∈certificate1493.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4993,MergedCutCells.Batch416.certificate4994], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound4993,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound4994,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1493 : ∀ c∈certificate1493.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4993,MergedCutCells.Batch416.certificate4994], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid4993,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid4994,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1493 : ∀ c∈certificate1493.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4993,MergedCutCells.Batch416.certificate4994], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid727,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid727,List.forall_mem_nil _⟩⟩
theorem populationMatches1493 : ∀ c∈certificate1493.cells, c.population=certificate1493.population := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4993,MergedCutCells.Batch416.certificate4994], c.population=PopulationCertificates.Batch050.certificate1016
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1493 {x : ℝ} (hx : certificate1493.interval.Contains x) : ∃ c∈certificate1493.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1493 numericValid1493 hx

def certificate1494 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1016,PopulationCertificates.Batch050.certificate1016,[MergedCutCells.Batch416.certificate4995,MergedCutCells.Batch416.certificate4996,MergedCutCells.Batch416.certificate4997,MergedCutCells.Batch416.certificate4998],(136295453/125000000),none,(1/2),(50015837345433419/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1494 : certificate1494.NumericValid := by decide +kernel
theorem cellsSound1494 : ∀ c∈certificate1494.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4995,MergedCutCells.Batch416.certificate4996,MergedCutCells.Batch416.certificate4997,MergedCutCells.Batch416.certificate4998], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound4995,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound4996,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound4997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound4998,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1494 : ∀ c∈certificate1494.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4995,MergedCutCells.Batch416.certificate4996,MergedCutCells.Batch416.certificate4997,MergedCutCells.Batch416.certificate4998], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid4995,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid4996,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid4997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid4998,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1494 : ∀ c∈certificate1494.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4995,MergedCutCells.Batch416.certificate4996,MergedCutCells.Batch416.certificate4997,MergedCutCells.Batch416.certificate4998], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1494 : ∀ c∈certificate1494.cells, c.population=certificate1494.population := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4995,MergedCutCells.Batch416.certificate4996,MergedCutCells.Batch416.certificate4997,MergedCutCells.Batch416.certificate4998], c.population=PopulationCertificates.Batch050.certificate1016
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1494 {x : ℝ} (hx : certificate1494.interval.Contains x) : ∃ c∈certificate1494.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1494 numericValid1494 hx

def certificate1495 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1017,PopulationCertificates.Batch050.certificate1017,[MergedCutCells.Batch416.certificate4999,MergedCutCells.Batch416.certificate5000],(38121104132082364829/1000000000000000000),none,(1/2),(1904179387914188473/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1495 : certificate1495.NumericValid := by decide +kernel
theorem cellsSound1495 : ∀ c∈certificate1495.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4999,MergedCutCells.Batch416.certificate5000], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound4999,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound5000,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1495 : ∀ c∈certificate1495.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4999,MergedCutCells.Batch416.certificate5000], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid4999,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid5000,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1495 : ∀ c∈certificate1495.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4999,MergedCutCells.Batch416.certificate5000], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1495 : ∀ c∈certificate1495.cells, c.population=certificate1495.population := by
  change ∀ c∈[MergedCutCells.Batch416.certificate4999,MergedCutCells.Batch416.certificate5000], c.population=PopulationCertificates.Batch050.certificate1017
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1495 {x : ℝ} (hx : certificate1495.interval.Contains x) : ∃ c∈certificate1495.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1495 numericValid1495 hx

def certificate1496 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1018,PopulationCertificates.Batch050.certificate1018,[MergedCutCells.Batch416.certificate5001,MergedCutCells.Batch416.certificate5002,MergedCutCells.Batch416.certificate5003,MergedCutCells.Batch417.certificate5004,MergedCutCells.Batch417.certificate5005],(359615104341485643/500000000000000000),none,(1/40),(56193834592772193/1000000000000000000),none,none⟩
theorem numericValid1496 : certificate1496.NumericValid := by decide +kernel
theorem cellsSound1496 : ∀ c∈certificate1496.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch416.certificate5001,MergedCutCells.Batch416.certificate5002,MergedCutCells.Batch416.certificate5003,MergedCutCells.Batch417.certificate5004,MergedCutCells.Batch417.certificate5005], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound5001,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound5002,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.sound5003,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5004,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5005,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1496 : ∀ c∈certificate1496.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch416.certificate5001,MergedCutCells.Batch416.certificate5002,MergedCutCells.Batch416.certificate5003,MergedCutCells.Batch417.certificate5004,MergedCutCells.Batch417.certificate5005], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid5001,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid5002,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch416.numericValid5003,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5004,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5005,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1496 : ∀ c∈certificate1496.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch416.certificate5001,MergedCutCells.Batch416.certificate5002,MergedCutCells.Batch416.certificate5003,MergedCutCells.Batch417.certificate5004,MergedCutCells.Batch417.certificate5005], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid728,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid729,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid730,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid731,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid732,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1496 : ∀ c∈certificate1496.cells, c.population=certificate1496.population := by
  change ∀ c∈[MergedCutCells.Batch416.certificate5001,MergedCutCells.Batch416.certificate5002,MergedCutCells.Batch416.certificate5003,MergedCutCells.Batch417.certificate5004,MergedCutCells.Batch417.certificate5005], c.population=PopulationCertificates.Batch050.certificate1018
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1496 {x : ℝ} (hx : certificate1496.interval.Contains x) : ∃ c∈certificate1496.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1496 numericValid1496 hx

def certificate1497 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1019,PopulationCertificates.Batch050.certificate1019,[MergedCutCells.Batch417.certificate5006,MergedCutCells.Batch417.certificate5007],(120990572862120839/200000000000000000),(some (1093441681/1000000000)),(1/2),(257143543635576573/1000000000000000000),(some (15439651528894609/500000000000000000)),(some (4886938604044481/1000000000000000000))⟩
theorem numericValid1497 : certificate1497.NumericValid := by decide +kernel
theorem cellsSound1497 : ∀ c∈certificate1497.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5006,MergedCutCells.Batch417.certificate5007], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5006,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5007,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1497 : ∀ c∈certificate1497.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5006,MergedCutCells.Batch417.certificate5007], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5006,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5007,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1497 : ∀ c∈certificate1497.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5006,MergedCutCells.Batch417.certificate5007], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid733,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid733,List.forall_mem_nil _⟩⟩
theorem populationMatches1497 : ∀ c∈certificate1497.cells, c.population=certificate1497.population := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5006,MergedCutCells.Batch417.certificate5007], c.population=PopulationCertificates.Batch050.certificate1019
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1497 {x : ℝ} (hx : certificate1497.interval.Contains x) : ∃ c∈certificate1497.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1497 numericValid1497 hx

def certificate1498 : RatCutGroup := ⟨GeometryCertificates.Batch050.certificate1019,PopulationCertificates.Batch050.certificate1019,[MergedCutCells.Batch417.certificate5008,MergedCutCells.Batch417.certificate5009,MergedCutCells.Batch417.certificate5010],(1093441681/1000000000),none,(1/2),(254964904060980961/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1498 : certificate1498.NumericValid := by decide +kernel
theorem cellsSound1498 : ∀ c∈certificate1498.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5008,MergedCutCells.Batch417.certificate5009,MergedCutCells.Batch417.certificate5010], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5008,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5009,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5010,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1498 : ∀ c∈certificate1498.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5008,MergedCutCells.Batch417.certificate5009,MergedCutCells.Batch417.certificate5010], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5008,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5009,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5010,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1498 : ∀ c∈certificate1498.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5008,MergedCutCells.Batch417.certificate5009,MergedCutCells.Batch417.certificate5010], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1498 : ∀ c∈certificate1498.cells, c.population=certificate1498.population := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5008,MergedCutCells.Batch417.certificate5009,MergedCutCells.Batch417.certificate5010], c.population=PopulationCertificates.Batch050.certificate1019
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1498 {x : ℝ} (hx : certificate1498.interval.Contains x) : ∃ c∈certificate1498.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1498 numericValid1498 hx

def certificate1499 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1020,PopulationCertificates.Batch051.certificate1020,[MergedCutCells.Batch417.certificate5011,MergedCutCells.Batch417.certificate5012],(9734184480236888221/250000000000000000),none,(1/2),(388988218674010603/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1499 : certificate1499.NumericValid := by decide +kernel
theorem cellsSound1499 : ∀ c∈certificate1499.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5011,MergedCutCells.Batch417.certificate5012], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5011,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5012,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1499 : ∀ c∈certificate1499.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5011,MergedCutCells.Batch417.certificate5012], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5011,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5012,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1499 : ∀ c∈certificate1499.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5011,MergedCutCells.Batch417.certificate5012], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1499 : ∀ c∈certificate1499.cells, c.population=certificate1499.population := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5011,MergedCutCells.Batch417.certificate5012], c.population=PopulationCertificates.Batch051.certificate1020
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1499 {x : ℝ} (hx : certificate1499.interval.Contains x) : ∃ c∈certificate1499.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1499 numericValid1499 hx

end Cycle12.MergedCutGroups.Batch124
