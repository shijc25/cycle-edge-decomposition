import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch036
import Cycle12.MergedCutCells.Batch323
import Cycle12.MergedCutCells.Batch324
import Cycle12.MergedCutCells.Batch325
import Cycle12.PopulationCertificates.Batch036

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch090

def certificate1080 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate720,PopulationCertificates.Batch036.certificate720,[MergedCutCells.Batch323.certificate3876,MergedCutCells.Batch323.certificate3877],(557118389944444469/1000000000000000000),(some (29840471/25000000)),(1/2),(25504982594959399/250000000000000000),(some (33771674946986609/1000000000000000000)),(some (5436634183405621/1000000000000000000))⟩
theorem numericValid1080 : certificate1080.NumericValid := by decide +kernel
theorem cellsSound1080 : ∀ c∈certificate1080.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3876,MergedCutCells.Batch323.certificate3877], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3876,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3877,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1080 : ∀ c∈certificate1080.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3876,MergedCutCells.Batch323.certificate3877], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3876,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3877,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1080 : ∀ c∈certificate1080.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3876,MergedCutCells.Batch323.certificate3877], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid361,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid361,List.forall_mem_nil _⟩⟩
theorem populationMatches1080 : ∀ c∈certificate1080.cells, c.population=certificate1080.population := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3876,MergedCutCells.Batch323.certificate3877], c.population=PopulationCertificates.Batch036.certificate720
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1080 {x : ℝ} (hx : certificate1080.interval.Contains x) : ∃ c∈certificate1080.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1080 numericValid1080 hx

def certificate1081 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate720,PopulationCertificates.Batch036.certificate720,[MergedCutCells.Batch323.certificate3878,MergedCutCells.Batch323.certificate3879,MergedCutCells.Batch323.certificate3880,MergedCutCells.Batch323.certificate3881],(29840471/25000000),none,(1/2),(49865657628810061/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1081 : certificate1081.NumericValid := by decide +kernel
theorem cellsSound1081 : ∀ c∈certificate1081.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3878,MergedCutCells.Batch323.certificate3879,MergedCutCells.Batch323.certificate3880,MergedCutCells.Batch323.certificate3881], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3879,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3880,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3881,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1081 : ∀ c∈certificate1081.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3878,MergedCutCells.Batch323.certificate3879,MergedCutCells.Batch323.certificate3880,MergedCutCells.Batch323.certificate3881], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3879,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3880,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3881,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1081 : ∀ c∈certificate1081.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3878,MergedCutCells.Batch323.certificate3879,MergedCutCells.Batch323.certificate3880,MergedCutCells.Batch323.certificate3881], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1081 : ∀ c∈certificate1081.cells, c.population=certificate1081.population := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3878,MergedCutCells.Batch323.certificate3879,MergedCutCells.Batch323.certificate3880,MergedCutCells.Batch323.certificate3881], c.population=PopulationCertificates.Batch036.certificate720
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1081 {x : ℝ} (hx : certificate1081.interval.Contains x) : ∃ c∈certificate1081.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1081 numericValid1081 hx

def certificate1082 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate721,PopulationCertificates.Batch036.certificate721,[MergedCutCells.Batch323.certificate3882,MergedCutCells.Batch323.certificate3883],(5068235283554220991/250000000000000000),none,(1/2),(2708243552386934833/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1082 : certificate1082.NumericValid := by decide +kernel
theorem cellsSound1082 : ∀ c∈certificate1082.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3882,MergedCutCells.Batch323.certificate3883], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3882,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3883,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1082 : ∀ c∈certificate1082.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3882,MergedCutCells.Batch323.certificate3883], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3882,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3883,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1082 : ∀ c∈certificate1082.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3882,MergedCutCells.Batch323.certificate3883], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1082 : ∀ c∈certificate1082.cells, c.population=certificate1082.population := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3882,MergedCutCells.Batch323.certificate3883], c.population=PopulationCertificates.Batch036.certificate721
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1082 {x : ℝ} (hx : certificate1082.interval.Contains x) : ∃ c∈certificate1082.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1082 numericValid1082 hx

def certificate1083 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate722,PopulationCertificates.Batch036.certificate722,[MergedCutCells.Batch323.certificate3884,MergedCutCells.Batch323.certificate3885],(278680727196157819/500000000000000000),(some (1194055941/1000000000)),(1/2),(95812205105666071/1000000000000000000),(some (18037677248054313/500000000000000000)),(some (47058445471961/8000000000000000))⟩
theorem numericValid1083 : certificate1083.NumericValid := by decide +kernel
theorem cellsSound1083 : ∀ c∈certificate1083.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3884,MergedCutCells.Batch323.certificate3885], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3884,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3885,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1083 : ∀ c∈certificate1083.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3884,MergedCutCells.Batch323.certificate3885], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3884,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3885,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1083 : ∀ c∈certificate1083.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3884,MergedCutCells.Batch323.certificate3885], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid362,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid362,List.forall_mem_nil _⟩⟩
theorem populationMatches1083 : ∀ c∈certificate1083.cells, c.population=certificate1083.population := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3884,MergedCutCells.Batch323.certificate3885], c.population=PopulationCertificates.Batch036.certificate722
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1083 {x : ℝ} (hx : certificate1083.interval.Contains x) : ∃ c∈certificate1083.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1083 numericValid1083 hx

def certificate1084 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate722,PopulationCertificates.Batch036.certificate722,[MergedCutCells.Batch323.certificate3886,MergedCutCells.Batch323.certificate3887,MergedCutCells.Batch324.certificate3888],(1194055941/1000000000),none,(1/2),(93696482173557949/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1084 : certificate1084.NumericValid := by decide +kernel
theorem cellsSound1084 : ∀ c∈certificate1084.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3886,MergedCutCells.Batch323.certificate3887,MergedCutCells.Batch324.certificate3888], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3886,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.sound3887,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3888,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1084 : ∀ c∈certificate1084.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3886,MergedCutCells.Batch323.certificate3887,MergedCutCells.Batch324.certificate3888], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3886,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch323.numericValid3887,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3888,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1084 : ∀ c∈certificate1084.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3886,MergedCutCells.Batch323.certificate3887,MergedCutCells.Batch324.certificate3888], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1084 : ∀ c∈certificate1084.cells, c.population=certificate1084.population := by
  change ∀ c∈[MergedCutCells.Batch323.certificate3886,MergedCutCells.Batch323.certificate3887,MergedCutCells.Batch324.certificate3888], c.population=PopulationCertificates.Batch036.certificate722
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1084 {x : ℝ} (hx : certificate1084.interval.Contains x) : ∃ c∈certificate1084.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1084 numericValid1084 hx

def certificate1085 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate723,PopulationCertificates.Batch036.certificate723,[MergedCutCells.Batch324.certificate3889,MergedCutCells.Batch324.certificate3890],(128305231017609091/6250000000000000),none,(1/2),(5513935454105521919/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1085 : certificate1085.NumericValid := by decide +kernel
theorem cellsSound1085 : ∀ c∈certificate1085.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3889,MergedCutCells.Batch324.certificate3890], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3889,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3890,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1085 : ∀ c∈certificate1085.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3889,MergedCutCells.Batch324.certificate3890], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3889,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3890,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1085 : ∀ c∈certificate1085.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3889,MergedCutCells.Batch324.certificate3890], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1085 : ∀ c∈certificate1085.cells, c.population=certificate1085.population := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3889,MergedCutCells.Batch324.certificate3890], c.population=PopulationCertificates.Batch036.certificate723
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1085 {x : ℝ} (hx : certificate1085.interval.Contains x) : ∃ c∈certificate1085.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1085 numericValid1085 hx

def certificate1086 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate724,PopulationCertificates.Batch036.certificate724,[MergedCutCells.Batch324.certificate3891,MergedCutCells.Batch324.certificate3892],(557866170824488749/1000000000000000000),(some (119496347/100000000)),(1/2),(89816885400816111/1000000000000000000),(some (38463847704443237/1000000000000000000)),(some (1587870773960371/250000000000000000))⟩
theorem numericValid1086 : certificate1086.NumericValid := by decide +kernel
theorem cellsSound1086 : ∀ c∈certificate1086.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3891,MergedCutCells.Batch324.certificate3892], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3891,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3892,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1086 : ∀ c∈certificate1086.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3891,MergedCutCells.Batch324.certificate3892], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3891,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3892,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1086 : ∀ c∈certificate1086.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3891,MergedCutCells.Batch324.certificate3892], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid363,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid363,List.forall_mem_nil _⟩⟩
theorem populationMatches1086 : ∀ c∈certificate1086.cells, c.population=certificate1086.population := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3891,MergedCutCells.Batch324.certificate3892], c.population=PopulationCertificates.Batch036.certificate724
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1086 {x : ℝ} (hx : certificate1086.interval.Contains x) : ∃ c∈certificate1086.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1086 numericValid1086 hx

def certificate1087 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate724,PopulationCertificates.Batch036.certificate724,[MergedCutCells.Batch324.certificate3893,MergedCutCells.Batch324.certificate3894,MergedCutCells.Batch324.certificate3895],(119496347/100000000),none,(1/2),(21879881957336111/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1087 : certificate1087.NumericValid := by decide +kernel
theorem cellsSound1087 : ∀ c∈certificate1087.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3893,MergedCutCells.Batch324.certificate3894,MergedCutCells.Batch324.certificate3895], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3893,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3894,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3895,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1087 : ∀ c∈certificate1087.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3893,MergedCutCells.Batch324.certificate3894,MergedCutCells.Batch324.certificate3895], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3893,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3894,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3895,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1087 : ∀ c∈certificate1087.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3893,MergedCutCells.Batch324.certificate3894,MergedCutCells.Batch324.certificate3895], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1087 : ∀ c∈certificate1087.cells, c.population=certificate1087.population := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3893,MergedCutCells.Batch324.certificate3894,MergedCutCells.Batch324.certificate3895], c.population=PopulationCertificates.Batch036.certificate724
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1087 {x : ℝ} (hx : certificate1087.interval.Contains x) : ∃ c∈certificate1087.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1087 numericValid1087 hx

def certificate1088 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate725,PopulationCertificates.Batch036.certificate725,[MergedCutCells.Batch324.certificate3896,MergedCutCells.Batch324.certificate3897],(4158093384958469767/200000000000000000),none,(1/2),(701704140751972643/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1088 : certificate1088.NumericValid := by decide +kernel
theorem cellsSound1088 : ∀ c∈certificate1088.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3896,MergedCutCells.Batch324.certificate3897], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3896,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3897,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1088 : ∀ c∈certificate1088.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3896,MergedCutCells.Batch324.certificate3897], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3896,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3897,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1088 : ∀ c∈certificate1088.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3896,MergedCutCells.Batch324.certificate3897], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1088 : ∀ c∈certificate1088.cells, c.population=certificate1088.population := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3896,MergedCutCells.Batch324.certificate3897], c.population=PopulationCertificates.Batch036.certificate725
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1088 {x : ℝ} (hx : certificate1088.interval.Contains x) : ∃ c∈certificate1088.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1088 numericValid1088 hx

def certificate1089 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate726,PopulationCertificates.Batch036.certificate726,[MergedCutCells.Batch324.certificate3898,MergedCutCells.Batch324.certificate3899],(558404560244987407/1000000000000000000),(some (1195931403/1000000000)),(1/2),(8377975982810723/100000000000000000),(some (20459110233743991/500000000000000000)),(some (1710225428304321/250000000000000000))⟩
theorem numericValid1089 : certificate1089.NumericValid := by decide +kernel
theorem cellsSound1089 : ∀ c∈certificate1089.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3898,MergedCutCells.Batch324.certificate3899], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3898,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.sound3899,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1089 : ∀ c∈certificate1089.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3898,MergedCutCells.Batch324.certificate3899], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3898,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch324.numericValid3899,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1089 : ∀ c∈certificate1089.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3898,MergedCutCells.Batch324.certificate3899], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid364,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid364,List.forall_mem_nil _⟩⟩
theorem populationMatches1089 : ∀ c∈certificate1089.cells, c.population=certificate1089.population := by
  change ∀ c∈[MergedCutCells.Batch324.certificate3898,MergedCutCells.Batch324.certificate3899], c.population=PopulationCertificates.Batch036.certificate726
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1089 {x : ℝ} (hx : certificate1089.interval.Contains x) : ∃ c∈certificate1089.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1089 numericValid1089 hx

def certificate1090 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate726,PopulationCertificates.Batch036.certificate726,[MergedCutCells.Batch325.certificate3900,MergedCutCells.Batch325.certificate3901,MergedCutCells.Batch325.certificate3902],(1195931403/1000000000),none,(1/2),(162580496926347/2000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1090 : certificate1090.NumericValid := by decide +kernel
theorem cellsSound1090 : ∀ c∈certificate1090.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3900,MergedCutCells.Batch325.certificate3901,MergedCutCells.Batch325.certificate3902], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3901,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3902,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1090 : ∀ c∈certificate1090.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3900,MergedCutCells.Batch325.certificate3901,MergedCutCells.Batch325.certificate3902], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3901,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3902,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1090 : ∀ c∈certificate1090.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3900,MergedCutCells.Batch325.certificate3901,MergedCutCells.Batch325.certificate3902], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1090 : ∀ c∈certificate1090.cells, c.population=certificate1090.population := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3900,MergedCutCells.Batch325.certificate3901,MergedCutCells.Batch325.certificate3902], c.population=PopulationCertificates.Batch036.certificate726
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1090 {x : ℝ} (hx : certificate1090.interval.Contains x) : ∃ c∈certificate1090.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1090 numericValid1090 hx

def certificate1091 : RatCutGroup := ⟨GeometryCertificates.Batch036.certificate727,PopulationCertificates.Batch036.certificate727,[MergedCutCells.Batch325.certificate3903,MergedCutCells.Batch325.certificate3904],(5264505017135815123/250000000000000000),none,(1/2),(5715656157946987939/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1091 : certificate1091.NumericValid := by decide +kernel
theorem cellsSound1091 : ∀ c∈certificate1091.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3903,MergedCutCells.Batch325.certificate3904], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3903,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.sound3904,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1091 : ∀ c∈certificate1091.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3903,MergedCutCells.Batch325.certificate3904], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3903,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch325.numericValid3904,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1091 : ∀ c∈certificate1091.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3903,MergedCutCells.Batch325.certificate3904], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1091 : ∀ c∈certificate1091.cells, c.population=certificate1091.population := by
  change ∀ c∈[MergedCutCells.Batch325.certificate3903,MergedCutCells.Batch325.certificate3904], c.population=PopulationCertificates.Batch036.certificate727
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1091 {x : ℝ} (hx : certificate1091.interval.Contains x) : ∃ c∈certificate1091.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1091 numericValid1091 hx

end Cycle12.MergedCutGroups.Batch090
