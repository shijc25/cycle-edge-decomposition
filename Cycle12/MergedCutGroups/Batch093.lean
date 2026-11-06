import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch037
import Cycle12.MergedCutCells.Batch330
import Cycle12.MergedCutCells.Batch331
import Cycle12.MergedCutCells.Batch332
import Cycle12.PopulationCertificates.Batch037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch093

def certificate1116 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate744,PopulationCertificates.Batch037.certificate744,[MergedCutCells.Batch330.certificate3962,MergedCutCells.Batch330.certificate3963],(287543669406785989/500000000000000000),(some (1147456911/1000000000)),(1/2),(37175689482020561/500000000000000000),(some (12969624212433949/200000000000000000)),(some (2393029731131419/200000000000000000))⟩
theorem numericValid1116 : certificate1116.NumericValid := by decide +kernel
theorem cellsSound1116 : ∀ c∈certificate1116.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3962,MergedCutCells.Batch330.certificate3963], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3962,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3963,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1116 : ∀ c∈certificate1116.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3962,MergedCutCells.Batch330.certificate3963], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3962,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3963,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1116 : ∀ c∈certificate1116.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3962,MergedCutCells.Batch330.certificate3963], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid373,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid373,List.forall_mem_nil _⟩⟩
theorem populationMatches1116 : ∀ c∈certificate1116.cells, c.population=certificate1116.population := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3962,MergedCutCells.Batch330.certificate3963], c.population=PopulationCertificates.Batch037.certificate744
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1116 {x : ℝ} (hx : certificate1116.interval.Contains x) : ∃ c∈certificate1116.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1116 numericValid1116 hx

def certificate1117 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate744,PopulationCertificates.Batch037.certificate744,[MergedCutCells.Batch330.certificate3964,MergedCutCells.Batch330.certificate3965,MergedCutCells.Batch330.certificate3966],(1147456911/1000000000),none,(1/2),(69568762334485499/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1117 : certificate1117.NumericValid := by decide +kernel
theorem cellsSound1117 : ∀ c∈certificate1117.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3964,MergedCutCells.Batch330.certificate3965,MergedCutCells.Batch330.certificate3966], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3965,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3966,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1117 : ∀ c∈certificate1117.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3964,MergedCutCells.Batch330.certificate3965,MergedCutCells.Batch330.certificate3966], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3965,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3966,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1117 : ∀ c∈certificate1117.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3964,MergedCutCells.Batch330.certificate3965,MergedCutCells.Batch330.certificate3966], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1117 : ∀ c∈certificate1117.cells, c.population=certificate1117.population := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3964,MergedCutCells.Batch330.certificate3965,MergedCutCells.Batch330.certificate3966], c.population=PopulationCertificates.Batch037.certificate744
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1117 {x : ℝ} (hx : certificate1117.interval.Contains x) : ∃ c∈certificate1117.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1117 numericValid1117 hx

def certificate1118 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate745,PopulationCertificates.Batch037.certificate745,[MergedCutCells.Batch330.certificate3967,MergedCutCells.Batch330.certificate3968],(23296051771607351497/1000000000000000000),none,(1/2),(3369070819238053639/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1118 : certificate1118.NumericValid := by decide +kernel
theorem cellsSound1118 : ∀ c∈certificate1118.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3967,MergedCutCells.Batch330.certificate3968], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3967,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3968,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1118 : ∀ c∈certificate1118.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3967,MergedCutCells.Batch330.certificate3968], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3967,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3968,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1118 : ∀ c∈certificate1118.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3967,MergedCutCells.Batch330.certificate3968], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1118 : ∀ c∈certificate1118.cells, c.population=certificate1118.population := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3967,MergedCutCells.Batch330.certificate3968], c.population=PopulationCertificates.Batch037.certificate745
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1118 {x : ℝ} (hx : certificate1118.interval.Contains x) : ∃ c∈certificate1118.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1118 numericValid1118 hx

def certificate1119 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate746,PopulationCertificates.Batch037.certificate746,[MergedCutCells.Batch330.certificate3969,MergedCutCells.Batch330.certificate3970],(72316638492406341/125000000000000000),(some (576660851/500000000)),(1/2),(79889053884129911/1000000000000000000),(some (67898642032214797/1000000000000000000)),(some (6330422656540923/500000000000000000))⟩
theorem numericValid1119 : certificate1119.NumericValid := by decide +kernel
theorem cellsSound1119 : ∀ c∈certificate1119.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3969,MergedCutCells.Batch330.certificate3970], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3970,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1119 : ∀ c∈certificate1119.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3969,MergedCutCells.Batch330.certificate3970], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3970,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1119 : ∀ c∈certificate1119.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3969,MergedCutCells.Batch330.certificate3970], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid374,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid374,List.forall_mem_nil _⟩⟩
theorem populationMatches1119 : ∀ c∈certificate1119.cells, c.population=certificate1119.population := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3969,MergedCutCells.Batch330.certificate3970], c.population=PopulationCertificates.Batch037.certificate746
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1119 {x : ℝ} (hx : certificate1119.interval.Contains x) : ∃ c∈certificate1119.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1119 numericValid1119 hx

def certificate1120 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate746,PopulationCertificates.Batch037.certificate746,[MergedCutCells.Batch330.certificate3971,MergedCutCells.Batch331.certificate3972,MergedCutCells.Batch331.certificate3973],(576660851/500000000),none,(1/2),(18746814732047831/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1120 : certificate1120.NumericValid := by decide +kernel
theorem cellsSound1120 : ∀ c∈certificate1120.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3971,MergedCutCells.Batch331.certificate3972,MergedCutCells.Batch331.certificate3973], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.sound3971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3972,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3973,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1120 : ∀ c∈certificate1120.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3971,MergedCutCells.Batch331.certificate3972,MergedCutCells.Batch331.certificate3973], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch330.numericValid3971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3972,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3973,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1120 : ∀ c∈certificate1120.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3971,MergedCutCells.Batch331.certificate3972,MergedCutCells.Batch331.certificate3973], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1120 : ∀ c∈certificate1120.cells, c.population=certificate1120.population := by
  change ∀ c∈[MergedCutCells.Batch330.certificate3971,MergedCutCells.Batch331.certificate3972,MergedCutCells.Batch331.certificate3973], c.population=PopulationCertificates.Batch037.certificate746
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1120 {x : ℝ} (hx : certificate1120.interval.Contains x) : ∃ c∈certificate1120.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1120 numericValid1120 hx

def certificate1121 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate747,PopulationCertificates.Batch037.certificate747,[MergedCutCells.Batch331.certificate3974,MergedCutCells.Batch331.certificate3975],(23405900672940531853/1000000000000000000),none,(1/2),(685641382576796703/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1121 : certificate1121.NumericValid := by decide +kernel
theorem cellsSound1121 : ∀ c∈certificate1121.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3974,MergedCutCells.Batch331.certificate3975], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3974,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3975,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1121 : ∀ c∈certificate1121.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3974,MergedCutCells.Batch331.certificate3975], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3974,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3975,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1121 : ∀ c∈certificate1121.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3974,MergedCutCells.Batch331.certificate3975], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1121 : ∀ c∈certificate1121.cells, c.population=certificate1121.population := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3974,MergedCutCells.Batch331.certificate3975], c.population=PopulationCertificates.Batch037.certificate747
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1121 {x : ℝ} (hx : certificate1121.interval.Contains x) : ∃ c∈certificate1121.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1121 numericValid1121 hx

def certificate1122 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate748,PopulationCertificates.Batch037.certificate748,[MergedCutCells.Batch331.certificate3976,MergedCutCells.Batch331.certificate3977],(290927358553692631/500000000000000000),(some (1130796719/1000000000)),(1/2),(10728924134211243/125000000000000000),(some (1764430414122073/25000000000000000)),(some (13279145817559323/1000000000000000000))⟩
theorem numericValid1122 : certificate1122.NumericValid := by decide +kernel
theorem cellsSound1122 : ∀ c∈certificate1122.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3976,MergedCutCells.Batch331.certificate3977], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3976,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3977,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1122 : ∀ c∈certificate1122.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3976,MergedCutCells.Batch331.certificate3977], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3976,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3977,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1122 : ∀ c∈certificate1122.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3976,MergedCutCells.Batch331.certificate3977], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid375,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid375,List.forall_mem_nil _⟩⟩
theorem populationMatches1122 : ∀ c∈certificate1122.cells, c.population=certificate1122.population := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3976,MergedCutCells.Batch331.certificate3977], c.population=PopulationCertificates.Batch037.certificate748
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1122 {x : ℝ} (hx : certificate1122.interval.Contains x) : ∃ c∈certificate1122.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1122 numericValid1122 hx

def certificate1123 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate748,PopulationCertificates.Batch037.certificate748,[MergedCutCells.Batch331.certificate3978,MergedCutCells.Batch331.certificate3979,MergedCutCells.Batch331.certificate3980,MergedCutCells.Batch331.certificate3981],(1130796719/1000000000),none,(1/2),(80594059419547973/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1123 : certificate1123.NumericValid := by decide +kernel
theorem cellsSound1123 : ∀ c∈certificate1123.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3978,MergedCutCells.Batch331.certificate3979,MergedCutCells.Batch331.certificate3980,MergedCutCells.Batch331.certificate3981], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3978,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3979,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3980,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3981,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1123 : ∀ c∈certificate1123.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3978,MergedCutCells.Batch331.certificate3979,MergedCutCells.Batch331.certificate3980,MergedCutCells.Batch331.certificate3981], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3978,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3979,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3980,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3981,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1123 : ∀ c∈certificate1123.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3978,MergedCutCells.Batch331.certificate3979,MergedCutCells.Batch331.certificate3980,MergedCutCells.Batch331.certificate3981], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1123 : ∀ c∈certificate1123.cells, c.population=certificate1123.population := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3978,MergedCutCells.Batch331.certificate3979,MergedCutCells.Batch331.certificate3980,MergedCutCells.Batch331.certificate3981], c.population=PopulationCertificates.Batch037.certificate748
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1123 {x : ℝ} (hx : certificate1123.interval.Contains x) : ∃ c∈certificate1123.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1123 numericValid1123 hx

def certificate1124 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate749,PopulationCertificates.Batch037.certificate749,[MergedCutCells.Batch331.certificate3982,MergedCutCells.Batch331.certificate3983],(2366603828322453309/100000000000000000),none,(1/2),(6988815413757728779/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1124 : certificate1124.NumericValid := by decide +kernel
theorem cellsSound1124 : ∀ c∈certificate1124.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3982,MergedCutCells.Batch331.certificate3983], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3982,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.sound3983,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1124 : ∀ c∈certificate1124.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3982,MergedCutCells.Batch331.certificate3983], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3982,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch331.numericValid3983,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1124 : ∀ c∈certificate1124.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3982,MergedCutCells.Batch331.certificate3983], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1124 : ∀ c∈certificate1124.cells, c.population=certificate1124.population := by
  change ∀ c∈[MergedCutCells.Batch331.certificate3982,MergedCutCells.Batch331.certificate3983], c.population=PopulationCertificates.Batch037.certificate749
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1124 {x : ℝ} (hx : certificate1124.interval.Contains x) : ∃ c∈certificate1124.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1124 numericValid1124 hx

def certificate1125 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate750,PopulationCertificates.Batch037.certificate750,[MergedCutCells.Batch332.certificate3984,MergedCutCells.Batch332.certificate3985],(585370505487193749/1000000000000000000),(some (284165261/250000000)),(1/2),(11499422722046427/125000000000000000),(some (36866366864542987/500000000000000000)),(some (14016319432755097/1000000000000000000))⟩
theorem numericValid1125 : certificate1125.NumericValid := by decide +kernel
theorem cellsSound1125 : ∀ c∈certificate1125.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3984,MergedCutCells.Batch332.certificate3985], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3984,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3985,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1125 : ∀ c∈certificate1125.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3984,MergedCutCells.Batch332.certificate3985], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3984,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3985,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1125 : ∀ c∈certificate1125.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3984,MergedCutCells.Batch332.certificate3985], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid376,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid376,List.forall_mem_nil _⟩⟩
theorem populationMatches1125 : ∀ c∈certificate1125.cells, c.population=certificate1125.population := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3984,MergedCutCells.Batch332.certificate3985], c.population=PopulationCertificates.Batch037.certificate750
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1125 {x : ℝ} (hx : certificate1125.interval.Contains x) : ∃ c∈certificate1125.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1125 numericValid1125 hx

def certificate1126 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate750,PopulationCertificates.Batch037.certificate750,[MergedCutCells.Batch332.certificate3986,MergedCutCells.Batch332.certificate3987,MergedCutCells.Batch332.certificate3988],(284165261/250000000),none,(1/2),(86337452102628693/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1126 : certificate1126.NumericValid := by decide +kernel
theorem cellsSound1126 : ∀ c∈certificate1126.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3986,MergedCutCells.Batch332.certificate3987,MergedCutCells.Batch332.certificate3988], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3986,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3987,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3988,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1126 : ∀ c∈certificate1126.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3986,MergedCutCells.Batch332.certificate3987,MergedCutCells.Batch332.certificate3988], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3986,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3987,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3988,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1126 : ∀ c∈certificate1126.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3986,MergedCutCells.Batch332.certificate3987,MergedCutCells.Batch332.certificate3988], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1126 : ∀ c∈certificate1126.cells, c.population=certificate1126.population := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3986,MergedCutCells.Batch332.certificate3987,MergedCutCells.Batch332.certificate3988], c.population=PopulationCertificates.Batch037.certificate750
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1126 {x : ℝ} (hx : certificate1126.interval.Contains x) : ∃ c∈certificate1126.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1126 numericValid1126 hx

def certificate1127 : RatCutGroup := ⟨GeometryCertificates.Batch037.certificate751,PopulationCertificates.Batch037.certificate751,[MergedCutCells.Batch332.certificate3989,MergedCutCells.Batch332.certificate3990],(23933415582803348961/1000000000000000000),none,(1/2),(7124605551781344497/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1127 : certificate1127.NumericValid := by decide +kernel
theorem cellsSound1127 : ∀ c∈certificate1127.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3989,MergedCutCells.Batch332.certificate3990], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.sound3990,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1127 : ∀ c∈certificate1127.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3989,MergedCutCells.Batch332.certificate3990], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch332.numericValid3990,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1127 : ∀ c∈certificate1127.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3989,MergedCutCells.Batch332.certificate3990], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1127 : ∀ c∈certificate1127.cells, c.population=certificate1127.population := by
  change ∀ c∈[MergedCutCells.Batch332.certificate3989,MergedCutCells.Batch332.certificate3990], c.population=PopulationCertificates.Batch037.certificate751
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1127 {x : ℝ} (hx : certificate1127.interval.Contains x) : ∃ c∈certificate1127.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1127 numericValid1127 hx

end Cycle12.MergedCutGroups.Batch093
