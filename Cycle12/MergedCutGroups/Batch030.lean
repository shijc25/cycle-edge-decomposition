import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch012
import Cycle12.MergedCutCells.Batch116
import Cycle12.MergedCutCells.Batch117
import Cycle12.MergedCutCells.Batch118
import Cycle12.MergedCutCells.Batch119
import Cycle12.MergedCutCells.Batch120
import Cycle12.PopulationCertificates.Batch012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch030

def certificate360 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate240,PopulationCertificates.Batch012.certificate240,[MergedCutCells.Batch116.certificate1398,MergedCutCells.Batch116.certificate1399,MergedCutCells.Batch116.certificate1400,MergedCutCells.Batch116.certificate1401,MergedCutCells.Batch116.certificate1402,MergedCutCells.Batch116.certificate1403,MergedCutCells.Batch117.certificate1404],(845495122562524397/1000000000000000000),(some 64),(1/2),(660604096842328519/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1493605175801107597/1000000000000000000))⟩
theorem numericValid360 : certificate360.NumericValid := by decide +kernel
theorem cellsSound360 : ∀ c∈certificate360.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1398,MergedCutCells.Batch116.certificate1399,MergedCutCells.Batch116.certificate1400,MergedCutCells.Batch116.certificate1401,MergedCutCells.Batch116.certificate1402,MergedCutCells.Batch116.certificate1403,MergedCutCells.Batch117.certificate1404], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1398,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1399,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1400,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1401,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1402,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1403,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1404,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric360 : ∀ c∈certificate360.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1398,MergedCutCells.Batch116.certificate1399,MergedCutCells.Batch116.certificate1400,MergedCutCells.Batch116.certificate1401,MergedCutCells.Batch116.certificate1402,MergedCutCells.Batch116.certificate1403,MergedCutCells.Batch117.certificate1404], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1398,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1399,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1400,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1401,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1402,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1403,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1404,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid360 : ∀ c∈certificate360.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1398,MergedCutCells.Batch116.certificate1399,MergedCutCells.Batch116.certificate1400,MergedCutCells.Batch116.certificate1401,MergedCutCells.Batch116.certificate1402,MergedCutCells.Batch116.certificate1403,MergedCutCells.Batch117.certificate1404], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid121,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid121,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid121,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid121,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid121,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid121,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid121,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches360 : ∀ c∈certificate360.cells, c.population=certificate360.population := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1398,MergedCutCells.Batch116.certificate1399,MergedCutCells.Batch116.certificate1400,MergedCutCells.Batch116.certificate1401,MergedCutCells.Batch116.certificate1402,MergedCutCells.Batch116.certificate1403,MergedCutCells.Batch117.certificate1404], c.population=PopulationCertificates.Batch012.certificate240
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers360 {x : ℝ} (hx : certificate360.interval.Contains x) : ∃ c∈certificate360.cells, c.region.interval.Contains x := rat_cut_group_covers certificate360 numericValid360 hx

def certificate361 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate240,PopulationCertificates.Batch012.certificate240,[MergedCutCells.Batch117.certificate1405],64,none,(1/2),(420908776863326023/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid361 : certificate361.NumericValid := by decide +kernel
theorem cellsSound361 : ∀ c∈certificate361.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1405], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1405,List.forall_mem_nil _⟩
theorem cellsNumeric361 : ∀ c∈certificate361.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1405], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1405,List.forall_mem_nil _⟩
theorem cellsEntropyValid361 : ∀ c∈certificate361.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1405], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches361 : ∀ c∈certificate361.cells, c.population=certificate361.population := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1405], c.population=PopulationCertificates.Batch012.certificate240
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers361 {x : ℝ} (hx : certificate361.interval.Contains x) : ∃ c∈certificate361.cells, c.region.interval.Contains x := rat_cut_group_covers certificate361 numericValid361 hx

def certificate362 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate241,PopulationCertificates.Batch012.certificate241,[MergedCutCells.Batch117.certificate1406,MergedCutCells.Batch117.certificate1407,MergedCutCells.Batch117.certificate1408,MergedCutCells.Batch117.certificate1409],(3598277792004977133/1000000000000000000),none,(1/2),(42794778128742233/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid362 : certificate362.NumericValid := by decide +kernel
theorem cellsSound362 : ∀ c∈certificate362.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1406,MergedCutCells.Batch117.certificate1407,MergedCutCells.Batch117.certificate1408,MergedCutCells.Batch117.certificate1409], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1406,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1408,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1409,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric362 : ∀ c∈certificate362.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1406,MergedCutCells.Batch117.certificate1407,MergedCutCells.Batch117.certificate1408,MergedCutCells.Batch117.certificate1409], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1406,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1408,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1409,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid362 : ∀ c∈certificate362.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1406,MergedCutCells.Batch117.certificate1407,MergedCutCells.Batch117.certificate1408,MergedCutCells.Batch117.certificate1409], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches362 : ∀ c∈certificate362.cells, c.population=certificate362.population := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1406,MergedCutCells.Batch117.certificate1407,MergedCutCells.Batch117.certificate1408,MergedCutCells.Batch117.certificate1409], c.population=PopulationCertificates.Batch012.certificate241
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers362 {x : ℝ} (hx : certificate362.interval.Contains x) : ∃ c∈certificate362.cells, c.region.interval.Contains x := rat_cut_group_covers certificate362 numericValid362 hx

def certificate363 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate242,PopulationCertificates.Batch012.certificate242,[MergedCutCells.Batch117.certificate1410,MergedCutCells.Batch117.certificate1411,MergedCutCells.Batch117.certificate1412,MergedCutCells.Batch117.certificate1413,MergedCutCells.Batch117.certificate1414,MergedCutCells.Batch117.certificate1415,MergedCutCells.Batch118.certificate1416],(106401079830983311/125000000000000000),(some 64),(1/2),(686574756530537259/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (93482652549381927/62500000000000000))⟩
theorem numericValid363 : certificate363.NumericValid := by decide +kernel
theorem cellsSound363 : ∀ c∈certificate363.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1410,MergedCutCells.Batch117.certificate1411,MergedCutCells.Batch117.certificate1412,MergedCutCells.Batch117.certificate1413,MergedCutCells.Batch117.certificate1414,MergedCutCells.Batch117.certificate1415,MergedCutCells.Batch118.certificate1416], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1410,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1411,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1413,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1414,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.sound1415,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1416,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric363 : ∀ c∈certificate363.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1410,MergedCutCells.Batch117.certificate1411,MergedCutCells.Batch117.certificate1412,MergedCutCells.Batch117.certificate1413,MergedCutCells.Batch117.certificate1414,MergedCutCells.Batch117.certificate1415,MergedCutCells.Batch118.certificate1416], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1410,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1411,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1413,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1414,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch117.numericValid1415,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1416,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid363 : ∀ c∈certificate363.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1410,MergedCutCells.Batch117.certificate1411,MergedCutCells.Batch117.certificate1412,MergedCutCells.Batch117.certificate1413,MergedCutCells.Batch117.certificate1414,MergedCutCells.Batch117.certificate1415,MergedCutCells.Batch118.certificate1416], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid122,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid122,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid122,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid122,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid122,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid122,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid122,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches363 : ∀ c∈certificate363.cells, c.population=certificate363.population := by
  change ∀ c∈[MergedCutCells.Batch117.certificate1410,MergedCutCells.Batch117.certificate1411,MergedCutCells.Batch117.certificate1412,MergedCutCells.Batch117.certificate1413,MergedCutCells.Batch117.certificate1414,MergedCutCells.Batch117.certificate1415,MergedCutCells.Batch118.certificate1416], c.population=PopulationCertificates.Batch012.certificate242
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers363 {x : ℝ} (hx : certificate363.interval.Contains x) : ∃ c∈certificate363.cells, c.region.interval.Contains x := rat_cut_group_covers certificate363 numericValid363 hx

def certificate364 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate242,PopulationCertificates.Batch012.certificate242,[MergedCutCells.Batch118.certificate1417],64,none,(1/2),(343549276854151879/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid364 : certificate364.NumericValid := by decide +kernel
theorem cellsSound364 : ∀ c∈certificate364.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1417], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1417,List.forall_mem_nil _⟩
theorem cellsNumeric364 : ∀ c∈certificate364.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1417], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1417,List.forall_mem_nil _⟩
theorem cellsEntropyValid364 : ∀ c∈certificate364.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1417], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches364 : ∀ c∈certificate364.cells, c.population=certificate364.population := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1417], c.population=PopulationCertificates.Batch012.certificate242
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers364 {x : ℝ} (hx : certificate364.interval.Contains x) : ∃ c∈certificate364.cells, c.region.interval.Contains x := rat_cut_group_covers certificate364 numericValid364 hx

def certificate365 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate243,PopulationCertificates.Batch012.certificate243,[MergedCutCells.Batch118.certificate1418,MergedCutCells.Batch118.certificate1419,MergedCutCells.Batch118.certificate1420,MergedCutCells.Batch118.certificate1421],(359579035586901193/100000000000000000),none,(1/2),(877594560183732551/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid365 : certificate365.NumericValid := by decide +kernel
theorem cellsSound365 : ∀ c∈certificate365.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1418,MergedCutCells.Batch118.certificate1419,MergedCutCells.Batch118.certificate1420,MergedCutCells.Batch118.certificate1421], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1418,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1419,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1420,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1421,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric365 : ∀ c∈certificate365.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1418,MergedCutCells.Batch118.certificate1419,MergedCutCells.Batch118.certificate1420,MergedCutCells.Batch118.certificate1421], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1418,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1419,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1420,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1421,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid365 : ∀ c∈certificate365.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1418,MergedCutCells.Batch118.certificate1419,MergedCutCells.Batch118.certificate1420,MergedCutCells.Batch118.certificate1421], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches365 : ∀ c∈certificate365.cells, c.population=certificate365.population := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1418,MergedCutCells.Batch118.certificate1419,MergedCutCells.Batch118.certificate1420,MergedCutCells.Batch118.certificate1421], c.population=PopulationCertificates.Batch012.certificate243
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers365 {x : ℝ} (hx : certificate365.interval.Contains x) : ∃ c∈certificate365.cells, c.region.interval.Contains x := rat_cut_group_covers certificate365 numericValid365 hx

def certificate366 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate244,PopulationCertificates.Batch012.certificate244,[MergedCutCells.Batch118.certificate1422,MergedCutCells.Batch118.certificate1423,MergedCutCells.Batch118.certificate1424,MergedCutCells.Batch118.certificate1425,MergedCutCells.Batch118.certificate1426,MergedCutCells.Batch118.certificate1427,MergedCutCells.Batch119.certificate1428,MergedCutCells.Batch119.certificate1429],(425061427235076229/500000000000000000),(some 64),(1/2),(404694452666587433/500000000000000000),(some (69314718055994531/100000000000000000)),(some (1493150539088580797/1000000000000000000))⟩
theorem numericValid366 : certificate366.NumericValid := by decide +kernel
theorem cellsSound366 : ∀ c∈certificate366.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1422,MergedCutCells.Batch118.certificate1423,MergedCutCells.Batch118.certificate1424,MergedCutCells.Batch118.certificate1425,MergedCutCells.Batch118.certificate1426,MergedCutCells.Batch118.certificate1427,MergedCutCells.Batch119.certificate1428,MergedCutCells.Batch119.certificate1429], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1422,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1423,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1424,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1426,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.sound1427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1428,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1429,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric366 : ∀ c∈certificate366.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1422,MergedCutCells.Batch118.certificate1423,MergedCutCells.Batch118.certificate1424,MergedCutCells.Batch118.certificate1425,MergedCutCells.Batch118.certificate1426,MergedCutCells.Batch118.certificate1427,MergedCutCells.Batch119.certificate1428,MergedCutCells.Batch119.certificate1429], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1422,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1423,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1424,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1426,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch118.numericValid1427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1428,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1429,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid366 : ∀ c∈certificate366.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1422,MergedCutCells.Batch118.certificate1423,MergedCutCells.Batch118.certificate1424,MergedCutCells.Batch118.certificate1425,MergedCutCells.Batch118.certificate1426,MergedCutCells.Batch118.certificate1427,MergedCutCells.Batch119.certificate1428,MergedCutCells.Batch119.certificate1429], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid123,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid123,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid123,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid123,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid123,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid123,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid123,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid123,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches366 : ∀ c∈certificate366.cells, c.population=certificate366.population := by
  change ∀ c∈[MergedCutCells.Batch118.certificate1422,MergedCutCells.Batch118.certificate1423,MergedCutCells.Batch118.certificate1424,MergedCutCells.Batch118.certificate1425,MergedCutCells.Batch118.certificate1426,MergedCutCells.Batch118.certificate1427,MergedCutCells.Batch119.certificate1428,MergedCutCells.Batch119.certificate1429], c.population=PopulationCertificates.Batch012.certificate244
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers366 {x : ℝ} (hx : certificate366.interval.Contains x) : ∃ c∈certificate366.cells, c.region.interval.Contains x := rat_cut_group_covers certificate366 numericValid366 hx

def certificate367 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate244,PopulationCertificates.Batch012.certificate244,[MergedCutCells.Batch119.certificate1430],64,none,(1/2),(951770363631903977/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid367 : certificate367.NumericValid := by decide +kernel
theorem cellsSound367 : ∀ c∈certificate367.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1430], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1430,List.forall_mem_nil _⟩
theorem cellsNumeric367 : ∀ c∈certificate367.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1430], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1430,List.forall_mem_nil _⟩
theorem cellsEntropyValid367 : ∀ c∈certificate367.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1430], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches367 : ∀ c∈certificate367.cells, c.population=certificate367.population := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1430], c.population=PopulationCertificates.Batch012.certificate244
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers367 {x : ℝ} (hx : certificate367.interval.Contains x) : ∃ c∈certificate367.cells, c.region.interval.Contains x := rat_cut_group_covers certificate367 numericValid367 hx

def certificate368 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate245,PopulationCertificates.Batch012.certificate245,[MergedCutCells.Batch119.certificate1431,MergedCutCells.Batch119.certificate1432,MergedCutCells.Batch119.certificate1433,MergedCutCells.Batch119.certificate1434],(3527585483698771833/1000000000000000000),none,(1/2),(908083238306268317/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid368 : certificate368.NumericValid := by decide +kernel
theorem cellsSound368 : ∀ c∈certificate368.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1431,MergedCutCells.Batch119.certificate1432,MergedCutCells.Batch119.certificate1433,MergedCutCells.Batch119.certificate1434], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1431,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1433,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1434,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric368 : ∀ c∈certificate368.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1431,MergedCutCells.Batch119.certificate1432,MergedCutCells.Batch119.certificate1433,MergedCutCells.Batch119.certificate1434], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1431,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1433,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1434,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid368 : ∀ c∈certificate368.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1431,MergedCutCells.Batch119.certificate1432,MergedCutCells.Batch119.certificate1433,MergedCutCells.Batch119.certificate1434], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches368 : ∀ c∈certificate368.cells, c.population=certificate368.population := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1431,MergedCutCells.Batch119.certificate1432,MergedCutCells.Batch119.certificate1433,MergedCutCells.Batch119.certificate1434], c.population=PopulationCertificates.Batch012.certificate245
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers368 {x : ℝ} (hx : certificate368.interval.Contains x) : ∃ c∈certificate368.cells, c.region.interval.Contains x := rat_cut_group_covers certificate368 numericValid368 hx

def certificate369 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate246,PopulationCertificates.Batch012.certificate246,[MergedCutCells.Batch119.certificate1435,MergedCutCells.Batch119.certificate1436,MergedCutCells.Batch119.certificate1437,MergedCutCells.Batch119.certificate1438,MergedCutCells.Batch119.certificate1439,MergedCutCells.Batch120.certificate1440],(880733450041343617/1000000000000000000),(some 64),(1/2),(3190659987223477/3906250000000000),(some (69314718055994531/100000000000000000)),(some (1498111990263760023/1000000000000000000))⟩
theorem numericValid369 : certificate369.NumericValid := by decide +kernel
theorem cellsSound369 : ∀ c∈certificate369.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1435,MergedCutCells.Batch119.certificate1436,MergedCutCells.Batch119.certificate1437,MergedCutCells.Batch119.certificate1438,MergedCutCells.Batch119.certificate1439,MergedCutCells.Batch120.certificate1440], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1435,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1436,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1437,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.sound1439,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1440,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric369 : ∀ c∈certificate369.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1435,MergedCutCells.Batch119.certificate1436,MergedCutCells.Batch119.certificate1437,MergedCutCells.Batch119.certificate1438,MergedCutCells.Batch119.certificate1439,MergedCutCells.Batch120.certificate1440], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1435,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1436,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1437,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch119.numericValid1439,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1440,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid369 : ∀ c∈certificate369.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1435,MergedCutCells.Batch119.certificate1436,MergedCutCells.Batch119.certificate1437,MergedCutCells.Batch119.certificate1438,MergedCutCells.Batch119.certificate1439,MergedCutCells.Batch120.certificate1440], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid124,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid124,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid124,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid124,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid124,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid124,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches369 : ∀ c∈certificate369.cells, c.population=certificate369.population := by
  change ∀ c∈[MergedCutCells.Batch119.certificate1435,MergedCutCells.Batch119.certificate1436,MergedCutCells.Batch119.certificate1437,MergedCutCells.Batch119.certificate1438,MergedCutCells.Batch119.certificate1439,MergedCutCells.Batch120.certificate1440], c.population=PopulationCertificates.Batch012.certificate246
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers369 {x : ℝ} (hx : certificate369.interval.Contains x) : ∃ c∈certificate369.cells, c.region.interval.Contains x := rat_cut_group_covers certificate369 numericValid369 hx

def certificate370 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate246,PopulationCertificates.Batch012.certificate246,[MergedCutCells.Batch120.certificate1441],64,none,(1/2),(1897718095599499641/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid370 : certificate370.NumericValid := by decide +kernel
theorem cellsSound370 : ∀ c∈certificate370.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1441], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1441,List.forall_mem_nil _⟩
theorem cellsNumeric370 : ∀ c∈certificate370.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1441], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1441,List.forall_mem_nil _⟩
theorem cellsEntropyValid370 : ∀ c∈certificate370.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1441], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches370 : ∀ c∈certificate370.cells, c.population=certificate370.population := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1441], c.population=PopulationCertificates.Batch012.certificate246
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers370 {x : ℝ} (hx : certificate370.interval.Contains x) : ∃ c∈certificate370.cells, c.region.interval.Contains x := rat_cut_group_covers certificate370 numericValid370 hx

def certificate371 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate247,PopulationCertificates.Batch012.certificate247,[MergedCutCells.Batch120.certificate1442,MergedCutCells.Batch120.certificate1443,MergedCutCells.Batch120.certificate1444,MergedCutCells.Batch120.certificate1445],(1765746277517712801/500000000000000000),none,(1/2),(931607308798583453/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid371 : certificate371.NumericValid := by decide +kernel
theorem cellsSound371 : ∀ c∈certificate371.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1442,MergedCutCells.Batch120.certificate1443,MergedCutCells.Batch120.certificate1444,MergedCutCells.Batch120.certificate1445], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1442,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1443,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1444,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1445,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric371 : ∀ c∈certificate371.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1442,MergedCutCells.Batch120.certificate1443,MergedCutCells.Batch120.certificate1444,MergedCutCells.Batch120.certificate1445], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1442,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1443,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1444,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1445,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid371 : ∀ c∈certificate371.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1442,MergedCutCells.Batch120.certificate1443,MergedCutCells.Batch120.certificate1444,MergedCutCells.Batch120.certificate1445], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches371 : ∀ c∈certificate371.cells, c.population=certificate371.population := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1442,MergedCutCells.Batch120.certificate1443,MergedCutCells.Batch120.certificate1444,MergedCutCells.Batch120.certificate1445], c.population=PopulationCertificates.Batch012.certificate247
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers371 {x : ℝ} (hx : certificate371.interval.Contains x) : ∃ c∈certificate371.cells, c.region.interval.Contains x := rat_cut_group_covers certificate371 numericValid371 hx

end Cycle12.MergedCutGroups.Batch030
