import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch011
import Cycle12.MergedCutCells.Batch112
import Cycle12.MergedCutCells.Batch113
import Cycle12.MergedCutCells.Batch114
import Cycle12.MergedCutCells.Batch115
import Cycle12.MergedCutCells.Batch116
import Cycle12.PopulationCertificates.Batch011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch029

def certificate348 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate232,PopulationCertificates.Batch011.certificate232,[MergedCutCells.Batch112.certificate1354,MergedCutCells.Batch112.certificate1355,MergedCutCells.Batch113.certificate1356,MergedCutCells.Batch113.certificate1357,MergedCutCells.Batch113.certificate1358,MergedCutCells.Batch113.certificate1359],(443989775251555199/500000000000000000),(some 64),(1/2),(699726419879498577/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (296236711591295629/200000000000000000))⟩
theorem numericValid348 : certificate348.NumericValid := by decide +kernel
theorem cellsSound348 : ∀ c∈certificate348.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1354,MergedCutCells.Batch112.certificate1355,MergedCutCells.Batch113.certificate1356,MergedCutCells.Batch113.certificate1357,MergedCutCells.Batch113.certificate1358,MergedCutCells.Batch113.certificate1359], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1354,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1355,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1357,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1359,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric348 : ∀ c∈certificate348.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1354,MergedCutCells.Batch112.certificate1355,MergedCutCells.Batch113.certificate1356,MergedCutCells.Batch113.certificate1357,MergedCutCells.Batch113.certificate1358,MergedCutCells.Batch113.certificate1359], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1354,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1355,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1357,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1359,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid348 : ∀ c∈certificate348.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1354,MergedCutCells.Batch112.certificate1355,MergedCutCells.Batch113.certificate1356,MergedCutCells.Batch113.certificate1357,MergedCutCells.Batch113.certificate1358,MergedCutCells.Batch113.certificate1359], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid117,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid117,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid117,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid117,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid117,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid117,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches348 : ∀ c∈certificate348.cells, c.population=certificate348.population := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1354,MergedCutCells.Batch112.certificate1355,MergedCutCells.Batch113.certificate1356,MergedCutCells.Batch113.certificate1357,MergedCutCells.Batch113.certificate1358,MergedCutCells.Batch113.certificate1359], c.population=PopulationCertificates.Batch011.certificate232
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers348 {x : ℝ} (hx : certificate348.interval.Contains x) : ∃ c∈certificate348.cells, c.region.interval.Contains x := rat_cut_group_covers certificate348 numericValid348 hx

def certificate349 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate232,PopulationCertificates.Batch011.certificate232,[MergedCutCells.Batch113.certificate1360],64,none,(1/2),(1636741103750856619/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid349 : certificate349.NumericValid := by decide +kernel
theorem cellsSound349 : ∀ c∈certificate349.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1360], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1360,List.forall_mem_nil _⟩
theorem cellsNumeric349 : ∀ c∈certificate349.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1360], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1360,List.forall_mem_nil _⟩
theorem cellsEntropyValid349 : ∀ c∈certificate349.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1360], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches349 : ∀ c∈certificate349.cells, c.population=certificate349.population := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1360], c.population=PopulationCertificates.Batch011.certificate232
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers349 {x : ℝ} (hx : certificate349.interval.Contains x) : ∃ c∈certificate349.cells, c.region.interval.Contains x := rat_cut_group_covers certificate349 numericValid349 hx

def certificate350 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate233,PopulationCertificates.Batch011.certificate233,[MergedCutCells.Batch113.certificate1361,MergedCutCells.Batch113.certificate1362,MergedCutCells.Batch113.certificate1363],(1791724087690645273/500000000000000000),none,(1/2),(880241268733759029/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid350 : certificate350.NumericValid := by decide +kernel
theorem cellsSound350 : ∀ c∈certificate350.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1361,MergedCutCells.Batch113.certificate1362,MergedCutCells.Batch113.certificate1363], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1362,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1363,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric350 : ∀ c∈certificate350.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1361,MergedCutCells.Batch113.certificate1362,MergedCutCells.Batch113.certificate1363], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1362,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1363,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid350 : ∀ c∈certificate350.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1361,MergedCutCells.Batch113.certificate1362,MergedCutCells.Batch113.certificate1363], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches350 : ∀ c∈certificate350.cells, c.population=certificate350.population := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1361,MergedCutCells.Batch113.certificate1362,MergedCutCells.Batch113.certificate1363], c.population=PopulationCertificates.Batch011.certificate233
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers350 {x : ℝ} (hx : certificate350.interval.Contains x) : ∃ c∈certificate350.cells, c.region.interval.Contains x := rat_cut_group_covers certificate350 numericValid350 hx

def certificate351 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate234,PopulationCertificates.Batch011.certificate234,[MergedCutCells.Batch113.certificate1364,MergedCutCells.Batch113.certificate1365,MergedCutCells.Batch113.certificate1366,MergedCutCells.Batch113.certificate1367,MergedCutCells.Batch114.certificate1368,MergedCutCells.Batch114.certificate1369],(435864302863164401/500000000000000000),(some 64),(1/2),(179691402478158357/250000000000000000),(some (69314718055994531/100000000000000000)),(some (740824507963772581/500000000000000000))⟩
theorem numericValid351 : certificate351.NumericValid := by decide +kernel
theorem cellsSound351 : ∀ c∈certificate351.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1364,MergedCutCells.Batch113.certificate1365,MergedCutCells.Batch113.certificate1366,MergedCutCells.Batch113.certificate1367,MergedCutCells.Batch114.certificate1368,MergedCutCells.Batch114.certificate1369], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1365,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1366,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.sound1367,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1369,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric351 : ∀ c∈certificate351.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1364,MergedCutCells.Batch113.certificate1365,MergedCutCells.Batch113.certificate1366,MergedCutCells.Batch113.certificate1367,MergedCutCells.Batch114.certificate1368,MergedCutCells.Batch114.certificate1369], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1365,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1366,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch113.numericValid1367,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1369,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid351 : ∀ c∈certificate351.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1364,MergedCutCells.Batch113.certificate1365,MergedCutCells.Batch113.certificate1366,MergedCutCells.Batch113.certificate1367,MergedCutCells.Batch114.certificate1368,MergedCutCells.Batch114.certificate1369], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid118,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid118,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid118,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid118,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid118,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid118,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches351 : ∀ c∈certificate351.cells, c.population=certificate351.population := by
  change ∀ c∈[MergedCutCells.Batch113.certificate1364,MergedCutCells.Batch113.certificate1365,MergedCutCells.Batch113.certificate1366,MergedCutCells.Batch113.certificate1367,MergedCutCells.Batch114.certificate1368,MergedCutCells.Batch114.certificate1369], c.population=PopulationCertificates.Batch011.certificate234
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers351 {x : ℝ} (hx : certificate351.interval.Contains x) : ∃ c∈certificate351.cells, c.region.interval.Contains x := rat_cut_group_covers certificate351 numericValid351 hx

def certificate352 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate234,PopulationCertificates.Batch011.certificate234,[MergedCutCells.Batch114.certificate1370],64,none,(1/2),(422120379933541429/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid352 : certificate352.NumericValid := by decide +kernel
theorem cellsSound352 : ∀ c∈certificate352.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1370], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1370,List.forall_mem_nil _⟩
theorem cellsNumeric352 : ∀ c∈certificate352.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1370], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1370,List.forall_mem_nil _⟩
theorem cellsEntropyValid352 : ∀ c∈certificate352.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1370], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches352 : ∀ c∈certificate352.cells, c.population=certificate352.population := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1370], c.population=PopulationCertificates.Batch011.certificate234
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers352 {x : ℝ} (hx : certificate352.interval.Contains x) : ∃ c∈certificate352.cells, c.region.interval.Contains x := rat_cut_group_covers certificate352 numericValid352 hx

def certificate353 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate235,PopulationCertificates.Batch011.certificate235,[MergedCutCells.Batch114.certificate1371,MergedCutCells.Batch114.certificate1372,MergedCutCells.Batch114.certificate1373],(3507046356201153171/1000000000000000000),none,(1/2),(784964756550206213/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid353 : certificate353.NumericValid := by decide +kernel
theorem cellsSound353 : ∀ c∈certificate353.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1371,MergedCutCells.Batch114.certificate1372,MergedCutCells.Batch114.certificate1373], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1372,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1373,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric353 : ∀ c∈certificate353.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1371,MergedCutCells.Batch114.certificate1372,MergedCutCells.Batch114.certificate1373], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1372,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1373,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid353 : ∀ c∈certificate353.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1371,MergedCutCells.Batch114.certificate1372,MergedCutCells.Batch114.certificate1373], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches353 : ∀ c∈certificate353.cells, c.population=certificate353.population := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1371,MergedCutCells.Batch114.certificate1372,MergedCutCells.Batch114.certificate1373], c.population=PopulationCertificates.Batch011.certificate235
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers353 {x : ℝ} (hx : certificate353.interval.Contains x) : ∃ c∈certificate353.cells, c.region.interval.Contains x := rat_cut_group_covers certificate353 numericValid353 hx

def certificate354 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate236,PopulationCertificates.Batch011.certificate236,[MergedCutCells.Batch114.certificate1374,MergedCutCells.Batch114.certificate1375,MergedCutCells.Batch114.certificate1376,MergedCutCells.Batch114.certificate1377,MergedCutCells.Batch114.certificate1378,MergedCutCells.Batch114.certificate1379,MergedCutCells.Batch115.certificate1380,MergedCutCells.Batch115.certificate1381],(850165604323558663/1000000000000000000),(some 64),(1/2),(740791569271963277/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1480787779058735909/1000000000000000000))⟩
theorem numericValid354 : certificate354.NumericValid := by decide +kernel
theorem cellsSound354 : ∀ c∈certificate354.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1374,MergedCutCells.Batch114.certificate1375,MergedCutCells.Batch114.certificate1376,MergedCutCells.Batch114.certificate1377,MergedCutCells.Batch114.certificate1378,MergedCutCells.Batch114.certificate1379,MergedCutCells.Batch115.certificate1380,MergedCutCells.Batch115.certificate1381], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1375,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1377,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1378,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.sound1379,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1380,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1381,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric354 : ∀ c∈certificate354.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1374,MergedCutCells.Batch114.certificate1375,MergedCutCells.Batch114.certificate1376,MergedCutCells.Batch114.certificate1377,MergedCutCells.Batch114.certificate1378,MergedCutCells.Batch114.certificate1379,MergedCutCells.Batch115.certificate1380,MergedCutCells.Batch115.certificate1381], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1375,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1377,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1378,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch114.numericValid1379,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1380,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1381,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid354 : ∀ c∈certificate354.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1374,MergedCutCells.Batch114.certificate1375,MergedCutCells.Batch114.certificate1376,MergedCutCells.Batch114.certificate1377,MergedCutCells.Batch114.certificate1378,MergedCutCells.Batch114.certificate1379,MergedCutCells.Batch115.certificate1380,MergedCutCells.Batch115.certificate1381], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid119,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid119,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid119,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid119,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid119,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid119,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid119,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid119,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches354 : ∀ c∈certificate354.cells, c.population=certificate354.population := by
  change ∀ c∈[MergedCutCells.Batch114.certificate1374,MergedCutCells.Batch114.certificate1375,MergedCutCells.Batch114.certificate1376,MergedCutCells.Batch114.certificate1377,MergedCutCells.Batch114.certificate1378,MergedCutCells.Batch114.certificate1379,MergedCutCells.Batch115.certificate1380,MergedCutCells.Batch115.certificate1381], c.population=PopulationCertificates.Batch011.certificate236
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers354 {x : ℝ} (hx : certificate354.interval.Contains x) : ∃ c∈certificate354.cells, c.region.interval.Contains x := rat_cut_group_covers certificate354 numericValid354 hx

def certificate355 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate236,PopulationCertificates.Batch011.certificate236,[MergedCutCells.Batch115.certificate1382],64,none,(1/2),(1747392802354346527/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid355 : certificate355.NumericValid := by decide +kernel
theorem cellsSound355 : ∀ c∈certificate355.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1382], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1382,List.forall_mem_nil _⟩
theorem cellsNumeric355 : ∀ c∈certificate355.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1382], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1382,List.forall_mem_nil _⟩
theorem cellsEntropyValid355 : ∀ c∈certificate355.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1382], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches355 : ∀ c∈certificate355.cells, c.population=certificate355.population := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1382], c.population=PopulationCertificates.Batch011.certificate236
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers355 {x : ℝ} (hx : certificate355.interval.Contains x) : ∃ c∈certificate355.cells, c.region.interval.Contains x := rat_cut_group_covers certificate355 numericValid355 hx

def certificate356 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate237,PopulationCertificates.Batch011.certificate237,[MergedCutCells.Batch115.certificate1383,MergedCutCells.Batch115.certificate1384,MergedCutCells.Batch115.certificate1385],(3510763974248104549/1000000000000000000),none,(1/2),(804082026019454493/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid356 : certificate356.NumericValid := by decide +kernel
theorem cellsSound356 : ∀ c∈certificate356.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1383,MergedCutCells.Batch115.certificate1384,MergedCutCells.Batch115.certificate1385], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1385,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric356 : ∀ c∈certificate356.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1383,MergedCutCells.Batch115.certificate1384,MergedCutCells.Batch115.certificate1385], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1385,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid356 : ∀ c∈certificate356.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1383,MergedCutCells.Batch115.certificate1384,MergedCutCells.Batch115.certificate1385], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches356 : ∀ c∈certificate356.cells, c.population=certificate356.population := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1383,MergedCutCells.Batch115.certificate1384,MergedCutCells.Batch115.certificate1385], c.population=PopulationCertificates.Batch011.certificate237
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers356 {x : ℝ} (hx : certificate356.interval.Contains x) : ∃ c∈certificate356.cells, c.region.interval.Contains x := rat_cut_group_covers certificate356 numericValid356 hx

def certificate357 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate238,PopulationCertificates.Batch011.certificate238,[MergedCutCells.Batch115.certificate1386,MergedCutCells.Batch115.certificate1387,MergedCutCells.Batch115.certificate1388,MergedCutCells.Batch115.certificate1389,MergedCutCells.Batch115.certificate1390,MergedCutCells.Batch115.certificate1391,MergedCutCells.Batch116.certificate1392,MergedCutCells.Batch116.certificate1393],(414714105513335847/500000000000000000),(some 64),(1/2),(77812086429377973/125000000000000000),(some (69314718055994531/100000000000000000)),(some (748184312536576973/500000000000000000))⟩
theorem numericValid357 : certificate357.NumericValid := by decide +kernel
theorem cellsSound357 : ∀ c∈certificate357.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1386,MergedCutCells.Batch115.certificate1387,MergedCutCells.Batch115.certificate1388,MergedCutCells.Batch115.certificate1389,MergedCutCells.Batch115.certificate1390,MergedCutCells.Batch115.certificate1391,MergedCutCells.Batch116.certificate1392,MergedCutCells.Batch116.certificate1393], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1386,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1387,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1388,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1389,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1390,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.sound1391,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1392,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1393,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric357 : ∀ c∈certificate357.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1386,MergedCutCells.Batch115.certificate1387,MergedCutCells.Batch115.certificate1388,MergedCutCells.Batch115.certificate1389,MergedCutCells.Batch115.certificate1390,MergedCutCells.Batch115.certificate1391,MergedCutCells.Batch116.certificate1392,MergedCutCells.Batch116.certificate1393], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1386,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1387,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1388,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1389,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1390,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch115.numericValid1391,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1392,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1393,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid357 : ∀ c∈certificate357.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1386,MergedCutCells.Batch115.certificate1387,MergedCutCells.Batch115.certificate1388,MergedCutCells.Batch115.certificate1389,MergedCutCells.Batch115.certificate1390,MergedCutCells.Batch115.certificate1391,MergedCutCells.Batch116.certificate1392,MergedCutCells.Batch116.certificate1393], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid120,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid120,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid120,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid120,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid120,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid120,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid120,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid120,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches357 : ∀ c∈certificate357.cells, c.population=certificate357.population := by
  change ∀ c∈[MergedCutCells.Batch115.certificate1386,MergedCutCells.Batch115.certificate1387,MergedCutCells.Batch115.certificate1388,MergedCutCells.Batch115.certificate1389,MergedCutCells.Batch115.certificate1390,MergedCutCells.Batch115.certificate1391,MergedCutCells.Batch116.certificate1392,MergedCutCells.Batch116.certificate1393], c.population=PopulationCertificates.Batch011.certificate238
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers357 {x : ℝ} (hx : certificate357.interval.Contains x) : ∃ c∈certificate357.cells, c.region.interval.Contains x := rat_cut_group_covers certificate357 numericValid357 hx

def certificate358 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate238,PopulationCertificates.Batch011.certificate238,[MergedCutCells.Batch116.certificate1394],64,none,(1/2),(325390068519892097/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid358 : certificate358.NumericValid := by decide +kernel
theorem cellsSound358 : ∀ c∈certificate358.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1394], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1394,List.forall_mem_nil _⟩
theorem cellsNumeric358 : ∀ c∈certificate358.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1394], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1394,List.forall_mem_nil _⟩
theorem cellsEntropyValid358 : ∀ c∈certificate358.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1394], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches358 : ∀ c∈certificate358.cells, c.population=certificate358.population := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1394], c.population=PopulationCertificates.Batch011.certificate238
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers358 {x : ℝ} (hx : certificate358.interval.Contains x) : ∃ c∈certificate358.cells, c.region.interval.Contains x := rat_cut_group_covers certificate358 numericValid358 hx

def certificate359 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate239,PopulationCertificates.Batch011.certificate239,[MergedCutCells.Batch116.certificate1395,MergedCutCells.Batch116.certificate1396,MergedCutCells.Batch116.certificate1397],(1791367052134145021/500000000000000000),none,(1/2),(793958583807975279/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid359 : certificate359.NumericValid := by decide +kernel
theorem cellsSound359 : ∀ c∈certificate359.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1395,MergedCutCells.Batch116.certificate1396,MergedCutCells.Batch116.certificate1397], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1395,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.sound1397,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric359 : ∀ c∈certificate359.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1395,MergedCutCells.Batch116.certificate1396,MergedCutCells.Batch116.certificate1397], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1395,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch116.numericValid1397,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid359 : ∀ c∈certificate359.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1395,MergedCutCells.Batch116.certificate1396,MergedCutCells.Batch116.certificate1397], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches359 : ∀ c∈certificate359.cells, c.population=certificate359.population := by
  change ∀ c∈[MergedCutCells.Batch116.certificate1395,MergedCutCells.Batch116.certificate1396,MergedCutCells.Batch116.certificate1397], c.population=PopulationCertificates.Batch011.certificate239
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers359 {x : ℝ} (hx : certificate359.interval.Contains x) : ∃ c∈certificate359.cells, c.region.interval.Contains x := rat_cut_group_covers certificate359 numericValid359 hx

end Cycle12.MergedCutGroups.Batch029
