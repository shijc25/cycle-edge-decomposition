import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch012
import Cycle12.MergedCutCells.Batch120
import Cycle12.MergedCutCells.Batch121
import Cycle12.MergedCutCells.Batch122
import Cycle12.MergedCutCells.Batch123
import Cycle12.MergedCutCells.Batch124
import Cycle12.PopulationCertificates.Batch012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch031

def certificate372 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate248,PopulationCertificates.Batch012.certificate248,[MergedCutCells.Batch120.certificate1446,MergedCutCells.Batch120.certificate1447,MergedCutCells.Batch120.certificate1448,MergedCutCells.Batch120.certificate1449,MergedCutCells.Batch120.certificate1450,MergedCutCells.Batch120.certificate1451],(894975505182909117/1000000000000000000),(some 64),(1/2),(166701729060973669/200000000000000000),(some (69314718055994531/100000000000000000)),(some (1499826228486390729/1000000000000000000))⟩
theorem numericValid372 : certificate372.NumericValid := by decide +kernel
theorem cellsSound372 : ∀ c∈certificate372.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1446,MergedCutCells.Batch120.certificate1447,MergedCutCells.Batch120.certificate1448,MergedCutCells.Batch120.certificate1449,MergedCutCells.Batch120.certificate1450,MergedCutCells.Batch120.certificate1451], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1446,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1447,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1448,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1449,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1450,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.sound1451,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric372 : ∀ c∈certificate372.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1446,MergedCutCells.Batch120.certificate1447,MergedCutCells.Batch120.certificate1448,MergedCutCells.Batch120.certificate1449,MergedCutCells.Batch120.certificate1450,MergedCutCells.Batch120.certificate1451], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1446,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1447,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1448,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1449,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1450,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch120.numericValid1451,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid372 : ∀ c∈certificate372.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1446,MergedCutCells.Batch120.certificate1447,MergedCutCells.Batch120.certificate1448,MergedCutCells.Batch120.certificate1449,MergedCutCells.Batch120.certificate1450,MergedCutCells.Batch120.certificate1451], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid125,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid125,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid125,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid125,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid125,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid125,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches372 : ∀ c∈certificate372.cells, c.population=certificate372.population := by
  change ∀ c∈[MergedCutCells.Batch120.certificate1446,MergedCutCells.Batch120.certificate1447,MergedCutCells.Batch120.certificate1448,MergedCutCells.Batch120.certificate1449,MergedCutCells.Batch120.certificate1450,MergedCutCells.Batch120.certificate1451], c.population=PopulationCertificates.Batch012.certificate248
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers372 {x : ℝ} (hx : certificate372.interval.Contains x) : ∃ c∈certificate372.cells, c.region.interval.Contains x := rat_cut_group_covers certificate372 numericValid372 hx

def certificate373 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate248,PopulationCertificates.Batch012.certificate248,[MergedCutCells.Batch121.certificate1452],64,none,(1/2),(47768761885576309/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid373 : certificate373.NumericValid := by decide +kernel
theorem cellsSound373 : ∀ c∈certificate373.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1452], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1452,List.forall_mem_nil _⟩
theorem cellsNumeric373 : ∀ c∈certificate373.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1452], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1452,List.forall_mem_nil _⟩
theorem cellsEntropyValid373 : ∀ c∈certificate373.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1452], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches373 : ∀ c∈certificate373.cells, c.population=certificate373.population := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1452], c.population=PopulationCertificates.Batch012.certificate248
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers373 {x : ℝ} (hx : certificate373.interval.Contains x) : ∃ c∈certificate373.cells, c.region.interval.Contains x := rat_cut_group_covers certificate373 numericValid373 hx

def certificate374 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate249,PopulationCertificates.Batch012.certificate249,[MergedCutCells.Batch121.certificate1453,MergedCutCells.Batch121.certificate1454,MergedCutCells.Batch121.certificate1455],(3461659917592212391/1000000000000000000),none,(1/2),(168704926337027551/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid374 : certificate374.NumericValid := by decide +kernel
theorem cellsSound374 : ∀ c∈certificate374.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1453,MergedCutCells.Batch121.certificate1454,MergedCutCells.Batch121.certificate1455], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1454,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1455,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric374 : ∀ c∈certificate374.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1453,MergedCutCells.Batch121.certificate1454,MergedCutCells.Batch121.certificate1455], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1454,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1455,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid374 : ∀ c∈certificate374.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1453,MergedCutCells.Batch121.certificate1454,MergedCutCells.Batch121.certificate1455], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches374 : ∀ c∈certificate374.cells, c.population=certificate374.population := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1453,MergedCutCells.Batch121.certificate1454,MergedCutCells.Batch121.certificate1455], c.population=PopulationCertificates.Batch012.certificate249
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers374 {x : ℝ} (hx : certificate374.interval.Contains x) : ∃ c∈certificate374.cells, c.region.interval.Contains x := rat_cut_group_covers certificate374 numericValid374 hx

def certificate375 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate250,PopulationCertificates.Batch012.certificate250,[MergedCutCells.Batch121.certificate1456,MergedCutCells.Batch121.certificate1457,MergedCutCells.Batch121.certificate1458,MergedCutCells.Batch121.certificate1459,MergedCutCells.Batch121.certificate1460,MergedCutCells.Batch121.certificate1461,MergedCutCells.Batch121.certificate1462],(174283948041443991/200000000000000000),(some 64),(1/2),(84876119725245239/100000000000000000),(some (69314718055994531/100000000000000000)),(some (299773051429710449/200000000000000000))⟩
theorem numericValid375 : certificate375.NumericValid := by decide +kernel
theorem cellsSound375 : ∀ c∈certificate375.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1456,MergedCutCells.Batch121.certificate1457,MergedCutCells.Batch121.certificate1458,MergedCutCells.Batch121.certificate1459,MergedCutCells.Batch121.certificate1460,MergedCutCells.Batch121.certificate1461,MergedCutCells.Batch121.certificate1462], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1456,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1457,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1460,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1461,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1462,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric375 : ∀ c∈certificate375.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1456,MergedCutCells.Batch121.certificate1457,MergedCutCells.Batch121.certificate1458,MergedCutCells.Batch121.certificate1459,MergedCutCells.Batch121.certificate1460,MergedCutCells.Batch121.certificate1461,MergedCutCells.Batch121.certificate1462], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1456,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1457,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1460,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1461,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1462,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid375 : ∀ c∈certificate375.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1456,MergedCutCells.Batch121.certificate1457,MergedCutCells.Batch121.certificate1458,MergedCutCells.Batch121.certificate1459,MergedCutCells.Batch121.certificate1460,MergedCutCells.Batch121.certificate1461,MergedCutCells.Batch121.certificate1462], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid126,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid126,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid126,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid126,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid126,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid126,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid126,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches375 : ∀ c∈certificate375.cells, c.population=certificate375.population := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1456,MergedCutCells.Batch121.certificate1457,MergedCutCells.Batch121.certificate1458,MergedCutCells.Batch121.certificate1459,MergedCutCells.Batch121.certificate1460,MergedCutCells.Batch121.certificate1461,MergedCutCells.Batch121.certificate1462], c.population=PopulationCertificates.Batch012.certificate250
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers375 {x : ℝ} (hx : certificate375.interval.Contains x) : ∃ c∈certificate375.cells, c.region.interval.Contains x := rat_cut_group_covers certificate375 numericValid375 hx

def certificate376 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate250,PopulationCertificates.Batch012.certificate250,[MergedCutCells.Batch121.certificate1463],64,none,(1/2),(122687398448817417/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid376 : certificate376.NumericValid := by decide +kernel
theorem cellsSound376 : ∀ c∈certificate376.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1463], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.sound1463,List.forall_mem_nil _⟩
theorem cellsNumeric376 : ∀ c∈certificate376.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1463], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch121.numericValid1463,List.forall_mem_nil _⟩
theorem cellsEntropyValid376 : ∀ c∈certificate376.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1463], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches376 : ∀ c∈certificate376.cells, c.population=certificate376.population := by
  change ∀ c∈[MergedCutCells.Batch121.certificate1463], c.population=PopulationCertificates.Batch012.certificate250
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers376 {x : ℝ} (hx : certificate376.interval.Contains x) : ∃ c∈certificate376.cells, c.region.interval.Contains x := rat_cut_group_covers certificate376 numericValid376 hx

def certificate377 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate251,PopulationCertificates.Batch012.certificate251,[MergedCutCells.Batch122.certificate1464,MergedCutCells.Batch122.certificate1465,MergedCutCells.Batch122.certificate1466,MergedCutCells.Batch122.certificate1467],(3462494706945550139/1000000000000000000),none,(1/2),(428293213751939849/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid377 : certificate377.NumericValid := by decide +kernel
theorem cellsSound377 : ∀ c∈certificate377.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1464,MergedCutCells.Batch122.certificate1465,MergedCutCells.Batch122.certificate1466,MergedCutCells.Batch122.certificate1467], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1464,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1466,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1467,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric377 : ∀ c∈certificate377.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1464,MergedCutCells.Batch122.certificate1465,MergedCutCells.Batch122.certificate1466,MergedCutCells.Batch122.certificate1467], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1464,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1466,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1467,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid377 : ∀ c∈certificate377.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1464,MergedCutCells.Batch122.certificate1465,MergedCutCells.Batch122.certificate1466,MergedCutCells.Batch122.certificate1467], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches377 : ∀ c∈certificate377.cells, c.population=certificate377.population := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1464,MergedCutCells.Batch122.certificate1465,MergedCutCells.Batch122.certificate1466,MergedCutCells.Batch122.certificate1467], c.population=PopulationCertificates.Batch012.certificate251
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers377 {x : ℝ} (hx : certificate377.interval.Contains x) : ∃ c∈certificate377.cells, c.region.interval.Contains x := rat_cut_group_covers certificate377 numericValid377 hx

def certificate378 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate252,PopulationCertificates.Batch012.certificate252,[MergedCutCells.Batch122.certificate1468,MergedCutCells.Batch122.certificate1469,MergedCutCells.Batch122.certificate1470,MergedCutCells.Batch122.certificate1471,MergedCutCells.Batch122.certificate1472,MergedCutCells.Batch122.certificate1473,MergedCutCells.Batch122.certificate1474],(173470286226738963/200000000000000000),(some 64),(1/2),(106862418653560103/125000000000000000),(some (69314718055994531/100000000000000000)),(some (1501470392973215867/1000000000000000000))⟩
theorem numericValid378 : certificate378.NumericValid := by decide +kernel
theorem cellsSound378 : ∀ c∈certificate378.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1468,MergedCutCells.Batch122.certificate1469,MergedCutCells.Batch122.certificate1470,MergedCutCells.Batch122.certificate1471,MergedCutCells.Batch122.certificate1472,MergedCutCells.Batch122.certificate1473,MergedCutCells.Batch122.certificate1474], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1468,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1469,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1470,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1472,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1474,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric378 : ∀ c∈certificate378.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1468,MergedCutCells.Batch122.certificate1469,MergedCutCells.Batch122.certificate1470,MergedCutCells.Batch122.certificate1471,MergedCutCells.Batch122.certificate1472,MergedCutCells.Batch122.certificate1473,MergedCutCells.Batch122.certificate1474], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1468,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1469,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1470,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1472,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1474,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid378 : ∀ c∈certificate378.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1468,MergedCutCells.Batch122.certificate1469,MergedCutCells.Batch122.certificate1470,MergedCutCells.Batch122.certificate1471,MergedCutCells.Batch122.certificate1472,MergedCutCells.Batch122.certificate1473,MergedCutCells.Batch122.certificate1474], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid127,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid127,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid127,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid127,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid127,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid127,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid127,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches378 : ∀ c∈certificate378.cells, c.population=certificate378.population := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1468,MergedCutCells.Batch122.certificate1469,MergedCutCells.Batch122.certificate1470,MergedCutCells.Batch122.certificate1471,MergedCutCells.Batch122.certificate1472,MergedCutCells.Batch122.certificate1473,MergedCutCells.Batch122.certificate1474], c.population=PopulationCertificates.Batch012.certificate252
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers378 {x : ℝ} (hx : certificate378.interval.Contains x) : ∃ c∈certificate378.cells, c.region.interval.Contains x := rat_cut_group_covers certificate378 numericValid378 hx

def certificate379 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate252,PopulationCertificates.Batch012.certificate252,[MergedCutCells.Batch122.certificate1475],64,none,(1/2),(79410541214004197/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid379 : certificate379.NumericValid := by decide +kernel
theorem cellsSound379 : ∀ c∈certificate379.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1475], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.sound1475,List.forall_mem_nil _⟩
theorem cellsNumeric379 : ∀ c∈certificate379.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1475], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch122.numericValid1475,List.forall_mem_nil _⟩
theorem cellsEntropyValid379 : ∀ c∈certificate379.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1475], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches379 : ∀ c∈certificate379.cells, c.population=certificate379.population := by
  change ∀ c∈[MergedCutCells.Batch122.certificate1475], c.population=PopulationCertificates.Batch012.certificate252
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers379 {x : ℝ} (hx : certificate379.interval.Contains x) : ∃ c∈certificate379.cells, c.region.interval.Contains x := rat_cut_group_covers certificate379 numericValid379 hx

def certificate380 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate253,PopulationCertificates.Batch012.certificate253,[MergedCutCells.Batch123.certificate1476,MergedCutCells.Batch123.certificate1477,MergedCutCells.Batch123.certificate1478,MergedCutCells.Batch123.certificate1479],(691950162740474947/200000000000000000),none,(1/2),(107264887474603787/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid380 : certificate380.NumericValid := by decide +kernel
theorem cellsSound380 : ∀ c∈certificate380.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1476,MergedCutCells.Batch123.certificate1477,MergedCutCells.Batch123.certificate1478,MergedCutCells.Batch123.certificate1479], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1476,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1477,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1478,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1479,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric380 : ∀ c∈certificate380.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1476,MergedCutCells.Batch123.certificate1477,MergedCutCells.Batch123.certificate1478,MergedCutCells.Batch123.certificate1479], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1476,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1477,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1478,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1479,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid380 : ∀ c∈certificate380.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1476,MergedCutCells.Batch123.certificate1477,MergedCutCells.Batch123.certificate1478,MergedCutCells.Batch123.certificate1479], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches380 : ∀ c∈certificate380.cells, c.population=certificate380.population := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1476,MergedCutCells.Batch123.certificate1477,MergedCutCells.Batch123.certificate1478,MergedCutCells.Batch123.certificate1479], c.population=PopulationCertificates.Batch012.certificate253
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers380 {x : ℝ} (hx : certificate380.interval.Contains x) : ∃ c∈certificate380.cells, c.region.interval.Contains x := rat_cut_group_covers certificate380 numericValid380 hx

def certificate381 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate254,PopulationCertificates.Batch012.certificate254,[MergedCutCells.Batch123.certificate1480,MergedCutCells.Batch123.certificate1481,MergedCutCells.Batch123.certificate1482,MergedCutCells.Batch123.certificate1483,MergedCutCells.Batch123.certificate1484,MergedCutCells.Batch123.certificate1485],(451753199865233743/500000000000000000),(some 64),(1/2),(863375311174272407/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (18808852936887641/12500000000000000))⟩
theorem numericValid381 : certificate381.NumericValid := by decide +kernel
theorem cellsSound381 : ∀ c∈certificate381.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1480,MergedCutCells.Batch123.certificate1481,MergedCutCells.Batch123.certificate1482,MergedCutCells.Batch123.certificate1483,MergedCutCells.Batch123.certificate1484,MergedCutCells.Batch123.certificate1485], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1481,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1482,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1483,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1485,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric381 : ∀ c∈certificate381.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1480,MergedCutCells.Batch123.certificate1481,MergedCutCells.Batch123.certificate1482,MergedCutCells.Batch123.certificate1483,MergedCutCells.Batch123.certificate1484,MergedCutCells.Batch123.certificate1485], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1481,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1482,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1483,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1485,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid381 : ∀ c∈certificate381.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1480,MergedCutCells.Batch123.certificate1481,MergedCutCells.Batch123.certificate1482,MergedCutCells.Batch123.certificate1483,MergedCutCells.Batch123.certificate1484,MergedCutCells.Batch123.certificate1485], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid128,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid128,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid128,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid128,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid128,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid128,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches381 : ∀ c∈certificate381.cells, c.population=certificate381.population := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1480,MergedCutCells.Batch123.certificate1481,MergedCutCells.Batch123.certificate1482,MergedCutCells.Batch123.certificate1483,MergedCutCells.Batch123.certificate1484,MergedCutCells.Batch123.certificate1485], c.population=PopulationCertificates.Batch012.certificate254
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers381 {x : ℝ} (hx : certificate381.interval.Contains x) : ∃ c∈certificate381.cells, c.region.interval.Contains x := rat_cut_group_covers certificate381 numericValid381 hx

def certificate382 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate254,PopulationCertificates.Batch012.certificate254,[MergedCutCells.Batch123.certificate1486],64,none,(1/2),(1968405628488258931/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid382 : certificate382.NumericValid := by decide +kernel
theorem cellsSound382 : ∀ c∈certificate382.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1486], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1486,List.forall_mem_nil _⟩
theorem cellsNumeric382 : ∀ c∈certificate382.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1486], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1486,List.forall_mem_nil _⟩
theorem cellsEntropyValid382 : ∀ c∈certificate382.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1486], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches382 : ∀ c∈certificate382.cells, c.population=certificate382.population := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1486], c.population=PopulationCertificates.Batch012.certificate254
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers382 {x : ℝ} (hx : certificate382.interval.Contains x) : ∃ c∈certificate382.cells, c.region.interval.Contains x := rat_cut_group_covers certificate382 numericValid382 hx

def certificate383 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate255,PopulationCertificates.Batch012.certificate255,[MergedCutCells.Batch123.certificate1487,MergedCutCells.Batch124.certificate1488,MergedCutCells.Batch124.certificate1489,MergedCutCells.Batch124.certificate1490],(3450994702818436267/1000000000000000000),none,(1/2),(892880514043416697/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid383 : certificate383.NumericValid := by decide +kernel
theorem cellsSound383 : ∀ c∈certificate383.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1487,MergedCutCells.Batch124.certificate1488,MergedCutCells.Batch124.certificate1489,MergedCutCells.Batch124.certificate1490], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.sound1487,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1488,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1489,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1490,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric383 : ∀ c∈certificate383.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1487,MergedCutCells.Batch124.certificate1488,MergedCutCells.Batch124.certificate1489,MergedCutCells.Batch124.certificate1490], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch123.numericValid1487,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1488,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1489,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1490,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid383 : ∀ c∈certificate383.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1487,MergedCutCells.Batch124.certificate1488,MergedCutCells.Batch124.certificate1489,MergedCutCells.Batch124.certificate1490], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches383 : ∀ c∈certificate383.cells, c.population=certificate383.population := by
  change ∀ c∈[MergedCutCells.Batch123.certificate1487,MergedCutCells.Batch124.certificate1488,MergedCutCells.Batch124.certificate1489,MergedCutCells.Batch124.certificate1490], c.population=PopulationCertificates.Batch012.certificate255
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers383 {x : ℝ} (hx : certificate383.interval.Contains x) : ∃ c∈certificate383.cells, c.region.interval.Contains x := rat_cut_group_covers certificate383 numericValid383 hx

end Cycle12.MergedCutGroups.Batch031
