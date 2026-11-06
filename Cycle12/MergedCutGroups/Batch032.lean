import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch012
import Cycle12.GeometryCertificates.Batch013
import Cycle12.MergedCutCells.Batch124
import Cycle12.MergedCutCells.Batch125
import Cycle12.MergedCutCells.Batch126
import Cycle12.MergedCutCells.Batch127
import Cycle12.PopulationCertificates.Batch012
import Cycle12.PopulationCertificates.Batch013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch032

def certificate384 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate256,PopulationCertificates.Batch012.certificate256,[MergedCutCells.Batch124.certificate1491,MergedCutCells.Batch124.certificate1492,MergedCutCells.Batch124.certificate1493,MergedCutCells.Batch124.certificate1494,MergedCutCells.Batch124.certificate1495,MergedCutCells.Batch124.certificate1496],(436923918714374483/500000000000000000),(some 64),(1/2),(886617837456619641/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (375983634481043399/250000000000000000))⟩
theorem numericValid384 : certificate384.NumericValid := by decide +kernel
theorem cellsSound384 : ∀ c∈certificate384.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1491,MergedCutCells.Batch124.certificate1492,MergedCutCells.Batch124.certificate1493,MergedCutCells.Batch124.certificate1494,MergedCutCells.Batch124.certificate1495,MergedCutCells.Batch124.certificate1496], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1491,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1492,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1494,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1495,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1496,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric384 : ∀ c∈certificate384.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1491,MergedCutCells.Batch124.certificate1492,MergedCutCells.Batch124.certificate1493,MergedCutCells.Batch124.certificate1494,MergedCutCells.Batch124.certificate1495,MergedCutCells.Batch124.certificate1496], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1491,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1492,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1494,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1495,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1496,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid384 : ∀ c∈certificate384.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1491,MergedCutCells.Batch124.certificate1492,MergedCutCells.Batch124.certificate1493,MergedCutCells.Batch124.certificate1494,MergedCutCells.Batch124.certificate1495,MergedCutCells.Batch124.certificate1496], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid129,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid129,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid129,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid129,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid129,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid129,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches384 : ∀ c∈certificate384.cells, c.population=certificate384.population := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1491,MergedCutCells.Batch124.certificate1492,MergedCutCells.Batch124.certificate1493,MergedCutCells.Batch124.certificate1494,MergedCutCells.Batch124.certificate1495,MergedCutCells.Batch124.certificate1496], c.population=PopulationCertificates.Batch012.certificate256
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers384 {x : ℝ} (hx : certificate384.interval.Contains x) : ∃ c∈certificate384.cells, c.region.interval.Contains x := rat_cut_group_covers certificate384 numericValid384 hx

def certificate385 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate256,PopulationCertificates.Batch012.certificate256,[MergedCutCells.Batch124.certificate1497],64,none,(1/2),(2037503881104662889/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid385 : certificate385.NumericValid := by decide +kernel
theorem cellsSound385 : ∀ c∈certificate385.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1497], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1497,List.forall_mem_nil _⟩
theorem cellsNumeric385 : ∀ c∈certificate385.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1497], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1497,List.forall_mem_nil _⟩
theorem cellsEntropyValid385 : ∀ c∈certificate385.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1497], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches385 : ∀ c∈certificate385.cells, c.population=certificate385.population := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1497], c.population=PopulationCertificates.Batch012.certificate256
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers385 {x : ℝ} (hx : certificate385.interval.Contains x) : ∃ c∈certificate385.cells, c.region.interval.Contains x := rat_cut_group_covers certificate385 numericValid385 hx

def certificate386 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate257,PopulationCertificates.Batch012.certificate257,[MergedCutCells.Batch124.certificate1498,MergedCutCells.Batch124.certificate1499,MergedCutCells.Batch125.certificate1500,MergedCutCells.Batch125.certificate1501],(3434098583795208547/1000000000000000000),none,(1/2),(903464384040106729/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid386 : certificate386.NumericValid := by decide +kernel
theorem cellsSound386 : ∀ c∈certificate386.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1498,MergedCutCells.Batch124.certificate1499,MergedCutCells.Batch125.certificate1500,MergedCutCells.Batch125.certificate1501], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.sound1499,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1500,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1501,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric386 : ∀ c∈certificate386.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1498,MergedCutCells.Batch124.certificate1499,MergedCutCells.Batch125.certificate1500,MergedCutCells.Batch125.certificate1501], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch124.numericValid1499,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1500,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1501,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid386 : ∀ c∈certificate386.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1498,MergedCutCells.Batch124.certificate1499,MergedCutCells.Batch125.certificate1500,MergedCutCells.Batch125.certificate1501], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches386 : ∀ c∈certificate386.cells, c.population=certificate386.population := by
  change ∀ c∈[MergedCutCells.Batch124.certificate1498,MergedCutCells.Batch124.certificate1499,MergedCutCells.Batch125.certificate1500,MergedCutCells.Batch125.certificate1501], c.population=PopulationCertificates.Batch012.certificate257
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers386 {x : ℝ} (hx : certificate386.interval.Contains x) : ∃ c∈certificate386.cells, c.region.interval.Contains x := rat_cut_group_covers certificate386 numericValid386 hx

def certificate387 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate258,PopulationCertificates.Batch012.certificate258,[MergedCutCells.Batch125.certificate1502,MergedCutCells.Batch125.certificate1503,MergedCutCells.Batch125.certificate1504,MergedCutCells.Batch125.certificate1505,MergedCutCells.Batch125.certificate1506,MergedCutCells.Batch125.certificate1507,MergedCutCells.Batch125.certificate1508],(217854935891653033/250000000000000000),(some 64),(1/2),(178352591128005607/200000000000000000),(some (69314718055994531/100000000000000000)),(some (300830395635925693/200000000000000000))⟩
theorem numericValid387 : certificate387.NumericValid := by decide +kernel
theorem cellsSound387 : ∀ c∈certificate387.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1502,MergedCutCells.Batch125.certificate1503,MergedCutCells.Batch125.certificate1504,MergedCutCells.Batch125.certificate1505,MergedCutCells.Batch125.certificate1506,MergedCutCells.Batch125.certificate1507,MergedCutCells.Batch125.certificate1508], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1504,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1505,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1507,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1508,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric387 : ∀ c∈certificate387.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1502,MergedCutCells.Batch125.certificate1503,MergedCutCells.Batch125.certificate1504,MergedCutCells.Batch125.certificate1505,MergedCutCells.Batch125.certificate1506,MergedCutCells.Batch125.certificate1507,MergedCutCells.Batch125.certificate1508], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1504,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1505,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1507,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1508,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid387 : ∀ c∈certificate387.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1502,MergedCutCells.Batch125.certificate1503,MergedCutCells.Batch125.certificate1504,MergedCutCells.Batch125.certificate1505,MergedCutCells.Batch125.certificate1506,MergedCutCells.Batch125.certificate1507,MergedCutCells.Batch125.certificate1508], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid130,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid130,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid130,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid130,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid130,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid130,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid130,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches387 : ∀ c∈certificate387.cells, c.population=certificate387.population := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1502,MergedCutCells.Batch125.certificate1503,MergedCutCells.Batch125.certificate1504,MergedCutCells.Batch125.certificate1505,MergedCutCells.Batch125.certificate1506,MergedCutCells.Batch125.certificate1507,MergedCutCells.Batch125.certificate1508], c.population=PopulationCertificates.Batch012.certificate258
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers387 {x : ℝ} (hx : certificate387.interval.Contains x) : ∃ c∈certificate387.cells, c.region.interval.Contains x := rat_cut_group_covers certificate387 numericValid387 hx

def certificate388 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate258,PopulationCertificates.Batch012.certificate258,[MergedCutCells.Batch125.certificate1509],64,none,(1/2),(513323957733618593/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid388 : certificate388.NumericValid := by decide +kernel
theorem cellsSound388 : ∀ c∈certificate388.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1509], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1509,List.forall_mem_nil _⟩
theorem cellsNumeric388 : ∀ c∈certificate388.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1509], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1509,List.forall_mem_nil _⟩
theorem cellsEntropyValid388 : ∀ c∈certificate388.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1509], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches388 : ∀ c∈certificate388.cells, c.population=certificate388.population := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1509], c.population=PopulationCertificates.Batch012.certificate258
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers388 {x : ℝ} (hx : certificate388.interval.Contains x) : ∃ c∈certificate388.cells, c.region.interval.Contains x := rat_cut_group_covers certificate388 numericValid388 hx

def certificate389 : RatCutGroup := ⟨GeometryCertificates.Batch012.certificate259,PopulationCertificates.Batch012.certificate259,[MergedCutCells.Batch125.certificate1510,MergedCutCells.Batch125.certificate1511,MergedCutCells.Batch126.certificate1512,MergedCutCells.Batch126.certificate1513],(3416943893315611577/1000000000000000000),none,(1/2),(228032116474001041/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid389 : certificate389.NumericValid := by decide +kernel
theorem cellsSound389 : ∀ c∈certificate389.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1510,MergedCutCells.Batch125.certificate1511,MergedCutCells.Batch126.certificate1512,MergedCutCells.Batch126.certificate1513], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1510,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.sound1511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1512,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1513,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric389 : ∀ c∈certificate389.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1510,MergedCutCells.Batch125.certificate1511,MergedCutCells.Batch126.certificate1512,MergedCutCells.Batch126.certificate1513], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1510,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch125.numericValid1511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1512,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1513,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid389 : ∀ c∈certificate389.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1510,MergedCutCells.Batch125.certificate1511,MergedCutCells.Batch126.certificate1512,MergedCutCells.Batch126.certificate1513], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches389 : ∀ c∈certificate389.cells, c.population=certificate389.population := by
  change ∀ c∈[MergedCutCells.Batch125.certificate1510,MergedCutCells.Batch125.certificate1511,MergedCutCells.Batch126.certificate1512,MergedCutCells.Batch126.certificate1513], c.population=PopulationCertificates.Batch012.certificate259
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers389 {x : ℝ} (hx : certificate389.interval.Contains x) : ∃ c∈certificate389.cells, c.region.interval.Contains x := rat_cut_group_covers certificate389 numericValid389 hx

def certificate390 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate260,PopulationCertificates.Batch013.certificate260,[MergedCutCells.Batch126.certificate1514,MergedCutCells.Batch126.certificate1515,MergedCutCells.Batch126.certificate1516,MergedCutCells.Batch126.certificate1517,MergedCutCells.Batch126.certificate1518,MergedCutCells.Batch126.certificate1519],(223301309621467113/250000000000000000),(some 64),(1/2),(89377670384855449/100000000000000000),(some (69314718055994531/100000000000000000)),(some (1506824466071003619/1000000000000000000))⟩
theorem numericValid390 : certificate390.NumericValid := by decide +kernel
theorem cellsSound390 : ∀ c∈certificate390.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1514,MergedCutCells.Batch126.certificate1515,MergedCutCells.Batch126.certificate1516,MergedCutCells.Batch126.certificate1517,MergedCutCells.Batch126.certificate1518,MergedCutCells.Batch126.certificate1519], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1514,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1515,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1516,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1517,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1518,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1519,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric390 : ∀ c∈certificate390.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1514,MergedCutCells.Batch126.certificate1515,MergedCutCells.Batch126.certificate1516,MergedCutCells.Batch126.certificate1517,MergedCutCells.Batch126.certificate1518,MergedCutCells.Batch126.certificate1519], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1514,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1515,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1516,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1517,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1518,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1519,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid390 : ∀ c∈certificate390.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1514,MergedCutCells.Batch126.certificate1515,MergedCutCells.Batch126.certificate1516,MergedCutCells.Batch126.certificate1517,MergedCutCells.Batch126.certificate1518,MergedCutCells.Batch126.certificate1519], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid131,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid131,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid131,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid131,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid131,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid131,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches390 : ∀ c∈certificate390.cells, c.population=certificate390.population := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1514,MergedCutCells.Batch126.certificate1515,MergedCutCells.Batch126.certificate1516,MergedCutCells.Batch126.certificate1517,MergedCutCells.Batch126.certificate1518,MergedCutCells.Batch126.certificate1519], c.population=PopulationCertificates.Batch013.certificate260
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers390 {x : ℝ} (hx : certificate390.interval.Contains x) : ∃ c∈certificate390.cells, c.region.interval.Contains x := rat_cut_group_covers certificate390 numericValid390 hx

def certificate391 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate260,PopulationCertificates.Batch013.certificate260,[MergedCutCells.Batch126.certificate1520],64,none,(1/2),(1019023435684070647/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid391 : certificate391.NumericValid := by decide +kernel
theorem cellsSound391 : ∀ c∈certificate391.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1520], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1520,List.forall_mem_nil _⟩
theorem cellsNumeric391 : ∀ c∈certificate391.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1520], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1520,List.forall_mem_nil _⟩
theorem cellsEntropyValid391 : ∀ c∈certificate391.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1520], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches391 : ∀ c∈certificate391.cells, c.population=certificate391.population := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1520], c.population=PopulationCertificates.Batch013.certificate260
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers391 {x : ℝ} (hx : certificate391.interval.Contains x) : ∃ c∈certificate391.cells, c.region.interval.Contains x := rat_cut_group_covers certificate391 numericValid391 hx

def certificate392 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate261,PopulationCertificates.Batch013.certificate261,[MergedCutCells.Batch126.certificate1521,MergedCutCells.Batch126.certificate1522,MergedCutCells.Batch126.certificate1523],(337930889062405409/100000000000000000),none,(1/2),(889875822348817769/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid392 : certificate392.NumericValid := by decide +kernel
theorem cellsSound392 : ∀ c∈certificate392.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1521,MergedCutCells.Batch126.certificate1522,MergedCutCells.Batch126.certificate1523], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1521,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1522,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.sound1523,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric392 : ∀ c∈certificate392.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1521,MergedCutCells.Batch126.certificate1522,MergedCutCells.Batch126.certificate1523], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1521,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1522,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch126.numericValid1523,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid392 : ∀ c∈certificate392.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1521,MergedCutCells.Batch126.certificate1522,MergedCutCells.Batch126.certificate1523], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches392 : ∀ c∈certificate392.cells, c.population=certificate392.population := by
  change ∀ c∈[MergedCutCells.Batch126.certificate1521,MergedCutCells.Batch126.certificate1522,MergedCutCells.Batch126.certificate1523], c.population=PopulationCertificates.Batch013.certificate261
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers392 {x : ℝ} (hx : certificate392.interval.Contains x) : ∃ c∈certificate392.cells, c.region.interval.Contains x := rat_cut_group_covers certificate392 numericValid392 hx

def certificate393 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate262,PopulationCertificates.Batch013.certificate262,[MergedCutCells.Batch127.certificate1524,MergedCutCells.Batch127.certificate1525,MergedCutCells.Batch127.certificate1526,MergedCutCells.Batch127.certificate1527,MergedCutCells.Batch127.certificate1528,MergedCutCells.Batch127.certificate1529,MergedCutCells.Batch127.certificate1530],(868157907783427697/1000000000000000000),(some 64),(1/2),(905305420274116431/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1506376266369174153/1000000000000000000))⟩
theorem numericValid393 : certificate393.NumericValid := by decide +kernel
theorem cellsSound393 : ∀ c∈certificate393.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1524,MergedCutCells.Batch127.certificate1525,MergedCutCells.Batch127.certificate1526,MergedCutCells.Batch127.certificate1527,MergedCutCells.Batch127.certificate1528,MergedCutCells.Batch127.certificate1529,MergedCutCells.Batch127.certificate1530], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1525,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1526,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1527,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1529,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1530,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric393 : ∀ c∈certificate393.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1524,MergedCutCells.Batch127.certificate1525,MergedCutCells.Batch127.certificate1526,MergedCutCells.Batch127.certificate1527,MergedCutCells.Batch127.certificate1528,MergedCutCells.Batch127.certificate1529,MergedCutCells.Batch127.certificate1530], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1525,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1526,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1527,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1529,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1530,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid393 : ∀ c∈certificate393.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1524,MergedCutCells.Batch127.certificate1525,MergedCutCells.Batch127.certificate1526,MergedCutCells.Batch127.certificate1527,MergedCutCells.Batch127.certificate1528,MergedCutCells.Batch127.certificate1529,MergedCutCells.Batch127.certificate1530], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid132,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid132,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid132,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid132,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid132,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid132,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid132,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches393 : ∀ c∈certificate393.cells, c.population=certificate393.population := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1524,MergedCutCells.Batch127.certificate1525,MergedCutCells.Batch127.certificate1526,MergedCutCells.Batch127.certificate1527,MergedCutCells.Batch127.certificate1528,MergedCutCells.Batch127.certificate1529,MergedCutCells.Batch127.certificate1530], c.population=PopulationCertificates.Batch013.certificate262
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers393 {x : ℝ} (hx : certificate393.interval.Contains x) : ∃ c∈certificate393.cells, c.region.interval.Contains x := rat_cut_group_covers certificate393 numericValid393 hx

def certificate394 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate262,PopulationCertificates.Batch013.certificate262,[MergedCutCells.Batch127.certificate1531],64,none,(1/2),(2090787174275559097/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid394 : certificate394.NumericValid := by decide +kernel
theorem cellsSound394 : ∀ c∈certificate394.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1531], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1531,List.forall_mem_nil _⟩
theorem cellsNumeric394 : ∀ c∈certificate394.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1531], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1531,List.forall_mem_nil _⟩
theorem cellsEntropyValid394 : ∀ c∈certificate394.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1531], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches394 : ∀ c∈certificate394.cells, c.population=certificate394.population := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1531], c.population=PopulationCertificates.Batch013.certificate262
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers394 {x : ℝ} (hx : certificate394.interval.Contains x) : ∃ c∈certificate394.cells, c.region.interval.Contains x := rat_cut_group_covers certificate394 numericValid394 hx

def certificate395 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate263,PopulationCertificates.Batch013.certificate263,[MergedCutCells.Batch127.certificate1532,MergedCutCells.Batch127.certificate1533,MergedCutCells.Batch127.certificate1534,MergedCutCells.Batch127.certificate1535],(3359894490835449699/1000000000000000000),none,(1/2),(452280481494328303/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid395 : certificate395.NumericValid := by decide +kernel
theorem cellsSound395 : ∀ c∈certificate395.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1532,MergedCutCells.Batch127.certificate1533,MergedCutCells.Batch127.certificate1534,MergedCutCells.Batch127.certificate1535], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1532,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1533,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1534,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.sound1535,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric395 : ∀ c∈certificate395.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1532,MergedCutCells.Batch127.certificate1533,MergedCutCells.Batch127.certificate1534,MergedCutCells.Batch127.certificate1535], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1532,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1533,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1534,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch127.numericValid1535,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid395 : ∀ c∈certificate395.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1532,MergedCutCells.Batch127.certificate1533,MergedCutCells.Batch127.certificate1534,MergedCutCells.Batch127.certificate1535], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches395 : ∀ c∈certificate395.cells, c.population=certificate395.population := by
  change ∀ c∈[MergedCutCells.Batch127.certificate1532,MergedCutCells.Batch127.certificate1533,MergedCutCells.Batch127.certificate1534,MergedCutCells.Batch127.certificate1535], c.population=PopulationCertificates.Batch013.certificate263
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers395 {x : ℝ} (hx : certificate395.interval.Contains x) : ∃ c∈certificate395.cells, c.region.interval.Contains x := rat_cut_group_covers certificate395 numericValid395 hx

end Cycle12.MergedCutGroups.Batch032
