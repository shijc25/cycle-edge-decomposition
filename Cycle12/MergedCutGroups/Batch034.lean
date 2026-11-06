import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch013
import Cycle12.MergedCutCells.Batch131
import Cycle12.MergedCutCells.Batch132
import Cycle12.MergedCutCells.Batch133
import Cycle12.MergedCutCells.Batch134
import Cycle12.MergedCutCells.Batch135
import Cycle12.PopulationCertificates.Batch013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch034

def certificate408 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate272,PopulationCertificates.Batch013.certificate272,[MergedCutCells.Batch131.certificate1578,MergedCutCells.Batch131.certificate1579,MergedCutCells.Batch131.certificate1580,MergedCutCells.Batch131.certificate1581,MergedCutCells.Batch131.certificate1582,MergedCutCells.Batch131.certificate1583,MergedCutCells.Batch132.certificate1584,MergedCutCells.Batch132.certificate1585],(683847784274293/800000000000000),(some 64),(1/2),(479030008415178963/500000000000000000),(some (69314718055994531/100000000000000000)),(some (757099154530185831/500000000000000000))⟩
theorem numericValid408 : certificate408.NumericValid := by decide +kernel
theorem cellsSound408 : ∀ c∈certificate408.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1578,MergedCutCells.Batch131.certificate1579,MergedCutCells.Batch131.certificate1580,MergedCutCells.Batch131.certificate1581,MergedCutCells.Batch131.certificate1582,MergedCutCells.Batch131.certificate1583,MergedCutCells.Batch132.certificate1584,MergedCutCells.Batch132.certificate1585], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1578,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1579,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1580,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1581,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.sound1583,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1584,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1585,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric408 : ∀ c∈certificate408.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1578,MergedCutCells.Batch131.certificate1579,MergedCutCells.Batch131.certificate1580,MergedCutCells.Batch131.certificate1581,MergedCutCells.Batch131.certificate1582,MergedCutCells.Batch131.certificate1583,MergedCutCells.Batch132.certificate1584,MergedCutCells.Batch132.certificate1585], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1578,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1579,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1580,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1581,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch131.numericValid1583,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1584,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1585,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid408 : ∀ c∈certificate408.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1578,MergedCutCells.Batch131.certificate1579,MergedCutCells.Batch131.certificate1580,MergedCutCells.Batch131.certificate1581,MergedCutCells.Batch131.certificate1582,MergedCutCells.Batch131.certificate1583,MergedCutCells.Batch132.certificate1584,MergedCutCells.Batch132.certificate1585], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid137,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid137,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid137,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid137,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid137,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid137,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid137,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid137,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches408 : ∀ c∈certificate408.cells, c.population=certificate408.population := by
  change ∀ c∈[MergedCutCells.Batch131.certificate1578,MergedCutCells.Batch131.certificate1579,MergedCutCells.Batch131.certificate1580,MergedCutCells.Batch131.certificate1581,MergedCutCells.Batch131.certificate1582,MergedCutCells.Batch131.certificate1583,MergedCutCells.Batch132.certificate1584,MergedCutCells.Batch132.certificate1585], c.population=PopulationCertificates.Batch013.certificate272
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers408 {x : ℝ} (hx : certificate408.interval.Contains x) : ∃ c∈certificate408.cells, c.region.interval.Contains x := rat_cut_group_covers certificate408 numericValid408 hx

def certificate409 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate272,PopulationCertificates.Batch013.certificate272,[MergedCutCells.Batch132.certificate1586],64,none,(1/2),(111054092436039803/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid409 : certificate409.NumericValid := by decide +kernel
theorem cellsSound409 : ∀ c∈certificate409.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1586], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1586,List.forall_mem_nil _⟩
theorem cellsNumeric409 : ∀ c∈certificate409.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1586], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1586,List.forall_mem_nil _⟩
theorem cellsEntropyValid409 : ∀ c∈certificate409.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1586], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches409 : ∀ c∈certificate409.cells, c.population=certificate409.population := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1586], c.population=PopulationCertificates.Batch013.certificate272
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers409 {x : ℝ} (hx : certificate409.interval.Contains x) : ∃ c∈certificate409.cells, c.region.interval.Contains x := rat_cut_group_covers certificate409 numericValid409 hx

def certificate410 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate273,PopulationCertificates.Batch013.certificate273,[MergedCutCells.Batch132.certificate1587,MergedCutCells.Batch132.certificate1588,MergedCutCells.Batch132.certificate1589,MergedCutCells.Batch132.certificate1590],(3244068728965307713/1000000000000000000),none,(1/2),(55819771429050483/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid410 : certificate410.NumericValid := by decide +kernel
theorem cellsSound410 : ∀ c∈certificate410.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1587,MergedCutCells.Batch132.certificate1588,MergedCutCells.Batch132.certificate1589,MergedCutCells.Batch132.certificate1590], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1587,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1588,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1590,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric410 : ∀ c∈certificate410.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1587,MergedCutCells.Batch132.certificate1588,MergedCutCells.Batch132.certificate1589,MergedCutCells.Batch132.certificate1590], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1587,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1588,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1590,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid410 : ∀ c∈certificate410.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1587,MergedCutCells.Batch132.certificate1588,MergedCutCells.Batch132.certificate1589,MergedCutCells.Batch132.certificate1590], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches410 : ∀ c∈certificate410.cells, c.population=certificate410.population := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1587,MergedCutCells.Batch132.certificate1588,MergedCutCells.Batch132.certificate1589,MergedCutCells.Batch132.certificate1590], c.population=PopulationCertificates.Batch013.certificate273
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers410 {x : ℝ} (hx : certificate410.interval.Contains x) : ∃ c∈certificate410.cells, c.region.interval.Contains x := rat_cut_group_covers certificate410 numericValid410 hx

def certificate411 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate274,PopulationCertificates.Batch013.certificate274,[MergedCutCells.Batch132.certificate1591,MergedCutCells.Batch132.certificate1592,MergedCutCells.Batch132.certificate1593,MergedCutCells.Batch132.certificate1594,MergedCutCells.Batch132.certificate1595,MergedCutCells.Batch133.certificate1596],(457767686730367713/500000000000000000),(some 64),(1/2),(483795705725894937/500000000000000000),(some (69314718055994531/100000000000000000)),(some (758918832449853141/500000000000000000))⟩
theorem numericValid411 : certificate411.NumericValid := by decide +kernel
theorem cellsSound411 : ∀ c∈certificate411.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1591,MergedCutCells.Batch132.certificate1592,MergedCutCells.Batch132.certificate1593,MergedCutCells.Batch132.certificate1594,MergedCutCells.Batch132.certificate1595,MergedCutCells.Batch133.certificate1596], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1593,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1594,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.sound1595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1596,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric411 : ∀ c∈certificate411.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1591,MergedCutCells.Batch132.certificate1592,MergedCutCells.Batch132.certificate1593,MergedCutCells.Batch132.certificate1594,MergedCutCells.Batch132.certificate1595,MergedCutCells.Batch133.certificate1596], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1593,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1594,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch132.numericValid1595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1596,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid411 : ∀ c∈certificate411.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1591,MergedCutCells.Batch132.certificate1592,MergedCutCells.Batch132.certificate1593,MergedCutCells.Batch132.certificate1594,MergedCutCells.Batch132.certificate1595,MergedCutCells.Batch133.certificate1596], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid138,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid138,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid138,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid138,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid138,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid138,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches411 : ∀ c∈certificate411.cells, c.population=certificate411.population := by
  change ∀ c∈[MergedCutCells.Batch132.certificate1591,MergedCutCells.Batch132.certificate1592,MergedCutCells.Batch132.certificate1593,MergedCutCells.Batch132.certificate1594,MergedCutCells.Batch132.certificate1595,MergedCutCells.Batch133.certificate1596], c.population=PopulationCertificates.Batch013.certificate274
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers411 {x : ℝ} (hx : certificate411.interval.Contains x) : ∃ c∈certificate411.cells, c.region.interval.Contains x := rat_cut_group_covers certificate411 numericValid411 hx

def certificate412 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate274,PopulationCertificates.Batch013.certificate274,[MergedCutCells.Batch133.certificate1597],64,none,(1/2),(2176312300990879299/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid412 : certificate412.NumericValid := by decide +kernel
theorem cellsSound412 : ∀ c∈certificate412.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1597], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1597,List.forall_mem_nil _⟩
theorem cellsNumeric412 : ∀ c∈certificate412.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1597], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1597,List.forall_mem_nil _⟩
theorem cellsEntropyValid412 : ∀ c∈certificate412.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1597], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches412 : ∀ c∈certificate412.cells, c.population=certificate412.population := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1597], c.population=PopulationCertificates.Batch013.certificate274
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers412 {x : ℝ} (hx : certificate412.interval.Contains x) : ∃ c∈certificate412.cells, c.region.interval.Contains x := rat_cut_group_covers certificate412 numericValid412 hx

def certificate413 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate275,PopulationCertificates.Batch013.certificate275,[MergedCutCells.Batch133.certificate1598,MergedCutCells.Batch133.certificate1599,MergedCutCells.Batch133.certificate1600,MergedCutCells.Batch133.certificate1601],(806378388037493157/250000000000000000),none,(1/2),(930480240468592323/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid413 : certificate413.NumericValid := by decide +kernel
theorem cellsSound413 : ∀ c∈certificate413.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1598,MergedCutCells.Batch133.certificate1599,MergedCutCells.Batch133.certificate1600,MergedCutCells.Batch133.certificate1601], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1599,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1600,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1601,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric413 : ∀ c∈certificate413.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1598,MergedCutCells.Batch133.certificate1599,MergedCutCells.Batch133.certificate1600,MergedCutCells.Batch133.certificate1601], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1599,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1600,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1601,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid413 : ∀ c∈certificate413.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1598,MergedCutCells.Batch133.certificate1599,MergedCutCells.Batch133.certificate1600,MergedCutCells.Batch133.certificate1601], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches413 : ∀ c∈certificate413.cells, c.population=certificate413.population := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1598,MergedCutCells.Batch133.certificate1599,MergedCutCells.Batch133.certificate1600,MergedCutCells.Batch133.certificate1601], c.population=PopulationCertificates.Batch013.certificate275
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers413 {x : ℝ} (hx : certificate413.interval.Contains x) : ∃ c∈certificate413.cells, c.region.interval.Contains x := rat_cut_group_covers certificate413 numericValid413 hx

def certificate414 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate276,PopulationCertificates.Batch013.certificate276,[MergedCutCells.Batch133.certificate1602,MergedCutCells.Batch133.certificate1603,MergedCutCells.Batch133.certificate1604,MergedCutCells.Batch133.certificate1605,MergedCutCells.Batch133.certificate1606,MergedCutCells.Batch133.certificate1607,MergedCutCells.Batch134.certificate1608],(871328204294733959/1000000000000000000),(some 64),(1/2),(197857591395264649/200000000000000000),(some (69314718055994531/100000000000000000)),(some (1516022764334457521/1000000000000000000))⟩
theorem numericValid414 : certificate414.NumericValid := by decide +kernel
theorem cellsSound414 : ∀ c∈certificate414.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1602,MergedCutCells.Batch133.certificate1603,MergedCutCells.Batch133.certificate1604,MergedCutCells.Batch133.certificate1605,MergedCutCells.Batch133.certificate1606,MergedCutCells.Batch133.certificate1607,MergedCutCells.Batch134.certificate1608], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1602,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1605,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1606,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.sound1607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1608,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric414 : ∀ c∈certificate414.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1602,MergedCutCells.Batch133.certificate1603,MergedCutCells.Batch133.certificate1604,MergedCutCells.Batch133.certificate1605,MergedCutCells.Batch133.certificate1606,MergedCutCells.Batch133.certificate1607,MergedCutCells.Batch134.certificate1608], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1602,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1605,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1606,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch133.numericValid1607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1608,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid414 : ∀ c∈certificate414.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1602,MergedCutCells.Batch133.certificate1603,MergedCutCells.Batch133.certificate1604,MergedCutCells.Batch133.certificate1605,MergedCutCells.Batch133.certificate1606,MergedCutCells.Batch133.certificate1607,MergedCutCells.Batch134.certificate1608], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid139,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid139,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid139,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid139,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid139,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid139,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy006.valid139,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches414 : ∀ c∈certificate414.cells, c.population=certificate414.population := by
  change ∀ c∈[MergedCutCells.Batch133.certificate1602,MergedCutCells.Batch133.certificate1603,MergedCutCells.Batch133.certificate1604,MergedCutCells.Batch133.certificate1605,MergedCutCells.Batch133.certificate1606,MergedCutCells.Batch133.certificate1607,MergedCutCells.Batch134.certificate1608], c.population=PopulationCertificates.Batch013.certificate276
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers414 {x : ℝ} (hx : certificate414.interval.Contains x) : ∃ c∈certificate414.cells, c.region.interval.Contains x := rat_cut_group_covers certificate414 numericValid414 hx

def certificate415 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate276,PopulationCertificates.Batch013.certificate276,[MergedCutCells.Batch134.certificate1609],64,none,(1/2),(2262151486749319941/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid415 : certificate415.NumericValid := by decide +kernel
theorem cellsSound415 : ∀ c∈certificate415.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1609], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1609,List.forall_mem_nil _⟩
theorem cellsNumeric415 : ∀ c∈certificate415.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1609], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1609,List.forall_mem_nil _⟩
theorem cellsEntropyValid415 : ∀ c∈certificate415.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1609], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches415 : ∀ c∈certificate415.cells, c.population=certificate415.population := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1609], c.population=PopulationCertificates.Batch013.certificate276
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers415 {x : ℝ} (hx : certificate415.interval.Contains x) : ∃ c∈certificate415.cells, c.region.interval.Contains x := rat_cut_group_covers certificate415 numericValid415 hx

def certificate416 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate277,PopulationCertificates.Batch013.certificate277,[MergedCutCells.Batch134.certificate1610,MergedCutCells.Batch134.certificate1611,MergedCutCells.Batch134.certificate1612],(3222321565108766203/1000000000000000000),none,(1/2),(192413839960204127/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid416 : certificate416.NumericValid := by decide +kernel
theorem cellsSound416 : ∀ c∈certificate416.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1610,MergedCutCells.Batch134.certificate1611,MergedCutCells.Batch134.certificate1612], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1610,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1611,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1612,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric416 : ∀ c∈certificate416.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1610,MergedCutCells.Batch134.certificate1611,MergedCutCells.Batch134.certificate1612], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1610,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1611,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1612,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid416 : ∀ c∈certificate416.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1610,MergedCutCells.Batch134.certificate1611,MergedCutCells.Batch134.certificate1612], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches416 : ∀ c∈certificate416.cells, c.population=certificate416.population := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1610,MergedCutCells.Batch134.certificate1611,MergedCutCells.Batch134.certificate1612], c.population=PopulationCertificates.Batch013.certificate277
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers416 {x : ℝ} (hx : certificate416.interval.Contains x) : ∃ c∈certificate416.cells, c.region.interval.Contains x := rat_cut_group_covers certificate416 numericValid416 hx

def certificate417 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate278,PopulationCertificates.Batch013.certificate278,[MergedCutCells.Batch134.certificate1613,MergedCutCells.Batch134.certificate1614,MergedCutCells.Batch134.certificate1615,MergedCutCells.Batch134.certificate1616,MergedCutCells.Batch134.certificate1617,MergedCutCells.Batch134.certificate1618,MergedCutCells.Batch134.certificate1619],(174109942955663927/200000000000000000),(some 64),(1/2),(248005718152655249/250000000000000000),(some (69314718055994531/100000000000000000)),(some (303479650578294397/200000000000000000))⟩
theorem numericValid417 : certificate417.NumericValid := by decide +kernel
theorem cellsSound417 : ∀ c∈certificate417.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1613,MergedCutCells.Batch134.certificate1614,MergedCutCells.Batch134.certificate1615,MergedCutCells.Batch134.certificate1616,MergedCutCells.Batch134.certificate1617,MergedCutCells.Batch134.certificate1618,MergedCutCells.Batch134.certificate1619], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1613,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1614,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1615,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1616,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1617,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.sound1619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric417 : ∀ c∈certificate417.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1613,MergedCutCells.Batch134.certificate1614,MergedCutCells.Batch134.certificate1615,MergedCutCells.Batch134.certificate1616,MergedCutCells.Batch134.certificate1617,MergedCutCells.Batch134.certificate1618,MergedCutCells.Batch134.certificate1619], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1613,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1614,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1615,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1616,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1617,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch134.numericValid1619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid417 : ∀ c∈certificate417.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1613,MergedCutCells.Batch134.certificate1614,MergedCutCells.Batch134.certificate1615,MergedCutCells.Batch134.certificate1616,MergedCutCells.Batch134.certificate1617,MergedCutCells.Batch134.certificate1618,MergedCutCells.Batch134.certificate1619], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid140,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid140,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid140,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid140,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid140,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid140,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid140,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches417 : ∀ c∈certificate417.cells, c.population=certificate417.population := by
  change ∀ c∈[MergedCutCells.Batch134.certificate1613,MergedCutCells.Batch134.certificate1614,MergedCutCells.Batch134.certificate1615,MergedCutCells.Batch134.certificate1616,MergedCutCells.Batch134.certificate1617,MergedCutCells.Batch134.certificate1618,MergedCutCells.Batch134.certificate1619], c.population=PopulationCertificates.Batch013.certificate278
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers417 {x : ℝ} (hx : certificate417.interval.Contains x) : ∃ c∈certificate417.cells, c.region.interval.Contains x := rat_cut_group_covers certificate417 numericValid417 hx

def certificate418 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate278,PopulationCertificates.Batch013.certificate278,[MergedCutCells.Batch135.certificate1620],64,none,(1/2),(2282065833144531667/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid418 : certificate418.NumericValid := by decide +kernel
theorem cellsSound418 : ∀ c∈certificate418.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1620], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1620,List.forall_mem_nil _⟩
theorem cellsNumeric418 : ∀ c∈certificate418.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1620], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1620,List.forall_mem_nil _⟩
theorem cellsEntropyValid418 : ∀ c∈certificate418.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1620], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches418 : ∀ c∈certificate418.cells, c.population=certificate418.population := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1620], c.population=PopulationCertificates.Batch013.certificate278
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers418 {x : ℝ} (hx : certificate418.interval.Contains x) : ∃ c∈certificate418.cells, c.region.interval.Contains x := rat_cut_group_covers certificate418 numericValid418 hx

def certificate419 : RatCutGroup := ⟨GeometryCertificates.Batch013.certificate279,PopulationCertificates.Batch013.certificate279,[MergedCutCells.Batch135.certificate1621,MergedCutCells.Batch135.certificate1622,MergedCutCells.Batch135.certificate1623,MergedCutCells.Batch135.certificate1624],(3205360645708925957/1000000000000000000),none,(1/2),(488913350574049787/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid419 : certificate419.NumericValid := by decide +kernel
theorem cellsSound419 : ∀ c∈certificate419.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1621,MergedCutCells.Batch135.certificate1622,MergedCutCells.Batch135.certificate1623,MergedCutCells.Batch135.certificate1624], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1622,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1623,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.sound1624,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric419 : ∀ c∈certificate419.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1621,MergedCutCells.Batch135.certificate1622,MergedCutCells.Batch135.certificate1623,MergedCutCells.Batch135.certificate1624], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1622,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1623,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch135.numericValid1624,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid419 : ∀ c∈certificate419.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1621,MergedCutCells.Batch135.certificate1622,MergedCutCells.Batch135.certificate1623,MergedCutCells.Batch135.certificate1624], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches419 : ∀ c∈certificate419.cells, c.population=certificate419.population := by
  change ∀ c∈[MergedCutCells.Batch135.certificate1621,MergedCutCells.Batch135.certificate1622,MergedCutCells.Batch135.certificate1623,MergedCutCells.Batch135.certificate1624], c.population=PopulationCertificates.Batch013.certificate279
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers419 {x : ℝ} (hx : certificate419.interval.Contains x) : ∃ c∈certificate419.cells, c.region.interval.Contains x := rat_cut_group_covers certificate419 numericValid419 hx

end Cycle12.MergedCutGroups.Batch034
