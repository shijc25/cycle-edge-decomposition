import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch016
import Cycle12.MergedCutCells.Batch155
import Cycle12.MergedCutCells.Batch156
import Cycle12.MergedCutCells.Batch157
import Cycle12.MergedCutCells.Batch158
import Cycle12.PopulationCertificates.Batch016

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch040

def certificate480 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate320,PopulationCertificates.Batch016.certificate320,[MergedCutCells.Batch155.certificate1861,MergedCutCells.Batch155.certificate1862,MergedCutCells.Batch155.certificate1863,MergedCutCells.Batch155.certificate1864,MergedCutCells.Batch155.certificate1865,MergedCutCells.Batch155.certificate1866],(223281346151771371/250000000000000000),(some 64),(1/2),(1200430390072739949/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1541343368582078201/1000000000000000000))⟩
theorem numericValid480 : certificate480.NumericValid := by decide +kernel
theorem cellsSound480 : ∀ c∈certificate480.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1861,MergedCutCells.Batch155.certificate1862,MergedCutCells.Batch155.certificate1863,MergedCutCells.Batch155.certificate1864,MergedCutCells.Batch155.certificate1865,MergedCutCells.Batch155.certificate1866], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1861,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1862,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1863,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1864,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1866,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric480 : ∀ c∈certificate480.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1861,MergedCutCells.Batch155.certificate1862,MergedCutCells.Batch155.certificate1863,MergedCutCells.Batch155.certificate1864,MergedCutCells.Batch155.certificate1865,MergedCutCells.Batch155.certificate1866], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1861,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1862,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1863,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1864,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1866,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid480 : ∀ c∈certificate480.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1861,MergedCutCells.Batch155.certificate1862,MergedCutCells.Batch155.certificate1863,MergedCutCells.Batch155.certificate1864,MergedCutCells.Batch155.certificate1865,MergedCutCells.Batch155.certificate1866], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid161,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid161,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid161,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid161,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid161,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid161,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches480 : ∀ c∈certificate480.cells, c.population=certificate480.population := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1861,MergedCutCells.Batch155.certificate1862,MergedCutCells.Batch155.certificate1863,MergedCutCells.Batch155.certificate1864,MergedCutCells.Batch155.certificate1865,MergedCutCells.Batch155.certificate1866], c.population=PopulationCertificates.Batch016.certificate320
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers480 {x : ℝ} (hx : certificate480.interval.Contains x) : ∃ c∈certificate480.cells, c.region.interval.Contains x := rat_cut_group_covers certificate480 numericValid480 hx

def certificate481 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate320,PopulationCertificates.Batch016.certificate320,[MergedCutCells.Batch155.certificate1867],64,none,(1/2),(21654238513435163/8000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid481 : certificate481.NumericValid := by decide +kernel
theorem cellsSound481 : ∀ c∈certificate481.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1867], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1867,List.forall_mem_nil _⟩
theorem cellsNumeric481 : ∀ c∈certificate481.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1867], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1867,List.forall_mem_nil _⟩
theorem cellsEntropyValid481 : ∀ c∈certificate481.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1867], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches481 : ∀ c∈certificate481.cells, c.population=certificate481.population := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1867], c.population=PopulationCertificates.Batch016.certificate320
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers481 {x : ℝ} (hx : certificate481.interval.Contains x) : ∃ c∈certificate481.cells, c.region.interval.Contains x := rat_cut_group_covers certificate481 numericValid481 hx

def certificate482 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate321,PopulationCertificates.Batch016.certificate321,[MergedCutCells.Batch155.certificate1868,MergedCutCells.Batch155.certificate1869,MergedCutCells.Batch155.certificate1870],(2881984746303996301/1000000000000000000),none,(1/2),(281410679994066407/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid482 : certificate482.NumericValid := by decide +kernel
theorem cellsSound482 : ∀ c∈certificate482.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1868,MergedCutCells.Batch155.certificate1869,MergedCutCells.Batch155.certificate1870], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1868,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1869,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1870,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric482 : ∀ c∈certificate482.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1868,MergedCutCells.Batch155.certificate1869,MergedCutCells.Batch155.certificate1870], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1868,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1869,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1870,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid482 : ∀ c∈certificate482.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1868,MergedCutCells.Batch155.certificate1869,MergedCutCells.Batch155.certificate1870], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches482 : ∀ c∈certificate482.cells, c.population=certificate482.population := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1868,MergedCutCells.Batch155.certificate1869,MergedCutCells.Batch155.certificate1870], c.population=PopulationCertificates.Batch016.certificate321
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers482 {x : ℝ} (hx : certificate482.interval.Contains x) : ∃ c∈certificate482.cells, c.region.interval.Contains x := rat_cut_group_covers certificate482 numericValid482 hx

def certificate483 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate322,PopulationCertificates.Batch016.certificate322,[MergedCutCells.Batch155.certificate1871,MergedCutCells.Batch156.certificate1872,MergedCutCells.Batch156.certificate1873,MergedCutCells.Batch156.certificate1874,MergedCutCells.Batch156.certificate1875,MergedCutCells.Batch156.certificate1876],(886323062046346751/1000000000000000000),(some 64),(1/2),(241396292947153351/200000000000000000),(some (69314718055994531/100000000000000000)),(some (771187030157534051/500000000000000000))⟩
theorem numericValid483 : certificate483.NumericValid := by decide +kernel
theorem cellsSound483 : ∀ c∈certificate483.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1871,MergedCutCells.Batch156.certificate1872,MergedCutCells.Batch156.certificate1873,MergedCutCells.Batch156.certificate1874,MergedCutCells.Batch156.certificate1875,MergedCutCells.Batch156.certificate1876], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.sound1871,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1872,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1873,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1874,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1875,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1876,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric483 : ∀ c∈certificate483.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1871,MergedCutCells.Batch156.certificate1872,MergedCutCells.Batch156.certificate1873,MergedCutCells.Batch156.certificate1874,MergedCutCells.Batch156.certificate1875,MergedCutCells.Batch156.certificate1876], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch155.numericValid1871,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1872,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1873,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1874,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1875,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1876,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid483 : ∀ c∈certificate483.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1871,MergedCutCells.Batch156.certificate1872,MergedCutCells.Batch156.certificate1873,MergedCutCells.Batch156.certificate1874,MergedCutCells.Batch156.certificate1875,MergedCutCells.Batch156.certificate1876], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid162,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid162,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid162,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid162,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid162,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid162,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches483 : ∀ c∈certificate483.cells, c.population=certificate483.population := by
  change ∀ c∈[MergedCutCells.Batch155.certificate1871,MergedCutCells.Batch156.certificate1872,MergedCutCells.Batch156.certificate1873,MergedCutCells.Batch156.certificate1874,MergedCutCells.Batch156.certificate1875,MergedCutCells.Batch156.certificate1876], c.population=PopulationCertificates.Batch016.certificate322
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers483 {x : ℝ} (hx : certificate483.interval.Contains x) : ∃ c∈certificate483.cells, c.region.interval.Contains x := rat_cut_group_covers certificate483 numericValid483 hx

def certificate484 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate322,PopulationCertificates.Batch016.certificate322,[MergedCutCells.Batch156.certificate1877],64,none,(1/2),(2739959597303299037/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid484 : certificate484.NumericValid := by decide +kernel
theorem cellsSound484 : ∀ c∈certificate484.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1877], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1877,List.forall_mem_nil _⟩
theorem cellsNumeric484 : ∀ c∈certificate484.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1877], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1877,List.forall_mem_nil _⟩
theorem cellsEntropyValid484 : ∀ c∈certificate484.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1877], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches484 : ∀ c∈certificate484.cells, c.population=certificate484.population := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1877], c.population=PopulationCertificates.Batch016.certificate322
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers484 {x : ℝ} (hx : certificate484.interval.Contains x) : ∃ c∈certificate484.cells, c.region.interval.Contains x := rat_cut_group_covers certificate484 numericValid484 hx

def certificate485 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate323,PopulationCertificates.Batch016.certificate323,[MergedCutCells.Batch156.certificate1878,MergedCutCells.Batch156.certificate1879,MergedCutCells.Batch156.certificate1880],(573599707040021293/200000000000000000),none,(1/2),(1143736813049285929/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid485 : certificate485.NumericValid := by decide +kernel
theorem cellsSound485 : ∀ c∈certificate485.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1878,MergedCutCells.Batch156.certificate1879,MergedCutCells.Batch156.certificate1880], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1879,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1880,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric485 : ∀ c∈certificate485.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1878,MergedCutCells.Batch156.certificate1879,MergedCutCells.Batch156.certificate1880], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1879,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1880,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid485 : ∀ c∈certificate485.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1878,MergedCutCells.Batch156.certificate1879,MergedCutCells.Batch156.certificate1880], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches485 : ∀ c∈certificate485.cells, c.population=certificate485.population := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1878,MergedCutCells.Batch156.certificate1879,MergedCutCells.Batch156.certificate1880], c.population=PopulationCertificates.Batch016.certificate323
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers485 {x : ℝ} (hx : certificate485.interval.Contains x) : ∃ c∈certificate485.cells, c.region.interval.Contains x := rat_cut_group_covers certificate485 numericValid485 hx

def certificate486 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate324,PopulationCertificates.Batch016.certificate324,[MergedCutCells.Batch156.certificate1881,MergedCutCells.Batch156.certificate1882,MergedCutCells.Batch156.certificate1883,MergedCutCells.Batch157.certificate1884,MergedCutCells.Batch157.certificate1885,MergedCutCells.Batch157.certificate1886],(450824224646158339/500000000000000000),(some 64),(1/2),(609664367115582063/500000000000000000),(some (69314718055994531/100000000000000000)),(some (77190396200158529/50000000000000000))⟩
theorem numericValid486 : certificate486.NumericValid := by decide +kernel
theorem cellsSound486 : ∀ c∈certificate486.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1881,MergedCutCells.Batch156.certificate1882,MergedCutCells.Batch156.certificate1883,MergedCutCells.Batch157.certificate1884,MergedCutCells.Batch157.certificate1885,MergedCutCells.Batch157.certificate1886], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1881,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1882,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.sound1883,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1884,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1885,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1886,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric486 : ∀ c∈certificate486.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1881,MergedCutCells.Batch156.certificate1882,MergedCutCells.Batch156.certificate1883,MergedCutCells.Batch157.certificate1884,MergedCutCells.Batch157.certificate1885,MergedCutCells.Batch157.certificate1886], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1881,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1882,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch156.numericValid1883,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1884,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1885,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1886,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid486 : ∀ c∈certificate486.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1881,MergedCutCells.Batch156.certificate1882,MergedCutCells.Batch156.certificate1883,MergedCutCells.Batch157.certificate1884,MergedCutCells.Batch157.certificate1885,MergedCutCells.Batch157.certificate1886], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid163,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid163,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid163,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid163,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid163,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid163,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches486 : ∀ c∈certificate486.cells, c.population=certificate486.population := by
  change ∀ c∈[MergedCutCells.Batch156.certificate1881,MergedCutCells.Batch156.certificate1882,MergedCutCells.Batch156.certificate1883,MergedCutCells.Batch157.certificate1884,MergedCutCells.Batch157.certificate1885,MergedCutCells.Batch157.certificate1886], c.population=PopulationCertificates.Batch016.certificate324
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers486 {x : ℝ} (hx : certificate486.interval.Contains x) : ∃ c∈certificate486.cells, c.region.interval.Contains x := rat_cut_group_covers certificate486 numericValid486 hx

def certificate487 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate324,PopulationCertificates.Batch016.certificate324,[MergedCutCells.Batch157.certificate1887],64,none,(1/2),(342541555903717937/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid487 : certificate487.NumericValid := by decide +kernel
theorem cellsSound487 : ∀ c∈certificate487.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1887], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1887,List.forall_mem_nil _⟩
theorem cellsNumeric487 : ∀ c∈certificate487.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1887], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1887,List.forall_mem_nil _⟩
theorem cellsEntropyValid487 : ∀ c∈certificate487.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1887], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches487 : ∀ c∈certificate487.cells, c.population=certificate487.population := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1887], c.population=PopulationCertificates.Batch016.certificate324
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers487 {x : ℝ} (hx : certificate487.interval.Contains x) : ∃ c∈certificate487.cells, c.region.interval.Contains x := rat_cut_group_covers certificate487 numericValid487 hx

def certificate488 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate325,PopulationCertificates.Batch016.certificate325,[MergedCutCells.Batch157.certificate1888,MergedCutCells.Batch157.certificate1889,MergedCutCells.Batch157.certificate1890],(2854098053099252309/1000000000000000000),none,(1/2),(36310275112907719/31250000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid488 : certificate488.NumericValid := by decide +kernel
theorem cellsSound488 : ∀ c∈certificate488.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1888,MergedCutCells.Batch157.certificate1889,MergedCutCells.Batch157.certificate1890], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1888,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1889,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1890,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric488 : ∀ c∈certificate488.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1888,MergedCutCells.Batch157.certificate1889,MergedCutCells.Batch157.certificate1890], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1888,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1889,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1890,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid488 : ∀ c∈certificate488.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1888,MergedCutCells.Batch157.certificate1889,MergedCutCells.Batch157.certificate1890], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches488 : ∀ c∈certificate488.cells, c.population=certificate488.population := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1888,MergedCutCells.Batch157.certificate1889,MergedCutCells.Batch157.certificate1890], c.population=PopulationCertificates.Batch016.certificate325
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers488 {x : ℝ} (hx : certificate488.interval.Contains x) : ∃ c∈certificate488.cells, c.region.interval.Contains x := rat_cut_group_covers certificate488 numericValid488 hx

def certificate489 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate326,PopulationCertificates.Batch016.certificate326,[MergedCutCells.Batch157.certificate1891,MergedCutCells.Batch157.certificate1892,MergedCutCells.Batch157.certificate1893,MergedCutCells.Batch157.certificate1894,MergedCutCells.Batch157.certificate1895,MergedCutCells.Batch158.certificate1896],(917332949193513101/1000000000000000000),(some 64),(1/2),(30770325780896793/25000000000000000),(some (69314718055994531/100000000000000000)),(some (193192031631279777/125000000000000000))⟩
theorem numericValid489 : certificate489.NumericValid := by decide +kernel
theorem cellsSound489 : ∀ c∈certificate489.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1891,MergedCutCells.Batch157.certificate1892,MergedCutCells.Batch157.certificate1893,MergedCutCells.Batch157.certificate1894,MergedCutCells.Batch157.certificate1895,MergedCutCells.Batch158.certificate1896], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1891,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1892,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1893,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1894,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.sound1895,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1896,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric489 : ∀ c∈certificate489.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1891,MergedCutCells.Batch157.certificate1892,MergedCutCells.Batch157.certificate1893,MergedCutCells.Batch157.certificate1894,MergedCutCells.Batch157.certificate1895,MergedCutCells.Batch158.certificate1896], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1891,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1892,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1893,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1894,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch157.numericValid1895,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1896,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid489 : ∀ c∈certificate489.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1891,MergedCutCells.Batch157.certificate1892,MergedCutCells.Batch157.certificate1893,MergedCutCells.Batch157.certificate1894,MergedCutCells.Batch157.certificate1895,MergedCutCells.Batch158.certificate1896], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid164,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid164,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid164,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid164,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid164,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid164,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches489 : ∀ c∈certificate489.cells, c.population=certificate489.population := by
  change ∀ c∈[MergedCutCells.Batch157.certificate1891,MergedCutCells.Batch157.certificate1892,MergedCutCells.Batch157.certificate1893,MergedCutCells.Batch157.certificate1894,MergedCutCells.Batch157.certificate1895,MergedCutCells.Batch158.certificate1896], c.population=PopulationCertificates.Batch016.certificate326
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers489 {x : ℝ} (hx : certificate489.interval.Contains x) : ∃ c∈certificate489.cells, c.region.interval.Contains x := rat_cut_group_covers certificate489 numericValid489 hx

def certificate490 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate326,PopulationCertificates.Batch016.certificate326,[MergedCutCells.Batch158.certificate1897],64,none,(1/2),(2738088428274595293/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid490 : certificate490.NumericValid := by decide +kernel
theorem cellsSound490 : ∀ c∈certificate490.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1897], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1897,List.forall_mem_nil _⟩
theorem cellsNumeric490 : ∀ c∈certificate490.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1897], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1897,List.forall_mem_nil _⟩
theorem cellsEntropyValid490 : ∀ c∈certificate490.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1897], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches490 : ∀ c∈certificate490.cells, c.population=certificate490.population := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1897], c.population=PopulationCertificates.Batch016.certificate326
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers490 {x : ℝ} (hx : certificate490.interval.Contains x) : ∃ c∈certificate490.cells, c.region.interval.Contains x := rat_cut_group_covers certificate490 numericValid490 hx

def certificate491 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate327,PopulationCertificates.Batch016.certificate327,[MergedCutCells.Batch158.certificate1898,MergedCutCells.Batch158.certificate1899,MergedCutCells.Batch158.certificate1900,MergedCutCells.Batch158.certificate1901],(1420299980490139253/500000000000000000),none,(1/2),(1181777466125118649/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid491 : certificate491.NumericValid := by decide +kernel
theorem cellsSound491 : ∀ c∈certificate491.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1898,MergedCutCells.Batch158.certificate1899,MergedCutCells.Batch158.certificate1900,MergedCutCells.Batch158.certificate1901], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1898,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1899,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1901,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric491 : ∀ c∈certificate491.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1898,MergedCutCells.Batch158.certificate1899,MergedCutCells.Batch158.certificate1900,MergedCutCells.Batch158.certificate1901], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1898,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1899,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1901,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid491 : ∀ c∈certificate491.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1898,MergedCutCells.Batch158.certificate1899,MergedCutCells.Batch158.certificate1900,MergedCutCells.Batch158.certificate1901], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches491 : ∀ c∈certificate491.cells, c.population=certificate491.population := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1898,MergedCutCells.Batch158.certificate1899,MergedCutCells.Batch158.certificate1900,MergedCutCells.Batch158.certificate1901], c.population=PopulationCertificates.Batch016.certificate327
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers491 {x : ℝ} (hx : certificate491.interval.Contains x) : ∃ c∈certificate491.cells, c.region.interval.Contains x := rat_cut_group_covers certificate491 numericValid491 hx

end Cycle12.MergedCutGroups.Batch040
