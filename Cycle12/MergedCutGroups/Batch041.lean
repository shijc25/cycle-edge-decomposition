import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch016
import Cycle12.MergedCutCells.Batch158
import Cycle12.MergedCutCells.Batch159
import Cycle12.MergedCutCells.Batch160
import Cycle12.MergedCutCells.Batch161
import Cycle12.PopulationCertificates.Batch016

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch041

def certificate492 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate328,PopulationCertificates.Batch016.certificate328,[MergedCutCells.Batch158.certificate1902,MergedCutCells.Batch158.certificate1903,MergedCutCells.Batch158.certificate1904,MergedCutCells.Batch158.certificate1905,MergedCutCells.Batch158.certificate1906,MergedCutCells.Batch158.certificate1907,MergedCutCells.Batch159.certificate1908],(36621414749100103/40000000000000000),(some 64),(1/2),(1245738239548648021/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (30926889169404861/20000000000000000))⟩
theorem numericValid492 : certificate492.NumericValid := by decide +kernel
theorem cellsSound492 : ∀ c∈certificate492.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1902,MergedCutCells.Batch158.certificate1903,MergedCutCells.Batch158.certificate1904,MergedCutCells.Batch158.certificate1905,MergedCutCells.Batch158.certificate1906,MergedCutCells.Batch158.certificate1907,MergedCutCells.Batch159.certificate1908], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1902,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1903,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1904,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1905,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1906,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.sound1907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1908,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric492 : ∀ c∈certificate492.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1902,MergedCutCells.Batch158.certificate1903,MergedCutCells.Batch158.certificate1904,MergedCutCells.Batch158.certificate1905,MergedCutCells.Batch158.certificate1906,MergedCutCells.Batch158.certificate1907,MergedCutCells.Batch159.certificate1908], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1902,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1903,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1904,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1905,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1906,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch158.numericValid1907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1908,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid492 : ∀ c∈certificate492.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1902,MergedCutCells.Batch158.certificate1903,MergedCutCells.Batch158.certificate1904,MergedCutCells.Batch158.certificate1905,MergedCutCells.Batch158.certificate1906,MergedCutCells.Batch158.certificate1907,MergedCutCells.Batch159.certificate1908], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid165,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid165,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid165,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid165,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid165,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid165,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid165,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches492 : ∀ c∈certificate492.cells, c.population=certificate492.population := by
  change ∀ c∈[MergedCutCells.Batch158.certificate1902,MergedCutCells.Batch158.certificate1903,MergedCutCells.Batch158.certificate1904,MergedCutCells.Batch158.certificate1905,MergedCutCells.Batch158.certificate1906,MergedCutCells.Batch158.certificate1907,MergedCutCells.Batch159.certificate1908], c.population=PopulationCertificates.Batch016.certificate328
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers492 {x : ℝ} (hx : certificate492.interval.Contains x) : ∃ c∈certificate492.cells, c.region.interval.Contains x := rat_cut_group_covers certificate492 numericValid492 hx

def certificate493 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate328,PopulationCertificates.Batch016.certificate328,[MergedCutCells.Batch159.certificate1909],64,none,(1/2),(691597381721919769/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid493 : certificate493.NumericValid := by decide +kernel
theorem cellsSound493 : ∀ c∈certificate493.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1909], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1909,List.forall_mem_nil _⟩
theorem cellsNumeric493 : ∀ c∈certificate493.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1909], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1909,List.forall_mem_nil _⟩
theorem cellsEntropyValid493 : ∀ c∈certificate493.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1909], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches493 : ∀ c∈certificate493.cells, c.population=certificate493.population := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1909], c.population=PopulationCertificates.Batch016.certificate328
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers493 {x : ℝ} (hx : certificate493.interval.Contains x) : ∃ c∈certificate493.cells, c.region.interval.Contains x := rat_cut_group_covers certificate493 numericValid493 hx

def certificate494 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate329,PopulationCertificates.Batch016.certificate329,[MergedCutCells.Batch159.certificate1910,MergedCutCells.Batch159.certificate1911,MergedCutCells.Batch159.certificate1912,MergedCutCells.Batch159.certificate1913],(1413435205725931191/500000000000000000),none,(1/2),(1202478786994085647/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid494 : certificate494.NumericValid := by decide +kernel
theorem cellsSound494 : ∀ c∈certificate494.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1910,MergedCutCells.Batch159.certificate1911,MergedCutCells.Batch159.certificate1912,MergedCutCells.Batch159.certificate1913], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1910,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1911,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1913,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric494 : ∀ c∈certificate494.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1910,MergedCutCells.Batch159.certificate1911,MergedCutCells.Batch159.certificate1912,MergedCutCells.Batch159.certificate1913], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1910,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1911,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1913,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid494 : ∀ c∈certificate494.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1910,MergedCutCells.Batch159.certificate1911,MergedCutCells.Batch159.certificate1912,MergedCutCells.Batch159.certificate1913], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches494 : ∀ c∈certificate494.cells, c.population=certificate494.population := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1910,MergedCutCells.Batch159.certificate1911,MergedCutCells.Batch159.certificate1912,MergedCutCells.Batch159.certificate1913], c.population=PopulationCertificates.Batch016.certificate329
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers494 {x : ℝ} (hx : certificate494.interval.Contains x) : ∃ c∈certificate494.cells, c.region.interval.Contains x := rat_cut_group_covers certificate494 numericValid494 hx

def certificate495 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate330,PopulationCertificates.Batch016.certificate330,[MergedCutCells.Batch159.certificate1914,MergedCutCells.Batch159.certificate1915,MergedCutCells.Batch159.certificate1916,MergedCutCells.Batch159.certificate1917,MergedCutCells.Batch159.certificate1918,MergedCutCells.Batch159.certificate1919,MergedCutCells.Batch160.certificate1920],(56112657262993401/62500000000000000),(some 64),(1/2),(1101762941124032817/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (777802003310447887/500000000000000000))⟩
theorem numericValid495 : certificate495.NumericValid := by decide +kernel
theorem cellsSound495 : ∀ c∈certificate495.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1914,MergedCutCells.Batch159.certificate1915,MergedCutCells.Batch159.certificate1916,MergedCutCells.Batch159.certificate1917,MergedCutCells.Batch159.certificate1918,MergedCutCells.Batch159.certificate1919,MergedCutCells.Batch160.certificate1920], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1915,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1916,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1917,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1918,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.sound1919,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1920,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric495 : ∀ c∈certificate495.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1914,MergedCutCells.Batch159.certificate1915,MergedCutCells.Batch159.certificate1916,MergedCutCells.Batch159.certificate1917,MergedCutCells.Batch159.certificate1918,MergedCutCells.Batch159.certificate1919,MergedCutCells.Batch160.certificate1920], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1915,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1916,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1917,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1918,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch159.numericValid1919,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1920,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid495 : ∀ c∈certificate495.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1914,MergedCutCells.Batch159.certificate1915,MergedCutCells.Batch159.certificate1916,MergedCutCells.Batch159.certificate1917,MergedCutCells.Batch159.certificate1918,MergedCutCells.Batch159.certificate1919,MergedCutCells.Batch160.certificate1920], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid166,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid166,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid166,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid166,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid166,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid166,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid166,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches495 : ∀ c∈certificate495.cells, c.population=certificate495.population := by
  change ∀ c∈[MergedCutCells.Batch159.certificate1914,MergedCutCells.Batch159.certificate1915,MergedCutCells.Batch159.certificate1916,MergedCutCells.Batch159.certificate1917,MergedCutCells.Batch159.certificate1918,MergedCutCells.Batch159.certificate1919,MergedCutCells.Batch160.certificate1920], c.population=PopulationCertificates.Batch016.certificate330
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers495 {x : ℝ} (hx : certificate495.interval.Contains x) : ∃ c∈certificate495.cells, c.region.interval.Contains x := rat_cut_group_covers certificate495 numericValid495 hx

def certificate496 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate330,PopulationCertificates.Batch016.certificate330,[MergedCutCells.Batch160.certificate1921],64,none,(1/2),(104809893297217179/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid496 : certificate496.NumericValid := by decide +kernel
theorem cellsSound496 : ∀ c∈certificate496.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1921], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1921,List.forall_mem_nil _⟩
theorem cellsNumeric496 : ∀ c∈certificate496.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1921], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1921,List.forall_mem_nil _⟩
theorem cellsEntropyValid496 : ∀ c∈certificate496.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1921], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches496 : ∀ c∈certificate496.cells, c.population=certificate496.population := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1921], c.population=PopulationCertificates.Batch016.certificate330
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers496 {x : ℝ} (hx : certificate496.interval.Contains x) : ∃ c∈certificate496.cells, c.region.interval.Contains x := rat_cut_group_covers certificate496 numericValid496 hx

def certificate497 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate331,PopulationCertificates.Batch016.certificate331,[MergedCutCells.Batch160.certificate1922,MergedCutCells.Batch160.certificate1923,MergedCutCells.Batch160.certificate1924,MergedCutCells.Batch160.certificate1925],(2767977877874708691/1000000000000000000),none,(1/2),(9226002556302373/7812500000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid497 : certificate497.NumericValid := by decide +kernel
theorem cellsSound497 : ∀ c∈certificate497.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1922,MergedCutCells.Batch160.certificate1923,MergedCutCells.Batch160.certificate1924,MergedCutCells.Batch160.certificate1925], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1922,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1923,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1925,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric497 : ∀ c∈certificate497.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1922,MergedCutCells.Batch160.certificate1923,MergedCutCells.Batch160.certificate1924,MergedCutCells.Batch160.certificate1925], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1922,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1923,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1925,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid497 : ∀ c∈certificate497.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1922,MergedCutCells.Batch160.certificate1923,MergedCutCells.Batch160.certificate1924,MergedCutCells.Batch160.certificate1925], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches497 : ∀ c∈certificate497.cells, c.population=certificate497.population := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1922,MergedCutCells.Batch160.certificate1923,MergedCutCells.Batch160.certificate1924,MergedCutCells.Batch160.certificate1925], c.population=PopulationCertificates.Batch016.certificate331
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers497 {x : ℝ} (hx : certificate497.interval.Contains x) : ∃ c∈certificate497.cells, c.region.interval.Contains x := rat_cut_group_covers certificate497 numericValid497 hx

def certificate498 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate332,PopulationCertificates.Batch016.certificate332,[MergedCutCells.Batch160.certificate1926,MergedCutCells.Batch160.certificate1927,MergedCutCells.Batch160.certificate1928,MergedCutCells.Batch160.certificate1929,MergedCutCells.Batch160.certificate1930,MergedCutCells.Batch160.certificate1931],(453735087501386871/500000000000000000),(some 64),(1/2),(288048761278232777/250000000000000000),(some (69314718055994531/100000000000000000)),(some (97511076965477787/62500000000000000))⟩
theorem numericValid498 : certificate498.NumericValid := by decide +kernel
theorem cellsSound498 : ∀ c∈certificate498.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1926,MergedCutCells.Batch160.certificate1927,MergedCutCells.Batch160.certificate1928,MergedCutCells.Batch160.certificate1929,MergedCutCells.Batch160.certificate1930,MergedCutCells.Batch160.certificate1931], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1926,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1927,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1928,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1930,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.sound1931,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric498 : ∀ c∈certificate498.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1926,MergedCutCells.Batch160.certificate1927,MergedCutCells.Batch160.certificate1928,MergedCutCells.Batch160.certificate1929,MergedCutCells.Batch160.certificate1930,MergedCutCells.Batch160.certificate1931], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1926,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1927,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1928,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1930,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch160.numericValid1931,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid498 : ∀ c∈certificate498.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1926,MergedCutCells.Batch160.certificate1927,MergedCutCells.Batch160.certificate1928,MergedCutCells.Batch160.certificate1929,MergedCutCells.Batch160.certificate1930,MergedCutCells.Batch160.certificate1931], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid167,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid167,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid167,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid167,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid167,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid167,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches498 : ∀ c∈certificate498.cells, c.population=certificate498.population := by
  change ∀ c∈[MergedCutCells.Batch160.certificate1926,MergedCutCells.Batch160.certificate1927,MergedCutCells.Batch160.certificate1928,MergedCutCells.Batch160.certificate1929,MergedCutCells.Batch160.certificate1930,MergedCutCells.Batch160.certificate1931], c.population=PopulationCertificates.Batch016.certificate332
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers498 {x : ℝ} (hx : certificate498.interval.Contains x) : ∃ c∈certificate498.cells, c.region.interval.Contains x := rat_cut_group_covers certificate498 numericValid498 hx

def certificate499 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate332,PopulationCertificates.Batch016.certificate332,[MergedCutCells.Batch161.certificate1932],64,none,(1/2),(542719964161845139/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid499 : certificate499.NumericValid := by decide +kernel
theorem cellsSound499 : ∀ c∈certificate499.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1932], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1932,List.forall_mem_nil _⟩
theorem cellsNumeric499 : ∀ c∈certificate499.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1932], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1932,List.forall_mem_nil _⟩
theorem cellsEntropyValid499 : ∀ c∈certificate499.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1932], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches499 : ∀ c∈certificate499.cells, c.population=certificate499.population := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1932], c.population=PopulationCertificates.Batch016.certificate332
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers499 {x : ℝ} (hx : certificate499.interval.Contains x) : ∃ c∈certificate499.cells, c.region.interval.Contains x := rat_cut_group_covers certificate499 numericValid499 hx

def certificate500 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate333,PopulationCertificates.Batch016.certificate333,[MergedCutCells.Batch161.certificate1933,MergedCutCells.Batch161.certificate1934,MergedCutCells.Batch161.certificate1935,MergedCutCells.Batch161.certificate1936],(339413571042567119/125000000000000000),none,(1/2),(627421046648653443/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid500 : certificate500.NumericValid := by decide +kernel
theorem cellsSound500 : ∀ c∈certificate500.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1933,MergedCutCells.Batch161.certificate1934,MergedCutCells.Batch161.certificate1935,MergedCutCells.Batch161.certificate1936], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1934,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1935,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1936,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric500 : ∀ c∈certificate500.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1933,MergedCutCells.Batch161.certificate1934,MergedCutCells.Batch161.certificate1935,MergedCutCells.Batch161.certificate1936], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1934,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1935,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1936,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid500 : ∀ c∈certificate500.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1933,MergedCutCells.Batch161.certificate1934,MergedCutCells.Batch161.certificate1935,MergedCutCells.Batch161.certificate1936], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches500 : ∀ c∈certificate500.cells, c.population=certificate500.population := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1933,MergedCutCells.Batch161.certificate1934,MergedCutCells.Batch161.certificate1935,MergedCutCells.Batch161.certificate1936], c.population=PopulationCertificates.Batch016.certificate333
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers500 {x : ℝ} (hx : certificate500.interval.Contains x) : ∃ c∈certificate500.cells, c.region.interval.Contains x := rat_cut_group_covers certificate500 numericValid500 hx

def certificate501 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate334,PopulationCertificates.Batch016.certificate334,[MergedCutCells.Batch161.certificate1937,MergedCutCells.Batch161.certificate1938],(35724418940030839/62500000000000000),(some (659045959/500000000)),(1/2),(150815529153364347/500000000000000000),(some (9332583607727791/1000000000000000000)),(some (1209342291522181/1000000000000000000))⟩
theorem numericValid501 : certificate501.NumericValid := by decide +kernel
theorem cellsSound501 : ∀ c∈certificate501.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1937,MergedCutCells.Batch161.certificate1938], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1937,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1938,List.forall_mem_nil _⟩⟩
theorem cellsNumeric501 : ∀ c∈certificate501.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1937,MergedCutCells.Batch161.certificate1938], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1937,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1938,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid501 : ∀ c∈certificate501.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1937,MergedCutCells.Batch161.certificate1938], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid168,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid168,List.forall_mem_nil _⟩⟩
theorem populationMatches501 : ∀ c∈certificate501.cells, c.population=certificate501.population := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1937,MergedCutCells.Batch161.certificate1938], c.population=PopulationCertificates.Batch016.certificate334
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers501 {x : ℝ} (hx : certificate501.interval.Contains x) : ∃ c∈certificate501.cells, c.region.interval.Contains x := rat_cut_group_covers certificate501 numericValid501 hx

def certificate502 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate334,PopulationCertificates.Batch016.certificate334,[MergedCutCells.Batch161.certificate1939,MergedCutCells.Batch161.certificate1940,MergedCutCells.Batch161.certificate1941],(659045959/500000000),none,(1/2),(150541368633435963/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid502 : certificate502.NumericValid := by decide +kernel
theorem cellsSound502 : ∀ c∈certificate502.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1939,MergedCutCells.Batch161.certificate1940,MergedCutCells.Batch161.certificate1941], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1939,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1940,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1941,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric502 : ∀ c∈certificate502.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1939,MergedCutCells.Batch161.certificate1940,MergedCutCells.Batch161.certificate1941], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1939,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1940,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1941,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid502 : ∀ c∈certificate502.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1939,MergedCutCells.Batch161.certificate1940,MergedCutCells.Batch161.certificate1941], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches502 : ∀ c∈certificate502.cells, c.population=certificate502.population := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1939,MergedCutCells.Batch161.certificate1940,MergedCutCells.Batch161.certificate1941], c.population=PopulationCertificates.Batch016.certificate334
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers502 {x : ℝ} (hx : certificate502.interval.Contains x) : ∃ c∈certificate502.cells, c.region.interval.Contains x := rat_cut_group_covers certificate502 numericValid502 hx

def certificate503 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate335,PopulationCertificates.Batch016.certificate335,[MergedCutCells.Batch161.certificate1942,MergedCutCells.Batch161.certificate1943],(2306072357448409151/500000000000000000),none,(1/2),(1305734835835261763/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid503 : certificate503.NumericValid := by decide +kernel
theorem cellsSound503 : ∀ c∈certificate503.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1942,MergedCutCells.Batch161.certificate1943], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1942,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.sound1943,List.forall_mem_nil _⟩⟩
theorem cellsNumeric503 : ∀ c∈certificate503.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1942,MergedCutCells.Batch161.certificate1943], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1942,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch161.numericValid1943,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid503 : ∀ c∈certificate503.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1942,MergedCutCells.Batch161.certificate1943], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches503 : ∀ c∈certificate503.cells, c.population=certificate503.population := by
  change ∀ c∈[MergedCutCells.Batch161.certificate1942,MergedCutCells.Batch161.certificate1943], c.population=PopulationCertificates.Batch016.certificate335
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers503 {x : ℝ} (hx : certificate503.interval.Contains x) : ∃ c∈certificate503.cells, c.region.interval.Contains x := rat_cut_group_covers certificate503 numericValid503 hx

end Cycle12.MergedCutGroups.Batch041
