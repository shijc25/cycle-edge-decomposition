import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch016
import Cycle12.GeometryCertificates.Batch017
import Cycle12.MergedCutCells.Batch162
import Cycle12.MergedCutCells.Batch163
import Cycle12.MergedCutCells.Batch164
import Cycle12.PopulationCertificates.Batch016
import Cycle12.PopulationCertificates.Batch017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch042

def certificate504 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate336,PopulationCertificates.Batch016.certificate336,[MergedCutCells.Batch162.certificate1944,MergedCutCells.Batch162.certificate1945],(286817804046467961/500000000000000000),(some (331940589/250000000)),(1/2),(302303942827118669/1000000000000000000),(some (13791142965931707/1000000000000000000)),(some (59313824402313/31250000000000000))⟩
theorem numericValid504 : certificate504.NumericValid := by decide +kernel
theorem cellsSound504 : ∀ c∈certificate504.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1944,MergedCutCells.Batch162.certificate1945], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1944,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1945,List.forall_mem_nil _⟩⟩
theorem cellsNumeric504 : ∀ c∈certificate504.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1944,MergedCutCells.Batch162.certificate1945], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1944,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1945,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid504 : ∀ c∈certificate504.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1944,MergedCutCells.Batch162.certificate1945], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid169,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid169,List.forall_mem_nil _⟩⟩
theorem populationMatches504 : ∀ c∈certificate504.cells, c.population=certificate504.population := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1944,MergedCutCells.Batch162.certificate1945], c.population=PopulationCertificates.Batch016.certificate336
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers504 {x : ℝ} (hx : certificate504.interval.Contains x) : ∃ c∈certificate504.cells, c.region.interval.Contains x := rat_cut_group_covers certificate504 numericValid504 hx

def certificate505 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate336,PopulationCertificates.Batch016.certificate336,[MergedCutCells.Batch162.certificate1946,MergedCutCells.Batch162.certificate1947,MergedCutCells.Batch162.certificate1948],(331940589/250000000),none,(1/2),(7542499285035911/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid505 : certificate505.NumericValid := by decide +kernel
theorem cellsSound505 : ∀ c∈certificate505.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1946,MergedCutCells.Batch162.certificate1947,MergedCutCells.Batch162.certificate1948], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1946,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1947,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1948,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric505 : ∀ c∈certificate505.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1946,MergedCutCells.Batch162.certificate1947,MergedCutCells.Batch162.certificate1948], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1946,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1947,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1948,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid505 : ∀ c∈certificate505.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1946,MergedCutCells.Batch162.certificate1947,MergedCutCells.Batch162.certificate1948], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches505 : ∀ c∈certificate505.cells, c.population=certificate505.population := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1946,MergedCutCells.Batch162.certificate1947,MergedCutCells.Batch162.certificate1948], c.population=PopulationCertificates.Batch016.certificate336
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers505 {x : ℝ} (hx : certificate505.interval.Contains x) : ∃ c∈certificate505.cells, c.region.interval.Contains x := rat_cut_group_covers certificate505 numericValid505 hx

def certificate506 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate337,PopulationCertificates.Batch016.certificate337,[MergedCutCells.Batch162.certificate1949,MergedCutCells.Batch162.certificate1950],(910224633697091599/200000000000000000),none,(1/2),(642889524658843919/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid506 : certificate506.NumericValid := by decide +kernel
theorem cellsSound506 : ∀ c∈certificate506.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1949,MergedCutCells.Batch162.certificate1950], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1949,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1950,List.forall_mem_nil _⟩⟩
theorem cellsNumeric506 : ∀ c∈certificate506.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1949,MergedCutCells.Batch162.certificate1950], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1949,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1950,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid506 : ∀ c∈certificate506.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1949,MergedCutCells.Batch162.certificate1950], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches506 : ∀ c∈certificate506.cells, c.population=certificate506.population := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1949,MergedCutCells.Batch162.certificate1950], c.population=PopulationCertificates.Batch016.certificate337
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers506 {x : ℝ} (hx : certificate506.interval.Contains x) : ∃ c∈certificate506.cells, c.region.interval.Contains x := rat_cut_group_covers certificate506 numericValid506 hx

def certificate507 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate338,PopulationCertificates.Batch016.certificate338,[MergedCutCells.Batch162.certificate1951,MergedCutCells.Batch162.certificate1952],(573463758674682273/1000000000000000000),(some (647534017/500000000)),(1/2),(292502444769705443/1000000000000000000),(some (9378994993876499/500000000000000000)),(some (339456345882849/125000000000000000))⟩
theorem numericValid507 : certificate507.NumericValid := by decide +kernel
theorem cellsSound507 : ∀ c∈certificate507.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1951,MergedCutCells.Batch162.certificate1952], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1951,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1952,List.forall_mem_nil _⟩⟩
theorem cellsNumeric507 : ∀ c∈certificate507.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1951,MergedCutCells.Batch162.certificate1952], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1951,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1952,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid507 : ∀ c∈certificate507.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1951,MergedCutCells.Batch162.certificate1952], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid170,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid170,List.forall_mem_nil _⟩⟩
theorem populationMatches507 : ∀ c∈certificate507.cells, c.population=certificate507.population := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1951,MergedCutCells.Batch162.certificate1952], c.population=PopulationCertificates.Batch016.certificate338
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers507 {x : ℝ} (hx : certificate507.interval.Contains x) : ∃ c∈certificate507.cells, c.region.interval.Contains x := rat_cut_group_covers certificate507 numericValid507 hx

def certificate508 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate338,PopulationCertificates.Batch016.certificate338,[MergedCutCells.Batch162.certificate1953,MergedCutCells.Batch162.certificate1954,MergedCutCells.Batch162.certificate1955,MergedCutCells.Batch163.certificate1956],(647534017/500000000),none,(1/2),(291589867043936763/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid508 : certificate508.NumericValid := by decide +kernel
theorem cellsSound508 : ∀ c∈certificate508.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1953,MergedCutCells.Batch162.certificate1954,MergedCutCells.Batch162.certificate1955,MergedCutCells.Batch163.certificate1956], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1954,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.sound1955,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1956,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric508 : ∀ c∈certificate508.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1953,MergedCutCells.Batch162.certificate1954,MergedCutCells.Batch162.certificate1955,MergedCutCells.Batch163.certificate1956], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1954,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch162.numericValid1955,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1956,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid508 : ∀ c∈certificate508.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1953,MergedCutCells.Batch162.certificate1954,MergedCutCells.Batch162.certificate1955,MergedCutCells.Batch163.certificate1956], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches508 : ∀ c∈certificate508.cells, c.population=certificate508.population := by
  change ∀ c∈[MergedCutCells.Batch162.certificate1953,MergedCutCells.Batch162.certificate1954,MergedCutCells.Batch162.certificate1955,MergedCutCells.Batch163.certificate1956], c.population=PopulationCertificates.Batch016.certificate338
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers508 {x : ℝ} (hx : certificate508.interval.Contains x) : ∃ c∈certificate508.cells, c.region.interval.Contains x := rat_cut_group_covers certificate508 numericValid508 hx

def certificate509 : RatCutGroup := ⟨GeometryCertificates.Batch016.certificate339,PopulationCertificates.Batch016.certificate339,[MergedCutCells.Batch163.certificate1957,MergedCutCells.Batch163.certificate1958],(2311402822644835119/500000000000000000),none,(1/2),(267762466128757887/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid509 : certificate509.NumericValid := by decide +kernel
theorem cellsSound509 : ∀ c∈certificate509.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1957,MergedCutCells.Batch163.certificate1958], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1958,List.forall_mem_nil _⟩⟩
theorem cellsNumeric509 : ∀ c∈certificate509.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1957,MergedCutCells.Batch163.certificate1958], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1958,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid509 : ∀ c∈certificate509.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1957,MergedCutCells.Batch163.certificate1958], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches509 : ∀ c∈certificate509.cells, c.population=certificate509.population := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1957,MergedCutCells.Batch163.certificate1958], c.population=PopulationCertificates.Batch016.certificate339
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers509 {x : ℝ} (hx : certificate509.interval.Contains x) : ∃ c∈certificate509.cells, c.region.interval.Contains x := rat_cut_group_covers certificate509 numericValid509 hx

def certificate510 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate340,PopulationCertificates.Batch017.certificate340,[MergedCutCells.Batch163.certificate1959,MergedCutCells.Batch163.certificate1960],(575581717866339571/1000000000000000000),(some (51960937/40000000)),(1/2),(9150824461389049/31250000000000000),(some (24420579270983407/1000000000000000000)),(some (231356890103859/62500000000000000))⟩
theorem numericValid510 : certificate510.NumericValid := by decide +kernel
theorem cellsSound510 : ∀ c∈certificate510.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1959,MergedCutCells.Batch163.certificate1960], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1959,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1960,List.forall_mem_nil _⟩⟩
theorem cellsNumeric510 : ∀ c∈certificate510.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1959,MergedCutCells.Batch163.certificate1960], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1959,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1960,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid510 : ∀ c∈certificate510.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1959,MergedCutCells.Batch163.certificate1960], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid171,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid171,List.forall_mem_nil _⟩⟩
theorem populationMatches510 : ∀ c∈certificate510.cells, c.population=certificate510.population := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1959,MergedCutCells.Batch163.certificate1960], c.population=PopulationCertificates.Batch017.certificate340
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers510 {x : ℝ} (hx : certificate510.interval.Contains x) : ∃ c∈certificate510.cells, c.region.interval.Contains x := rat_cut_group_covers certificate510 numericValid510 hx

def certificate511 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate340,PopulationCertificates.Batch017.certificate340,[MergedCutCells.Batch163.certificate1961,MergedCutCells.Batch163.certificate1962,MergedCutCells.Batch163.certificate1963],(51960937/40000000),none,(1/2),(145895134552456589/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid511 : certificate511.NumericValid := by decide +kernel
theorem cellsSound511 : ∀ c∈certificate511.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1961,MergedCutCells.Batch163.certificate1962,MergedCutCells.Batch163.certificate1963], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1961,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1962,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1963,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric511 : ∀ c∈certificate511.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1961,MergedCutCells.Batch163.certificate1962,MergedCutCells.Batch163.certificate1963], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1961,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1962,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1963,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid511 : ∀ c∈certificate511.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1961,MergedCutCells.Batch163.certificate1962,MergedCutCells.Batch163.certificate1963], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches511 : ∀ c∈certificate511.cells, c.population=certificate511.population := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1961,MergedCutCells.Batch163.certificate1962,MergedCutCells.Batch163.certificate1963], c.population=PopulationCertificates.Batch017.certificate340
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers511 {x : ℝ} (hx : certificate511.interval.Contains x) : ∃ c∈certificate511.cells, c.region.interval.Contains x := rat_cut_group_covers certificate511 numericValid511 hx

def certificate512 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate341,PopulationCertificates.Batch017.certificate341,[MergedCutCells.Batch163.certificate1964,MergedCutCells.Batch163.certificate1965],(2337335379661358019/500000000000000000),none,(1/2),(695900502449443863/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid512 : certificate512.NumericValid := by decide +kernel
theorem cellsSound512 : ∀ c∈certificate512.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1964,MergedCutCells.Batch163.certificate1965], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1965,List.forall_mem_nil _⟩⟩
theorem cellsNumeric512 : ∀ c∈certificate512.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1964,MergedCutCells.Batch163.certificate1965], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1965,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid512 : ∀ c∈certificate512.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1964,MergedCutCells.Batch163.certificate1965], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches512 : ∀ c∈certificate512.cells, c.population=certificate512.population := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1964,MergedCutCells.Batch163.certificate1965], c.population=PopulationCertificates.Batch017.certificate341
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers512 {x : ℝ} (hx : certificate512.interval.Contains x) : ∃ c∈certificate512.cells, c.region.interval.Contains x := rat_cut_group_covers certificate512 numericValid512 hx

def certificate513 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate342,PopulationCertificates.Batch017.certificate342,[MergedCutCells.Batch163.certificate1966,MergedCutCells.Batch163.certificate1967],(289084772545842269/500000000000000000),(some (1303852909/1000000000)),(1/2),(293568475533460917/1000000000000000000),(some (6129947945905403/200000000000000000)),(some (484379359859359/100000000000000000))⟩
theorem numericValid513 : certificate513.NumericValid := by decide +kernel
theorem cellsSound513 : ∀ c∈certificate513.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1966,MergedCutCells.Batch163.certificate1967], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1966,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.sound1967,List.forall_mem_nil _⟩⟩
theorem cellsNumeric513 : ∀ c∈certificate513.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1966,MergedCutCells.Batch163.certificate1967], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1966,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch163.numericValid1967,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid513 : ∀ c∈certificate513.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1966,MergedCutCells.Batch163.certificate1967], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid172,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid172,List.forall_mem_nil _⟩⟩
theorem populationMatches513 : ∀ c∈certificate513.cells, c.population=certificate513.population := by
  change ∀ c∈[MergedCutCells.Batch163.certificate1966,MergedCutCells.Batch163.certificate1967], c.population=PopulationCertificates.Batch017.certificate342
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers513 {x : ℝ} (hx : certificate513.interval.Contains x) : ∃ c∈certificate513.cells, c.region.interval.Contains x := rat_cut_group_covers certificate513 numericValid513 hx

def certificate514 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate342,PopulationCertificates.Batch017.certificate342,[MergedCutCells.Batch164.certificate1968,MergedCutCells.Batch164.certificate1969,MergedCutCells.Batch164.certificate1970],(1303852909/1000000000),none,(1/2),(146017373574236217/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid514 : certificate514.NumericValid := by decide +kernel
theorem cellsSound514 : ∀ c∈certificate514.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1968,MergedCutCells.Batch164.certificate1969,MergedCutCells.Batch164.certificate1970], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1968,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1970,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric514 : ∀ c∈certificate514.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1968,MergedCutCells.Batch164.certificate1969,MergedCutCells.Batch164.certificate1970], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1968,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1970,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid514 : ∀ c∈certificate514.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1968,MergedCutCells.Batch164.certificate1969,MergedCutCells.Batch164.certificate1970], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches514 : ∀ c∈certificate514.cells, c.population=certificate514.population := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1968,MergedCutCells.Batch164.certificate1969,MergedCutCells.Batch164.certificate1970], c.population=PopulationCertificates.Batch017.certificate342
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers514 {x : ℝ} (hx : certificate514.interval.Contains x) : ∃ c∈certificate514.cells, c.region.interval.Contains x := rat_cut_group_covers certificate514 numericValid514 hx

def certificate515 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate343,PopulationCertificates.Batch017.certificate343,[MergedCutCells.Batch164.certificate1971,MergedCutCells.Batch164.certificate1972],(2363971914728149319/500000000000000000),none,(1/2),(144552433078278141/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid515 : certificate515.NumericValid := by decide +kernel
theorem cellsSound515 : ∀ c∈certificate515.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1971,MergedCutCells.Batch164.certificate1972], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1972,List.forall_mem_nil _⟩⟩
theorem cellsNumeric515 : ∀ c∈certificate515.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1971,MergedCutCells.Batch164.certificate1972], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1972,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid515 : ∀ c∈certificate515.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1971,MergedCutCells.Batch164.certificate1972], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches515 : ∀ c∈certificate515.cells, c.population=certificate515.population := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1971,MergedCutCells.Batch164.certificate1972], c.population=PopulationCertificates.Batch017.certificate343
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers515 {x : ℝ} (hx : certificate515.interval.Contains x) : ∃ c∈certificate515.cells, c.region.interval.Contains x := rat_cut_group_covers certificate515 numericValid515 hx

end Cycle12.MergedCutGroups.Batch042
