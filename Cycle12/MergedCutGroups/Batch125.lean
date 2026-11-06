import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch051
import Cycle12.MergedCutCells.Batch417
import Cycle12.MergedCutCells.Batch418
import Cycle12.MergedCutCells.Batch419
import Cycle12.MergedCutCells.Batch420
import Cycle12.PopulationCertificates.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch125

def certificate1500 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1021,PopulationCertificates.Batch051.certificate1021,[MergedCutCells.Batch417.certificate5013,MergedCutCells.Batch417.certificate5014,MergedCutCells.Batch417.certificate5015,MergedCutCells.Batch418.certificate5016,MergedCutCells.Batch418.certificate5017],(723251227635485873/1000000000000000000),none,(1/40),(7966079306356201/125000000000000000),none,none⟩
theorem numericValid1500 : certificate1500.NumericValid := by decide +kernel
theorem cellsSound1500 : ∀ c∈certificate1500.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5013,MergedCutCells.Batch417.certificate5014,MergedCutCells.Batch417.certificate5015,MergedCutCells.Batch418.certificate5016,MergedCutCells.Batch418.certificate5017], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5013,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5014,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.sound5015,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5016,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5017,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1500 : ∀ c∈certificate1500.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5013,MergedCutCells.Batch417.certificate5014,MergedCutCells.Batch417.certificate5015,MergedCutCells.Batch418.certificate5016,MergedCutCells.Batch418.certificate5017], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5013,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5014,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch417.numericValid5015,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5016,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5017,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1500 : ∀ c∈certificate1500.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5013,MergedCutCells.Batch417.certificate5014,MergedCutCells.Batch417.certificate5015,MergedCutCells.Batch418.certificate5016,MergedCutCells.Batch418.certificate5017], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid734,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid735,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid736,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid737,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid738,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1500 : ∀ c∈certificate1500.cells, c.population=certificate1500.population := by
  change ∀ c∈[MergedCutCells.Batch417.certificate5013,MergedCutCells.Batch417.certificate5014,MergedCutCells.Batch417.certificate5015,MergedCutCells.Batch418.certificate5016,MergedCutCells.Batch418.certificate5017], c.population=PopulationCertificates.Batch051.certificate1021
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1500 {x : ℝ} (hx : certificate1500.interval.Contains x) : ∃ c∈certificate1500.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1500 numericValid1500 hx

def certificate1501 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1022,PopulationCertificates.Batch051.certificate1022,[MergedCutCells.Batch418.certificate5018,MergedCutCells.Batch418.certificate5019],(60690300511494241/100000000000000000),(some (1096518297/1000000000)),(1/2),(262115301407818593/1000000000000000000),(some (16002782170940281/500000000000000000)),(some (5099652283014399/1000000000000000000))⟩
theorem numericValid1501 : certificate1501.NumericValid := by decide +kernel
theorem cellsSound1501 : ∀ c∈certificate1501.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5018,MergedCutCells.Batch418.certificate5019], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5018,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5019,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1501 : ∀ c∈certificate1501.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5018,MergedCutCells.Batch418.certificate5019], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5018,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5019,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1501 : ∀ c∈certificate1501.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5018,MergedCutCells.Batch418.certificate5019], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid739,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy036.valid739,List.forall_mem_nil _⟩⟩
theorem populationMatches1501 : ∀ c∈certificate1501.cells, c.population=certificate1501.population := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5018,MergedCutCells.Batch418.certificate5019], c.population=PopulationCertificates.Batch051.certificate1022
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1501 {x : ℝ} (hx : certificate1501.interval.Contains x) : ∃ c∈certificate1501.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1501 numericValid1501 hx

def certificate1502 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1022,PopulationCertificates.Batch051.certificate1022,[MergedCutCells.Batch418.certificate5020,MergedCutCells.Batch418.certificate5021,MergedCutCells.Batch418.certificate5022],(1096518297/1000000000),none,(1/2),(16250113409649463/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1502 : certificate1502.NumericValid := by decide +kernel
theorem cellsSound1502 : ∀ c∈certificate1502.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5020,MergedCutCells.Batch418.certificate5021,MergedCutCells.Batch418.certificate5022], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5020,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5021,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5022,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1502 : ∀ c∈certificate1502.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5020,MergedCutCells.Batch418.certificate5021,MergedCutCells.Batch418.certificate5022], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5020,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5021,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5022,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1502 : ∀ c∈certificate1502.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5020,MergedCutCells.Batch418.certificate5021,MergedCutCells.Batch418.certificate5022], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1502 : ∀ c∈certificate1502.cells, c.population=certificate1502.population := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5020,MergedCutCells.Batch418.certificate5021,MergedCutCells.Batch418.certificate5022], c.population=PopulationCertificates.Batch051.certificate1022
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1502 {x : ℝ} (hx : certificate1502.interval.Contains x) : ∃ c∈certificate1502.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1502 numericValid1502 hx

def certificate1503 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1023,PopulationCertificates.Batch051.certificate1023,[MergedCutCells.Batch418.certificate5023,MergedCutCells.Batch418.certificate5024],(19888301767217360797/500000000000000000),none,(1/2),(4966985201711958459/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1503 : certificate1503.NumericValid := by decide +kernel
theorem cellsSound1503 : ∀ c∈certificate1503.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5023,MergedCutCells.Batch418.certificate5024], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5023,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5024,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1503 : ∀ c∈certificate1503.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5023,MergedCutCells.Batch418.certificate5024], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5023,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5024,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1503 : ∀ c∈certificate1503.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5023,MergedCutCells.Batch418.certificate5024], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1503 : ∀ c∈certificate1503.cells, c.population=certificate1503.population := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5023,MergedCutCells.Batch418.certificate5024], c.population=PopulationCertificates.Batch051.certificate1023
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1503 {x : ℝ} (hx : certificate1503.interval.Contains x) : ∃ c∈certificate1503.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1503 numericValid1503 hx

def certificate1504 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1024,PopulationCertificates.Batch051.certificate1024,[MergedCutCells.Batch418.certificate5025,MergedCutCells.Batch418.certificate5026,MergedCutCells.Batch418.certificate5027,MergedCutCells.Batch419.certificate5028,MergedCutCells.Batch419.certificate5029],(727286547631696929/1000000000000000000),none,(1/40),(35850032036350233/500000000000000000),none,none⟩
theorem numericValid1504 : certificate1504.NumericValid := by decide +kernel
theorem cellsSound1504 : ∀ c∈certificate1504.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5025,MergedCutCells.Batch418.certificate5026,MergedCutCells.Batch418.certificate5027,MergedCutCells.Batch419.certificate5028,MergedCutCells.Batch419.certificate5029], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5025,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5026,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.sound5027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5028,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5029,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1504 : ∀ c∈certificate1504.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5025,MergedCutCells.Batch418.certificate5026,MergedCutCells.Batch418.certificate5027,MergedCutCells.Batch419.certificate5028,MergedCutCells.Batch419.certificate5029], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5025,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5026,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch418.numericValid5027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5028,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5029,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1504 : ∀ c∈certificate1504.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5025,MergedCutCells.Batch418.certificate5026,MergedCutCells.Batch418.certificate5027,MergedCutCells.Batch419.certificate5028,MergedCutCells.Batch419.certificate5029], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid740,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid741,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid742,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid743,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid744,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1504 : ∀ c∈certificate1504.cells, c.population=certificate1504.population := by
  change ∀ c∈[MergedCutCells.Batch418.certificate5025,MergedCutCells.Batch418.certificate5026,MergedCutCells.Batch418.certificate5027,MergedCutCells.Batch419.certificate5028,MergedCutCells.Batch419.certificate5029], c.population=PopulationCertificates.Batch051.certificate1024
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1504 {x : ℝ} (hx : certificate1504.interval.Contains x) : ∃ c∈certificate1504.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1504 numericValid1504 hx

def certificate1505 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1025,PopulationCertificates.Batch051.certificate1025,[MergedCutCells.Batch419.certificate5030,MergedCutCells.Batch419.certificate5031],(152220822724973043/250000000000000000),(some (1099641187/1000000000)),(1/2),(133761313444190301/500000000000000000),(some (16576490533258847/500000000000000000)),(some (212724584632999/40000000000000000))⟩
theorem numericValid1505 : certificate1505.NumericValid := by decide +kernel
theorem cellsSound1505 : ∀ c∈certificate1505.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5030,MergedCutCells.Batch419.certificate5031], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5030,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5031,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1505 : ∀ c∈certificate1505.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5030,MergedCutCells.Batch419.certificate5031], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5030,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5031,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1505 : ∀ c∈certificate1505.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5030,MergedCutCells.Batch419.certificate5031], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid745,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid745,List.forall_mem_nil _⟩⟩
theorem populationMatches1505 : ∀ c∈certificate1505.cells, c.population=certificate1505.population := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5030,MergedCutCells.Batch419.certificate5031], c.population=PopulationCertificates.Batch051.certificate1025
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1505 {x : ℝ} (hx : certificate1505.interval.Contains x) : ∃ c∈certificate1505.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1505 numericValid1505 hx

def certificate1506 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1025,PopulationCertificates.Batch051.certificate1025,[MergedCutCells.Batch419.certificate5032,MergedCutCells.Batch419.certificate5033,MergedCutCells.Batch419.certificate5034],(1099641187/1000000000),none,(1/2),(132596369204375327/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1506 : certificate1506.NumericValid := by decide +kernel
theorem cellsSound1506 : ∀ c∈certificate1506.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5032,MergedCutCells.Batch419.certificate5033,MergedCutCells.Batch419.certificate5034], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5032,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5033,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5034,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1506 : ∀ c∈certificate1506.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5032,MergedCutCells.Batch419.certificate5033,MergedCutCells.Batch419.certificate5034], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5032,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5033,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5034,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1506 : ∀ c∈certificate1506.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5032,MergedCutCells.Batch419.certificate5033,MergedCutCells.Batch419.certificate5034], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1506 : ∀ c∈certificate1506.cells, c.population=certificate1506.population := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5032,MergedCutCells.Batch419.certificate5033,MergedCutCells.Batch419.certificate5034], c.population=PopulationCertificates.Batch051.certificate1025
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1506 {x : ℝ} (hx : certificate1506.interval.Contains x) : ∃ c∈certificate1506.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1506 numericValid1506 hx

def certificate1507 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1026,PopulationCertificates.Batch051.certificate1026,[MergedCutCells.Batch419.certificate5035,MergedCutCells.Batch419.certificate5036],(40641669653263970401/1000000000000000000),none,(1/2),(10148896583497186903/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1507 : certificate1507.NumericValid := by decide +kernel
theorem cellsSound1507 : ∀ c∈certificate1507.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5035,MergedCutCells.Batch419.certificate5036], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5035,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5036,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1507 : ∀ c∈certificate1507.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5035,MergedCutCells.Batch419.certificate5036], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5035,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5036,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1507 : ∀ c∈certificate1507.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5035,MergedCutCells.Batch419.certificate5036], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1507 : ∀ c∈certificate1507.cells, c.population=certificate1507.population := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5035,MergedCutCells.Batch419.certificate5036], c.population=PopulationCertificates.Batch051.certificate1026
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1507 {x : ℝ} (hx : certificate1507.interval.Contains x) : ∃ c∈certificate1507.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1507 numericValid1507 hx

def certificate1508 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1027,PopulationCertificates.Batch051.certificate1027,[MergedCutCells.Batch419.certificate5037,MergedCutCells.Batch419.certificate5038,MergedCutCells.Batch419.certificate5039,MergedCutCells.Batch420.certificate5040,MergedCutCells.Batch420.certificate5041],(146267405418839919/200000000000000000),none,(1/40),(1251914166802503/15625000000000000),none,none⟩
theorem numericValid1508 : certificate1508.NumericValid := by decide +kernel
theorem cellsSound1508 : ∀ c∈certificate1508.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5037,MergedCutCells.Batch419.certificate5038,MergedCutCells.Batch419.certificate5039,MergedCutCells.Batch420.certificate5040,MergedCutCells.Batch420.certificate5041], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5038,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.sound5039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5040,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5041,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric1508 : ∀ c∈certificate1508.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5037,MergedCutCells.Batch419.certificate5038,MergedCutCells.Batch419.certificate5039,MergedCutCells.Batch420.certificate5040,MergedCutCells.Batch420.certificate5041], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5038,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch419.numericValid5039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5040,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5041,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid1508 : ∀ c∈certificate1508.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5037,MergedCutCells.Batch419.certificate5038,MergedCutCells.Batch419.certificate5039,MergedCutCells.Batch420.certificate5040,MergedCutCells.Batch420.certificate5041], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid746,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid747,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid748,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid749,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid750,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches1508 : ∀ c∈certificate1508.cells, c.population=certificate1508.population := by
  change ∀ c∈[MergedCutCells.Batch419.certificate5037,MergedCutCells.Batch419.certificate5038,MergedCutCells.Batch419.certificate5039,MergedCutCells.Batch420.certificate5040,MergedCutCells.Batch420.certificate5041], c.population=PopulationCertificates.Batch051.certificate1027
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers1508 {x : ℝ} (hx : certificate1508.interval.Contains x) : ∃ c∈certificate1508.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1508 numericValid1508 hx

def certificate1509 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1028,PopulationCertificates.Batch051.certificate1028,[MergedCutCells.Batch420.certificate5042,MergedCutCells.Batch420.certificate5043],(77681498776137211/125000000000000000),(some (273899363/250000000)),(1/2),(344178587018984019/1000000000000000000),(some (17063601360796129/500000000000000000)),(some (2752483722447793/500000000000000000))⟩
theorem numericValid1509 : certificate1509.NumericValid := by decide +kernel
theorem cellsSound1509 : ∀ c∈certificate1509.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5042,MergedCutCells.Batch420.certificate5043], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5042,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5043,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1509 : ∀ c∈certificate1509.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5042,MergedCutCells.Batch420.certificate5043], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5042,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5043,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1509 : ∀ c∈certificate1509.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5042,MergedCutCells.Batch420.certificate5043], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid751,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy037.valid751,List.forall_mem_nil _⟩⟩
theorem populationMatches1509 : ∀ c∈certificate1509.cells, c.population=certificate1509.population := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5042,MergedCutCells.Batch420.certificate5043], c.population=PopulationCertificates.Batch051.certificate1028
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1509 {x : ℝ} (hx : certificate1509.interval.Contains x) : ∃ c∈certificate1509.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1509 numericValid1509 hx

def certificate1510 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1028,PopulationCertificates.Batch051.certificate1028,[MergedCutCells.Batch420.certificate5044,MergedCutCells.Batch420.certificate5045,MergedCutCells.Batch420.certificate5046],(273899363/250000000),none,(1/2),(13647625113396523/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1510 : certificate1510.NumericValid := by decide +kernel
theorem cellsSound1510 : ∀ c∈certificate1510.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5044,MergedCutCells.Batch420.certificate5045,MergedCutCells.Batch420.certificate5046], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5044,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5045,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5046,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1510 : ∀ c∈certificate1510.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5044,MergedCutCells.Batch420.certificate5045,MergedCutCells.Batch420.certificate5046], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5044,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5045,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5046,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1510 : ∀ c∈certificate1510.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5044,MergedCutCells.Batch420.certificate5045,MergedCutCells.Batch420.certificate5046], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1510 : ∀ c∈certificate1510.cells, c.population=certificate1510.population := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5044,MergedCutCells.Batch420.certificate5045,MergedCutCells.Batch420.certificate5046], c.population=PopulationCertificates.Batch051.certificate1028
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1510 {x : ℝ} (hx : certificate1510.interval.Contains x) : ∃ c∈certificate1510.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1510 numericValid1510 hx

def certificate1511 : RatCutGroup := ⟨GeometryCertificates.Batch051.certificate1029,PopulationCertificates.Batch051.certificate1029,[MergedCutCells.Batch420.certificate5047,MergedCutCells.Batch420.certificate5048],(40895616397978384099/1000000000000000000),none,(1/2),(1036747575676858729/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1511 : certificate1511.NumericValid := by decide +kernel
theorem cellsSound1511 : ∀ c∈certificate1511.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5047,MergedCutCells.Batch420.certificate5048], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5047,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.sound5048,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1511 : ∀ c∈certificate1511.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5047,MergedCutCells.Batch420.certificate5048], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5047,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch420.numericValid5048,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1511 : ∀ c∈certificate1511.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5047,MergedCutCells.Batch420.certificate5048], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1511 : ∀ c∈certificate1511.cells, c.population=certificate1511.population := by
  change ∀ c∈[MergedCutCells.Batch420.certificate5047,MergedCutCells.Batch420.certificate5048], c.population=PopulationCertificates.Batch051.certificate1029
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1511 {x : ℝ} (hx : certificate1511.interval.Contains x) : ∃ c∈certificate1511.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1511 numericValid1511 hx

end Cycle12.MergedCutGroups.Batch125
