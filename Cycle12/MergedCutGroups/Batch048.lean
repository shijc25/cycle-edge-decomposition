import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch019
import Cycle12.MergedCutCells.Batch178
import Cycle12.MergedCutCells.Batch179
import Cycle12.MergedCutCells.Batch180
import Cycle12.MergedCutCells.Batch181
import Cycle12.MergedCutCells.Batch182
import Cycle12.PopulationCertificates.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch048

def certificate576 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate384,PopulationCertificates.Batch019.certificate384,[MergedCutCells.Batch178.certificate2139,MergedCutCells.Batch178.certificate2140,MergedCutCells.Batch178.certificate2141],(171310745060039467/250000000000000000),(some (46002329/40000000)),(1/2),(344195585509776041/1000000000000000000),(some (232250556359232017/1000000000000000000)),(some (967686528648681/15625000000000000))⟩
theorem numericValid576 : certificate576.NumericValid := by decide +kernel
theorem cellsSound576 : ∀ c∈certificate576.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2139,MergedCutCells.Batch178.certificate2140,MergedCutCells.Batch178.certificate2141], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2139,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2141,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric576 : ∀ c∈certificate576.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2139,MergedCutCells.Batch178.certificate2140,MergedCutCells.Batch178.certificate2141], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2139,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2141,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid576 : ∀ c∈certificate576.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2139,MergedCutCells.Batch178.certificate2140,MergedCutCells.Batch178.certificate2141], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid193,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid193,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid193,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches576 : ∀ c∈certificate576.cells, c.population=certificate576.population := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2139,MergedCutCells.Batch178.certificate2140,MergedCutCells.Batch178.certificate2141], c.population=PopulationCertificates.Batch019.certificate384
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers576 {x : ℝ} (hx : certificate576.interval.Contains x) : ∃ c∈certificate576.cells, c.region.interval.Contains x := rat_cut_group_covers certificate576 numericValid576 hx

def certificate577 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate384,PopulationCertificates.Batch019.certificate384,[MergedCutCells.Batch178.certificate2142,MergedCutCells.Batch178.certificate2143,MergedCutCells.Batch178.certificate2144,MergedCutCells.Batch178.certificate2145,MergedCutCells.Batch178.certificate2146,MergedCutCells.Batch178.certificate2147],(46002329/40000000),none,(1/2),(163944433478822327/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid577 : certificate577.NumericValid := by decide +kernel
theorem cellsSound577 : ∀ c∈certificate577.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2142,MergedCutCells.Batch178.certificate2143,MergedCutCells.Batch178.certificate2144,MergedCutCells.Batch178.certificate2145,MergedCutCells.Batch178.certificate2146,MergedCutCells.Batch178.certificate2147], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2143,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2145,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.sound2147,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric577 : ∀ c∈certificate577.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2142,MergedCutCells.Batch178.certificate2143,MergedCutCells.Batch178.certificate2144,MergedCutCells.Batch178.certificate2145,MergedCutCells.Batch178.certificate2146,MergedCutCells.Batch178.certificate2147], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2143,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2145,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch178.numericValid2147,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid577 : ∀ c∈certificate577.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2142,MergedCutCells.Batch178.certificate2143,MergedCutCells.Batch178.certificate2144,MergedCutCells.Batch178.certificate2145,MergedCutCells.Batch178.certificate2146,MergedCutCells.Batch178.certificate2147], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches577 : ∀ c∈certificate577.cells, c.population=certificate577.population := by
  change ∀ c∈[MergedCutCells.Batch178.certificate2142,MergedCutCells.Batch178.certificate2143,MergedCutCells.Batch178.certificate2144,MergedCutCells.Batch178.certificate2145,MergedCutCells.Batch178.certificate2146,MergedCutCells.Batch178.certificate2147], c.population=PopulationCertificates.Batch019.certificate384
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers577 {x : ℝ} (hx : certificate577.interval.Contains x) : ∃ c∈certificate577.cells, c.region.interval.Contains x := rat_cut_group_covers certificate577 numericValid577 hx

def certificate578 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate385,PopulationCertificates.Batch019.certificate385,[MergedCutCells.Batch179.certificate2148,MergedCutCells.Batch179.certificate2149,MergedCutCells.Batch179.certificate2150],(5387970833370115109/1000000000000000000),none,(1/2),(1121652577420339647/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid578 : certificate578.NumericValid := by decide +kernel
theorem cellsSound578 : ∀ c∈certificate578.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2148,MergedCutCells.Batch179.certificate2149,MergedCutCells.Batch179.certificate2150], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2150,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric578 : ∀ c∈certificate578.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2148,MergedCutCells.Batch179.certificate2149,MergedCutCells.Batch179.certificate2150], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2150,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid578 : ∀ c∈certificate578.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2148,MergedCutCells.Batch179.certificate2149,MergedCutCells.Batch179.certificate2150], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches578 : ∀ c∈certificate578.cells, c.population=certificate578.population := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2148,MergedCutCells.Batch179.certificate2149,MergedCutCells.Batch179.certificate2150], c.population=PopulationCertificates.Batch019.certificate385
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers578 {x : ℝ} (hx : certificate578.interval.Contains x) : ∃ c∈certificate578.cells, c.region.interval.Contains x := rat_cut_group_covers certificate578 numericValid578 hx

def certificate579 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate386,PopulationCertificates.Batch019.certificate386,[MergedCutCells.Batch179.certificate2151,MergedCutCells.Batch179.certificate2152,MergedCutCells.Batch179.certificate2153],(6900920076416981/10000000000000000),(some (1129122383/1000000000)),(1/2),(341891311158732961/1000000000000000000),(some (121579847103180991/500000000000000000)),(some (32998607749077457/500000000000000000))⟩
theorem numericValid579 : certificate579.NumericValid := by decide +kernel
theorem cellsSound579 : ∀ c∈certificate579.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2151,MergedCutCells.Batch179.certificate2152,MergedCutCells.Batch179.certificate2153], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2151,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2153,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric579 : ∀ c∈certificate579.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2151,MergedCutCells.Batch179.certificate2152,MergedCutCells.Batch179.certificate2153], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2151,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2153,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid579 : ∀ c∈certificate579.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2151,MergedCutCells.Batch179.certificate2152,MergedCutCells.Batch179.certificate2153], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid194,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid194,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid194,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches579 : ∀ c∈certificate579.cells, c.population=certificate579.population := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2151,MergedCutCells.Batch179.certificate2152,MergedCutCells.Batch179.certificate2153], c.population=PopulationCertificates.Batch019.certificate386
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers579 {x : ℝ} (hx : certificate579.interval.Contains x) : ∃ c∈certificate579.cells, c.region.interval.Contains x := rat_cut_group_covers certificate579 numericValid579 hx

def certificate580 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate386,PopulationCertificates.Batch019.certificate386,[MergedCutCells.Batch179.certificate2154,MergedCutCells.Batch179.certificate2155,MergedCutCells.Batch179.certificate2156,MergedCutCells.Batch179.certificate2157,MergedCutCells.Batch179.certificate2158,MergedCutCells.Batch179.certificate2159,MergedCutCells.Batch180.certificate2160],(1129122383/1000000000),none,(1/2),(323618422076616571/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid580 : certificate580.NumericValid := by decide +kernel
theorem cellsSound580 : ∀ c∈certificate580.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2154,MergedCutCells.Batch179.certificate2155,MergedCutCells.Batch179.certificate2156,MergedCutCells.Batch179.certificate2157,MergedCutCells.Batch179.certificate2158,MergedCutCells.Batch179.certificate2159,MergedCutCells.Batch180.certificate2160], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2154,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2157,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.sound2159,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2160,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric580 : ∀ c∈certificate580.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2154,MergedCutCells.Batch179.certificate2155,MergedCutCells.Batch179.certificate2156,MergedCutCells.Batch179.certificate2157,MergedCutCells.Batch179.certificate2158,MergedCutCells.Batch179.certificate2159,MergedCutCells.Batch180.certificate2160], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2154,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2157,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch179.numericValid2159,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2160,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid580 : ∀ c∈certificate580.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2154,MergedCutCells.Batch179.certificate2155,MergedCutCells.Batch179.certificate2156,MergedCutCells.Batch179.certificate2157,MergedCutCells.Batch179.certificate2158,MergedCutCells.Batch179.certificate2159,MergedCutCells.Batch180.certificate2160], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches580 : ∀ c∈certificate580.cells, c.population=certificate580.population := by
  change ∀ c∈[MergedCutCells.Batch179.certificate2154,MergedCutCells.Batch179.certificate2155,MergedCutCells.Batch179.certificate2156,MergedCutCells.Batch179.certificate2157,MergedCutCells.Batch179.certificate2158,MergedCutCells.Batch179.certificate2159,MergedCutCells.Batch180.certificate2160], c.population=PopulationCertificates.Batch019.certificate386
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers580 {x : ℝ} (hx : certificate580.interval.Contains x) : ∃ c∈certificate580.cells, c.region.interval.Contains x := rat_cut_group_covers certificate580 numericValid580 hx

def certificate581 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate387,PopulationCertificates.Batch019.certificate387,[MergedCutCells.Batch180.certificate2161,MergedCutCells.Batch180.certificate2162,MergedCutCells.Batch180.certificate2163,MergedCutCells.Batch180.certificate2164],(5467465790997523211/1000000000000000000),none,(1/2),(288623000607568891/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid581 : certificate581.NumericValid := by decide +kernel
theorem cellsSound581 : ∀ c∈certificate581.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2161,MergedCutCells.Batch180.certificate2162,MergedCutCells.Batch180.certificate2163,MergedCutCells.Batch180.certificate2164], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2162,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2164,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric581 : ∀ c∈certificate581.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2161,MergedCutCells.Batch180.certificate2162,MergedCutCells.Batch180.certificate2163,MergedCutCells.Batch180.certificate2164], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2162,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2164,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid581 : ∀ c∈certificate581.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2161,MergedCutCells.Batch180.certificate2162,MergedCutCells.Batch180.certificate2163,MergedCutCells.Batch180.certificate2164], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches581 : ∀ c∈certificate581.cells, c.population=certificate581.population := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2161,MergedCutCells.Batch180.certificate2162,MergedCutCells.Batch180.certificate2163,MergedCutCells.Batch180.certificate2164], c.population=PopulationCertificates.Batch019.certificate387
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers581 {x : ℝ} (hx : certificate581.interval.Contains x) : ∃ c∈certificate581.cells, c.region.interval.Contains x := rat_cut_group_covers certificate581 numericValid581 hx

def certificate582 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate388,PopulationCertificates.Batch019.certificate388,[MergedCutCells.Batch180.certificate2165,MergedCutCells.Batch180.certificate2166,MergedCutCells.Batch180.certificate2167],(348409672006801597/500000000000000000),(some (142365997/125000000)),(1/2),(87391496010991421/250000000000000000),(some (127699185721228491/500000000000000000)),(some (70681559087333923/1000000000000000000))⟩
theorem numericValid582 : certificate582.NumericValid := by decide +kernel
theorem cellsSound582 : ∀ c∈certificate582.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2165,MergedCutCells.Batch180.certificate2166,MergedCutCells.Batch180.certificate2167], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2166,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2167,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric582 : ∀ c∈certificate582.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2165,MergedCutCells.Batch180.certificate2166,MergedCutCells.Batch180.certificate2167], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2166,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2167,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid582 : ∀ c∈certificate582.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2165,MergedCutCells.Batch180.certificate2166,MergedCutCells.Batch180.certificate2167], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid195,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid195,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid195,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches582 : ∀ c∈certificate582.cells, c.population=certificate582.population := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2165,MergedCutCells.Batch180.certificate2166,MergedCutCells.Batch180.certificate2167], c.population=PopulationCertificates.Batch019.certificate388
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers582 {x : ℝ} (hx : certificate582.interval.Contains x) : ∃ c∈certificate582.cells, c.region.interval.Contains x := rat_cut_group_covers certificate582 numericValid582 hx

def certificate583 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate388,PopulationCertificates.Batch019.certificate388,[MergedCutCells.Batch180.certificate2168,MergedCutCells.Batch180.certificate2169,MergedCutCells.Batch180.certificate2170,MergedCutCells.Batch180.certificate2171,MergedCutCells.Batch181.certificate2172,MergedCutCells.Batch181.certificate2173],(142365997/125000000),none,(1/2),(16581152643162423/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid583 : certificate583.NumericValid := by decide +kernel
theorem cellsSound583 : ∀ c∈certificate583.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2168,MergedCutCells.Batch180.certificate2169,MergedCutCells.Batch180.certificate2170,MergedCutCells.Batch180.certificate2171,MergedCutCells.Batch181.certificate2172,MergedCutCells.Batch181.certificate2173], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2170,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.sound2171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2173,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric583 : ∀ c∈certificate583.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2168,MergedCutCells.Batch180.certificate2169,MergedCutCells.Batch180.certificate2170,MergedCutCells.Batch180.certificate2171,MergedCutCells.Batch181.certificate2172,MergedCutCells.Batch181.certificate2173], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2170,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch180.numericValid2171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2173,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid583 : ∀ c∈certificate583.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2168,MergedCutCells.Batch180.certificate2169,MergedCutCells.Batch180.certificate2170,MergedCutCells.Batch180.certificate2171,MergedCutCells.Batch181.certificate2172,MergedCutCells.Batch181.certificate2173], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches583 : ∀ c∈certificate583.cells, c.population=certificate583.population := by
  change ∀ c∈[MergedCutCells.Batch180.certificate2168,MergedCutCells.Batch180.certificate2169,MergedCutCells.Batch180.certificate2170,MergedCutCells.Batch180.certificate2171,MergedCutCells.Batch181.certificate2172,MergedCutCells.Batch181.certificate2173], c.population=PopulationCertificates.Batch019.certificate388
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers583 {x : ℝ} (hx : certificate583.interval.Contains x) : ∃ c∈certificate583.cells, c.region.interval.Contains x := rat_cut_group_covers certificate583 numericValid583 hx

def certificate584 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate389,PopulationCertificates.Batch019.certificate389,[MergedCutCells.Batch181.certificate2174,MergedCutCells.Batch181.certificate2175,MergedCutCells.Batch181.certificate2176],(2762889258877386963/500000000000000000),none,(1/2),(1186934045167196609/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid584 : certificate584.NumericValid := by decide +kernel
theorem cellsSound584 : ∀ c∈certificate584.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2174,MergedCutCells.Batch181.certificate2175,MergedCutCells.Batch181.certificate2176], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2174,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2176,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric584 : ∀ c∈certificate584.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2174,MergedCutCells.Batch181.certificate2175,MergedCutCells.Batch181.certificate2176], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2174,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2176,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid584 : ∀ c∈certificate584.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2174,MergedCutCells.Batch181.certificate2175,MergedCutCells.Batch181.certificate2176], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches584 : ∀ c∈certificate584.cells, c.population=certificate584.population := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2174,MergedCutCells.Batch181.certificate2175,MergedCutCells.Batch181.certificate2176], c.population=PopulationCertificates.Batch019.certificate389
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers584 {x : ℝ} (hx : certificate584.interval.Contains x) : ∃ c∈certificate584.cells, c.region.interval.Contains x := rat_cut_group_covers certificate584 numericValid584 hx

def certificate585 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate390,PopulationCertificates.Batch019.certificate390,[MergedCutCells.Batch181.certificate2177,MergedCutCells.Batch181.certificate2178,MergedCutCells.Batch181.certificate2179],(351852106767373981/500000000000000000),(some (280997063/250000000)),(1/2),(360778216902051527/1000000000000000000),(some (133225395164428589/500000000000000000)),(some (37513201436160917/500000000000000000))⟩
theorem numericValid585 : certificate585.NumericValid := by decide +kernel
theorem cellsSound585 : ∀ c∈certificate585.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2177,MergedCutCells.Batch181.certificate2178,MergedCutCells.Batch181.certificate2179], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2178,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2179,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric585 : ∀ c∈certificate585.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2177,MergedCutCells.Batch181.certificate2178,MergedCutCells.Batch181.certificate2179], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2178,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2179,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid585 : ∀ c∈certificate585.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2177,MergedCutCells.Batch181.certificate2178,MergedCutCells.Batch181.certificate2179], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid196,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid196,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid196,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches585 : ∀ c∈certificate585.cells, c.population=certificate585.population := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2177,MergedCutCells.Batch181.certificate2178,MergedCutCells.Batch181.certificate2179], c.population=PopulationCertificates.Batch019.certificate390
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers585 {x : ℝ} (hx : certificate585.interval.Contains x) : ∃ c∈certificate585.cells, c.region.interval.Contains x := rat_cut_group_covers certificate585 numericValid585 hx

def certificate586 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate390,PopulationCertificates.Batch019.certificate390,[MergedCutCells.Batch181.certificate2180,MergedCutCells.Batch181.certificate2181,MergedCutCells.Batch181.certificate2182,MergedCutCells.Batch181.certificate2183,MergedCutCells.Batch182.certificate2184,MergedCutCells.Batch182.certificate2185],(280997063/250000000),none,(1/2),(169626715249006419/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid586 : certificate586.NumericValid := by decide +kernel
theorem cellsSound586 : ∀ c∈certificate586.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2180,MergedCutCells.Batch181.certificate2181,MergedCutCells.Batch181.certificate2182,MergedCutCells.Batch181.certificate2183,MergedCutCells.Batch182.certificate2184,MergedCutCells.Batch182.certificate2185], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2182,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.sound2183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2184,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2185,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric586 : ∀ c∈certificate586.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2180,MergedCutCells.Batch181.certificate2181,MergedCutCells.Batch181.certificate2182,MergedCutCells.Batch181.certificate2183,MergedCutCells.Batch182.certificate2184,MergedCutCells.Batch182.certificate2185], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2182,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch181.numericValid2183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2184,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2185,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid586 : ∀ c∈certificate586.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2180,MergedCutCells.Batch181.certificate2181,MergedCutCells.Batch181.certificate2182,MergedCutCells.Batch181.certificate2183,MergedCutCells.Batch182.certificate2184,MergedCutCells.Batch182.certificate2185], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches586 : ∀ c∈certificate586.cells, c.population=certificate586.population := by
  change ∀ c∈[MergedCutCells.Batch181.certificate2180,MergedCutCells.Batch181.certificate2181,MergedCutCells.Batch181.certificate2182,MergedCutCells.Batch181.certificate2183,MergedCutCells.Batch182.certificate2184,MergedCutCells.Batch182.certificate2185], c.population=PopulationCertificates.Batch019.certificate390
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers586 {x : ℝ} (hx : certificate586.interval.Contains x) : ∃ c∈certificate586.cells, c.region.interval.Contains x := rat_cut_group_covers certificate586 numericValid586 hx

def certificate587 : RatCutGroup := ⟨GeometryCertificates.Batch019.certificate391,PopulationCertificates.Batch019.certificate391,[MergedCutCells.Batch182.certificate2186,MergedCutCells.Batch182.certificate2187,MergedCutCells.Batch182.certificate2188,MergedCutCells.Batch182.certificate2189],(1094312402224019879/200000000000000000),none,(1/2),(2359514207087412901/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid587 : certificate587.NumericValid := by decide +kernel
theorem cellsSound587 : ∀ c∈certificate587.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2186,MergedCutCells.Batch182.certificate2187,MergedCutCells.Batch182.certificate2188,MergedCutCells.Batch182.certificate2189], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2186,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2187,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.sound2189,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric587 : ∀ c∈certificate587.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2186,MergedCutCells.Batch182.certificate2187,MergedCutCells.Batch182.certificate2188,MergedCutCells.Batch182.certificate2189], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2186,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2187,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch182.numericValid2189,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid587 : ∀ c∈certificate587.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2186,MergedCutCells.Batch182.certificate2187,MergedCutCells.Batch182.certificate2188,MergedCutCells.Batch182.certificate2189], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches587 : ∀ c∈certificate587.cells, c.population=certificate587.population := by
  change ∀ c∈[MergedCutCells.Batch182.certificate2186,MergedCutCells.Batch182.certificate2187,MergedCutCells.Batch182.certificate2188,MergedCutCells.Batch182.certificate2189], c.population=PopulationCertificates.Batch019.certificate391
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers587 {x : ℝ} (hx : certificate587.interval.Contains x) : ∃ c∈certificate587.cells, c.region.interval.Contains x := rat_cut_group_covers certificate587 numericValid587 hx

end Cycle12.MergedCutGroups.Batch048
