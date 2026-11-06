import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch038
import Cycle12.MergedCutCells.Batch337
import Cycle12.MergedCutCells.Batch338
import Cycle12.MergedCutCells.Batch339
import Cycle12.MergedCutCells.Batch340
import Cycle12.PopulationCertificates.Batch038

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch096

def certificate1152 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate768,PopulationCertificates.Batch038.certificate768,[MergedCutCells.Batch337.certificate4054,MergedCutCells.Batch337.certificate4055],(637907902031676071/1000000000000000000),(some (219406449/200000000)),(1/2),(295428266633231541/1000000000000000000),(some (51020839182553541/500000000000000000)),(some (10517683327702621/500000000000000000))⟩
theorem numericValid1152 : certificate1152.NumericValid := by decide +kernel
theorem cellsSound1152 : ∀ c∈certificate1152.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4054,MergedCutCells.Batch337.certificate4055], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4054,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.sound4055,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1152 : ∀ c∈certificate1152.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4054,MergedCutCells.Batch337.certificate4055], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4054,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch337.numericValid4055,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1152 : ∀ c∈certificate1152.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4054,MergedCutCells.Batch337.certificate4055], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid385,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid385,List.forall_mem_nil _⟩⟩
theorem populationMatches1152 : ∀ c∈certificate1152.cells, c.population=certificate1152.population := by
  change ∀ c∈[MergedCutCells.Batch337.certificate4054,MergedCutCells.Batch337.certificate4055], c.population=PopulationCertificates.Batch038.certificate768
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1152 {x : ℝ} (hx : certificate1152.interval.Contains x) : ∃ c∈certificate1152.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1152 numericValid1152 hx

def certificate1153 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate768,PopulationCertificates.Batch038.certificate768,[MergedCutCells.Batch338.certificate4056,MergedCutCells.Batch338.certificate4057,MergedCutCells.Batch338.certificate4058,MergedCutCells.Batch338.certificate4059],(219406449/200000000),none,(1/2),(143267643025784023/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1153 : certificate1153.NumericValid := by decide +kernel
theorem cellsSound1153 : ∀ c∈certificate1153.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4056,MergedCutCells.Batch338.certificate4057,MergedCutCells.Batch338.certificate4058,MergedCutCells.Batch338.certificate4059], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4056,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4057,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4058,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4059,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1153 : ∀ c∈certificate1153.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4056,MergedCutCells.Batch338.certificate4057,MergedCutCells.Batch338.certificate4058,MergedCutCells.Batch338.certificate4059], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4056,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4057,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4058,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4059,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1153 : ∀ c∈certificate1153.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4056,MergedCutCells.Batch338.certificate4057,MergedCutCells.Batch338.certificate4058,MergedCutCells.Batch338.certificate4059], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1153 : ∀ c∈certificate1153.cells, c.population=certificate1153.population := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4056,MergedCutCells.Batch338.certificate4057,MergedCutCells.Batch338.certificate4058,MergedCutCells.Batch338.certificate4059], c.population=PopulationCertificates.Batch038.certificate768
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1153 {x : ℝ} (hx : certificate1153.interval.Contains x) : ∃ c∈certificate1153.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1153 numericValid1153 hx

def certificate1154 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate769,PopulationCertificates.Batch038.certificate769,[MergedCutCells.Batch338.certificate4060,MergedCutCells.Batch338.certificate4061],(12553391283835167719/500000000000000000),none,(1/2),(8458963110761092233/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1154 : certificate1154.NumericValid := by decide +kernel
theorem cellsSound1154 : ∀ c∈certificate1154.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4060,MergedCutCells.Batch338.certificate4061], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4060,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4061,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1154 : ∀ c∈certificate1154.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4060,MergedCutCells.Batch338.certificate4061], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4060,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4061,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1154 : ∀ c∈certificate1154.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4060,MergedCutCells.Batch338.certificate4061], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1154 : ∀ c∈certificate1154.cells, c.population=certificate1154.population := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4060,MergedCutCells.Batch338.certificate4061], c.population=PopulationCertificates.Batch038.certificate769
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1154 {x : ℝ} (hx : certificate1154.interval.Contains x) : ∃ c∈certificate1154.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1154 numericValid1154 hx

def certificate1155 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate770,PopulationCertificates.Batch038.certificate770,[MergedCutCells.Batch338.certificate4062,MergedCutCells.Batch338.certificate4063],(645630876560765797/1000000000000000000),(some (8869943/8000000)),(1/2),(83648574353047793/250000000000000000),(some (52847985544635693/500000000000000000)),(some (21992643139220211/1000000000000000000))⟩
theorem numericValid1155 : certificate1155.NumericValid := by decide +kernel
theorem cellsSound1155 : ∀ c∈certificate1155.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4062,MergedCutCells.Batch338.certificate4063], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4062,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4063,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1155 : ∀ c∈certificate1155.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4062,MergedCutCells.Batch338.certificate4063], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4062,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4063,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1155 : ∀ c∈certificate1155.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4062,MergedCutCells.Batch338.certificate4063], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid386,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid386,List.forall_mem_nil _⟩⟩
theorem populationMatches1155 : ∀ c∈certificate1155.cells, c.population=certificate1155.population := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4062,MergedCutCells.Batch338.certificate4063], c.population=PopulationCertificates.Batch038.certificate770
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1155 {x : ℝ} (hx : certificate1155.interval.Contains x) : ∃ c∈certificate1155.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1155 numericValid1155 hx

def certificate1156 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate770,PopulationCertificates.Batch038.certificate770,[MergedCutCells.Batch338.certificate4064,MergedCutCells.Batch338.certificate4065,MergedCutCells.Batch338.certificate4066,MergedCutCells.Batch338.certificate4067],(8869943/8000000),none,(1/2),(325276103149477083/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1156 : certificate1156.NumericValid := by decide +kernel
theorem cellsSound1156 : ∀ c∈certificate1156.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4064,MergedCutCells.Batch338.certificate4065,MergedCutCells.Batch338.certificate4066,MergedCutCells.Batch338.certificate4067], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4064,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4065,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4066,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.sound4067,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1156 : ∀ c∈certificate1156.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4064,MergedCutCells.Batch338.certificate4065,MergedCutCells.Batch338.certificate4066,MergedCutCells.Batch338.certificate4067], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4064,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4065,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4066,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch338.numericValid4067,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1156 : ∀ c∈certificate1156.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4064,MergedCutCells.Batch338.certificate4065,MergedCutCells.Batch338.certificate4066,MergedCutCells.Batch338.certificate4067], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1156 : ∀ c∈certificate1156.cells, c.population=certificate1156.population := by
  change ∀ c∈[MergedCutCells.Batch338.certificate4064,MergedCutCells.Batch338.certificate4065,MergedCutCells.Batch338.certificate4066,MergedCutCells.Batch338.certificate4067], c.population=PopulationCertificates.Batch038.certificate770
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1156 {x : ℝ} (hx : certificate1156.interval.Contains x) : ∃ c∈certificate1156.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1156 numericValid1156 hx

def certificate1157 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate771,PopulationCertificates.Batch038.certificate771,[MergedCutCells.Batch339.certificate4068,MergedCutCells.Batch339.certificate4069],(6283691172935282869/250000000000000000),none,(1/2),(1724685567143432767/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1157 : certificate1157.NumericValid := by decide +kernel
theorem cellsSound1157 : ∀ c∈certificate1157.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4068,MergedCutCells.Batch339.certificate4069], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4069,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1157 : ∀ c∈certificate1157.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4068,MergedCutCells.Batch339.certificate4069], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4069,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1157 : ∀ c∈certificate1157.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4068,MergedCutCells.Batch339.certificate4069], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1157 : ∀ c∈certificate1157.cells, c.population=certificate1157.population := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4068,MergedCutCells.Batch339.certificate4069], c.population=PopulationCertificates.Batch038.certificate771
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1157 {x : ℝ} (hx : certificate1157.interval.Contains x) : ∃ c∈certificate1157.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1157 numericValid1157 hx

def certificate1158 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate772,PopulationCertificates.Batch038.certificate772,[MergedCutCells.Batch339.certificate4070,MergedCutCells.Batch339.certificate4071],(163254570254392381/250000000000000000),(some (1095833091/1000000000)),(1/2),(46824117426672357/125000000000000000),(some (21763727128431921/200000000000000000)),(some (11409830196632553/500000000000000000))⟩
theorem numericValid1158 : certificate1158.NumericValid := by decide +kernel
theorem cellsSound1158 : ∀ c∈certificate1158.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4070,MergedCutCells.Batch339.certificate4071], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4070,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4071,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1158 : ∀ c∈certificate1158.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4070,MergedCutCells.Batch339.certificate4071], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4070,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4071,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1158 : ∀ c∈certificate1158.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4070,MergedCutCells.Batch339.certificate4071], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid387,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid387,List.forall_mem_nil _⟩⟩
theorem populationMatches1158 : ∀ c∈certificate1158.cells, c.population=certificate1158.population := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4070,MergedCutCells.Batch339.certificate4071], c.population=PopulationCertificates.Batch038.certificate772
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1158 {x : ℝ} (hx : certificate1158.interval.Contains x) : ∃ c∈certificate1158.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1158 numericValid1158 hx

def certificate1159 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate772,PopulationCertificates.Batch038.certificate772,[MergedCutCells.Batch339.certificate4072,MergedCutCells.Batch339.certificate4073,MergedCutCells.Batch339.certificate4074,MergedCutCells.Batch339.certificate4075],(1095833091/1000000000),none,(1/2),(365395626948620321/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1159 : certificate1159.NumericValid := by decide +kernel
theorem cellsSound1159 : ∀ c∈certificate1159.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4072,MergedCutCells.Batch339.certificate4073,MergedCutCells.Batch339.certificate4074,MergedCutCells.Batch339.certificate4075], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4072,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4074,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4075,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1159 : ∀ c∈certificate1159.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4072,MergedCutCells.Batch339.certificate4073,MergedCutCells.Batch339.certificate4074,MergedCutCells.Batch339.certificate4075], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4072,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4074,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4075,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1159 : ∀ c∈certificate1159.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4072,MergedCutCells.Batch339.certificate4073,MergedCutCells.Batch339.certificate4074,MergedCutCells.Batch339.certificate4075], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1159 : ∀ c∈certificate1159.cells, c.population=certificate1159.population := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4072,MergedCutCells.Batch339.certificate4073,MergedCutCells.Batch339.certificate4074,MergedCutCells.Batch339.certificate4075], c.population=PopulationCertificates.Batch038.certificate772
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1159 {x : ℝ} (hx : certificate1159.interval.Contains x) : ∃ c∈certificate1159.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1159 numericValid1159 hx

def certificate1160 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate773,PopulationCertificates.Batch038.certificate773,[MergedCutCells.Batch339.certificate4076,MergedCutCells.Batch339.certificate4077],(25170479803529277087/1000000000000000000),none,(1/2),(8792764749183085167/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1160 : certificate1160.NumericValid := by decide +kernel
theorem cellsSound1160 : ∀ c∈certificate1160.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4076,MergedCutCells.Batch339.certificate4077], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4077,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1160 : ∀ c∈certificate1160.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4076,MergedCutCells.Batch339.certificate4077], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4077,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1160 : ∀ c∈certificate1160.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4076,MergedCutCells.Batch339.certificate4077], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1160 : ∀ c∈certificate1160.cells, c.population=certificate1160.population := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4076,MergedCutCells.Batch339.certificate4077], c.population=PopulationCertificates.Batch038.certificate773
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1160 {x : ℝ} (hx : certificate1160.interval.Contains x) : ∃ c∈certificate1160.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1160 numericValid1160 hx

def certificate1161 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate774,PopulationCertificates.Batch038.certificate774,[MergedCutCells.Batch339.certificate4078,MergedCutCells.Batch339.certificate4079],(662979910562775701/1000000000000000000),(some (1110649687/1000000000)),(1/2),(215960521446182987/500000000000000000),(some (4502767100483813/40000000000000000)),(some (11911931257275859/500000000000000000))⟩
theorem numericValid1161 : certificate1161.NumericValid := by decide +kernel
theorem cellsSound1161 : ∀ c∈certificate1161.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4078,MergedCutCells.Batch339.certificate4079], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4078,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.sound4079,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1161 : ∀ c∈certificate1161.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4078,MergedCutCells.Batch339.certificate4079], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4078,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch339.numericValid4079,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1161 : ∀ c∈certificate1161.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4078,MergedCutCells.Batch339.certificate4079], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid388,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid388,List.forall_mem_nil _⟩⟩
theorem populationMatches1161 : ∀ c∈certificate1161.cells, c.population=certificate1161.population := by
  change ∀ c∈[MergedCutCells.Batch339.certificate4078,MergedCutCells.Batch339.certificate4079], c.population=PopulationCertificates.Batch038.certificate774
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1161 {x : ℝ} (hx : certificate1161.interval.Contains x) : ∃ c∈certificate1161.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1161 numericValid1161 hx

def certificate1162 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate774,PopulationCertificates.Batch038.certificate774,[MergedCutCells.Batch340.certificate4080,MergedCutCells.Batch340.certificate4081,MergedCutCells.Batch340.certificate4082,MergedCutCells.Batch340.certificate4083],(1110649687/1000000000),none,(1/2),(1319267570300913/3125000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1162 : certificate1162.NumericValid := by decide +kernel
theorem cellsSound1162 : ∀ c∈certificate1162.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4080,MergedCutCells.Batch340.certificate4081,MergedCutCells.Batch340.certificate4082,MergedCutCells.Batch340.certificate4083], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4080,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4083,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1162 : ∀ c∈certificate1162.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4080,MergedCutCells.Batch340.certificate4081,MergedCutCells.Batch340.certificate4082,MergedCutCells.Batch340.certificate4083], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4080,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4083,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1162 : ∀ c∈certificate1162.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4080,MergedCutCells.Batch340.certificate4081,MergedCutCells.Batch340.certificate4082,MergedCutCells.Batch340.certificate4083], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1162 : ∀ c∈certificate1162.cells, c.population=certificate1162.population := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4080,MergedCutCells.Batch340.certificate4081,MergedCutCells.Batch340.certificate4082,MergedCutCells.Batch340.certificate4083], c.population=PopulationCertificates.Batch038.certificate774
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1162 {x : ℝ} (hx : certificate1162.interval.Contains x) : ∃ c∈certificate1162.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1162 numericValid1162 hx

def certificate1163 : RatCutGroup := ⟨GeometryCertificates.Batch038.certificate775,PopulationCertificates.Batch038.certificate775,[MergedCutCells.Batch340.certificate4084,MergedCutCells.Batch340.certificate4085],(25261839224497482523/1000000000000000000),none,(1/2),(8977708364726789269/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1163 : certificate1163.NumericValid := by decide +kernel
theorem cellsSound1163 : ∀ c∈certificate1163.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4084,MergedCutCells.Batch340.certificate4085], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4084,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.sound4085,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1163 : ∀ c∈certificate1163.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4084,MergedCutCells.Batch340.certificate4085], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4084,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch340.numericValid4085,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1163 : ∀ c∈certificate1163.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4084,MergedCutCells.Batch340.certificate4085], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1163 : ∀ c∈certificate1163.cells, c.population=certificate1163.population := by
  change ∀ c∈[MergedCutCells.Batch340.certificate4084,MergedCutCells.Batch340.certificate4085], c.population=PopulationCertificates.Batch038.certificate775
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1163 {x : ℝ} (hx : certificate1163.interval.Contains x) : ∃ c∈certificate1163.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1163 numericValid1163 hx

end Cycle12.MergedCutGroups.Batch096
