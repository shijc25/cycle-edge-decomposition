import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch042
import Cycle12.MergedCutCells.Batch362
import Cycle12.MergedCutCells.Batch363
import Cycle12.MergedCutCells.Batch364
import Cycle12.PopulationCertificates.Batch042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch105

def certificate1260 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate841,PopulationCertificates.Batch042.certificate841,[MergedCutCells.Batch362.certificate4344,MergedCutCells.Batch362.certificate4345,MergedCutCells.Batch362.certificate4346],(673794391078246451/1000000000000000000),none,(1/40),(119252999396261133/1000000000000000000),none,none⟩
theorem numericValid1260 : certificate1260.NumericValid := by decide +kernel
theorem cellsSound1260 : ∀ c∈certificate1260.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4344,MergedCutCells.Batch362.certificate4345,MergedCutCells.Batch362.certificate4346], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4344,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4345,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4346,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1260 : ∀ c∈certificate1260.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4344,MergedCutCells.Batch362.certificate4345,MergedCutCells.Batch362.certificate4346], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4344,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4345,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4346,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1260 : ∀ c∈certificate1260.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4344,MergedCutCells.Batch362.certificate4345,MergedCutCells.Batch362.certificate4346], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid429,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid430,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid431,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1260 : ∀ c∈certificate1260.cells, c.population=certificate1260.population := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4344,MergedCutCells.Batch362.certificate4345,MergedCutCells.Batch362.certificate4346], c.population=PopulationCertificates.Batch042.certificate841
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1260 {x : ℝ} (hx : certificate1260.interval.Contains x) : ∃ c∈certificate1260.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1260 numericValid1260 hx

def certificate1261 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate842,PopulationCertificates.Batch042.certificate842,[MergedCutCells.Batch362.certificate4347,MergedCutCells.Batch362.certificate4348],(113098037643674347/200000000000000000),(some (653252141/500000000)),(1/2),(6239171062584891/20000000000000000),(some (497995969193537/500000000000000000)),(some (97285638889851/1000000000000000000))⟩
theorem numericValid1261 : certificate1261.NumericValid := by decide +kernel
theorem cellsSound1261 : ∀ c∈certificate1261.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4347,MergedCutCells.Batch362.certificate4348], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4348,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1261 : ∀ c∈certificate1261.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4347,MergedCutCells.Batch362.certificate4348], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4348,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1261 : ∀ c∈certificate1261.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4347,MergedCutCells.Batch362.certificate4348], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid432,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid432,List.forall_mem_nil _⟩⟩
theorem populationMatches1261 : ∀ c∈certificate1261.cells, c.population=certificate1261.population := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4347,MergedCutCells.Batch362.certificate4348], c.population=PopulationCertificates.Batch042.certificate842
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1261 {x : ℝ} (hx : certificate1261.interval.Contains x) : ∃ c∈certificate1261.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1261 numericValid1261 hx

def certificate1262 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate842,PopulationCertificates.Batch042.certificate842,[MergedCutCells.Batch362.certificate4349,MergedCutCells.Batch362.certificate4350],(653252141/500000000),none,(1/2),(312056914335158587/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1262 : certificate1262.NumericValid := by decide +kernel
theorem cellsSound1262 : ∀ c∈certificate1262.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4349,MergedCutCells.Batch362.certificate4350], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4349,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4350,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1262 : ∀ c∈certificate1262.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4349,MergedCutCells.Batch362.certificate4350], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4349,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4350,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1262 : ∀ c∈certificate1262.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4349,MergedCutCells.Batch362.certificate4350], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1262 : ∀ c∈certificate1262.cells, c.population=certificate1262.population := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4349,MergedCutCells.Batch362.certificate4350], c.population=PopulationCertificates.Batch042.certificate842
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1262 {x : ℝ} (hx : certificate1262.interval.Contains x) : ∃ c∈certificate1262.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1262 numericValid1262 hx

def certificate1263 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate843,PopulationCertificates.Batch042.certificate843,[MergedCutCells.Batch362.certificate4351,MergedCutCells.Batch362.certificate4352],(7772958745101689589/500000000000000000),none,(1/2),(395780518737143089/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1263 : certificate1263.NumericValid := by decide +kernel
theorem cellsSound1263 : ∀ c∈certificate1263.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4351,MergedCutCells.Batch362.certificate4352], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4352,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1263 : ∀ c∈certificate1263.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4351,MergedCutCells.Batch362.certificate4352], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4352,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1263 : ∀ c∈certificate1263.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4351,MergedCutCells.Batch362.certificate4352], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1263 : ∀ c∈certificate1263.cells, c.population=certificate1263.population := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4351,MergedCutCells.Batch362.certificate4352], c.population=PopulationCertificates.Batch042.certificate843
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1263 {x : ℝ} (hx : certificate1263.interval.Contains x) : ∃ c∈certificate1263.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1263 numericValid1263 hx

def certificate1264 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate844,PopulationCertificates.Batch042.certificate844,[MergedCutCells.Batch362.certificate4353,MergedCutCells.Batch362.certificate4354,MergedCutCells.Batch362.certificate4355],(676338166418668213/1000000000000000000),none,(1/40),(31280027543008001/250000000000000000),none,none⟩
theorem numericValid1264 : certificate1264.NumericValid := by decide +kernel
theorem cellsSound1264 : ∀ c∈certificate1264.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4353,MergedCutCells.Batch362.certificate4354,MergedCutCells.Batch362.certificate4355], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4353,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4354,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.sound4355,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1264 : ∀ c∈certificate1264.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4353,MergedCutCells.Batch362.certificate4354,MergedCutCells.Batch362.certificate4355], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4353,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4354,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch362.numericValid4355,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1264 : ∀ c∈certificate1264.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4353,MergedCutCells.Batch362.certificate4354,MergedCutCells.Batch362.certificate4355], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid433,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid434,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid435,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1264 : ∀ c∈certificate1264.cells, c.population=certificate1264.population := by
  change ∀ c∈[MergedCutCells.Batch362.certificate4353,MergedCutCells.Batch362.certificate4354,MergedCutCells.Batch362.certificate4355], c.population=PopulationCertificates.Batch042.certificate844
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1264 {x : ℝ} (hx : certificate1264.interval.Contains x) : ∃ c∈certificate1264.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1264 numericValid1264 hx

def certificate1265 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate845,PopulationCertificates.Batch042.certificate845,[MergedCutCells.Batch363.certificate4356,MergedCutCells.Batch363.certificate4357],(568997074186175471/1000000000000000000),(some (256252243/200000000)),(1/2),(16506151873783459/50000000000000000),(some (306248324192193/250000000000000000)),(some (122399458993017/1000000000000000000))⟩
theorem numericValid1265 : certificate1265.NumericValid := by decide +kernel
theorem cellsSound1265 : ∀ c∈certificate1265.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4356,MergedCutCells.Batch363.certificate4357], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4357,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1265 : ∀ c∈certificate1265.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4356,MergedCutCells.Batch363.certificate4357], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4357,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1265 : ∀ c∈certificate1265.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4356,MergedCutCells.Batch363.certificate4357], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid436,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid436,List.forall_mem_nil _⟩⟩
theorem populationMatches1265 : ∀ c∈certificate1265.cells, c.population=certificate1265.population := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4356,MergedCutCells.Batch363.certificate4357], c.population=PopulationCertificates.Batch042.certificate845
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1265 {x : ℝ} (hx : certificate1265.interval.Contains x) : ∃ c∈certificate1265.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1265 numericValid1265 hx

def certificate1266 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate845,PopulationCertificates.Batch042.certificate845,[MergedCutCells.Batch363.certificate4358,MergedCutCells.Batch363.certificate4359,MergedCutCells.Batch363.certificate4360],(256252243/200000000),none,(1/2),(41263680716761037/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1266 : certificate1266.NumericValid := by decide +kernel
theorem cellsSound1266 : ∀ c∈certificate1266.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4358,MergedCutCells.Batch363.certificate4359,MergedCutCells.Batch363.certificate4360], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4359,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4360,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1266 : ∀ c∈certificate1266.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4358,MergedCutCells.Batch363.certificate4359,MergedCutCells.Batch363.certificate4360], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4359,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4360,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1266 : ∀ c∈certificate1266.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4358,MergedCutCells.Batch363.certificate4359,MergedCutCells.Batch363.certificate4360], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1266 : ∀ c∈certificate1266.cells, c.population=certificate1266.population := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4358,MergedCutCells.Batch363.certificate4359,MergedCutCells.Batch363.certificate4360], c.population=PopulationCertificates.Batch042.certificate845
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1266 {x : ℝ} (hx : certificate1266.interval.Contains x) : ∃ c∈certificate1266.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1266 numericValid1266 hx

def certificate1267 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate846,PopulationCertificates.Batch042.certificate846,[MergedCutCells.Batch363.certificate4361,MergedCutCells.Batch363.certificate4362],(1964451296601608453/125000000000000000),none,(1/2),(20289110406727673/5000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1267 : certificate1267.NumericValid := by decide +kernel
theorem cellsSound1267 : ∀ c∈certificate1267.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4361,MergedCutCells.Batch363.certificate4362], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4362,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1267 : ∀ c∈certificate1267.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4361,MergedCutCells.Batch363.certificate4362], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4362,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1267 : ∀ c∈certificate1267.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4361,MergedCutCells.Batch363.certificate4362], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1267 : ∀ c∈certificate1267.cells, c.population=certificate1267.population := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4361,MergedCutCells.Batch363.certificate4362], c.population=PopulationCertificates.Batch042.certificate846
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1267 {x : ℝ} (hx : certificate1267.interval.Contains x) : ∃ c∈certificate1267.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1267 numericValid1267 hx

def certificate1268 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate847,PopulationCertificates.Batch042.certificate847,[MergedCutCells.Batch363.certificate4363,MergedCutCells.Batch363.certificate4364,MergedCutCells.Batch363.certificate4365],(27156481965446453/40000000000000000),none,(1/40),(131153649152459553/1000000000000000000),none,none⟩
theorem numericValid1268 : certificate1268.NumericValid := by decide +kernel
theorem cellsSound1268 : ∀ c∈certificate1268.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4363,MergedCutCells.Batch363.certificate4364,MergedCutCells.Batch363.certificate4365], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4363,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4365,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1268 : ∀ c∈certificate1268.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4363,MergedCutCells.Batch363.certificate4364,MergedCutCells.Batch363.certificate4365], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4363,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4365,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1268 : ∀ c∈certificate1268.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4363,MergedCutCells.Batch363.certificate4364,MergedCutCells.Batch363.certificate4365], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid437,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid438,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy021.valid439,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1268 : ∀ c∈certificate1268.cells, c.population=certificate1268.population := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4363,MergedCutCells.Batch363.certificate4364,MergedCutCells.Batch363.certificate4365], c.population=PopulationCertificates.Batch042.certificate847
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1268 {x : ℝ} (hx : certificate1268.interval.Contains x) : ∃ c∈certificate1268.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1268 numericValid1268 hx

def certificate1269 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate848,PopulationCertificates.Batch042.certificate848,[MergedCutCells.Batch363.certificate4366,MergedCutCells.Batch363.certificate4367],(573852896848046577/1000000000000000000),(some (647897479/500000000)),(1/2),(1362508342597249/3906250000000000),(some (745167994002537/500000000000000000)),(some (152229762109961/1000000000000000000))⟩
theorem numericValid1269 : certificate1269.NumericValid := by decide +kernel
theorem cellsSound1269 : ∀ c∈certificate1269.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4366,MergedCutCells.Batch363.certificate4367], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4366,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.sound4367,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1269 : ∀ c∈certificate1269.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4366,MergedCutCells.Batch363.certificate4367], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4366,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch363.numericValid4367,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1269 : ∀ c∈certificate1269.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4366,MergedCutCells.Batch363.certificate4367], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid440,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid440,List.forall_mem_nil _⟩⟩
theorem populationMatches1269 : ∀ c∈certificate1269.cells, c.population=certificate1269.population := by
  change ∀ c∈[MergedCutCells.Batch363.certificate4366,MergedCutCells.Batch363.certificate4367], c.population=PopulationCertificates.Batch042.certificate848
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1269 {x : ℝ} (hx : certificate1269.interval.Contains x) : ∃ c∈certificate1269.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1269 numericValid1269 hx

def certificate1270 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate848,PopulationCertificates.Batch042.certificate848,[MergedCutCells.Batch364.certificate4368,MergedCutCells.Batch364.certificate4369,MergedCutCells.Batch364.certificate4370],(647897479/500000000),none,(1/2),(69774351804438231/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1270 : certificate1270.NumericValid := by decide +kernel
theorem cellsSound1270 : ∀ c∈certificate1270.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4368,MergedCutCells.Batch364.certificate4369,MergedCutCells.Batch364.certificate4370], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4369,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4370,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1270 : ∀ c∈certificate1270.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4368,MergedCutCells.Batch364.certificate4369,MergedCutCells.Batch364.certificate4370], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4369,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4370,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1270 : ∀ c∈certificate1270.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4368,MergedCutCells.Batch364.certificate4369,MergedCutCells.Batch364.certificate4370], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1270 : ∀ c∈certificate1270.cells, c.population=certificate1270.population := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4368,MergedCutCells.Batch364.certificate4369,MergedCutCells.Batch364.certificate4370], c.population=PopulationCertificates.Batch042.certificate848
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1270 {x : ℝ} (hx : certificate1270.interval.Contains x) : ∃ c∈certificate1270.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1270 numericValid1270 hx

def certificate1271 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate849,PopulationCertificates.Batch042.certificate849,[MergedCutCells.Batch364.certificate4371,MergedCutCells.Batch364.certificate4372],(1986062178075019083/125000000000000000),none,(1/2),(1029859023715860119/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1271 : certificate1271.NumericValid := by decide +kernel
theorem cellsSound1271 : ∀ c∈certificate1271.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4371,MergedCutCells.Batch364.certificate4372], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4372,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1271 : ∀ c∈certificate1271.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4371,MergedCutCells.Batch364.certificate4372], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4372,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1271 : ∀ c∈certificate1271.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4371,MergedCutCells.Batch364.certificate4372], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1271 : ∀ c∈certificate1271.cells, c.population=certificate1271.population := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4371,MergedCutCells.Batch364.certificate4372], c.population=PopulationCertificates.Batch042.certificate849
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1271 {x : ℝ} (hx : certificate1271.interval.Contains x) : ∃ c∈certificate1271.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1271 numericValid1271 hx

end Cycle12.MergedCutGroups.Batch105
