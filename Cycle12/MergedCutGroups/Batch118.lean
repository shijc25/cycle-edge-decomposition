import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch047
import Cycle12.GeometryCertificates.Batch048
import Cycle12.MergedCutCells.Batch397
import Cycle12.MergedCutCells.Batch398
import Cycle12.MergedCutCells.Batch399
import Cycle12.MergedCutCells.Batch400
import Cycle12.PopulationCertificates.Batch047
import Cycle12.PopulationCertificates.Batch048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch118

def certificate1416 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate958,PopulationCertificates.Batch047.certificate958,[MergedCutCells.Batch397.certificate4769,MergedCutCells.Batch397.certificate4770,MergedCutCells.Batch397.certificate4771,MergedCutCells.Batch397.certificate4772],(170252485184665953/250000000000000000),none,(1/40),(232650686198159/15625000000000000),none,none⟩
theorem numericValid1416 : certificate1416.NumericValid := by decide +kernel
theorem cellsSound1416 : ∀ c∈certificate1416.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4769,MergedCutCells.Batch397.certificate4770,MergedCutCells.Batch397.certificate4771,MergedCutCells.Batch397.certificate4772], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4769,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4770,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4771,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4772,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1416 : ∀ c∈certificate1416.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4769,MergedCutCells.Batch397.certificate4770,MergedCutCells.Batch397.certificate4771,MergedCutCells.Batch397.certificate4772], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4769,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4770,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4771,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4772,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1416 : ∀ c∈certificate1416.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4769,MergedCutCells.Batch397.certificate4770,MergedCutCells.Batch397.certificate4771,MergedCutCells.Batch397.certificate4772], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid618,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy030.valid619,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid620,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid621,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1416 : ∀ c∈certificate1416.cells, c.population=certificate1416.population := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4769,MergedCutCells.Batch397.certificate4770,MergedCutCells.Batch397.certificate4771,MergedCutCells.Batch397.certificate4772], c.population=PopulationCertificates.Batch047.certificate958
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1416 {x : ℝ} (hx : certificate1416.interval.Contains x) : ∃ c∈certificate1416.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1416 numericValid1416 hx

def certificate1417 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate959,PopulationCertificates.Batch047.certificate959,[MergedCutCells.Batch397.certificate4773,MergedCutCells.Batch397.certificate4774],(580821184404415649/1000000000000000000),(some (1157213241/1000000000)),(1/2),(205594289235294297/1000000000000000000),(some (18545051211712653/1000000000000000000)),(some (167477304052983/62500000000000000))⟩
theorem numericValid1417 : certificate1417.NumericValid := by decide +kernel
theorem cellsSound1417 : ∀ c∈certificate1417.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4773,MergedCutCells.Batch397.certificate4774], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4773,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4774,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1417 : ∀ c∈certificate1417.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4773,MergedCutCells.Batch397.certificate4774], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4773,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4774,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1417 : ∀ c∈certificate1417.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4773,MergedCutCells.Batch397.certificate4774], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid622,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid622,List.forall_mem_nil _⟩⟩
theorem populationMatches1417 : ∀ c∈certificate1417.cells, c.population=certificate1417.population := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4773,MergedCutCells.Batch397.certificate4774], c.population=PopulationCertificates.Batch047.certificate959
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1417 {x : ℝ} (hx : certificate1417.interval.Contains x) : ∃ c∈certificate1417.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1417 numericValid1417 hx

def certificate1418 : RatCutGroup := ⟨GeometryCertificates.Batch047.certificate959,PopulationCertificates.Batch047.certificate959,[MergedCutCells.Batch397.certificate4775,MergedCutCells.Batch398.certificate4776,MergedCutCells.Batch398.certificate4777],(1157213241/1000000000),none,(1/2),(204594909229222329/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1418 : certificate1418.NumericValid := by decide +kernel
theorem cellsSound1418 : ∀ c∈certificate1418.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4775,MergedCutCells.Batch398.certificate4776,MergedCutCells.Batch398.certificate4777], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.sound4775,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4776,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4777,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1418 : ∀ c∈certificate1418.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4775,MergedCutCells.Batch398.certificate4776,MergedCutCells.Batch398.certificate4777], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch397.numericValid4775,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4776,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4777,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1418 : ∀ c∈certificate1418.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4775,MergedCutCells.Batch398.certificate4776,MergedCutCells.Batch398.certificate4777], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1418 : ∀ c∈certificate1418.cells, c.population=certificate1418.population := by
  change ∀ c∈[MergedCutCells.Batch397.certificate4775,MergedCutCells.Batch398.certificate4776,MergedCutCells.Batch398.certificate4777], c.population=PopulationCertificates.Batch047.certificate959
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1418 {x : ℝ} (hx : certificate1418.interval.Contains x) : ∃ c∈certificate1418.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1418 numericValid1418 hx

def certificate1419 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate960,PopulationCertificates.Batch048.certificate960,[MergedCutCells.Batch398.certificate4778,MergedCutCells.Batch398.certificate4779],(30216135628240838473/1000000000000000000),none,(1/2),(7517850739212297831/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1419 : certificate1419.NumericValid := by decide +kernel
theorem cellsSound1419 : ∀ c∈certificate1419.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4778,MergedCutCells.Batch398.certificate4779], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4778,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4779,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1419 : ∀ c∈certificate1419.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4778,MergedCutCells.Batch398.certificate4779], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4778,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4779,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1419 : ∀ c∈certificate1419.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4778,MergedCutCells.Batch398.certificate4779], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1419 : ∀ c∈certificate1419.cells, c.population=certificate1419.population := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4778,MergedCutCells.Batch398.certificate4779], c.population=PopulationCertificates.Batch048.certificate960
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1419 {x : ℝ} (hx : certificate1419.interval.Contains x) : ∃ c∈certificate1419.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1419 numericValid1419 hx

def certificate1420 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate961,PopulationCertificates.Batch048.certificate961,[MergedCutCells.Batch398.certificate4780,MergedCutCells.Batch398.certificate4781,MergedCutCells.Batch398.certificate4782,MergedCutCells.Batch398.certificate4783],(682902232475272117/1000000000000000000),none,(1/40),(1698290905798271/100000000000000000),none,none⟩
theorem numericValid1420 : certificate1420.NumericValid := by decide +kernel
theorem cellsSound1420 : ∀ c∈certificate1420.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4780,MergedCutCells.Batch398.certificate4781,MergedCutCells.Batch398.certificate4782,MergedCutCells.Batch398.certificate4783], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4780,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4781,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4782,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4783,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1420 : ∀ c∈certificate1420.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4780,MergedCutCells.Batch398.certificate4781,MergedCutCells.Batch398.certificate4782,MergedCutCells.Batch398.certificate4783], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4780,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4781,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4782,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4783,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1420 : ∀ c∈certificate1420.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4780,MergedCutCells.Batch398.certificate4781,MergedCutCells.Batch398.certificate4782,MergedCutCells.Batch398.certificate4783], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid623,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid624,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid625,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid626,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1420 : ∀ c∈certificate1420.cells, c.population=certificate1420.population := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4780,MergedCutCells.Batch398.certificate4781,MergedCutCells.Batch398.certificate4782,MergedCutCells.Batch398.certificate4783], c.population=PopulationCertificates.Batch048.certificate961
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1420 {x : ℝ} (hx : certificate1420.interval.Contains x) : ∃ c∈certificate1420.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1420 numericValid1420 hx

def certificate1421 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate962,PopulationCertificates.Batch048.certificate962,[MergedCutCells.Batch398.certificate4784,MergedCutCells.Batch398.certificate4785],(581730594132313983/1000000000000000000),(some (1158759331/1000000000)),(1/2),(4164400825700821/20000000000000000),(some (46899311180413/2500000000000000)),(some (2715944451293659/1000000000000000000))⟩
theorem numericValid1421 : certificate1421.NumericValid := by decide +kernel
theorem cellsSound1421 : ∀ c∈certificate1421.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4784,MergedCutCells.Batch398.certificate4785], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4784,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4785,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1421 : ∀ c∈certificate1421.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4784,MergedCutCells.Batch398.certificate4785], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4784,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4785,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1421 : ∀ c∈certificate1421.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4784,MergedCutCells.Batch398.certificate4785], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid627,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid627,List.forall_mem_nil _⟩⟩
theorem populationMatches1421 : ∀ c∈certificate1421.cells, c.population=certificate1421.population := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4784,MergedCutCells.Batch398.certificate4785], c.population=PopulationCertificates.Batch048.certificate962
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1421 {x : ℝ} (hx : certificate1421.interval.Contains x) : ∃ c∈certificate1421.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1421 numericValid1421 hx

def certificate1422 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate962,PopulationCertificates.Batch048.certificate962,[MergedCutCells.Batch398.certificate4786,MergedCutCells.Batch398.certificate4787,MergedCutCells.Batch399.certificate4788],(1158759331/1000000000),none,(1/2),(207172091511312551/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1422 : certificate1422.NumericValid := by decide +kernel
theorem cellsSound1422 : ∀ c∈certificate1422.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4786,MergedCutCells.Batch398.certificate4787,MergedCutCells.Batch399.certificate4788], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4786,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.sound4787,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4788,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1422 : ∀ c∈certificate1422.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4786,MergedCutCells.Batch398.certificate4787,MergedCutCells.Batch399.certificate4788], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4786,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch398.numericValid4787,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4788,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1422 : ∀ c∈certificate1422.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4786,MergedCutCells.Batch398.certificate4787,MergedCutCells.Batch399.certificate4788], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1422 : ∀ c∈certificate1422.cells, c.population=certificate1422.population := by
  change ∀ c∈[MergedCutCells.Batch398.certificate4786,MergedCutCells.Batch398.certificate4787,MergedCutCells.Batch399.certificate4788], c.population=PopulationCertificates.Batch048.certificate962
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1422 {x : ℝ} (hx : certificate1422.interval.Contains x) : ∃ c∈certificate1422.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1422 numericValid1422 hx

def certificate1423 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate963,PopulationCertificates.Batch048.certificate963,[MergedCutCells.Batch399.certificate4789,MergedCutCells.Batch399.certificate4790],(305114342985511693/10000000000000000),none,(1/2),(7595740872814924991/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1423 : certificate1423.NumericValid := by decide +kernel
theorem cellsSound1423 : ∀ c∈certificate1423.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4789,MergedCutCells.Batch399.certificate4790], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4789,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4790,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1423 : ∀ c∈certificate1423.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4789,MergedCutCells.Batch399.certificate4790], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4789,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4790,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1423 : ∀ c∈certificate1423.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4789,MergedCutCells.Batch399.certificate4790], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1423 : ∀ c∈certificate1423.cells, c.population=certificate1423.population := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4789,MergedCutCells.Batch399.certificate4790], c.population=PopulationCertificates.Batch048.certificate963
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1423 {x : ℝ} (hx : certificate1423.interval.Contains x) : ∃ c∈certificate1423.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1423 numericValid1423 hx

def certificate1424 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate964,PopulationCertificates.Batch048.certificate964,[MergedCutCells.Batch399.certificate4791,MergedCutCells.Batch399.certificate4792,MergedCutCells.Batch399.certificate4793,MergedCutCells.Batch399.certificate4794],(684734160699706557/1000000000000000000),none,(1/40),(4910382624832317/250000000000000000),none,none⟩
theorem numericValid1424 : certificate1424.NumericValid := by decide +kernel
theorem cellsSound1424 : ∀ c∈certificate1424.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4791,MergedCutCells.Batch399.certificate4792,MergedCutCells.Batch399.certificate4793,MergedCutCells.Batch399.certificate4794], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4791,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4792,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4793,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4794,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1424 : ∀ c∈certificate1424.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4791,MergedCutCells.Batch399.certificate4792,MergedCutCells.Batch399.certificate4793,MergedCutCells.Batch399.certificate4794], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4791,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4792,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4793,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4794,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1424 : ∀ c∈certificate1424.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4791,MergedCutCells.Batch399.certificate4792,MergedCutCells.Batch399.certificate4793,MergedCutCells.Batch399.certificate4794], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid628,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid629,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid630,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid631,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1424 : ∀ c∈certificate1424.cells, c.population=certificate1424.population := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4791,MergedCutCells.Batch399.certificate4792,MergedCutCells.Batch399.certificate4793,MergedCutCells.Batch399.certificate4794], c.population=PopulationCertificates.Batch048.certificate964
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1424 {x : ℝ} (hx : certificate1424.interval.Contains x) : ∃ c∈certificate1424.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1424 numericValid1424 hx

def certificate1425 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate965,PopulationCertificates.Batch048.certificate965,[MergedCutCells.Batch399.certificate4795,MergedCutCells.Batch399.certificate4796],(582159993684836807/1000000000000000000),(some (282826529/250000000)),(1/2),(52296287444115993/250000000000000000),(some (9429157257607583/500000000000000000)),(some (1366323323983619/500000000000000000))⟩
theorem numericValid1425 : certificate1425.NumericValid := by decide +kernel
theorem cellsSound1425 : ∀ c∈certificate1425.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4795,MergedCutCells.Batch399.certificate4796], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4795,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4796,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1425 : ∀ c∈certificate1425.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4795,MergedCutCells.Batch399.certificate4796], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4795,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4796,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1425 : ∀ c∈certificate1425.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4795,MergedCutCells.Batch399.certificate4796], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid632,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy031.valid632,List.forall_mem_nil _⟩⟩
theorem populationMatches1425 : ∀ c∈certificate1425.cells, c.population=certificate1425.population := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4795,MergedCutCells.Batch399.certificate4796], c.population=PopulationCertificates.Batch048.certificate965
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1425 {x : ℝ} (hx : certificate1425.interval.Contains x) : ∃ c∈certificate1425.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1425 numericValid1425 hx

def certificate1426 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate965,PopulationCertificates.Batch048.certificate965,[MergedCutCells.Batch399.certificate4797,MergedCutCells.Batch399.certificate4798,MergedCutCells.Batch399.certificate4799,MergedCutCells.Batch400.certificate4800],(282826529/250000000),none,(1/2),(104040479175117941/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1426 : certificate1426.NumericValid := by decide +kernel
theorem cellsSound1426 : ∀ c∈certificate1426.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4797,MergedCutCells.Batch399.certificate4798,MergedCutCells.Batch399.certificate4799,MergedCutCells.Batch400.certificate4800], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4797,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4798,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.sound4799,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4800,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1426 : ∀ c∈certificate1426.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4797,MergedCutCells.Batch399.certificate4798,MergedCutCells.Batch399.certificate4799,MergedCutCells.Batch400.certificate4800], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4797,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4798,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch399.numericValid4799,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4800,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1426 : ∀ c∈certificate1426.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4797,MergedCutCells.Batch399.certificate4798,MergedCutCells.Batch399.certificate4799,MergedCutCells.Batch400.certificate4800], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1426 : ∀ c∈certificate1426.cells, c.population=certificate1426.population := by
  change ∀ c∈[MergedCutCells.Batch399.certificate4797,MergedCutCells.Batch399.certificate4798,MergedCutCells.Batch399.certificate4799,MergedCutCells.Batch400.certificate4800], c.population=PopulationCertificates.Batch048.certificate965
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1426 {x : ℝ} (hx : certificate1426.interval.Contains x) : ∃ c∈certificate1426.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1426 numericValid1426 hx

def certificate1427 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate966,PopulationCertificates.Batch048.certificate966,[MergedCutCells.Batch400.certificate4801,MergedCutCells.Batch400.certificate4802],(6132091401067662353/200000000000000000),none,(1/2),(3816976497117786071/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1427 : certificate1427.NumericValid := by decide +kernel
theorem cellsSound1427 : ∀ c∈certificate1427.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4801,MergedCutCells.Batch400.certificate4802], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.sound4802,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1427 : ∀ c∈certificate1427.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4801,MergedCutCells.Batch400.certificate4802], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch400.numericValid4802,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1427 : ∀ c∈certificate1427.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4801,MergedCutCells.Batch400.certificate4802], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1427 : ∀ c∈certificate1427.cells, c.population=certificate1427.population := by
  change ∀ c∈[MergedCutCells.Batch400.certificate4801,MergedCutCells.Batch400.certificate4802], c.population=PopulationCertificates.Batch048.certificate966
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1427 {x : ℝ} (hx : certificate1427.interval.Contains x) : ∃ c∈certificate1427.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1427 numericValid1427 hx

end Cycle12.MergedCutGroups.Batch118
