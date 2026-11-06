import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch048
import Cycle12.GeometryCertificates.Batch049
import Cycle12.MergedCutCells.Batch403
import Cycle12.MergedCutCells.Batch404
import Cycle12.MergedCutCells.Batch405
import Cycle12.PopulationCertificates.Batch048
import Cycle12.PopulationCertificates.Batch049

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch120

def certificate1440 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate976,PopulationCertificates.Batch048.certificate976,[MergedCutCells.Batch403.certificate4836,MergedCutCells.Batch403.certificate4837,MergedCutCells.Batch403.certificate4838,MergedCutCells.Batch403.certificate4839],(86004090377435149/125000000000000000),none,(1/40),(23911012523664767/1000000000000000000),none,none⟩
theorem numericValid1440 : certificate1440.NumericValid := by decide +kernel
theorem cellsSound1440 : ∀ c∈certificate1440.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4836,MergedCutCells.Batch403.certificate4837,MergedCutCells.Batch403.certificate4838,MergedCutCells.Batch403.certificate4839], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4836,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4837,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4838,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4839,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1440 : ∀ c∈certificate1440.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4836,MergedCutCells.Batch403.certificate4837,MergedCutCells.Batch403.certificate4838,MergedCutCells.Batch403.certificate4839], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4836,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4837,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4838,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4839,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1440 : ∀ c∈certificate1440.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4836,MergedCutCells.Batch403.certificate4837,MergedCutCells.Batch403.certificate4838,MergedCutCells.Batch403.certificate4839], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid648,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid649,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid650,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid651,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1440 : ∀ c∈certificate1440.cells, c.population=certificate1440.population := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4836,MergedCutCells.Batch403.certificate4837,MergedCutCells.Batch403.certificate4838,MergedCutCells.Batch403.certificate4839], c.population=PopulationCertificates.Batch048.certificate976
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1440 {x : ℝ} (hx : certificate1440.interval.Contains x) : ∃ c∈certificate1440.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1440 numericValid1440 hx

def certificate1441 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate977,PopulationCertificates.Batch048.certificate977,[MergedCutCells.Batch403.certificate4840,MergedCutCells.Batch403.certificate4841],(67595933938051/122070312500000),(some (113051247/100000000)),(1/2),(36747089404805813/500000000000000000),(some (2038855540723227/100000000000000000)),(some (37426019682253/12500000000000000))⟩
theorem numericValid1441 : certificate1441.NumericValid := by decide +kernel
theorem cellsSound1441 : ∀ c∈certificate1441.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4840,MergedCutCells.Batch403.certificate4841], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4840,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4841,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1441 : ∀ c∈certificate1441.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4840,MergedCutCells.Batch403.certificate4841], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4840,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4841,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1441 : ∀ c∈certificate1441.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4840,MergedCutCells.Batch403.certificate4841], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid652,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid652,List.forall_mem_nil _⟩⟩
theorem populationMatches1441 : ∀ c∈certificate1441.cells, c.population=certificate1441.population := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4840,MergedCutCells.Batch403.certificate4841], c.population=PopulationCertificates.Batch048.certificate977
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1441 {x : ℝ} (hx : certificate1441.interval.Contains x) : ∃ c∈certificate1441.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1441 numericValid1441 hx

def certificate1442 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate977,PopulationCertificates.Batch048.certificate977,[MergedCutCells.Batch403.certificate4842,MergedCutCells.Batch403.certificate4843,MergedCutCells.Batch403.certificate4844],(113051247/100000000),none,(1/2),(36180882632273607/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1442 : certificate1442.NumericValid := by decide +kernel
theorem cellsSound1442 : ∀ c∈certificate1442.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4842,MergedCutCells.Batch403.certificate4843,MergedCutCells.Batch403.certificate4844], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4842,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4843,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4844,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1442 : ∀ c∈certificate1442.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4842,MergedCutCells.Batch403.certificate4843,MergedCutCells.Batch403.certificate4844], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4842,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4843,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4844,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1442 : ∀ c∈certificate1442.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4842,MergedCutCells.Batch403.certificate4843,MergedCutCells.Batch403.certificate4844], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1442 : ∀ c∈certificate1442.cells, c.population=certificate1442.population := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4842,MergedCutCells.Batch403.certificate4843,MergedCutCells.Batch403.certificate4844], c.population=PopulationCertificates.Batch048.certificate977
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1442 {x : ℝ} (hx : certificate1442.interval.Contains x) : ∃ c∈certificate1442.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1442 numericValid1442 hx

def certificate1443 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate978,PopulationCertificates.Batch048.certificate978,[MergedCutCells.Batch403.certificate4845,MergedCutCells.Batch403.certificate4846],(6460743440080467189/200000000000000000),none,(1/2),(1937726126374163/250000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1443 : certificate1443.NumericValid := by decide +kernel
theorem cellsSound1443 : ∀ c∈certificate1443.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4845,MergedCutCells.Batch403.certificate4846], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4845,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4846,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1443 : ∀ c∈certificate1443.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4845,MergedCutCells.Batch403.certificate4846], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4845,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4846,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1443 : ∀ c∈certificate1443.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4845,MergedCutCells.Batch403.certificate4846], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1443 : ∀ c∈certificate1443.cells, c.population=certificate1443.population := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4845,MergedCutCells.Batch403.certificate4846], c.population=PopulationCertificates.Batch048.certificate978
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1443 {x : ℝ} (hx : certificate1443.interval.Contains x) : ∃ c∈certificate1443.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1443 numericValid1443 hx

def certificate1444 : RatCutGroup := ⟨GeometryCertificates.Batch048.certificate979,PopulationCertificates.Batch048.certificate979,[MergedCutCells.Batch403.certificate4847,MergedCutCells.Batch404.certificate4848,MergedCutCells.Batch404.certificate4849,MergedCutCells.Batch404.certificate4850],(172222630635409803/250000000000000000),none,(1/40),(22702593133631731/1000000000000000000),none,none⟩
theorem numericValid1444 : certificate1444.NumericValid := by decide +kernel
theorem cellsSound1444 : ∀ c∈certificate1444.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4847,MergedCutCells.Batch404.certificate4848,MergedCutCells.Batch404.certificate4849,MergedCutCells.Batch404.certificate4850], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.sound4847,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4848,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4849,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4850,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1444 : ∀ c∈certificate1444.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4847,MergedCutCells.Batch404.certificate4848,MergedCutCells.Batch404.certificate4849,MergedCutCells.Batch404.certificate4850], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch403.numericValid4847,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4848,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4849,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4850,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1444 : ∀ c∈certificate1444.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4847,MergedCutCells.Batch404.certificate4848,MergedCutCells.Batch404.certificate4849,MergedCutCells.Batch404.certificate4850], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid653,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid654,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid655,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid656,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1444 : ∀ c∈certificate1444.cells, c.population=certificate1444.population := by
  change ∀ c∈[MergedCutCells.Batch403.certificate4847,MergedCutCells.Batch404.certificate4848,MergedCutCells.Batch404.certificate4849,MergedCutCells.Batch404.certificate4850], c.population=PopulationCertificates.Batch048.certificate979
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1444 {x : ℝ} (hx : certificate1444.interval.Contains x) : ∃ c∈certificate1444.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1444 numericValid1444 hx

def certificate1445 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate980,PopulationCertificates.Batch049.certificate980,[MergedCutCells.Batch404.certificate4851,MergedCutCells.Batch404.certificate4852],(555846555390123591/1000000000000000000),(some (1134155683/1000000000)),(1/2),(75831402927857607/1000000000000000000),(some (10656794917983431/500000000000000000)),(some (3154072735001799/1000000000000000000))⟩
theorem numericValid1445 : certificate1445.NumericValid := by decide +kernel
theorem cellsSound1445 : ∀ c∈certificate1445.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4851,MergedCutCells.Batch404.certificate4852], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4852,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1445 : ∀ c∈certificate1445.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4851,MergedCutCells.Batch404.certificate4852], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4852,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1445 : ∀ c∈certificate1445.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4851,MergedCutCells.Batch404.certificate4852], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid657,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid657,List.forall_mem_nil _⟩⟩
theorem populationMatches1445 : ∀ c∈certificate1445.cells, c.population=certificate1445.population := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4851,MergedCutCells.Batch404.certificate4852], c.population=PopulationCertificates.Batch049.certificate980
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1445 {x : ℝ} (hx : certificate1445.interval.Contains x) : ∃ c∈certificate1445.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1445 numericValid1445 hx

def certificate1446 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate980,PopulationCertificates.Batch049.certificate980,[MergedCutCells.Batch404.certificate4853,MergedCutCells.Batch404.certificate4854,MergedCutCells.Batch404.certificate4855],(1134155683/1000000000),none,(1/2),(37317571513129757/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1446 : certificate1446.NumericValid := by decide +kernel
theorem cellsSound1446 : ∀ c∈certificate1446.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4853,MergedCutCells.Batch404.certificate4854,MergedCutCells.Batch404.certificate4855], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4853,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4854,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4855,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1446 : ∀ c∈certificate1446.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4853,MergedCutCells.Batch404.certificate4854,MergedCutCells.Batch404.certificate4855], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4853,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4854,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4855,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1446 : ∀ c∈certificate1446.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4853,MergedCutCells.Batch404.certificate4854,MergedCutCells.Batch404.certificate4855], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1446 : ∀ c∈certificate1446.cells, c.population=certificate1446.population := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4853,MergedCutCells.Batch404.certificate4854,MergedCutCells.Batch404.certificate4855], c.population=PopulationCertificates.Batch049.certificate980
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1446 {x : ℝ} (hx : certificate1446.interval.Contains x) : ∃ c∈certificate1446.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1446 numericValid1446 hx

def certificate1447 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate981,PopulationCertificates.Batch049.certificate981,[MergedCutCells.Batch404.certificate4856,MergedCutCells.Batch404.certificate4857],(32939414938904403883/1000000000000000000),none,(1/2),(7909279511593036239/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1447 : certificate1447.NumericValid := by decide +kernel
theorem cellsSound1447 : ∀ c∈certificate1447.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4856,MergedCutCells.Batch404.certificate4857], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4856,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4857,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1447 : ∀ c∈certificate1447.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4856,MergedCutCells.Batch404.certificate4857], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4856,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4857,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1447 : ∀ c∈certificate1447.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4856,MergedCutCells.Batch404.certificate4857], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1447 : ∀ c∈certificate1447.cells, c.population=certificate1447.population := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4856,MergedCutCells.Batch404.certificate4857], c.population=PopulationCertificates.Batch049.certificate981
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1447 {x : ℝ} (hx : certificate1447.interval.Contains x) : ∃ c∈certificate1447.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1447 numericValid1447 hx

def certificate1448 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate982,PopulationCertificates.Batch049.certificate982,[MergedCutCells.Batch404.certificate4858,MergedCutCells.Batch404.certificate4859,MergedCutCells.Batch405.certificate4860,MergedCutCells.Batch405.certificate4861],(692741558799980191/1000000000000000000),none,(1/40),(6894741878854521/250000000000000000),none,none⟩
theorem numericValid1448 : certificate1448.NumericValid := by decide +kernel
theorem cellsSound1448 : ∀ c∈certificate1448.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4858,MergedCutCells.Batch404.certificate4859,MergedCutCells.Batch405.certificate4860,MergedCutCells.Batch405.certificate4861], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.sound4859,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4860,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4861,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1448 : ∀ c∈certificate1448.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4858,MergedCutCells.Batch404.certificate4859,MergedCutCells.Batch405.certificate4860,MergedCutCells.Batch405.certificate4861], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch404.numericValid4859,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4860,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4861,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1448 : ∀ c∈certificate1448.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4858,MergedCutCells.Batch404.certificate4859,MergedCutCells.Batch405.certificate4860,MergedCutCells.Batch405.certificate4861], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid658,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy032.valid659,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid660,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid661,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1448 : ∀ c∈certificate1448.cells, c.population=certificate1448.population := by
  change ∀ c∈[MergedCutCells.Batch404.certificate4858,MergedCutCells.Batch404.certificate4859,MergedCutCells.Batch405.certificate4860,MergedCutCells.Batch405.certificate4861], c.population=PopulationCertificates.Batch049.certificate982
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1448 {x : ℝ} (hx : certificate1448.interval.Contains x) : ∃ c∈certificate1448.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1448 numericValid1448 hx

def certificate1449 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate983,PopulationCertificates.Batch049.certificate983,[MergedCutCells.Batch405.certificate4862,MergedCutCells.Batch405.certificate4863],(557974181682358421/1000000000000000000),(some (284460887/250000000)),(1/2),(15663004192968789/200000000000000000),(some (11129817490889867/500000000000000000)),(some (3319173971121763/1000000000000000000))⟩
theorem numericValid1449 : certificate1449.NumericValid := by decide +kernel
theorem cellsSound1449 : ∀ c∈certificate1449.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4862,MergedCutCells.Batch405.certificate4863], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4862,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4863,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1449 : ∀ c∈certificate1449.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4862,MergedCutCells.Batch405.certificate4863], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4862,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4863,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1449 : ∀ c∈certificate1449.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4862,MergedCutCells.Batch405.certificate4863], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid662,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy033.valid662,List.forall_mem_nil _⟩⟩
theorem populationMatches1449 : ∀ c∈certificate1449.cells, c.population=certificate1449.population := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4862,MergedCutCells.Batch405.certificate4863], c.population=PopulationCertificates.Batch049.certificate983
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1449 {x : ℝ} (hx : certificate1449.interval.Contains x) : ∃ c∈certificate1449.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1449 numericValid1449 hx

def certificate1450 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate983,PopulationCertificates.Batch049.certificate983,[MergedCutCells.Batch405.certificate4864,MergedCutCells.Batch405.certificate4865,MergedCutCells.Batch405.certificate4866],(284460887/250000000),none,(1/2),(76977033084444287/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1450 : certificate1450.NumericValid := by decide +kernel
theorem cellsSound1450 : ∀ c∈certificate1450.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4864,MergedCutCells.Batch405.certificate4865,MergedCutCells.Batch405.certificate4866], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4864,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4866,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1450 : ∀ c∈certificate1450.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4864,MergedCutCells.Batch405.certificate4865,MergedCutCells.Batch405.certificate4866], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4864,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4866,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1450 : ∀ c∈certificate1450.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4864,MergedCutCells.Batch405.certificate4865,MergedCutCells.Batch405.certificate4866], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1450 : ∀ c∈certificate1450.cells, c.population=certificate1450.population := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4864,MergedCutCells.Batch405.certificate4865,MergedCutCells.Batch405.certificate4866], c.population=PopulationCertificates.Batch049.certificate983
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1450 {x : ℝ} (hx : certificate1450.interval.Contains x) : ∃ c∈certificate1450.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1450 numericValid1450 hx

def certificate1451 : RatCutGroup := ⟨GeometryCertificates.Batch049.certificate984,PopulationCertificates.Batch049.certificate984,[MergedCutCells.Batch405.certificate4867,MergedCutCells.Batch405.certificate4868],(16796095536033341597/500000000000000000),none,(1/2),(4035771522920117957/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1451 : certificate1451.NumericValid := by decide +kernel
theorem cellsSound1451 : ∀ c∈certificate1451.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4867,MergedCutCells.Batch405.certificate4868], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4867,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.sound4868,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1451 : ∀ c∈certificate1451.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4867,MergedCutCells.Batch405.certificate4868], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4867,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch405.numericValid4868,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1451 : ∀ c∈certificate1451.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4867,MergedCutCells.Batch405.certificate4868], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1451 : ∀ c∈certificate1451.cells, c.population=certificate1451.population := by
  change ∀ c∈[MergedCutCells.Batch405.certificate4867,MergedCutCells.Batch405.certificate4868], c.population=PopulationCertificates.Batch049.certificate984
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1451 {x : ℝ} (hx : certificate1451.interval.Contains x) : ∃ c∈certificate1451.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1451 numericValid1451 hx

end Cycle12.MergedCutGroups.Batch120
