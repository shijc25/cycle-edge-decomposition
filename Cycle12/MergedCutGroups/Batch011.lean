import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch004
import Cycle12.MergedCutCells.Batch038
import Cycle12.MergedCutCells.Batch039
import Cycle12.MergedCutCells.Batch040
import Cycle12.MergedCutCells.Batch041
import Cycle12.MergedCutCells.Batch042
import Cycle12.MergedCutCells.Batch043
import Cycle12.PopulationCertificates.Batch004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch011

def certificate132 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate88,PopulationCertificates.Batch004.certificate88,[MergedCutCells.Batch038.certificate465,MergedCutCells.Batch038.certificate466,MergedCutCells.Batch038.certificate467],(780516206655592521/1000000000000000000),(some (927306257/1000000000)),(1/2),(1006305779046133/3906250000000000),(some (505012776395713313/1000000000000000000)),(some (101675436300490267/500000000000000000))⟩
theorem numericValid132 : certificate132.NumericValid := by decide +kernel
theorem cellsSound132 : ∀ c∈certificate132.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch038.certificate465,MergedCutCells.Batch038.certificate466,MergedCutCells.Batch038.certificate467], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound466,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound467,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric132 : ∀ c∈certificate132.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch038.certificate465,MergedCutCells.Batch038.certificate466,MergedCutCells.Batch038.certificate467], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid466,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid467,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid132 : ∀ c∈certificate132.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch038.certificate465,MergedCutCells.Batch038.certificate466,MergedCutCells.Batch038.certificate467], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid45,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid45,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid45,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches132 : ∀ c∈certificate132.cells, c.population=certificate132.population := by
  change ∀ c∈[MergedCutCells.Batch038.certificate465,MergedCutCells.Batch038.certificate466,MergedCutCells.Batch038.certificate467], c.population=PopulationCertificates.Batch004.certificate88
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers132 {x : ℝ} (hx : certificate132.interval.Contains x) : ∃ c∈certificate132.cells, c.region.interval.Contains x := rat_cut_group_covers certificate132 numericValid132 hx

def certificate133 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate88,PopulationCertificates.Batch004.certificate88,[MergedCutCells.Batch039.certificate468,MergedCutCells.Batch039.certificate469,MergedCutCells.Batch039.certificate470,MergedCutCells.Batch039.certificate471,MergedCutCells.Batch039.certificate472,MergedCutCells.Batch039.certificate473,MergedCutCells.Batch039.certificate474],(927306257/1000000000),none,(1/2),(180132858935364013/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid133 : certificate133.NumericValid := by decide +kernel
theorem cellsSound133 : ∀ c∈certificate133.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch039.certificate468,MergedCutCells.Batch039.certificate469,MergedCutCells.Batch039.certificate470,MergedCutCells.Batch039.certificate471,MergedCutCells.Batch039.certificate472,MergedCutCells.Batch039.certificate473,MergedCutCells.Batch039.certificate474], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound468,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound469,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound470,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound472,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound474,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric133 : ∀ c∈certificate133.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch039.certificate468,MergedCutCells.Batch039.certificate469,MergedCutCells.Batch039.certificate470,MergedCutCells.Batch039.certificate471,MergedCutCells.Batch039.certificate472,MergedCutCells.Batch039.certificate473,MergedCutCells.Batch039.certificate474], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid468,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid469,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid470,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid472,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid474,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid133 : ∀ c∈certificate133.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch039.certificate468,MergedCutCells.Batch039.certificate469,MergedCutCells.Batch039.certificate470,MergedCutCells.Batch039.certificate471,MergedCutCells.Batch039.certificate472,MergedCutCells.Batch039.certificate473,MergedCutCells.Batch039.certificate474], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches133 : ∀ c∈certificate133.cells, c.population=certificate133.population := by
  change ∀ c∈[MergedCutCells.Batch039.certificate468,MergedCutCells.Batch039.certificate469,MergedCutCells.Batch039.certificate470,MergedCutCells.Batch039.certificate471,MergedCutCells.Batch039.certificate472,MergedCutCells.Batch039.certificate473,MergedCutCells.Batch039.certificate474], c.population=PopulationCertificates.Batch004.certificate88
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers133 {x : ℝ} (hx : certificate133.interval.Contains x) : ∃ c∈certificate133.cells, c.region.interval.Contains x := rat_cut_group_covers certificate133 numericValid133 hx

def certificate134 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate89,PopulationCertificates.Batch004.certificate89,[MergedCutCells.Batch039.certificate475,MergedCutCells.Batch039.certificate476,MergedCutCells.Batch039.certificate477,MergedCutCells.Batch039.certificate478],(3771431162707975121/1000000000000000000),none,(1/2),(281191724912514679/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid134 : certificate134.NumericValid := by decide +kernel
theorem cellsSound134 : ∀ c∈certificate134.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch039.certificate475,MergedCutCells.Batch039.certificate476,MergedCutCells.Batch039.certificate477,MergedCutCells.Batch039.certificate478], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound475,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound476,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound477,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound478,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric134 : ∀ c∈certificate134.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch039.certificate475,MergedCutCells.Batch039.certificate476,MergedCutCells.Batch039.certificate477,MergedCutCells.Batch039.certificate478], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid475,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid476,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid477,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid478,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid134 : ∀ c∈certificate134.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch039.certificate475,MergedCutCells.Batch039.certificate476,MergedCutCells.Batch039.certificate477,MergedCutCells.Batch039.certificate478], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches134 : ∀ c∈certificate134.cells, c.population=certificate134.population := by
  change ∀ c∈[MergedCutCells.Batch039.certificate475,MergedCutCells.Batch039.certificate476,MergedCutCells.Batch039.certificate477,MergedCutCells.Batch039.certificate478], c.population=PopulationCertificates.Batch004.certificate89
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers134 {x : ℝ} (hx : certificate134.interval.Contains x) : ∃ c∈certificate134.cells, c.region.interval.Contains x := rat_cut_group_covers certificate134 numericValid134 hx

def certificate135 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate90,PopulationCertificates.Batch004.certificate90,[MergedCutCells.Batch039.certificate479,MergedCutCells.Batch040.certificate480,MergedCutCells.Batch040.certificate481],(783004352654420077/1000000000000000000),(some (232536641/250000000)),(1/2),(51774654776350573/200000000000000000),(some (512346625507648477/1000000000000000000)),(some (208788148593487429/1000000000000000000))⟩
theorem numericValid135 : certificate135.NumericValid := by decide +kernel
theorem cellsSound135 : ∀ c∈certificate135.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch039.certificate479,MergedCutCells.Batch040.certificate480,MergedCutCells.Batch040.certificate481], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.sound479,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound481,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric135 : ∀ c∈certificate135.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch039.certificate479,MergedCutCells.Batch040.certificate480,MergedCutCells.Batch040.certificate481], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch039.numericValid479,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid481,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid135 : ∀ c∈certificate135.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch039.certificate479,MergedCutCells.Batch040.certificate480,MergedCutCells.Batch040.certificate481], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid46,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid46,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid46,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches135 : ∀ c∈certificate135.cells, c.population=certificate135.population := by
  change ∀ c∈[MergedCutCells.Batch039.certificate479,MergedCutCells.Batch040.certificate480,MergedCutCells.Batch040.certificate481], c.population=PopulationCertificates.Batch004.certificate90
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers135 {x : ℝ} (hx : certificate135.interval.Contains x) : ∃ c∈certificate135.cells, c.region.interval.Contains x := rat_cut_group_covers certificate135 numericValid135 hx

def certificate136 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate90,PopulationCertificates.Batch004.certificate90,[MergedCutCells.Batch040.certificate482,MergedCutCells.Batch040.certificate483,MergedCutCells.Batch040.certificate484,MergedCutCells.Batch040.certificate485,MergedCutCells.Batch040.certificate486,MergedCutCells.Batch040.certificate487],(232536641/250000000),none,(1/2),(36762348291747723/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid136 : certificate136.NumericValid := by decide +kernel
theorem cellsSound136 : ∀ c∈certificate136.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch040.certificate482,MergedCutCells.Batch040.certificate483,MergedCutCells.Batch040.certificate484,MergedCutCells.Batch040.certificate485,MergedCutCells.Batch040.certificate486,MergedCutCells.Batch040.certificate487], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound482,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound483,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound485,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound486,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound487,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric136 : ∀ c∈certificate136.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch040.certificate482,MergedCutCells.Batch040.certificate483,MergedCutCells.Batch040.certificate484,MergedCutCells.Batch040.certificate485,MergedCutCells.Batch040.certificate486,MergedCutCells.Batch040.certificate487], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid482,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid483,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid485,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid486,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid487,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid136 : ∀ c∈certificate136.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch040.certificate482,MergedCutCells.Batch040.certificate483,MergedCutCells.Batch040.certificate484,MergedCutCells.Batch040.certificate485,MergedCutCells.Batch040.certificate486,MergedCutCells.Batch040.certificate487], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches136 : ∀ c∈certificate136.cells, c.population=certificate136.population := by
  change ∀ c∈[MergedCutCells.Batch040.certificate482,MergedCutCells.Batch040.certificate483,MergedCutCells.Batch040.certificate484,MergedCutCells.Batch040.certificate485,MergedCutCells.Batch040.certificate486,MergedCutCells.Batch040.certificate487], c.population=PopulationCertificates.Batch004.certificate90
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers136 {x : ℝ} (hx : certificate136.interval.Contains x) : ∃ c∈certificate136.cells, c.region.interval.Contains x := rat_cut_group_covers certificate136 numericValid136 hx

def certificate137 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate91,PopulationCertificates.Batch004.certificate91,[MergedCutCells.Batch040.certificate488,MergedCutCells.Batch040.certificate489,MergedCutCells.Batch040.certificate490,MergedCutCells.Batch040.certificate491],(3789132726792578843/1000000000000000000),none,(1/2),(584287353664450223/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid137 : certificate137.NumericValid := by decide +kernel
theorem cellsSound137 : ∀ c∈certificate137.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch040.certificate488,MergedCutCells.Batch040.certificate489,MergedCutCells.Batch040.certificate490,MergedCutCells.Batch040.certificate491], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound488,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound489,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound490,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.sound491,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric137 : ∀ c∈certificate137.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch040.certificate488,MergedCutCells.Batch040.certificate489,MergedCutCells.Batch040.certificate490,MergedCutCells.Batch040.certificate491], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid488,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid489,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid490,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch040.numericValid491,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid137 : ∀ c∈certificate137.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch040.certificate488,MergedCutCells.Batch040.certificate489,MergedCutCells.Batch040.certificate490,MergedCutCells.Batch040.certificate491], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches137 : ∀ c∈certificate137.cells, c.population=certificate137.population := by
  change ∀ c∈[MergedCutCells.Batch040.certificate488,MergedCutCells.Batch040.certificate489,MergedCutCells.Batch040.certificate490,MergedCutCells.Batch040.certificate491], c.population=PopulationCertificates.Batch004.certificate91
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers137 {x : ℝ} (hx : certificate137.interval.Contains x) : ∃ c∈certificate137.cells, c.region.interval.Contains x := rat_cut_group_covers certificate137 numericValid137 hx

def certificate138 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate92,PopulationCertificates.Batch004.certificate92,[MergedCutCells.Batch041.certificate492,MergedCutCells.Batch041.certificate493,MergedCutCells.Batch041.certificate494],(781010383910416677/1000000000000000000),(some (463935203/500000000)),(1/2),(121993935048025991/500000000000000000),(some (10393937807025051/20000000000000000)),(some (214375821931108661/1000000000000000000))⟩
theorem numericValid138 : certificate138.NumericValid := by decide +kernel
theorem cellsSound138 : ∀ c∈certificate138.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch041.certificate492,MergedCutCells.Batch041.certificate493,MergedCutCells.Batch041.certificate494], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound492,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound494,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric138 : ∀ c∈certificate138.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch041.certificate492,MergedCutCells.Batch041.certificate493,MergedCutCells.Batch041.certificate494], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid492,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid494,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid138 : ∀ c∈certificate138.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch041.certificate492,MergedCutCells.Batch041.certificate493,MergedCutCells.Batch041.certificate494], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid47,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid47,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid47,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches138 : ∀ c∈certificate138.cells, c.population=certificate138.population := by
  change ∀ c∈[MergedCutCells.Batch041.certificate492,MergedCutCells.Batch041.certificate493,MergedCutCells.Batch041.certificate494], c.population=PopulationCertificates.Batch004.certificate92
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers138 {x : ℝ} (hx : certificate138.interval.Contains x) : ∃ c∈certificate138.cells, c.region.interval.Contains x := rat_cut_group_covers certificate138 numericValid138 hx

def certificate139 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate92,PopulationCertificates.Batch004.certificate92,[MergedCutCells.Batch041.certificate495,MergedCutCells.Batch041.certificate496,MergedCutCells.Batch041.certificate497,MergedCutCells.Batch041.certificate498,MergedCutCells.Batch041.certificate499,MergedCutCells.Batch041.certificate500],(463935203/500000000),none,(1/2),(188205708898316321/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid139 : certificate139.NumericValid := by decide +kernel
theorem cellsSound139 : ∀ c∈certificate139.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch041.certificate495,MergedCutCells.Batch041.certificate496,MergedCutCells.Batch041.certificate497,MergedCutCells.Batch041.certificate498,MergedCutCells.Batch041.certificate499,MergedCutCells.Batch041.certificate500], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound495,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound496,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound497,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound499,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound500,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric139 : ∀ c∈certificate139.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch041.certificate495,MergedCutCells.Batch041.certificate496,MergedCutCells.Batch041.certificate497,MergedCutCells.Batch041.certificate498,MergedCutCells.Batch041.certificate499,MergedCutCells.Batch041.certificate500], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid495,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid496,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid497,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid499,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid500,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid139 : ∀ c∈certificate139.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch041.certificate495,MergedCutCells.Batch041.certificate496,MergedCutCells.Batch041.certificate497,MergedCutCells.Batch041.certificate498,MergedCutCells.Batch041.certificate499,MergedCutCells.Batch041.certificate500], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches139 : ∀ c∈certificate139.cells, c.population=certificate139.population := by
  change ∀ c∈[MergedCutCells.Batch041.certificate495,MergedCutCells.Batch041.certificate496,MergedCutCells.Batch041.certificate497,MergedCutCells.Batch041.certificate498,MergedCutCells.Batch041.certificate499,MergedCutCells.Batch041.certificate500], c.population=PopulationCertificates.Batch004.certificate92
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers139 {x : ℝ} (hx : certificate139.interval.Contains x) : ∃ c∈certificate139.cells, c.region.interval.Contains x := rat_cut_group_covers certificate139 numericValid139 hx

def certificate140 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate93,PopulationCertificates.Batch004.certificate93,[MergedCutCells.Batch041.certificate501,MergedCutCells.Batch041.certificate502,MergedCutCells.Batch041.certificate503,MergedCutCells.Batch042.certificate504],(3701986394800524983/1000000000000000000),none,(1/2),(483723391285464671/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid140 : certificate140.NumericValid := by decide +kernel
theorem cellsSound140 : ∀ c∈certificate140.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch041.certificate501,MergedCutCells.Batch041.certificate502,MergedCutCells.Batch041.certificate503,MergedCutCells.Batch042.certificate504], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound501,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.sound503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound504,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric140 : ∀ c∈certificate140.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch041.certificate501,MergedCutCells.Batch041.certificate502,MergedCutCells.Batch041.certificate503,MergedCutCells.Batch042.certificate504], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid501,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch041.numericValid503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid504,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid140 : ∀ c∈certificate140.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch041.certificate501,MergedCutCells.Batch041.certificate502,MergedCutCells.Batch041.certificate503,MergedCutCells.Batch042.certificate504], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches140 : ∀ c∈certificate140.cells, c.population=certificate140.population := by
  change ∀ c∈[MergedCutCells.Batch041.certificate501,MergedCutCells.Batch041.certificate502,MergedCutCells.Batch041.certificate503,MergedCutCells.Batch042.certificate504], c.population=PopulationCertificates.Batch004.certificate93
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers140 {x : ℝ} (hx : certificate140.interval.Contains x) : ∃ c∈certificate140.cells, c.region.interval.Contains x := rat_cut_group_covers certificate140 numericValid140 hx

def certificate141 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate94,PopulationCertificates.Batch004.certificate94,[MergedCutCells.Batch042.certificate505,MergedCutCells.Batch042.certificate506,MergedCutCells.Batch042.certificate507],(24670727648591351/31250000000000000),(some (57220961/62500000)),(1/2),(272853606852218787/1000000000000000000),(some (262448727931993043/500000000000000000)),(some (218417281169139707/1000000000000000000))⟩
theorem numericValid141 : certificate141.NumericValid := by decide +kernel
theorem cellsSound141 : ∀ c∈certificate141.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch042.certificate505,MergedCutCells.Batch042.certificate506,MergedCutCells.Batch042.certificate507], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound505,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound507,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric141 : ∀ c∈certificate141.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch042.certificate505,MergedCutCells.Batch042.certificate506,MergedCutCells.Batch042.certificate507], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid505,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid507,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid141 : ∀ c∈certificate141.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch042.certificate505,MergedCutCells.Batch042.certificate506,MergedCutCells.Batch042.certificate507], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid48,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid48,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid48,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches141 : ∀ c∈certificate141.cells, c.population=certificate141.population := by
  change ∀ c∈[MergedCutCells.Batch042.certificate505,MergedCutCells.Batch042.certificate506,MergedCutCells.Batch042.certificate507], c.population=PopulationCertificates.Batch004.certificate94
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers141 {x : ℝ} (hx : certificate141.interval.Contains x) : ∃ c∈certificate141.cells, c.region.interval.Contains x := rat_cut_group_covers certificate141 numericValid141 hx

def certificate142 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate94,PopulationCertificates.Batch004.certificate94,[MergedCutCells.Batch042.certificate508,MergedCutCells.Batch042.certificate509,MergedCutCells.Batch042.certificate510,MergedCutCells.Batch042.certificate511,MergedCutCells.Batch042.certificate512,MergedCutCells.Batch042.certificate513,MergedCutCells.Batch042.certificate514,MergedCutCells.Batch042.certificate515],(57220961/62500000),none,(1/2),(192906772279595999/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid142 : certificate142.NumericValid := by decide +kernel
theorem cellsSound142 : ∀ c∈certificate142.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch042.certificate508,MergedCutCells.Batch042.certificate509,MergedCutCells.Batch042.certificate510,MergedCutCells.Batch042.certificate511,MergedCutCells.Batch042.certificate512,MergedCutCells.Batch042.certificate513,MergedCutCells.Batch042.certificate514,MergedCutCells.Batch042.certificate515], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound508,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound509,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound510,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound512,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound513,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound514,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.sound515,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric142 : ∀ c∈certificate142.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch042.certificate508,MergedCutCells.Batch042.certificate509,MergedCutCells.Batch042.certificate510,MergedCutCells.Batch042.certificate511,MergedCutCells.Batch042.certificate512,MergedCutCells.Batch042.certificate513,MergedCutCells.Batch042.certificate514,MergedCutCells.Batch042.certificate515], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid508,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid509,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid510,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid512,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid513,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid514,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch042.numericValid515,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid142 : ∀ c∈certificate142.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch042.certificate508,MergedCutCells.Batch042.certificate509,MergedCutCells.Batch042.certificate510,MergedCutCells.Batch042.certificate511,MergedCutCells.Batch042.certificate512,MergedCutCells.Batch042.certificate513,MergedCutCells.Batch042.certificate514,MergedCutCells.Batch042.certificate515], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches142 : ∀ c∈certificate142.cells, c.population=certificate142.population := by
  change ∀ c∈[MergedCutCells.Batch042.certificate508,MergedCutCells.Batch042.certificate509,MergedCutCells.Batch042.certificate510,MergedCutCells.Batch042.certificate511,MergedCutCells.Batch042.certificate512,MergedCutCells.Batch042.certificate513,MergedCutCells.Batch042.certificate514,MergedCutCells.Batch042.certificate515], c.population=PopulationCertificates.Batch004.certificate94
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers142 {x : ℝ} (hx : certificate142.interval.Contains x) : ∃ c∈certificate142.cells, c.region.interval.Contains x := rat_cut_group_covers certificate142 numericValid142 hx

def certificate143 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate95,PopulationCertificates.Batch004.certificate95,[MergedCutCells.Batch043.certificate516,MergedCutCells.Batch043.certificate517,MergedCutCells.Batch043.certificate518,MergedCutCells.Batch043.certificate519],(743950670740583891/200000000000000000),none,(1/2),(507535370141118263/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid143 : certificate143.NumericValid := by decide +kernel
theorem cellsSound143 : ∀ c∈certificate143.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch043.certificate516,MergedCutCells.Batch043.certificate517,MergedCutCells.Batch043.certificate518,MergedCutCells.Batch043.certificate519], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound516,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound517,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound518,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound519,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric143 : ∀ c∈certificate143.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch043.certificate516,MergedCutCells.Batch043.certificate517,MergedCutCells.Batch043.certificate518,MergedCutCells.Batch043.certificate519], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid516,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid517,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid518,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid519,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid143 : ∀ c∈certificate143.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch043.certificate516,MergedCutCells.Batch043.certificate517,MergedCutCells.Batch043.certificate518,MergedCutCells.Batch043.certificate519], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches143 : ∀ c∈certificate143.cells, c.population=certificate143.population := by
  change ∀ c∈[MergedCutCells.Batch043.certificate516,MergedCutCells.Batch043.certificate517,MergedCutCells.Batch043.certificate518,MergedCutCells.Batch043.certificate519], c.population=PopulationCertificates.Batch004.certificate95
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers143 {x : ℝ} (hx : certificate143.interval.Contains x) : ∃ c∈certificate143.cells, c.region.interval.Contains x := rat_cut_group_covers certificate143 numericValid143 hx

end Cycle12.MergedCutGroups.Batch011
