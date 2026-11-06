import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch032
import Cycle12.MergedCutCells.Batch296
import Cycle12.MergedCutCells.Batch297
import Cycle12.MergedCutCells.Batch298
import Cycle12.MergedCutCells.Batch299
import Cycle12.MergedCutCells.Batch300
import Cycle12.PopulationCertificates.Batch032

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch080

def certificate960 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate640,PopulationCertificates.Batch032.certificate640,[MergedCutCells.Batch296.certificate3555,MergedCutCells.Batch296.certificate3556],(922479934052004111/1000000000000000000),(some (548100791/500000000)),(1/2),(1262014965747037863/500000000000000000),(some (24086907445128713/62500000000000000)),(some (64738296620473889/500000000000000000))⟩
theorem numericValid960 : certificate960.NumericValid := by decide +kernel
theorem cellsSound960 : ∀ c∈certificate960.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch296.certificate3555,MergedCutCells.Batch296.certificate3556], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3555,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3556,List.forall_mem_nil _⟩⟩
theorem cellsNumeric960 : ∀ c∈certificate960.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch296.certificate3555,MergedCutCells.Batch296.certificate3556], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3555,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3556,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid960 : ∀ c∈certificate960.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch296.certificate3555,MergedCutCells.Batch296.certificate3556], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid321,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid321,List.forall_mem_nil _⟩⟩
theorem populationMatches960 : ∀ c∈certificate960.cells, c.population=certificate960.population := by
  change ∀ c∈[MergedCutCells.Batch296.certificate3555,MergedCutCells.Batch296.certificate3556], c.population=PopulationCertificates.Batch032.certificate640
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers960 {x : ℝ} (hx : certificate960.interval.Contains x) : ∃ c∈certificate960.cells, c.region.interval.Contains x := rat_cut_group_covers certificate960 numericValid960 hx

def certificate961 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate640,PopulationCertificates.Batch032.certificate640,[MergedCutCells.Batch296.certificate3557,MergedCutCells.Batch296.certificate3558,MergedCutCells.Batch296.certificate3559,MergedCutCells.Batch296.certificate3560,MergedCutCells.Batch296.certificate3561,MergedCutCells.Batch296.certificate3562,MergedCutCells.Batch296.certificate3563],(548100791/500000000),none,(1/2),(2486118827162268459/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid961 : certificate961.NumericValid := by decide +kernel
theorem cellsSound961 : ∀ c∈certificate961.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch296.certificate3557,MergedCutCells.Batch296.certificate3558,MergedCutCells.Batch296.certificate3559,MergedCutCells.Batch296.certificate3560,MergedCutCells.Batch296.certificate3561,MergedCutCells.Batch296.certificate3562,MergedCutCells.Batch296.certificate3563], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3558,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3560,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3561,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3562,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3563,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric961 : ∀ c∈certificate961.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch296.certificate3557,MergedCutCells.Batch296.certificate3558,MergedCutCells.Batch296.certificate3559,MergedCutCells.Batch296.certificate3560,MergedCutCells.Batch296.certificate3561,MergedCutCells.Batch296.certificate3562,MergedCutCells.Batch296.certificate3563], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3558,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3560,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3561,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3562,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3563,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid961 : ∀ c∈certificate961.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch296.certificate3557,MergedCutCells.Batch296.certificate3558,MergedCutCells.Batch296.certificate3559,MergedCutCells.Batch296.certificate3560,MergedCutCells.Batch296.certificate3561,MergedCutCells.Batch296.certificate3562,MergedCutCells.Batch296.certificate3563], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches961 : ∀ c∈certificate961.cells, c.population=certificate961.population := by
  change ∀ c∈[MergedCutCells.Batch296.certificate3557,MergedCutCells.Batch296.certificate3558,MergedCutCells.Batch296.certificate3559,MergedCutCells.Batch296.certificate3560,MergedCutCells.Batch296.certificate3561,MergedCutCells.Batch296.certificate3562,MergedCutCells.Batch296.certificate3563], c.population=PopulationCertificates.Batch032.certificate640
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers961 {x : ℝ} (hx : certificate961.interval.Contains x) : ∃ c∈certificate961.cells, c.region.interval.Contains x := rat_cut_group_covers certificate961 numericValid961 hx

def certificate962 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate641,PopulationCertificates.Batch032.certificate641,[MergedCutCells.Batch297.certificate3564,MergedCutCells.Batch297.certificate3565,MergedCutCells.Batch297.certificate3566],(2191236493344520453/250000000000000000),none,(1/2),(4065167378713198683/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid962 : certificate962.NumericValid := by decide +kernel
theorem cellsSound962 : ∀ c∈certificate962.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3564,MergedCutCells.Batch297.certificate3565,MergedCutCells.Batch297.certificate3566], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3564,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3566,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric962 : ∀ c∈certificate962.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3564,MergedCutCells.Batch297.certificate3565,MergedCutCells.Batch297.certificate3566], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3564,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3566,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid962 : ∀ c∈certificate962.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3564,MergedCutCells.Batch297.certificate3565,MergedCutCells.Batch297.certificate3566], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches962 : ∀ c∈certificate962.cells, c.population=certificate962.population := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3564,MergedCutCells.Batch297.certificate3565,MergedCutCells.Batch297.certificate3566], c.population=PopulationCertificates.Batch032.certificate641
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers962 {x : ℝ} (hx : certificate962.interval.Contains x) : ∃ c∈certificate962.cells, c.region.interval.Contains x := rat_cut_group_covers certificate962 numericValid962 hx

def certificate963 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate642,PopulationCertificates.Batch032.certificate642,[MergedCutCells.Batch297.certificate3567,MergedCutCells.Batch297.certificate3568,MergedCutCells.Batch297.certificate3569],(929051451956582937/1000000000000000000),(some (551845877/500000000)),(1/2),(653689722662032317/250000000000000000),(some (77949385211358791/200000000000000000)),(some (131774943201269773/1000000000000000000))⟩
theorem numericValid963 : certificate963.NumericValid := by decide +kernel
theorem cellsSound963 : ∀ c∈certificate963.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3567,MergedCutCells.Batch297.certificate3568,MergedCutCells.Batch297.certificate3569], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3568,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3569,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric963 : ∀ c∈certificate963.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3567,MergedCutCells.Batch297.certificate3568,MergedCutCells.Batch297.certificate3569], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3568,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3569,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid963 : ∀ c∈certificate963.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3567,MergedCutCells.Batch297.certificate3568,MergedCutCells.Batch297.certificate3569], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid322,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid322,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid322,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches963 : ∀ c∈certificate963.cells, c.population=certificate963.population := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3567,MergedCutCells.Batch297.certificate3568,MergedCutCells.Batch297.certificate3569], c.population=PopulationCertificates.Batch032.certificate642
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers963 {x : ℝ} (hx : certificate963.interval.Contains x) : ∃ c∈certificate963.cells, c.region.interval.Contains x := rat_cut_group_covers certificate963 numericValid963 hx

def certificate964 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate642,PopulationCertificates.Batch032.certificate642,[MergedCutCells.Batch297.certificate3570,MergedCutCells.Batch297.certificate3571,MergedCutCells.Batch297.certificate3572,MergedCutCells.Batch297.certificate3573,MergedCutCells.Batch297.certificate3574,MergedCutCells.Batch297.certificate3575],(551845877/500000000),none,(1/2),(2570005202631270069/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid964 : certificate964.NumericValid := by decide +kernel
theorem cellsSound964 : ∀ c∈certificate964.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3570,MergedCutCells.Batch297.certificate3571,MergedCutCells.Batch297.certificate3572,MergedCutCells.Batch297.certificate3573,MergedCutCells.Batch297.certificate3574,MergedCutCells.Batch297.certificate3575], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3571,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3572,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3573,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3574,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.sound3575,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric964 : ∀ c∈certificate964.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3570,MergedCutCells.Batch297.certificate3571,MergedCutCells.Batch297.certificate3572,MergedCutCells.Batch297.certificate3573,MergedCutCells.Batch297.certificate3574,MergedCutCells.Batch297.certificate3575], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3571,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3572,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3573,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3574,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch297.numericValid3575,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid964 : ∀ c∈certificate964.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3570,MergedCutCells.Batch297.certificate3571,MergedCutCells.Batch297.certificate3572,MergedCutCells.Batch297.certificate3573,MergedCutCells.Batch297.certificate3574,MergedCutCells.Batch297.certificate3575], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches964 : ∀ c∈certificate964.cells, c.population=certificate964.population := by
  change ∀ c∈[MergedCutCells.Batch297.certificate3570,MergedCutCells.Batch297.certificate3571,MergedCutCells.Batch297.certificate3572,MergedCutCells.Batch297.certificate3573,MergedCutCells.Batch297.certificate3574,MergedCutCells.Batch297.certificate3575], c.population=PopulationCertificates.Batch032.certificate642
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers964 {x : ℝ} (hx : certificate964.interval.Contains x) : ∃ c∈certificate964.cells, c.region.interval.Contains x := rat_cut_group_covers certificate964 numericValid964 hx

def certificate965 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate643,PopulationCertificates.Batch032.certificate643,[MergedCutCells.Batch298.certificate3576,MergedCutCells.Batch298.certificate3577,MergedCutCells.Batch298.certificate3578],(8673743889299722513/1000000000000000000),none,(1/2),(1639650477136821123/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid965 : certificate965.NumericValid := by decide +kernel
theorem cellsSound965 : ∀ c∈certificate965.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3576,MergedCutCells.Batch298.certificate3577,MergedCutCells.Batch298.certificate3578], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3576,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3577,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3578,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric965 : ∀ c∈certificate965.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3576,MergedCutCells.Batch298.certificate3577,MergedCutCells.Batch298.certificate3578], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3576,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3577,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3578,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid965 : ∀ c∈certificate965.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3576,MergedCutCells.Batch298.certificate3577,MergedCutCells.Batch298.certificate3578], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches965 : ∀ c∈certificate965.cells, c.population=certificate965.population := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3576,MergedCutCells.Batch298.certificate3577,MergedCutCells.Batch298.certificate3578], c.population=PopulationCertificates.Batch032.certificate643
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers965 {x : ℝ} (hx : certificate965.interval.Contains x) : ∃ c∈certificate965.cells, c.region.interval.Contains x := rat_cut_group_covers certificate965 numericValid965 hx

def certificate966 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate644,PopulationCertificates.Batch032.certificate644,[MergedCutCells.Batch298.certificate3579,MergedCutCells.Batch298.certificate3580,MergedCutCells.Batch298.certificate3581],(186799447593190181/200000000000000000),(some (1109327507/1000000000)),(1/2),(2700937960227868557/1000000000000000000),(some (12316361133558127/31250000000000000)),(some (134108889316480869/1000000000000000000))⟩
theorem numericValid966 : certificate966.NumericValid := by decide +kernel
theorem cellsSound966 : ∀ c∈certificate966.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3579,MergedCutCells.Batch298.certificate3580,MergedCutCells.Batch298.certificate3581], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3579,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3580,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3581,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric966 : ∀ c∈certificate966.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3579,MergedCutCells.Batch298.certificate3580,MergedCutCells.Batch298.certificate3581], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3579,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3580,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3581,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid966 : ∀ c∈certificate966.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3579,MergedCutCells.Batch298.certificate3580,MergedCutCells.Batch298.certificate3581], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid323,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid323,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid323,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches966 : ∀ c∈certificate966.cells, c.population=certificate966.population := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3579,MergedCutCells.Batch298.certificate3580,MergedCutCells.Batch298.certificate3581], c.population=PopulationCertificates.Batch032.certificate644
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers966 {x : ℝ} (hx : certificate966.interval.Contains x) : ∃ c∈certificate966.cells, c.region.interval.Contains x := rat_cut_group_covers certificate966 numericValid966 hx

def certificate967 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate644,PopulationCertificates.Batch032.certificate644,[MergedCutCells.Batch298.certificate3582,MergedCutCells.Batch298.certificate3583,MergedCutCells.Batch298.certificate3584,MergedCutCells.Batch298.certificate3585,MergedCutCells.Batch298.certificate3586,MergedCutCells.Batch298.certificate3587],(1109327507/1000000000),none,(1/2),(41555633929991657/15625000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid967 : certificate967.NumericValid := by decide +kernel
theorem cellsSound967 : ∀ c∈certificate967.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3582,MergedCutCells.Batch298.certificate3583,MergedCutCells.Batch298.certificate3584,MergedCutCells.Batch298.certificate3585,MergedCutCells.Batch298.certificate3586,MergedCutCells.Batch298.certificate3587], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3583,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3584,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3585,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3586,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.sound3587,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric967 : ∀ c∈certificate967.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3582,MergedCutCells.Batch298.certificate3583,MergedCutCells.Batch298.certificate3584,MergedCutCells.Batch298.certificate3585,MergedCutCells.Batch298.certificate3586,MergedCutCells.Batch298.certificate3587], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3583,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3584,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3585,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3586,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch298.numericValid3587,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid967 : ∀ c∈certificate967.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3582,MergedCutCells.Batch298.certificate3583,MergedCutCells.Batch298.certificate3584,MergedCutCells.Batch298.certificate3585,MergedCutCells.Batch298.certificate3586,MergedCutCells.Batch298.certificate3587], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches967 : ∀ c∈certificate967.cells, c.population=certificate967.population := by
  change ∀ c∈[MergedCutCells.Batch298.certificate3582,MergedCutCells.Batch298.certificate3583,MergedCutCells.Batch298.certificate3584,MergedCutCells.Batch298.certificate3585,MergedCutCells.Batch298.certificate3586,MergedCutCells.Batch298.certificate3587], c.population=PopulationCertificates.Batch032.certificate644
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers967 {x : ℝ} (hx : certificate967.interval.Contains x) : ∃ c∈certificate967.cells, c.region.interval.Contains x := rat_cut_group_covers certificate967 numericValid967 hx

def certificate968 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate645,PopulationCertificates.Batch032.certificate645,[MergedCutCells.Batch299.certificate3588,MergedCutCells.Batch299.certificate3589,MergedCutCells.Batch299.certificate3590],(4332173086668278667/500000000000000000),none,(1/2),(8309699163332649163/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid968 : certificate968.NumericValid := by decide +kernel
theorem cellsSound968 : ∀ c∈certificate968.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3588,MergedCutCells.Batch299.certificate3589,MergedCutCells.Batch299.certificate3590], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3588,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3590,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric968 : ∀ c∈certificate968.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3588,MergedCutCells.Batch299.certificate3589,MergedCutCells.Batch299.certificate3590], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3588,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3590,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid968 : ∀ c∈certificate968.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3588,MergedCutCells.Batch299.certificate3589,MergedCutCells.Batch299.certificate3590], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches968 : ∀ c∈certificate968.cells, c.population=certificate968.population := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3588,MergedCutCells.Batch299.certificate3589,MergedCutCells.Batch299.certificate3590], c.population=PopulationCertificates.Batch032.certificate645
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers968 {x : ℝ} (hx : certificate968.interval.Contains x) : ∃ c∈certificate968.cells, c.region.interval.Contains x := rat_cut_group_covers certificate968 numericValid968 hx

def certificate969 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate646,PopulationCertificates.Batch032.certificate646,[MergedCutCells.Batch299.certificate3591,MergedCutCells.Batch299.certificate3592,MergedCutCells.Batch299.certificate3593],(187684750543944661/200000000000000000),(some (1114370517/1000000000)),(1/2),(111428642231298141/40000000000000000),(some (199214480928076661/500000000000000000)),(some (34107414778527103/250000000000000000))⟩
theorem numericValid969 : certificate969.NumericValid := by decide +kernel
theorem cellsSound969 : ∀ c∈certificate969.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3591,MergedCutCells.Batch299.certificate3592,MergedCutCells.Batch299.certificate3593], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3593,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric969 : ∀ c∈certificate969.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3591,MergedCutCells.Batch299.certificate3592,MergedCutCells.Batch299.certificate3593], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3593,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid969 : ∀ c∈certificate969.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3591,MergedCutCells.Batch299.certificate3592,MergedCutCells.Batch299.certificate3593], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid324,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid324,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid324,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches969 : ∀ c∈certificate969.cells, c.population=certificate969.population := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3591,MergedCutCells.Batch299.certificate3592,MergedCutCells.Batch299.certificate3593], c.population=PopulationCertificates.Batch032.certificate646
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers969 {x : ℝ} (hx : certificate969.interval.Contains x) : ∃ c∈certificate969.cells, c.region.interval.Contains x := rat_cut_group_covers certificate969 numericValid969 hx

def certificate970 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate646,PopulationCertificates.Batch032.certificate646,[MergedCutCells.Batch299.certificate3594,MergedCutCells.Batch299.certificate3595,MergedCutCells.Batch299.certificate3596,MergedCutCells.Batch299.certificate3597,MergedCutCells.Batch299.certificate3598,MergedCutCells.Batch299.certificate3599],(1114370517/1000000000),none,(1/2),(687789483660628897/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid970 : certificate970.NumericValid := by decide +kernel
theorem cellsSound970 : ∀ c∈certificate970.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3594,MergedCutCells.Batch299.certificate3595,MergedCutCells.Batch299.certificate3596,MergedCutCells.Batch299.certificate3597,MergedCutCells.Batch299.certificate3598,MergedCutCells.Batch299.certificate3599], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3594,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3596,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3597,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.sound3599,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric970 : ∀ c∈certificate970.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3594,MergedCutCells.Batch299.certificate3595,MergedCutCells.Batch299.certificate3596,MergedCutCells.Batch299.certificate3597,MergedCutCells.Batch299.certificate3598,MergedCutCells.Batch299.certificate3599], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3594,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3596,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3597,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch299.numericValid3599,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid970 : ∀ c∈certificate970.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3594,MergedCutCells.Batch299.certificate3595,MergedCutCells.Batch299.certificate3596,MergedCutCells.Batch299.certificate3597,MergedCutCells.Batch299.certificate3598,MergedCutCells.Batch299.certificate3599], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches970 : ∀ c∈certificate970.cells, c.population=certificate970.population := by
  change ∀ c∈[MergedCutCells.Batch299.certificate3594,MergedCutCells.Batch299.certificate3595,MergedCutCells.Batch299.certificate3596,MergedCutCells.Batch299.certificate3597,MergedCutCells.Batch299.certificate3598,MergedCutCells.Batch299.certificate3599], c.population=PopulationCertificates.Batch032.certificate646
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers970 {x : ℝ} (hx : certificate970.interval.Contains x) : ∃ c∈certificate970.cells, c.region.interval.Contains x := rat_cut_group_covers certificate970 numericValid970 hx

def certificate971 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate647,PopulationCertificates.Batch032.certificate647,[MergedCutCells.Batch300.certificate3600,MergedCutCells.Batch300.certificate3601,MergedCutCells.Batch300.certificate3602],(8574242735071908409/1000000000000000000),none,(1/2),(8381091284213893679/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid971 : certificate971.NumericValid := by decide +kernel
theorem cellsSound971 : ∀ c∈certificate971.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3600,MergedCutCells.Batch300.certificate3601,MergedCutCells.Batch300.certificate3602], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3600,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3601,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3602,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric971 : ∀ c∈certificate971.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3600,MergedCutCells.Batch300.certificate3601,MergedCutCells.Batch300.certificate3602], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3600,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3601,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3602,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid971 : ∀ c∈certificate971.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3600,MergedCutCells.Batch300.certificate3601,MergedCutCells.Batch300.certificate3602], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches971 : ∀ c∈certificate971.cells, c.population=certificate971.population := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3600,MergedCutCells.Batch300.certificate3601,MergedCutCells.Batch300.certificate3602], c.population=PopulationCertificates.Batch032.certificate647
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers971 {x : ℝ} (hx : certificate971.interval.Contains x) : ∃ c∈certificate971.cells, c.region.interval.Contains x := rat_cut_group_covers certificate971 numericValid971 hx

end Cycle12.MergedCutGroups.Batch080
