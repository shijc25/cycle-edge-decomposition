import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch005
import Cycle12.MergedCutCells.Batch047
import Cycle12.MergedCutCells.Batch048
import Cycle12.MergedCutCells.Batch049
import Cycle12.MergedCutCells.Batch050
import Cycle12.MergedCutCells.Batch051
import Cycle12.PopulationCertificates.Batch005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch013

def certificate156 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate104,PopulationCertificates.Batch005.certificate104,[MergedCutCells.Batch047.certificate572,MergedCutCells.Batch047.certificate573,MergedCutCells.Batch047.certificate574],(400953972966075161/500000000000000000),(some (906886717/1000000000)),(1/2),(61464304119246553/200000000000000000),(some (34434691466086657/62500000000000000)),(some (119945851177609947/500000000000000000))⟩
theorem numericValid156 : certificate156.NumericValid := by decide +kernel
theorem cellsSound156 : ∀ c∈certificate156.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch047.certificate572,MergedCutCells.Batch047.certificate573,MergedCutCells.Batch047.certificate574], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound572,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound573,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound574,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric156 : ∀ c∈certificate156.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch047.certificate572,MergedCutCells.Batch047.certificate573,MergedCutCells.Batch047.certificate574], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid572,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid573,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid574,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid156 : ∀ c∈certificate156.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch047.certificate572,MergedCutCells.Batch047.certificate573,MergedCutCells.Batch047.certificate574], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid53,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid53,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid53,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches156 : ∀ c∈certificate156.cells, c.population=certificate156.population := by
  change ∀ c∈[MergedCutCells.Batch047.certificate572,MergedCutCells.Batch047.certificate573,MergedCutCells.Batch047.certificate574], c.population=PopulationCertificates.Batch005.certificate104
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers156 {x : ℝ} (hx : certificate156.interval.Contains x) : ∃ c∈certificate156.cells, c.region.interval.Contains x := rat_cut_group_covers certificate156 numericValid156 hx

def certificate157 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate104,PopulationCertificates.Batch005.certificate104,[MergedCutCells.Batch047.certificate575,MergedCutCells.Batch048.certificate576,MergedCutCells.Batch048.certificate577,MergedCutCells.Batch048.certificate578,MergedCutCells.Batch048.certificate579,MergedCutCells.Batch048.certificate580],(906886717/1000000000),none,(1/2),(219733059694731139/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid157 : certificate157.NumericValid := by decide +kernel
theorem cellsSound157 : ∀ c∈certificate157.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch047.certificate575,MergedCutCells.Batch048.certificate576,MergedCutCells.Batch048.certificate577,MergedCutCells.Batch048.certificate578,MergedCutCells.Batch048.certificate579,MergedCutCells.Batch048.certificate580], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound575,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound576,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound577,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound578,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound579,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound580,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric157 : ∀ c∈certificate157.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch047.certificate575,MergedCutCells.Batch048.certificate576,MergedCutCells.Batch048.certificate577,MergedCutCells.Batch048.certificate578,MergedCutCells.Batch048.certificate579,MergedCutCells.Batch048.certificate580], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid575,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid576,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid577,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid578,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid579,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid580,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid157 : ∀ c∈certificate157.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch047.certificate575,MergedCutCells.Batch048.certificate576,MergedCutCells.Batch048.certificate577,MergedCutCells.Batch048.certificate578,MergedCutCells.Batch048.certificate579,MergedCutCells.Batch048.certificate580], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches157 : ∀ c∈certificate157.cells, c.population=certificate157.population := by
  change ∀ c∈[MergedCutCells.Batch047.certificate575,MergedCutCells.Batch048.certificate576,MergedCutCells.Batch048.certificate577,MergedCutCells.Batch048.certificate578,MergedCutCells.Batch048.certificate579,MergedCutCells.Batch048.certificate580], c.population=PopulationCertificates.Batch005.certificate104
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers157 {x : ℝ} (hx : certificate157.interval.Contains x) : ∃ c∈certificate157.cells, c.region.interval.Contains x := rat_cut_group_covers certificate157 numericValid157 hx

def certificate158 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate105,PopulationCertificates.Batch005.certificate105,[MergedCutCells.Batch048.certificate581,MergedCutCells.Batch048.certificate582,MergedCutCells.Batch048.certificate583,MergedCutCells.Batch048.certificate584],(152030904439158931/40000000000000000),none,(1/2),(632698700889095399/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid158 : certificate158.NumericValid := by decide +kernel
theorem cellsSound158 : ∀ c∈certificate158.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch048.certificate581,MergedCutCells.Batch048.certificate582,MergedCutCells.Batch048.certificate583,MergedCutCells.Batch048.certificate584], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound581,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound583,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound584,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric158 : ∀ c∈certificate158.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch048.certificate581,MergedCutCells.Batch048.certificate582,MergedCutCells.Batch048.certificate583,MergedCutCells.Batch048.certificate584], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid581,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid583,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid584,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid158 : ∀ c∈certificate158.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch048.certificate581,MergedCutCells.Batch048.certificate582,MergedCutCells.Batch048.certificate583,MergedCutCells.Batch048.certificate584], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches158 : ∀ c∈certificate158.cells, c.population=certificate158.population := by
  change ∀ c∈[MergedCutCells.Batch048.certificate581,MergedCutCells.Batch048.certificate582,MergedCutCells.Batch048.certificate583,MergedCutCells.Batch048.certificate584], c.population=PopulationCertificates.Batch005.certificate105
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers158 {x : ℝ} (hx : certificate158.interval.Contains x) : ∃ c∈certificate158.cells, c.region.interval.Contains x := rat_cut_group_covers certificate158 numericValid158 hx

def certificate159 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate106,PopulationCertificates.Batch005.certificate106,[MergedCutCells.Batch048.certificate585,MergedCutCells.Batch048.certificate586],(161352630794922151/200000000000000000),(some (890081887/1000000000)),(1/2),(159522536954455791/500000000000000000),(some (555885613253892329/1000000000000000000)),(some (244211148755382263/1000000000000000000))⟩
theorem numericValid159 : certificate159.NumericValid := by decide +kernel
theorem cellsSound159 : ∀ c∈certificate159.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch048.certificate585,MergedCutCells.Batch048.certificate586], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound585,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound586,List.forall_mem_nil _⟩⟩
theorem cellsNumeric159 : ∀ c∈certificate159.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch048.certificate585,MergedCutCells.Batch048.certificate586], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid585,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid586,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid159 : ∀ c∈certificate159.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch048.certificate585,MergedCutCells.Batch048.certificate586], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid54,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid54,List.forall_mem_nil _⟩⟩
theorem populationMatches159 : ∀ c∈certificate159.cells, c.population=certificate159.population := by
  change ∀ c∈[MergedCutCells.Batch048.certificate585,MergedCutCells.Batch048.certificate586], c.population=PopulationCertificates.Batch005.certificate106
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers159 {x : ℝ} (hx : certificate159.interval.Contains x) : ∃ c∈certificate159.cells, c.region.interval.Contains x := rat_cut_group_covers certificate159 numericValid159 hx

def certificate160 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate106,PopulationCertificates.Batch005.certificate106,[MergedCutCells.Batch048.certificate587,MergedCutCells.Batch049.certificate588,MergedCutCells.Batch049.certificate589,MergedCutCells.Batch049.certificate590,MergedCutCells.Batch049.certificate591,MergedCutCells.Batch049.certificate592,MergedCutCells.Batch049.certificate593],(890081887/1000000000),none,(1/2),(215985410672312297/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid160 : certificate160.NumericValid := by decide +kernel
theorem cellsSound160 : ∀ c∈certificate160.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch048.certificate587,MergedCutCells.Batch049.certificate588,MergedCutCells.Batch049.certificate589,MergedCutCells.Batch049.certificate590,MergedCutCells.Batch049.certificate591,MergedCutCells.Batch049.certificate592,MergedCutCells.Batch049.certificate593], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.sound587,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound588,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound590,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound593,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric160 : ∀ c∈certificate160.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch048.certificate587,MergedCutCells.Batch049.certificate588,MergedCutCells.Batch049.certificate589,MergedCutCells.Batch049.certificate590,MergedCutCells.Batch049.certificate591,MergedCutCells.Batch049.certificate592,MergedCutCells.Batch049.certificate593], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch048.numericValid587,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid588,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid590,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid593,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid160 : ∀ c∈certificate160.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch048.certificate587,MergedCutCells.Batch049.certificate588,MergedCutCells.Batch049.certificate589,MergedCutCells.Batch049.certificate590,MergedCutCells.Batch049.certificate591,MergedCutCells.Batch049.certificate592,MergedCutCells.Batch049.certificate593], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches160 : ∀ c∈certificate160.cells, c.population=certificate160.population := by
  change ∀ c∈[MergedCutCells.Batch048.certificate587,MergedCutCells.Batch049.certificate588,MergedCutCells.Batch049.certificate589,MergedCutCells.Batch049.certificate590,MergedCutCells.Batch049.certificate591,MergedCutCells.Batch049.certificate592,MergedCutCells.Batch049.certificate593], c.population=PopulationCertificates.Batch005.certificate106
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers160 {x : ℝ} (hx : certificate160.interval.Contains x) : ∃ c∈certificate160.cells, c.region.interval.Contains x := rat_cut_group_covers certificate160 numericValid160 hx

def certificate161 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate107,PopulationCertificates.Batch005.certificate107,[MergedCutCells.Batch049.certificate594,MergedCutCells.Batch049.certificate595,MergedCutCells.Batch049.certificate596,MergedCutCells.Batch049.certificate597],(3702266616140335519/1000000000000000000),none,(1/2),(504817026134454273/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid161 : certificate161.NumericValid := by decide +kernel
theorem cellsSound161 : ∀ c∈certificate161.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch049.certificate594,MergedCutCells.Batch049.certificate595,MergedCutCells.Batch049.certificate596,MergedCutCells.Batch049.certificate597], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound594,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound596,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound597,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric161 : ∀ c∈certificate161.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch049.certificate594,MergedCutCells.Batch049.certificate595,MergedCutCells.Batch049.certificate596,MergedCutCells.Batch049.certificate597], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid594,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid596,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid597,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid161 : ∀ c∈certificate161.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch049.certificate594,MergedCutCells.Batch049.certificate595,MergedCutCells.Batch049.certificate596,MergedCutCells.Batch049.certificate597], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches161 : ∀ c∈certificate161.cells, c.population=certificate161.population := by
  change ∀ c∈[MergedCutCells.Batch049.certificate594,MergedCutCells.Batch049.certificate595,MergedCutCells.Batch049.certificate596,MergedCutCells.Batch049.certificate597], c.population=PopulationCertificates.Batch005.certificate107
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers161 {x : ℝ} (hx : certificate161.interval.Contains x) : ∃ c∈certificate161.cells, c.region.interval.Contains x := rat_cut_group_covers certificate161 numericValid161 hx

def certificate162 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate108,PopulationCertificates.Batch005.certificate108,[MergedCutCells.Batch049.certificate598,MergedCutCells.Batch049.certificate599],(201997856967259243/250000000000000000),(some (891406537/1000000000)),(1/2),(319404676245918401/1000000000000000000),(some (562427665820522119/1000000000000000000)),(some (250084233648277827/1000000000000000000))⟩
theorem numericValid162 : certificate162.NumericValid := by decide +kernel
theorem cellsSound162 : ∀ c∈certificate162.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch049.certificate598,MergedCutCells.Batch049.certificate599], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.sound599,List.forall_mem_nil _⟩⟩
theorem cellsNumeric162 : ∀ c∈certificate162.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch049.certificate598,MergedCutCells.Batch049.certificate599], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch049.numericValid599,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid162 : ∀ c∈certificate162.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch049.certificate598,MergedCutCells.Batch049.certificate599], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid55,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid55,List.forall_mem_nil _⟩⟩
theorem populationMatches162 : ∀ c∈certificate162.cells, c.population=certificate162.population := by
  change ∀ c∈[MergedCutCells.Batch049.certificate598,MergedCutCells.Batch049.certificate599], c.population=PopulationCertificates.Batch005.certificate108
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers162 {x : ℝ} (hx : certificate162.interval.Contains x) : ∃ c∈certificate162.cells, c.region.interval.Contains x := rat_cut_group_covers certificate162 numericValid162 hx

def certificate163 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate108,PopulationCertificates.Batch005.certificate108,[MergedCutCells.Batch050.certificate600,MergedCutCells.Batch050.certificate601,MergedCutCells.Batch050.certificate602,MergedCutCells.Batch050.certificate603,MergedCutCells.Batch050.certificate604,MergedCutCells.Batch050.certificate605,MergedCutCells.Batch050.certificate606],(891406537/1000000000),none,(1/2),(27826564895858759/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid163 : certificate163.NumericValid := by decide +kernel
theorem cellsSound163 : ∀ c∈certificate163.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch050.certificate600,MergedCutCells.Batch050.certificate601,MergedCutCells.Batch050.certificate602,MergedCutCells.Batch050.certificate603,MergedCutCells.Batch050.certificate604,MergedCutCells.Batch050.certificate605,MergedCutCells.Batch050.certificate606], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound600,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound601,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound602,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound605,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound606,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric163 : ∀ c∈certificate163.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch050.certificate600,MergedCutCells.Batch050.certificate601,MergedCutCells.Batch050.certificate602,MergedCutCells.Batch050.certificate603,MergedCutCells.Batch050.certificate604,MergedCutCells.Batch050.certificate605,MergedCutCells.Batch050.certificate606], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid600,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid601,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid602,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid605,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid606,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid163 : ∀ c∈certificate163.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch050.certificate600,MergedCutCells.Batch050.certificate601,MergedCutCells.Batch050.certificate602,MergedCutCells.Batch050.certificate603,MergedCutCells.Batch050.certificate604,MergedCutCells.Batch050.certificate605,MergedCutCells.Batch050.certificate606], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches163 : ∀ c∈certificate163.cells, c.population=certificate163.population := by
  change ∀ c∈[MergedCutCells.Batch050.certificate600,MergedCutCells.Batch050.certificate601,MergedCutCells.Batch050.certificate602,MergedCutCells.Batch050.certificate603,MergedCutCells.Batch050.certificate604,MergedCutCells.Batch050.certificate605,MergedCutCells.Batch050.certificate606], c.population=PopulationCertificates.Batch005.certificate108
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers163 {x : ℝ} (hx : certificate163.interval.Contains x) : ∃ c∈certificate163.cells, c.region.interval.Contains x := rat_cut_group_covers certificate163 numericValid163 hx

def certificate164 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate109,PopulationCertificates.Batch005.certificate109,[MergedCutCells.Batch050.certificate607,MergedCutCells.Batch050.certificate608,MergedCutCells.Batch050.certificate609,MergedCutCells.Batch050.certificate610],(929293473136722631/250000000000000000),none,(1/2),(33162450692727071/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid164 : certificate164.NumericValid := by decide +kernel
theorem cellsSound164 : ∀ c∈certificate164.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch050.certificate607,MergedCutCells.Batch050.certificate608,MergedCutCells.Batch050.certificate609,MergedCutCells.Batch050.certificate610], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound608,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound609,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound610,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric164 : ∀ c∈certificate164.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch050.certificate607,MergedCutCells.Batch050.certificate608,MergedCutCells.Batch050.certificate609,MergedCutCells.Batch050.certificate610], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid608,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid609,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid610,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid164 : ∀ c∈certificate164.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch050.certificate607,MergedCutCells.Batch050.certificate608,MergedCutCells.Batch050.certificate609,MergedCutCells.Batch050.certificate610], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches164 : ∀ c∈certificate164.cells, c.population=certificate164.population := by
  change ∀ c∈[MergedCutCells.Batch050.certificate607,MergedCutCells.Batch050.certificate608,MergedCutCells.Batch050.certificate609,MergedCutCells.Batch050.certificate610], c.population=PopulationCertificates.Batch005.certificate109
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers164 {x : ℝ} (hx : certificate164.interval.Contains x) : ∃ c∈certificate164.cells, c.region.interval.Contains x := rat_cut_group_covers certificate164 numericValid164 hx

def certificate165 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate110,PopulationCertificates.Batch005.certificate110,[MergedCutCells.Batch050.certificate611,MergedCutCells.Batch051.certificate612],(202656291763157641/250000000000000000),(some (223685731/250000000)),(1/2),(335895935457487531/1000000000000000000),(some (35357305556432217/62500000000000000)),(some (126550740543443809/500000000000000000))⟩
theorem numericValid165 : certificate165.NumericValid := by decide +kernel
theorem cellsSound165 : ∀ c∈certificate165.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch050.certificate611,MergedCutCells.Batch051.certificate612], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.sound611,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound612,List.forall_mem_nil _⟩⟩
theorem cellsNumeric165 : ∀ c∈certificate165.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch050.certificate611,MergedCutCells.Batch051.certificate612], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch050.numericValid611,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid612,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid165 : ∀ c∈certificate165.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch050.certificate611,MergedCutCells.Batch051.certificate612], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid56,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid56,List.forall_mem_nil _⟩⟩
theorem populationMatches165 : ∀ c∈certificate165.cells, c.population=certificate165.population := by
  change ∀ c∈[MergedCutCells.Batch050.certificate611,MergedCutCells.Batch051.certificate612], c.population=PopulationCertificates.Batch005.certificate110
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers165 {x : ℝ} (hx : certificate165.interval.Contains x) : ∃ c∈certificate165.cells, c.region.interval.Contains x := rat_cut_group_covers certificate165 numericValid165 hx

def certificate166 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate110,PopulationCertificates.Batch005.certificate110,[MergedCutCells.Batch051.certificate613,MergedCutCells.Batch051.certificate614,MergedCutCells.Batch051.certificate615,MergedCutCells.Batch051.certificate616,MergedCutCells.Batch051.certificate617,MergedCutCells.Batch051.certificate618,MergedCutCells.Batch051.certificate619],(223685731/250000000),none,(1/2),(237914083341076631/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid166 : certificate166.NumericValid := by decide +kernel
theorem cellsSound166 : ∀ c∈certificate166.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch051.certificate613,MergedCutCells.Batch051.certificate614,MergedCutCells.Batch051.certificate615,MergedCutCells.Batch051.certificate616,MergedCutCells.Batch051.certificate617,MergedCutCells.Batch051.certificate618,MergedCutCells.Batch051.certificate619], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound613,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound614,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound615,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound616,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound617,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric166 : ∀ c∈certificate166.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch051.certificate613,MergedCutCells.Batch051.certificate614,MergedCutCells.Batch051.certificate615,MergedCutCells.Batch051.certificate616,MergedCutCells.Batch051.certificate617,MergedCutCells.Batch051.certificate618,MergedCutCells.Batch051.certificate619], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid613,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid614,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid615,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid616,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid617,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid166 : ∀ c∈certificate166.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch051.certificate613,MergedCutCells.Batch051.certificate614,MergedCutCells.Batch051.certificate615,MergedCutCells.Batch051.certificate616,MergedCutCells.Batch051.certificate617,MergedCutCells.Batch051.certificate618,MergedCutCells.Batch051.certificate619], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches166 : ∀ c∈certificate166.cells, c.population=certificate166.population := by
  change ∀ c∈[MergedCutCells.Batch051.certificate613,MergedCutCells.Batch051.certificate614,MergedCutCells.Batch051.certificate615,MergedCutCells.Batch051.certificate616,MergedCutCells.Batch051.certificate617,MergedCutCells.Batch051.certificate618,MergedCutCells.Batch051.certificate619], c.population=PopulationCertificates.Batch005.certificate110
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers166 {x : ℝ} (hx : certificate166.interval.Contains x) : ∃ c∈certificate166.cells, c.region.interval.Contains x := rat_cut_group_covers certificate166 numericValid166 hx

def certificate167 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate111,PopulationCertificates.Batch005.certificate111,[MergedCutCells.Batch051.certificate620,MergedCutCells.Batch051.certificate621,MergedCutCells.Batch051.certificate622],(3737927244300435437/1000000000000000000),none,(1/2),(22895861924854137/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid167 : certificate167.NumericValid := by decide +kernel
theorem cellsSound167 : ∀ c∈certificate167.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch051.certificate620,MergedCutCells.Batch051.certificate621,MergedCutCells.Batch051.certificate622], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound620,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.sound622,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric167 : ∀ c∈certificate167.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch051.certificate620,MergedCutCells.Batch051.certificate621,MergedCutCells.Batch051.certificate622], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid620,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch051.numericValid622,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid167 : ∀ c∈certificate167.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch051.certificate620,MergedCutCells.Batch051.certificate621,MergedCutCells.Batch051.certificate622], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches167 : ∀ c∈certificate167.cells, c.population=certificate167.population := by
  change ∀ c∈[MergedCutCells.Batch051.certificate620,MergedCutCells.Batch051.certificate621,MergedCutCells.Batch051.certificate622], c.population=PopulationCertificates.Batch005.certificate111
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers167 {x : ℝ} (hx : certificate167.interval.Contains x) : ∃ c∈certificate167.cells, c.region.interval.Contains x := rat_cut_group_covers certificate167 numericValid167 hx

end Cycle12.MergedCutGroups.Batch013
