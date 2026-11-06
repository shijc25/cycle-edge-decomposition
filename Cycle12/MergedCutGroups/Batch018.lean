import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch007
import Cycle12.MergedCutCells.Batch068
import Cycle12.MergedCutCells.Batch069
import Cycle12.MergedCutCells.Batch070
import Cycle12.MergedCutCells.Batch071
import Cycle12.MergedCutCells.Batch072
import Cycle12.PopulationCertificates.Batch007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch018

def certificate216 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate144,PopulationCertificates.Batch007.certificate144,[MergedCutCells.Batch068.certificate823,MergedCutCells.Batch068.certificate824],(414714507507866883/500000000000000000),(some (435587883/500000000)),(1/2),(10300353167594341/25000000000000000),(some (124191404241479031/200000000000000000)),(some (78084005150508109/250000000000000000))⟩
theorem numericValid216 : certificate216.NumericValid := by decide +kernel
theorem cellsSound216 : ∀ c∈certificate216.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch068.certificate823,MergedCutCells.Batch068.certificate824], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound824,List.forall_mem_nil _⟩⟩
theorem cellsNumeric216 : ∀ c∈certificate216.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch068.certificate823,MergedCutCells.Batch068.certificate824], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid823,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid824,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid216 : ∀ c∈certificate216.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch068.certificate823,MergedCutCells.Batch068.certificate824], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid73,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid73,List.forall_mem_nil _⟩⟩
theorem populationMatches216 : ∀ c∈certificate216.cells, c.population=certificate216.population := by
  change ∀ c∈[MergedCutCells.Batch068.certificate823,MergedCutCells.Batch068.certificate824], c.population=PopulationCertificates.Batch007.certificate144
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers216 {x : ℝ} (hx : certificate216.interval.Contains x) : ∃ c∈certificate216.cells, c.region.interval.Contains x := rat_cut_group_covers certificate216 numericValid216 hx

def certificate217 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate144,PopulationCertificates.Batch007.certificate144,[MergedCutCells.Batch068.certificate825,MergedCutCells.Batch068.certificate826,MergedCutCells.Batch068.certificate827,MergedCutCells.Batch069.certificate828,MergedCutCells.Batch069.certificate829,MergedCutCells.Batch069.certificate830,MergedCutCells.Batch069.certificate831],(435587883/500000000),none,(1/2),(12823405830813099/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid217 : certificate217.NumericValid := by decide +kernel
theorem cellsSound217 : ∀ c∈certificate217.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch068.certificate825,MergedCutCells.Batch068.certificate826,MergedCutCells.Batch068.certificate827,MergedCutCells.Batch069.certificate828,MergedCutCells.Batch069.certificate829,MergedCutCells.Batch069.certificate830,MergedCutCells.Batch069.certificate831], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound825,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound826,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound827,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound828,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound829,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound830,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound831,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric217 : ∀ c∈certificate217.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch068.certificate825,MergedCutCells.Batch068.certificate826,MergedCutCells.Batch068.certificate827,MergedCutCells.Batch069.certificate828,MergedCutCells.Batch069.certificate829,MergedCutCells.Batch069.certificate830,MergedCutCells.Batch069.certificate831], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid825,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid826,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid827,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid828,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid829,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid830,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid831,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid217 : ∀ c∈certificate217.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch068.certificate825,MergedCutCells.Batch068.certificate826,MergedCutCells.Batch068.certificate827,MergedCutCells.Batch069.certificate828,MergedCutCells.Batch069.certificate829,MergedCutCells.Batch069.certificate830,MergedCutCells.Batch069.certificate831], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches217 : ∀ c∈certificate217.cells, c.population=certificate217.population := by
  change ∀ c∈[MergedCutCells.Batch068.certificate825,MergedCutCells.Batch068.certificate826,MergedCutCells.Batch068.certificate827,MergedCutCells.Batch069.certificate828,MergedCutCells.Batch069.certificate829,MergedCutCells.Batch069.certificate830,MergedCutCells.Batch069.certificate831], c.population=PopulationCertificates.Batch007.certificate144
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers217 {x : ℝ} (hx : certificate217.interval.Contains x) : ∃ c∈certificate217.cells, c.region.interval.Contains x := rat_cut_group_covers certificate217 numericValid217 hx

def certificate218 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate145,PopulationCertificates.Batch007.certificate145,[MergedCutCells.Batch069.certificate832,MergedCutCells.Batch069.certificate833,MergedCutCells.Batch069.certificate834,MergedCutCells.Batch069.certificate835],(3687748415883501937/1000000000000000000),none,(1/2),(74904998375689203/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid218 : certificate218.NumericValid := by decide +kernel
theorem cellsSound218 : ∀ c∈certificate218.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch069.certificate832,MergedCutCells.Batch069.certificate833,MergedCutCells.Batch069.certificate834,MergedCutCells.Batch069.certificate835], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound832,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound833,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound834,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound835,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric218 : ∀ c∈certificate218.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch069.certificate832,MergedCutCells.Batch069.certificate833,MergedCutCells.Batch069.certificate834,MergedCutCells.Batch069.certificate835], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid832,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid833,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid834,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid835,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid218 : ∀ c∈certificate218.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch069.certificate832,MergedCutCells.Batch069.certificate833,MergedCutCells.Batch069.certificate834,MergedCutCells.Batch069.certificate835], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches218 : ∀ c∈certificate218.cells, c.population=certificate218.population := by
  change ∀ c∈[MergedCutCells.Batch069.certificate832,MergedCutCells.Batch069.certificate833,MergedCutCells.Batch069.certificate834,MergedCutCells.Batch069.certificate835], c.population=PopulationCertificates.Batch007.certificate145
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers218 {x : ℝ} (hx : certificate218.interval.Contains x) : ∃ c∈certificate218.cells, c.region.interval.Contains x := rat_cut_group_covers certificate218 numericValid218 hx

def certificate219 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate146,PopulationCertificates.Batch007.certificate146,[MergedCutCells.Batch069.certificate836,MergedCutCells.Batch069.certificate837],(837412990508558581/1000000000000000000),(some (858301601/1000000000)),(1/2),(448076176397510067/1000000000000000000),(some (620052876446791823/1000000000000000000)),(some (38899281418905871/125000000000000000))⟩
theorem numericValid219 : certificate219.NumericValid := by decide +kernel
theorem cellsSound219 : ∀ c∈certificate219.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch069.certificate836,MergedCutCells.Batch069.certificate837], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound836,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound837,List.forall_mem_nil _⟩⟩
theorem cellsNumeric219 : ∀ c∈certificate219.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch069.certificate836,MergedCutCells.Batch069.certificate837], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid836,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid837,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid219 : ∀ c∈certificate219.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch069.certificate836,MergedCutCells.Batch069.certificate837], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid74,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid74,List.forall_mem_nil _⟩⟩
theorem populationMatches219 : ∀ c∈certificate219.cells, c.population=certificate219.population := by
  change ∀ c∈[MergedCutCells.Batch069.certificate836,MergedCutCells.Batch069.certificate837], c.population=PopulationCertificates.Batch007.certificate146
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers219 {x : ℝ} (hx : certificate219.interval.Contains x) : ∃ c∈certificate219.cells, c.region.interval.Contains x := rat_cut_group_covers certificate219 numericValid219 hx

def certificate220 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate146,PopulationCertificates.Batch007.certificate146,[MergedCutCells.Batch069.certificate838,MergedCutCells.Batch069.certificate839,MergedCutCells.Batch070.certificate840,MergedCutCells.Batch070.certificate841,MergedCutCells.Batch070.certificate842,MergedCutCells.Batch070.certificate843,MergedCutCells.Batch070.certificate844],(858301601/1000000000),none,(1/2),(64841366317051617/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid220 : certificate220.NumericValid := by decide +kernel
theorem cellsSound220 : ∀ c∈certificate220.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch069.certificate838,MergedCutCells.Batch069.certificate839,MergedCutCells.Batch070.certificate840,MergedCutCells.Batch070.certificate841,MergedCutCells.Batch070.certificate842,MergedCutCells.Batch070.certificate843,MergedCutCells.Batch070.certificate844], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound838,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.sound839,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound840,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound841,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound842,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound843,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound844,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric220 : ∀ c∈certificate220.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch069.certificate838,MergedCutCells.Batch069.certificate839,MergedCutCells.Batch070.certificate840,MergedCutCells.Batch070.certificate841,MergedCutCells.Batch070.certificate842,MergedCutCells.Batch070.certificate843,MergedCutCells.Batch070.certificate844], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid838,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch069.numericValid839,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid840,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid841,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid842,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid843,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid844,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid220 : ∀ c∈certificate220.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch069.certificate838,MergedCutCells.Batch069.certificate839,MergedCutCells.Batch070.certificate840,MergedCutCells.Batch070.certificate841,MergedCutCells.Batch070.certificate842,MergedCutCells.Batch070.certificate843,MergedCutCells.Batch070.certificate844], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches220 : ∀ c∈certificate220.cells, c.population=certificate220.population := by
  change ∀ c∈[MergedCutCells.Batch069.certificate838,MergedCutCells.Batch069.certificate839,MergedCutCells.Batch070.certificate840,MergedCutCells.Batch070.certificate841,MergedCutCells.Batch070.certificate842,MergedCutCells.Batch070.certificate843,MergedCutCells.Batch070.certificate844], c.population=PopulationCertificates.Batch007.certificate146
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers220 {x : ℝ} (hx : certificate220.interval.Contains x) : ∃ c∈certificate220.cells, c.region.interval.Contains x := rat_cut_group_covers certificate220 numericValid220 hx

def certificate221 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate147,PopulationCertificates.Batch007.certificate147,[MergedCutCells.Batch070.certificate845,MergedCutCells.Batch070.certificate846,MergedCutCells.Batch070.certificate847,MergedCutCells.Batch070.certificate848],(3694179525647318741/1000000000000000000),none,(1/2),(153955284107559431/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid221 : certificate221.NumericValid := by decide +kernel
theorem cellsSound221 : ∀ c∈certificate221.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch070.certificate845,MergedCutCells.Batch070.certificate846,MergedCutCells.Batch070.certificate847,MergedCutCells.Batch070.certificate848], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound845,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound846,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound847,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound848,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric221 : ∀ c∈certificate221.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch070.certificate845,MergedCutCells.Batch070.certificate846,MergedCutCells.Batch070.certificate847,MergedCutCells.Batch070.certificate848], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid845,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid846,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid847,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid848,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid221 : ∀ c∈certificate221.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch070.certificate845,MergedCutCells.Batch070.certificate846,MergedCutCells.Batch070.certificate847,MergedCutCells.Batch070.certificate848], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches221 : ∀ c∈certificate221.cells, c.population=certificate221.population := by
  change ∀ c∈[MergedCutCells.Batch070.certificate845,MergedCutCells.Batch070.certificate846,MergedCutCells.Batch070.certificate847,MergedCutCells.Batch070.certificate848], c.population=PopulationCertificates.Batch007.certificate147
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers221 {x : ℝ} (hx : certificate221.interval.Contains x) : ∃ c∈certificate221.cells, c.region.interval.Contains x := rat_cut_group_covers certificate221 numericValid221 hx

def certificate222 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate148,PopulationCertificates.Batch007.certificate148,[MergedCutCells.Batch070.certificate849,MergedCutCells.Batch070.certificate850,MergedCutCells.Batch070.certificate851,MergedCutCells.Batch071.certificate852,MergedCutCells.Batch071.certificate853,MergedCutCells.Batch071.certificate854,MergedCutCells.Batch071.certificate855,MergedCutCells.Batch071.certificate856],(26373684876365861/31250000000000000),(some 64),(1/2),(162534966683054059/500000000000000000),(some (69314718055994531/100000000000000000)),(some (1398665045297796437/1000000000000000000))⟩
theorem numericValid222 : certificate222.NumericValid := by decide +kernel
theorem cellsSound222 : ∀ c∈certificate222.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch070.certificate849,MergedCutCells.Batch070.certificate850,MergedCutCells.Batch070.certificate851,MergedCutCells.Batch071.certificate852,MergedCutCells.Batch071.certificate853,MergedCutCells.Batch071.certificate854,MergedCutCells.Batch071.certificate855,MergedCutCells.Batch071.certificate856], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound849,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound850,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.sound851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound852,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound853,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound854,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound855,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound856,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric222 : ∀ c∈certificate222.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch070.certificate849,MergedCutCells.Batch070.certificate850,MergedCutCells.Batch070.certificate851,MergedCutCells.Batch071.certificate852,MergedCutCells.Batch071.certificate853,MergedCutCells.Batch071.certificate854,MergedCutCells.Batch071.certificate855,MergedCutCells.Batch071.certificate856], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid849,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid850,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch070.numericValid851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid852,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid853,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid854,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid855,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid856,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid222 : ∀ c∈certificate222.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch070.certificate849,MergedCutCells.Batch070.certificate850,MergedCutCells.Batch070.certificate851,MergedCutCells.Batch071.certificate852,MergedCutCells.Batch071.certificate853,MergedCutCells.Batch071.certificate854,MergedCutCells.Batch071.certificate855,MergedCutCells.Batch071.certificate856], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid75,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid75,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid75,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid75,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid75,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid75,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid75,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid75,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches222 : ∀ c∈certificate222.cells, c.population=certificate222.population := by
  change ∀ c∈[MergedCutCells.Batch070.certificate849,MergedCutCells.Batch070.certificate850,MergedCutCells.Batch070.certificate851,MergedCutCells.Batch071.certificate852,MergedCutCells.Batch071.certificate853,MergedCutCells.Batch071.certificate854,MergedCutCells.Batch071.certificate855,MergedCutCells.Batch071.certificate856], c.population=PopulationCertificates.Batch007.certificate148
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers222 {x : ℝ} (hx : certificate222.interval.Contains x) : ∃ c∈certificate222.cells, c.region.interval.Contains x := rat_cut_group_covers certificate222 numericValid222 hx

def certificate223 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate148,PopulationCertificates.Batch007.certificate148,[MergedCutCells.Batch071.certificate857],64,none,(1/2),(395103605918362113/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid223 : certificate223.NumericValid := by decide +kernel
theorem cellsSound223 : ∀ c∈certificate223.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch071.certificate857], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound857,List.forall_mem_nil _⟩
theorem cellsNumeric223 : ∀ c∈certificate223.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch071.certificate857], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid857,List.forall_mem_nil _⟩
theorem cellsEntropyValid223 : ∀ c∈certificate223.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch071.certificate857], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches223 : ∀ c∈certificate223.cells, c.population=certificate223.population := by
  change ∀ c∈[MergedCutCells.Batch071.certificate857], c.population=PopulationCertificates.Batch007.certificate148
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers223 {x : ℝ} (hx : certificate223.interval.Contains x) : ∃ c∈certificate223.cells, c.region.interval.Contains x := rat_cut_group_covers certificate223 numericValid223 hx

def certificate224 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate149,PopulationCertificates.Batch007.certificate149,[MergedCutCells.Batch071.certificate858,MergedCutCells.Batch071.certificate859,MergedCutCells.Batch071.certificate860],(148110885905899893/40000000000000000),none,(1/2),(314098339942308109/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid224 : certificate224.NumericValid := by decide +kernel
theorem cellsSound224 : ∀ c∈certificate224.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch071.certificate858,MergedCutCells.Batch071.certificate859,MergedCutCells.Batch071.certificate860], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound859,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound860,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric224 : ∀ c∈certificate224.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch071.certificate858,MergedCutCells.Batch071.certificate859,MergedCutCells.Batch071.certificate860], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid859,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid860,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid224 : ∀ c∈certificate224.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch071.certificate858,MergedCutCells.Batch071.certificate859,MergedCutCells.Batch071.certificate860], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches224 : ∀ c∈certificate224.cells, c.population=certificate224.population := by
  change ∀ c∈[MergedCutCells.Batch071.certificate858,MergedCutCells.Batch071.certificate859,MergedCutCells.Batch071.certificate860], c.population=PopulationCertificates.Batch007.certificate149
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers224 {x : ℝ} (hx : certificate224.interval.Contains x) : ∃ c∈certificate224.cells, c.region.interval.Contains x := rat_cut_group_covers certificate224 numericValid224 hx

def certificate225 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate150,PopulationCertificates.Batch007.certificate150,[MergedCutCells.Batch071.certificate861,MergedCutCells.Batch071.certificate862],(168001325086786359/200000000000000000),(some (215236201/250000000)),(1/2),(229850387400721577/500000000000000000),(some (78180657984252677/125000000000000000)),(some (31812134711327303/100000000000000000))⟩
theorem numericValid225 : certificate225.NumericValid := by decide +kernel
theorem cellsSound225 : ∀ c∈certificate225.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch071.certificate861,MergedCutCells.Batch071.certificate862], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound861,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound862,List.forall_mem_nil _⟩⟩
theorem cellsNumeric225 : ∀ c∈certificate225.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch071.certificate861,MergedCutCells.Batch071.certificate862], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid861,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid862,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid225 : ∀ c∈certificate225.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch071.certificate861,MergedCutCells.Batch071.certificate862], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid76,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid76,List.forall_mem_nil _⟩⟩
theorem populationMatches225 : ∀ c∈certificate225.cells, c.population=certificate225.population := by
  change ∀ c∈[MergedCutCells.Batch071.certificate861,MergedCutCells.Batch071.certificate862], c.population=PopulationCertificates.Batch007.certificate150
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers225 {x : ℝ} (hx : certificate225.interval.Contains x) : ∃ c∈certificate225.cells, c.region.interval.Contains x := rat_cut_group_covers certificate225 numericValid225 hx

def certificate226 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate150,PopulationCertificates.Batch007.certificate150,[MergedCutCells.Batch071.certificate863,MergedCutCells.Batch072.certificate864,MergedCutCells.Batch072.certificate865,MergedCutCells.Batch072.certificate866,MergedCutCells.Batch072.certificate867,MergedCutCells.Batch072.certificate868,MergedCutCells.Batch072.certificate869],(215236201/250000000),none,(1/2),(41550280617688563/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid226 : certificate226.NumericValid := by decide +kernel
theorem cellsSound226 : ∀ c∈certificate226.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch071.certificate863,MergedCutCells.Batch072.certificate864,MergedCutCells.Batch072.certificate865,MergedCutCells.Batch072.certificate866,MergedCutCells.Batch072.certificate867,MergedCutCells.Batch072.certificate868,MergedCutCells.Batch072.certificate869], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.sound863,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound864,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound866,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound867,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound868,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound869,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric226 : ∀ c∈certificate226.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch071.certificate863,MergedCutCells.Batch072.certificate864,MergedCutCells.Batch072.certificate865,MergedCutCells.Batch072.certificate866,MergedCutCells.Batch072.certificate867,MergedCutCells.Batch072.certificate868,MergedCutCells.Batch072.certificate869], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch071.numericValid863,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid864,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid866,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid867,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid868,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid869,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid226 : ∀ c∈certificate226.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch071.certificate863,MergedCutCells.Batch072.certificate864,MergedCutCells.Batch072.certificate865,MergedCutCells.Batch072.certificate866,MergedCutCells.Batch072.certificate867,MergedCutCells.Batch072.certificate868,MergedCutCells.Batch072.certificate869], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches226 : ∀ c∈certificate226.cells, c.population=certificate226.population := by
  change ∀ c∈[MergedCutCells.Batch071.certificate863,MergedCutCells.Batch072.certificate864,MergedCutCells.Batch072.certificate865,MergedCutCells.Batch072.certificate866,MergedCutCells.Batch072.certificate867,MergedCutCells.Batch072.certificate868,MergedCutCells.Batch072.certificate869], c.population=PopulationCertificates.Batch007.certificate150
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers226 {x : ℝ} (hx : certificate226.interval.Contains x) : ∃ c∈certificate226.cells, c.region.interval.Contains x := rat_cut_group_covers certificate226 numericValid226 hx

def certificate227 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate151,PopulationCertificates.Batch007.certificate151,[MergedCutCells.Batch072.certificate870,MergedCutCells.Batch072.certificate871,MergedCutCells.Batch072.certificate872,MergedCutCells.Batch072.certificate873],(1854665013682387367/500000000000000000),none,(1/2),(645045551538313707/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid227 : certificate227.NumericValid := by decide +kernel
theorem cellsSound227 : ∀ c∈certificate227.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch072.certificate870,MergedCutCells.Batch072.certificate871,MergedCutCells.Batch072.certificate872,MergedCutCells.Batch072.certificate873], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound870,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound871,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound872,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound873,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric227 : ∀ c∈certificate227.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch072.certificate870,MergedCutCells.Batch072.certificate871,MergedCutCells.Batch072.certificate872,MergedCutCells.Batch072.certificate873], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid870,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid871,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid872,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid873,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid227 : ∀ c∈certificate227.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch072.certificate870,MergedCutCells.Batch072.certificate871,MergedCutCells.Batch072.certificate872,MergedCutCells.Batch072.certificate873], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches227 : ∀ c∈certificate227.cells, c.population=certificate227.population := by
  change ∀ c∈[MergedCutCells.Batch072.certificate870,MergedCutCells.Batch072.certificate871,MergedCutCells.Batch072.certificate872,MergedCutCells.Batch072.certificate873], c.population=PopulationCertificates.Batch007.certificate151
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers227 {x : ℝ} (hx : certificate227.interval.Contains x) : ∃ c∈certificate227.cells, c.region.interval.Contains x := rat_cut_group_covers certificate227 numericValid227 hx

end Cycle12.MergedCutGroups.Batch018
