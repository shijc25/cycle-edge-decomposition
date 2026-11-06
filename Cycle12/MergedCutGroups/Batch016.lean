import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch006
import Cycle12.MergedCutCells.Batch060
import Cycle12.MergedCutCells.Batch061
import Cycle12.MergedCutCells.Batch062
import Cycle12.MergedCutCells.Batch063
import Cycle12.MergedCutCells.Batch064
import Cycle12.PopulationCertificates.Batch006

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch016

def certificate192 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate128,PopulationCertificates.Batch006.certificate128,[MergedCutCells.Batch060.certificate725,MergedCutCells.Batch060.certificate726],(82673136777992377/100000000000000000),(some (434187153/500000000)),(1/2),(395725699874224423/1000000000000000000),(some (119257165368023363/200000000000000000)),(some (283561702334919239/1000000000000000000))⟩
theorem numericValid192 : certificate192.NumericValid := by decide +kernel
theorem cellsSound192 : ∀ c∈certificate192.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch060.certificate725,MergedCutCells.Batch060.certificate726], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound725,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound726,List.forall_mem_nil _⟩⟩
theorem cellsNumeric192 : ∀ c∈certificate192.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch060.certificate725,MergedCutCells.Batch060.certificate726], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid725,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid726,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid192 : ∀ c∈certificate192.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch060.certificate725,MergedCutCells.Batch060.certificate726], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid65,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid65,List.forall_mem_nil _⟩⟩
theorem populationMatches192 : ∀ c∈certificate192.cells, c.population=certificate192.population := by
  change ∀ c∈[MergedCutCells.Batch060.certificate725,MergedCutCells.Batch060.certificate726], c.population=PopulationCertificates.Batch006.certificate128
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers192 {x : ℝ} (hx : certificate192.interval.Contains x) : ∃ c∈certificate192.cells, c.region.interval.Contains x := rat_cut_group_covers certificate192 numericValid192 hx

def certificate193 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate128,PopulationCertificates.Batch006.certificate128,[MergedCutCells.Batch060.certificate727,MergedCutCells.Batch060.certificate728,MergedCutCells.Batch060.certificate729,MergedCutCells.Batch060.certificate730,MergedCutCells.Batch060.certificate731,MergedCutCells.Batch061.certificate732,MergedCutCells.Batch061.certificate733],(434187153/500000000),none,(1/2),(139190531991845173/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid193 : certificate193.NumericValid := by decide +kernel
theorem cellsSound193 : ∀ c∈certificate193.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch060.certificate727,MergedCutCells.Batch060.certificate728,MergedCutCells.Batch060.certificate729,MergedCutCells.Batch060.certificate730,MergedCutCells.Batch060.certificate731,MergedCutCells.Batch061.certificate732,MergedCutCells.Batch061.certificate733], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound727,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound728,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound729,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound730,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound732,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound733,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric193 : ∀ c∈certificate193.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch060.certificate727,MergedCutCells.Batch060.certificate728,MergedCutCells.Batch060.certificate729,MergedCutCells.Batch060.certificate730,MergedCutCells.Batch060.certificate731,MergedCutCells.Batch061.certificate732,MergedCutCells.Batch061.certificate733], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid727,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid728,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid729,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid730,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid732,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid733,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid193 : ∀ c∈certificate193.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch060.certificate727,MergedCutCells.Batch060.certificate728,MergedCutCells.Batch060.certificate729,MergedCutCells.Batch060.certificate730,MergedCutCells.Batch060.certificate731,MergedCutCells.Batch061.certificate732,MergedCutCells.Batch061.certificate733], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches193 : ∀ c∈certificate193.cells, c.population=certificate193.population := by
  change ∀ c∈[MergedCutCells.Batch060.certificate727,MergedCutCells.Batch060.certificate728,MergedCutCells.Batch060.certificate729,MergedCutCells.Batch060.certificate730,MergedCutCells.Batch060.certificate731,MergedCutCells.Batch061.certificate732,MergedCutCells.Batch061.certificate733], c.population=PopulationCertificates.Batch006.certificate128
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers193 {x : ℝ} (hx : certificate193.interval.Contains x) : ∃ c∈certificate193.cells, c.region.interval.Contains x := rat_cut_group_covers certificate193 numericValid193 hx

def certificate194 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate129,PopulationCertificates.Batch006.certificate129,[MergedCutCells.Batch061.certificate734,MergedCutCells.Batch061.certificate735,MergedCutCells.Batch061.certificate736,MergedCutCells.Batch061.certificate737],(3725643604067568697/1000000000000000000),none,(1/2),(603589697679141123/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid194 : certificate194.NumericValid := by decide +kernel
theorem cellsSound194 : ∀ c∈certificate194.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch061.certificate734,MergedCutCells.Batch061.certificate735,MergedCutCells.Batch061.certificate736,MergedCutCells.Batch061.certificate737], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound734,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound735,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound736,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound737,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric194 : ∀ c∈certificate194.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch061.certificate734,MergedCutCells.Batch061.certificate735,MergedCutCells.Batch061.certificate736,MergedCutCells.Batch061.certificate737], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid734,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid735,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid736,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid737,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid194 : ∀ c∈certificate194.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch061.certificate734,MergedCutCells.Batch061.certificate735,MergedCutCells.Batch061.certificate736,MergedCutCells.Batch061.certificate737], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches194 : ∀ c∈certificate194.cells, c.population=certificate194.population := by
  change ∀ c∈[MergedCutCells.Batch061.certificate734,MergedCutCells.Batch061.certificate735,MergedCutCells.Batch061.certificate736,MergedCutCells.Batch061.certificate737], c.population=PopulationCertificates.Batch006.certificate129
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers194 {x : ℝ} (hx : certificate194.interval.Contains x) : ∃ c∈certificate194.cells, c.region.interval.Contains x := rat_cut_group_covers certificate194 numericValid194 hx

def certificate195 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate130,PopulationCertificates.Batch006.certificate130,[MergedCutCells.Batch061.certificate738,MergedCutCells.Batch061.certificate739],(51839366171195887/62500000000000000),(some (174283949/200000000)),(1/2),(101771327961693037/250000000000000000),(some (585246855891333/976562500000000)),(some (8963572015422101/31250000000000000))⟩
theorem numericValid195 : certificate195.NumericValid := by decide +kernel
theorem cellsSound195 : ∀ c∈certificate195.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch061.certificate738,MergedCutCells.Batch061.certificate739], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound739,List.forall_mem_nil _⟩⟩
theorem cellsNumeric195 : ∀ c∈certificate195.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch061.certificate738,MergedCutCells.Batch061.certificate739], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid738,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid739,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid195 : ∀ c∈certificate195.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch061.certificate738,MergedCutCells.Batch061.certificate739], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid66,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid66,List.forall_mem_nil _⟩⟩
theorem populationMatches195 : ∀ c∈certificate195.cells, c.population=certificate195.population := by
  change ∀ c∈[MergedCutCells.Batch061.certificate738,MergedCutCells.Batch061.certificate739], c.population=PopulationCertificates.Batch006.certificate130
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers195 {x : ℝ} (hx : certificate195.interval.Contains x) : ∃ c∈certificate195.cells, c.region.interval.Contains x := rat_cut_group_covers certificate195 numericValid195 hx

def certificate196 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate130,PopulationCertificates.Batch006.certificate130,[MergedCutCells.Batch061.certificate740,MergedCutCells.Batch061.certificate741,MergedCutCells.Batch061.certificate742,MergedCutCells.Batch061.certificate743,MergedCutCells.Batch062.certificate744,MergedCutCells.Batch062.certificate745],(174283949/200000000),none,(1/2),(281381946085224067/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid196 : certificate196.NumericValid := by decide +kernel
theorem cellsSound196 : ∀ c∈certificate196.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch061.certificate740,MergedCutCells.Batch061.certificate741,MergedCutCells.Batch061.certificate742,MergedCutCells.Batch061.certificate743,MergedCutCells.Batch062.certificate744,MergedCutCells.Batch062.certificate745], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound740,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound741,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.sound743,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound744,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound745,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric196 : ∀ c∈certificate196.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch061.certificate740,MergedCutCells.Batch061.certificate741,MergedCutCells.Batch061.certificate742,MergedCutCells.Batch061.certificate743,MergedCutCells.Batch062.certificate744,MergedCutCells.Batch062.certificate745], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid740,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid741,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid742,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch061.numericValid743,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid744,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid745,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid196 : ∀ c∈certificate196.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch061.certificate740,MergedCutCells.Batch061.certificate741,MergedCutCells.Batch061.certificate742,MergedCutCells.Batch061.certificate743,MergedCutCells.Batch062.certificate744,MergedCutCells.Batch062.certificate745], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches196 : ∀ c∈certificate196.cells, c.population=certificate196.population := by
  change ∀ c∈[MergedCutCells.Batch061.certificate740,MergedCutCells.Batch061.certificate741,MergedCutCells.Batch061.certificate742,MergedCutCells.Batch061.certificate743,MergedCutCells.Batch062.certificate744,MergedCutCells.Batch062.certificate745], c.population=PopulationCertificates.Batch006.certificate130
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers196 {x : ℝ} (hx : certificate196.interval.Contains x) : ∃ c∈certificate196.cells, c.region.interval.Contains x := rat_cut_group_covers certificate196 numericValid196 hx

def certificate197 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate131,PopulationCertificates.Batch006.certificate131,[MergedCutCells.Batch062.certificate746,MergedCutCells.Batch062.certificate747,MergedCutCells.Batch062.certificate748],(746357658101164341/200000000000000000),none,(1/2),(616649136847292971/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid197 : certificate197.NumericValid := by decide +kernel
theorem cellsSound197 : ∀ c∈certificate197.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch062.certificate746,MergedCutCells.Batch062.certificate747,MergedCutCells.Batch062.certificate748], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound746,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound747,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound748,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric197 : ∀ c∈certificate197.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch062.certificate746,MergedCutCells.Batch062.certificate747,MergedCutCells.Batch062.certificate748], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid746,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid747,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid748,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid197 : ∀ c∈certificate197.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch062.certificate746,MergedCutCells.Batch062.certificate747,MergedCutCells.Batch062.certificate748], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches197 : ∀ c∈certificate197.cells, c.population=certificate197.population := by
  change ∀ c∈[MergedCutCells.Batch062.certificate746,MergedCutCells.Batch062.certificate747,MergedCutCells.Batch062.certificate748], c.population=PopulationCertificates.Batch006.certificate131
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers197 {x : ℝ} (hx : certificate197.interval.Contains x) : ∃ c∈certificate197.cells, c.region.interval.Contains x := rat_cut_group_covers certificate197 numericValid197 hx

def certificate198 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate132,PopulationCertificates.Batch006.certificate132,[MergedCutCells.Batch062.certificate749,MergedCutCells.Batch062.certificate750],(829188430150720329/1000000000000000000),(some (870925927/1000000000)),(1/2),(202778482604389441/500000000000000000),(some (301123645322572033/500000000000000000)),(some (72526702439674817/250000000000000000))⟩
theorem numericValid198 : certificate198.NumericValid := by decide +kernel
theorem cellsSound198 : ∀ c∈certificate198.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch062.certificate749,MergedCutCells.Batch062.certificate750], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound750,List.forall_mem_nil _⟩⟩
theorem cellsNumeric198 : ∀ c∈certificate198.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch062.certificate749,MergedCutCells.Batch062.certificate750], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid749,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid750,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid198 : ∀ c∈certificate198.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch062.certificate749,MergedCutCells.Batch062.certificate750], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid67,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid67,List.forall_mem_nil _⟩⟩
theorem populationMatches198 : ∀ c∈certificate198.cells, c.population=certificate198.population := by
  change ∀ c∈[MergedCutCells.Batch062.certificate749,MergedCutCells.Batch062.certificate750], c.population=PopulationCertificates.Batch006.certificate132
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers198 {x : ℝ} (hx : certificate198.interval.Contains x) : ∃ c∈certificate198.cells, c.region.interval.Contains x := rat_cut_group_covers certificate198 numericValid198 hx

def certificate199 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate132,PopulationCertificates.Batch006.certificate132,[MergedCutCells.Batch062.certificate751,MergedCutCells.Batch062.certificate752,MergedCutCells.Batch062.certificate753,MergedCutCells.Batch062.certificate754,MergedCutCells.Batch062.certificate755,MergedCutCells.Batch063.certificate756,MergedCutCells.Batch063.certificate757],(870925927/1000000000),none,(1/2),(35814388106081381/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid199 : certificate199.NumericValid := by decide +kernel
theorem cellsSound199 : ∀ c∈certificate199.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch062.certificate751,MergedCutCells.Batch062.certificate752,MergedCutCells.Batch062.certificate753,MergedCutCells.Batch062.certificate754,MergedCutCells.Batch062.certificate755,MergedCutCells.Batch063.certificate756,MergedCutCells.Batch063.certificate757], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound751,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound752,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound753,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.sound755,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound757,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric199 : ∀ c∈certificate199.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch062.certificate751,MergedCutCells.Batch062.certificate752,MergedCutCells.Batch062.certificate753,MergedCutCells.Batch062.certificate754,MergedCutCells.Batch062.certificate755,MergedCutCells.Batch063.certificate756,MergedCutCells.Batch063.certificate757], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid751,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid752,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid753,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch062.numericValid755,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid757,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid199 : ∀ c∈certificate199.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch062.certificate751,MergedCutCells.Batch062.certificate752,MergedCutCells.Batch062.certificate753,MergedCutCells.Batch062.certificate754,MergedCutCells.Batch062.certificate755,MergedCutCells.Batch063.certificate756,MergedCutCells.Batch063.certificate757], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches199 : ∀ c∈certificate199.cells, c.population=certificate199.population := by
  change ∀ c∈[MergedCutCells.Batch062.certificate751,MergedCutCells.Batch062.certificate752,MergedCutCells.Batch062.certificate753,MergedCutCells.Batch062.certificate754,MergedCutCells.Batch062.certificate755,MergedCutCells.Batch063.certificate756,MergedCutCells.Batch063.certificate757], c.population=PopulationCertificates.Batch006.certificate132
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers199 {x : ℝ} (hx : certificate199.interval.Contains x) : ∃ c∈certificate199.cells, c.region.interval.Contains x := rat_cut_group_covers certificate199 numericValid199 hx

def certificate200 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate133,PopulationCertificates.Batch006.certificate133,[MergedCutCells.Batch063.certificate758,MergedCutCells.Batch063.certificate759,MergedCutCells.Batch063.certificate760,MergedCutCells.Batch063.certificate761],(1870025630398570227/500000000000000000),none,(1/2),(126555142996167017/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid200 : certificate200.NumericValid := by decide +kernel
theorem cellsSound200 : ∀ c∈certificate200.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch063.certificate758,MergedCutCells.Batch063.certificate759,MergedCutCells.Batch063.certificate760,MergedCutCells.Batch063.certificate761], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound759,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound760,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound761,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric200 : ∀ c∈certificate200.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch063.certificate758,MergedCutCells.Batch063.certificate759,MergedCutCells.Batch063.certificate760,MergedCutCells.Batch063.certificate761], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid759,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid760,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid761,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid200 : ∀ c∈certificate200.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch063.certificate758,MergedCutCells.Batch063.certificate759,MergedCutCells.Batch063.certificate760,MergedCutCells.Batch063.certificate761], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches200 : ∀ c∈certificate200.cells, c.population=certificate200.population := by
  change ∀ c∈[MergedCutCells.Batch063.certificate758,MergedCutCells.Batch063.certificate759,MergedCutCells.Batch063.certificate760,MergedCutCells.Batch063.certificate761], c.population=PopulationCertificates.Batch006.certificate133
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers200 {x : ℝ} (hx : certificate200.interval.Contains x) : ∃ c∈certificate200.cells, c.region.interval.Contains x := rat_cut_group_covers certificate200 numericValid200 hx

def certificate201 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate134,PopulationCertificates.Batch006.certificate134,[MergedCutCells.Batch063.certificate762,MergedCutCells.Batch063.certificate763],(831061211833614349/1000000000000000000),(some (87311419/100000000)),(1/2),(661855679654491/1600000000000000),(some (302598652612107811/500000000000000000)),(some (146716683407820811/500000000000000000))⟩
theorem numericValid201 : certificate201.NumericValid := by decide +kernel
theorem cellsSound201 : ∀ c∈certificate201.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch063.certificate762,MergedCutCells.Batch063.certificate763], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound762,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound763,List.forall_mem_nil _⟩⟩
theorem cellsNumeric201 : ∀ c∈certificate201.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch063.certificate762,MergedCutCells.Batch063.certificate763], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid762,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid763,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid201 : ∀ c∈certificate201.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch063.certificate762,MergedCutCells.Batch063.certificate763], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid68,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid68,List.forall_mem_nil _⟩⟩
theorem populationMatches201 : ∀ c∈certificate201.cells, c.population=certificate201.population := by
  change ∀ c∈[MergedCutCells.Batch063.certificate762,MergedCutCells.Batch063.certificate763], c.population=PopulationCertificates.Batch006.certificate134
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers201 {x : ℝ} (hx : certificate201.interval.Contains x) : ∃ c∈certificate201.cells, c.region.interval.Contains x := rat_cut_group_covers certificate201 numericValid201 hx

def certificate202 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate134,PopulationCertificates.Batch006.certificate134,[MergedCutCells.Batch063.certificate764,MergedCutCells.Batch063.certificate765,MergedCutCells.Batch063.certificate766,MergedCutCells.Batch063.certificate767,MergedCutCells.Batch064.certificate768,MergedCutCells.Batch064.certificate769,MergedCutCells.Batch064.certificate770],(87311419/100000000),none,(1/2),(146767544172616809/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid202 : certificate202.NumericValid := by decide +kernel
theorem cellsSound202 : ∀ c∈certificate202.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch063.certificate764,MergedCutCells.Batch063.certificate765,MergedCutCells.Batch063.certificate766,MergedCutCells.Batch063.certificate767,MergedCutCells.Batch064.certificate768,MergedCutCells.Batch064.certificate769,MergedCutCells.Batch064.certificate770], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound764,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound765,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound766,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.sound767,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound768,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound769,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound770,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric202 : ∀ c∈certificate202.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch063.certificate764,MergedCutCells.Batch063.certificate765,MergedCutCells.Batch063.certificate766,MergedCutCells.Batch063.certificate767,MergedCutCells.Batch064.certificate768,MergedCutCells.Batch064.certificate769,MergedCutCells.Batch064.certificate770], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid764,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid765,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid766,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch063.numericValid767,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid768,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid769,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid770,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid202 : ∀ c∈certificate202.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch063.certificate764,MergedCutCells.Batch063.certificate765,MergedCutCells.Batch063.certificate766,MergedCutCells.Batch063.certificate767,MergedCutCells.Batch064.certificate768,MergedCutCells.Batch064.certificate769,MergedCutCells.Batch064.certificate770], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches202 : ∀ c∈certificate202.cells, c.population=certificate202.population := by
  change ∀ c∈[MergedCutCells.Batch063.certificate764,MergedCutCells.Batch063.certificate765,MergedCutCells.Batch063.certificate766,MergedCutCells.Batch063.certificate767,MergedCutCells.Batch064.certificate768,MergedCutCells.Batch064.certificate769,MergedCutCells.Batch064.certificate770], c.population=PopulationCertificates.Batch006.certificate134
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers202 {x : ℝ} (hx : certificate202.interval.Contains x) : ∃ c∈certificate202.cells, c.region.interval.Contains x := rat_cut_group_covers certificate202 numericValid202 hx

def certificate203 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate135,PopulationCertificates.Batch006.certificate135,[MergedCutCells.Batch064.certificate771,MergedCutCells.Batch064.certificate772,MergedCutCells.Batch064.certificate773],(1873149586018979/500000000000000),none,(1/2),(2012962157522813/3125000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid203 : certificate203.NumericValid := by decide +kernel
theorem cellsSound203 : ∀ c∈certificate203.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch064.certificate771,MergedCutCells.Batch064.certificate772,MergedCutCells.Batch064.certificate773], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound771,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound772,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound773,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric203 : ∀ c∈certificate203.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch064.certificate771,MergedCutCells.Batch064.certificate772,MergedCutCells.Batch064.certificate773], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid771,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid772,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid773,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid203 : ∀ c∈certificate203.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch064.certificate771,MergedCutCells.Batch064.certificate772,MergedCutCells.Batch064.certificate773], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches203 : ∀ c∈certificate203.cells, c.population=certificate203.population := by
  change ∀ c∈[MergedCutCells.Batch064.certificate771,MergedCutCells.Batch064.certificate772,MergedCutCells.Batch064.certificate773], c.population=PopulationCertificates.Batch006.certificate135
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers203 {x : ℝ} (hx : certificate203.interval.Contains x) : ∃ c∈certificate203.cells, c.region.interval.Contains x := rat_cut_group_covers certificate203 numericValid203 hx

end Cycle12.MergedCutGroups.Batch016
