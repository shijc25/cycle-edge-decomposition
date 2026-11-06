import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch004
import Cycle12.MergedCutCells.Batch034
import Cycle12.MergedCutCells.Batch035
import Cycle12.MergedCutCells.Batch036
import Cycle12.MergedCutCells.Batch037
import Cycle12.MergedCutCells.Batch038
import Cycle12.PopulationCertificates.Batch004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch010

def certificate120 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate80,PopulationCertificates.Batch004.certificate80,[MergedCutCells.Batch034.certificate415,MergedCutCells.Batch034.certificate416,MergedCutCells.Batch034.certificate417],(190178377266053027/250000000000000000),(some (243278257/250000000)),(1/2),(98513068427681009/500000000000000000),(some (480156389584171471/1000000000000000000)),(some (92927449319207087/500000000000000000))⟩
theorem numericValid120 : certificate120.NumericValid := by decide +kernel
theorem cellsSound120 : ∀ c∈certificate120.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch034.certificate415,MergedCutCells.Batch034.certificate416,MergedCutCells.Batch034.certificate417], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound415,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound416,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound417,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric120 : ∀ c∈certificate120.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch034.certificate415,MergedCutCells.Batch034.certificate416,MergedCutCells.Batch034.certificate417], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid415,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid416,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid417,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid120 : ∀ c∈certificate120.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch034.certificate415,MergedCutCells.Batch034.certificate416,MergedCutCells.Batch034.certificate417], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid41,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid41,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid41,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches120 : ∀ c∈certificate120.cells, c.population=certificate120.population := by
  change ∀ c∈[MergedCutCells.Batch034.certificate415,MergedCutCells.Batch034.certificate416,MergedCutCells.Batch034.certificate417], c.population=PopulationCertificates.Batch004.certificate80
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers120 {x : ℝ} (hx : certificate120.interval.Contains x) : ∃ c∈certificate120.cells, c.region.interval.Contains x := rat_cut_group_covers certificate120 numericValid120 hx

def certificate121 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate80,PopulationCertificates.Batch004.certificate80,[MergedCutCells.Batch034.certificate418,MergedCutCells.Batch034.certificate419,MergedCutCells.Batch035.certificate420,MergedCutCells.Batch035.certificate421,MergedCutCells.Batch035.certificate422,MergedCutCells.Batch035.certificate423],(243278257/250000000),none,(1/2),(157201645648082929/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid121 : certificate121.NumericValid := by decide +kernel
theorem cellsSound121 : ∀ c∈certificate121.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch034.certificate418,MergedCutCells.Batch034.certificate419,MergedCutCells.Batch035.certificate420,MergedCutCells.Batch035.certificate421,MergedCutCells.Batch035.certificate422,MergedCutCells.Batch035.certificate423], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound418,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound419,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound420,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound421,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound422,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound423,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric121 : ∀ c∈certificate121.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch034.certificate418,MergedCutCells.Batch034.certificate419,MergedCutCells.Batch035.certificate420,MergedCutCells.Batch035.certificate421,MergedCutCells.Batch035.certificate422,MergedCutCells.Batch035.certificate423], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid418,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid419,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid420,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid421,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid422,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid423,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid121 : ∀ c∈certificate121.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch034.certificate418,MergedCutCells.Batch034.certificate419,MergedCutCells.Batch035.certificate420,MergedCutCells.Batch035.certificate421,MergedCutCells.Batch035.certificate422,MergedCutCells.Batch035.certificate423], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches121 : ∀ c∈certificate121.cells, c.population=certificate121.population := by
  change ∀ c∈[MergedCutCells.Batch034.certificate418,MergedCutCells.Batch034.certificate419,MergedCutCells.Batch035.certificate420,MergedCutCells.Batch035.certificate421,MergedCutCells.Batch035.certificate422,MergedCutCells.Batch035.certificate423], c.population=PopulationCertificates.Batch004.certificate80
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers121 {x : ℝ} (hx : certificate121.interval.Contains x) : ∃ c∈certificate121.cells, c.region.interval.Contains x := rat_cut_group_covers certificate121 numericValid121 hx

def certificate122 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate81,PopulationCertificates.Batch004.certificate81,[MergedCutCells.Batch035.certificate424,MergedCutCells.Batch035.certificate425,MergedCutCells.Batch035.certificate426],(3675516644893656647/1000000000000000000),none,(1/2),(421359289474236451/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid122 : certificate122.NumericValid := by decide +kernel
theorem cellsSound122 : ∀ c∈certificate122.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch035.certificate424,MergedCutCells.Batch035.certificate425,MergedCutCells.Batch035.certificate426], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound424,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound426,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric122 : ∀ c∈certificate122.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch035.certificate424,MergedCutCells.Batch035.certificate425,MergedCutCells.Batch035.certificate426], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid424,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid426,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid122 : ∀ c∈certificate122.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch035.certificate424,MergedCutCells.Batch035.certificate425,MergedCutCells.Batch035.certificate426], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches122 : ∀ c∈certificate122.cells, c.population=certificate122.population := by
  change ∀ c∈[MergedCutCells.Batch035.certificate424,MergedCutCells.Batch035.certificate425,MergedCutCells.Batch035.certificate426], c.population=PopulationCertificates.Batch004.certificate81
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers122 {x : ℝ} (hx : certificate122.interval.Contains x) : ∃ c∈certificate122.cells, c.region.interval.Contains x := rat_cut_group_covers certificate122 numericValid122 hx

def certificate123 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate82,PopulationCertificates.Batch004.certificate82,[MergedCutCells.Batch035.certificate427,MergedCutCells.Batch035.certificate428,MergedCutCells.Batch035.certificate429],(48138004847872429/62500000000000000),(some (240174377/250000000)),(1/2),(47364356591784227/200000000000000000),(some (485685429527268173/1000000000000000000)),(some (18962959627375679/100000000000000000))⟩
theorem numericValid123 : certificate123.NumericValid := by decide +kernel
theorem cellsSound123 : ∀ c∈certificate123.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch035.certificate427,MergedCutCells.Batch035.certificate428,MergedCutCells.Batch035.certificate429], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound428,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound429,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric123 : ∀ c∈certificate123.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch035.certificate427,MergedCutCells.Batch035.certificate428,MergedCutCells.Batch035.certificate429], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid428,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid429,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid123 : ∀ c∈certificate123.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch035.certificate427,MergedCutCells.Batch035.certificate428,MergedCutCells.Batch035.certificate429], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid42,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid42,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid42,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches123 : ∀ c∈certificate123.cells, c.population=certificate123.population := by
  change ∀ c∈[MergedCutCells.Batch035.certificate427,MergedCutCells.Batch035.certificate428,MergedCutCells.Batch035.certificate429], c.population=PopulationCertificates.Batch004.certificate82
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers123 {x : ℝ} (hx : certificate123.interval.Contains x) : ∃ c∈certificate123.cells, c.region.interval.Contains x := rat_cut_group_covers certificate123 numericValid123 hx

def certificate124 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate82,PopulationCertificates.Batch004.certificate82,[MergedCutCells.Batch035.certificate430,MergedCutCells.Batch035.certificate431,MergedCutCells.Batch036.certificate432,MergedCutCells.Batch036.certificate433,MergedCutCells.Batch036.certificate434,MergedCutCells.Batch036.certificate435],(240174377/250000000),none,(1/2),(176215940232835739/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid124 : certificate124.NumericValid := by decide +kernel
theorem cellsSound124 : ∀ c∈certificate124.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch035.certificate430,MergedCutCells.Batch035.certificate431,MergedCutCells.Batch036.certificate432,MergedCutCells.Batch036.certificate433,MergedCutCells.Batch036.certificate434,MergedCutCells.Batch036.certificate435], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound430,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.sound431,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound433,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound434,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound435,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric124 : ∀ c∈certificate124.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch035.certificate430,MergedCutCells.Batch035.certificate431,MergedCutCells.Batch036.certificate432,MergedCutCells.Batch036.certificate433,MergedCutCells.Batch036.certificate434,MergedCutCells.Batch036.certificate435], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid430,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch035.numericValid431,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid433,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid434,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid435,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid124 : ∀ c∈certificate124.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch035.certificate430,MergedCutCells.Batch035.certificate431,MergedCutCells.Batch036.certificate432,MergedCutCells.Batch036.certificate433,MergedCutCells.Batch036.certificate434,MergedCutCells.Batch036.certificate435], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches124 : ∀ c∈certificate124.cells, c.population=certificate124.population := by
  change ∀ c∈[MergedCutCells.Batch035.certificate430,MergedCutCells.Batch035.certificate431,MergedCutCells.Batch036.certificate432,MergedCutCells.Batch036.certificate433,MergedCutCells.Batch036.certificate434,MergedCutCells.Batch036.certificate435], c.population=PopulationCertificates.Batch004.certificate82
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers124 {x : ℝ} (hx : certificate124.interval.Contains x) : ∃ c∈certificate124.cells, c.region.interval.Contains x := rat_cut_group_covers certificate124 numericValid124 hx

def certificate125 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate83,PopulationCertificates.Batch004.certificate83,[MergedCutCells.Batch036.certificate436,MergedCutCells.Batch036.certificate437,MergedCutCells.Batch036.certificate438,MergedCutCells.Batch036.certificate439],(3717979666524110001/1000000000000000000),none,(1/2),(494810524427979169/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid125 : certificate125.NumericValid := by decide +kernel
theorem cellsSound125 : ∀ c∈certificate125.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch036.certificate436,MergedCutCells.Batch036.certificate437,MergedCutCells.Batch036.certificate438,MergedCutCells.Batch036.certificate439], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound436,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound437,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound439,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric125 : ∀ c∈certificate125.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch036.certificate436,MergedCutCells.Batch036.certificate437,MergedCutCells.Batch036.certificate438,MergedCutCells.Batch036.certificate439], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid436,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid437,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid439,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid125 : ∀ c∈certificate125.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch036.certificate436,MergedCutCells.Batch036.certificate437,MergedCutCells.Batch036.certificate438,MergedCutCells.Batch036.certificate439], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches125 : ∀ c∈certificate125.cells, c.population=certificate125.population := by
  change ∀ c∈[MergedCutCells.Batch036.certificate436,MergedCutCells.Batch036.certificate437,MergedCutCells.Batch036.certificate438,MergedCutCells.Batch036.certificate439], c.population=PopulationCertificates.Batch004.certificate83
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers125 {x : ℝ} (hx : certificate125.interval.Contains x) : ∃ c∈certificate125.cells, c.region.interval.Contains x := rat_cut_group_covers certificate125 numericValid125 hx

def certificate126 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate84,PopulationCertificates.Batch004.certificate84,[MergedCutCells.Batch036.certificate440,MergedCutCells.Batch036.certificate441,MergedCutCells.Batch036.certificate442],(385104038312703523/500000000000000000),(some (240174377/250000000)),(1/2),(227082794812610293/1000000000000000000),(some (123334787556331779/250000000000000000)),(some (194962494405438691/1000000000000000000))⟩
theorem numericValid126 : certificate126.NumericValid := by decide +kernel
theorem cellsSound126 : ∀ c∈certificate126.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch036.certificate440,MergedCutCells.Batch036.certificate441,MergedCutCells.Batch036.certificate442], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound440,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound441,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound442,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric126 : ∀ c∈certificate126.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch036.certificate440,MergedCutCells.Batch036.certificate441,MergedCutCells.Batch036.certificate442], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid440,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid441,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid442,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid126 : ∀ c∈certificate126.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch036.certificate440,MergedCutCells.Batch036.certificate441,MergedCutCells.Batch036.certificate442], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid43,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid43,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid43,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches126 : ∀ c∈certificate126.cells, c.population=certificate126.population := by
  change ∀ c∈[MergedCutCells.Batch036.certificate440,MergedCutCells.Batch036.certificate441,MergedCutCells.Batch036.certificate442], c.population=PopulationCertificates.Batch004.certificate84
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers126 {x : ℝ} (hx : certificate126.interval.Contains x) : ∃ c∈certificate126.cells, c.region.interval.Contains x := rat_cut_group_covers certificate126 numericValid126 hx

def certificate127 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate84,PopulationCertificates.Batch004.certificate84,[MergedCutCells.Batch036.certificate443,MergedCutCells.Batch037.certificate444,MergedCutCells.Batch037.certificate445,MergedCutCells.Batch037.certificate446,MergedCutCells.Batch037.certificate447,MergedCutCells.Batch037.certificate448],(240174377/250000000),none,(1/2),(176453143499863109/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid127 : certificate127.NumericValid := by decide +kernel
theorem cellsSound127 : ∀ c∈certificate127.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch036.certificate443,MergedCutCells.Batch037.certificate444,MergedCutCells.Batch037.certificate445,MergedCutCells.Batch037.certificate446,MergedCutCells.Batch037.certificate447,MergedCutCells.Batch037.certificate448], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.sound443,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound444,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound445,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound446,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound447,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound448,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric127 : ∀ c∈certificate127.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch036.certificate443,MergedCutCells.Batch037.certificate444,MergedCutCells.Batch037.certificate445,MergedCutCells.Batch037.certificate446,MergedCutCells.Batch037.certificate447,MergedCutCells.Batch037.certificate448], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch036.numericValid443,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid444,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid445,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid446,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid447,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid448,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid127 : ∀ c∈certificate127.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch036.certificate443,MergedCutCells.Batch037.certificate444,MergedCutCells.Batch037.certificate445,MergedCutCells.Batch037.certificate446,MergedCutCells.Batch037.certificate447,MergedCutCells.Batch037.certificate448], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches127 : ∀ c∈certificate127.cells, c.population=certificate127.population := by
  change ∀ c∈[MergedCutCells.Batch036.certificate443,MergedCutCells.Batch037.certificate444,MergedCutCells.Batch037.certificate445,MergedCutCells.Batch037.certificate446,MergedCutCells.Batch037.certificate447,MergedCutCells.Batch037.certificate448], c.population=PopulationCertificates.Batch004.certificate84
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers127 {x : ℝ} (hx : certificate127.interval.Contains x) : ∃ c∈certificate127.cells, c.region.interval.Contains x := rat_cut_group_covers certificate127 numericValid127 hx

def certificate128 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate85,PopulationCertificates.Batch004.certificate85,[MergedCutCells.Batch037.certificate449,MergedCutCells.Batch037.certificate450,MergedCutCells.Batch037.certificate451],(3736849452142867737/1000000000000000000),none,(1/2),(103149529799450947/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid128 : certificate128.NumericValid := by decide +kernel
theorem cellsSound128 : ∀ c∈certificate128.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch037.certificate449,MergedCutCells.Batch037.certificate450,MergedCutCells.Batch037.certificate451], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound449,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound450,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound451,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric128 : ∀ c∈certificate128.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch037.certificate449,MergedCutCells.Batch037.certificate450,MergedCutCells.Batch037.certificate451], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid449,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid450,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid451,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid128 : ∀ c∈certificate128.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch037.certificate449,MergedCutCells.Batch037.certificate450,MergedCutCells.Batch037.certificate451], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches128 : ∀ c∈certificate128.cells, c.population=certificate128.population := by
  change ∀ c∈[MergedCutCells.Batch037.certificate449,MergedCutCells.Batch037.certificate450,MergedCutCells.Batch037.certificate451], c.population=PopulationCertificates.Batch004.certificate85
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers128 {x : ℝ} (hx : certificate128.interval.Contains x) : ∃ c∈certificate128.cells, c.region.interval.Contains x := rat_cut_group_covers certificate128 numericValid128 hx

def certificate129 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate86,PopulationCertificates.Batch004.certificate86,[MergedCutCells.Batch037.certificate452,MergedCutCells.Batch037.certificate453,MergedCutCells.Batch037.certificate454],(775899431984715143/1000000000000000000),(some (945047109/1000000000)),(1/2),(12221822553294667/50000000000000000),(some (7805427995565387/15625000000000000)),(some (49846020181123377/250000000000000000))⟩
theorem numericValid129 : certificate129.NumericValid := by decide +kernel
theorem cellsSound129 : ∀ c∈certificate129.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch037.certificate452,MergedCutCells.Batch037.certificate453,MergedCutCells.Batch037.certificate454], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound452,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound454,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric129 : ∀ c∈certificate129.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch037.certificate452,MergedCutCells.Batch037.certificate453,MergedCutCells.Batch037.certificate454], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid452,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid454,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid129 : ∀ c∈certificate129.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch037.certificate452,MergedCutCells.Batch037.certificate453,MergedCutCells.Batch037.certificate454], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid44,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid44,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid44,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches129 : ∀ c∈certificate129.cells, c.population=certificate129.population := by
  change ∀ c∈[MergedCutCells.Batch037.certificate452,MergedCutCells.Batch037.certificate453,MergedCutCells.Batch037.certificate454], c.population=PopulationCertificates.Batch004.certificate86
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers129 {x : ℝ} (hx : certificate129.interval.Contains x) : ∃ c∈certificate129.cells, c.region.interval.Contains x := rat_cut_group_covers certificate129 numericValid129 hx

def certificate130 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate86,PopulationCertificates.Batch004.certificate86,[MergedCutCells.Batch037.certificate455,MergedCutCells.Batch038.certificate456,MergedCutCells.Batch038.certificate457,MergedCutCells.Batch038.certificate458,MergedCutCells.Batch038.certificate459,MergedCutCells.Batch038.certificate460,MergedCutCells.Batch038.certificate461],(945047109/1000000000),none,(1/2),(22380854059216619/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid130 : certificate130.NumericValid := by decide +kernel
theorem cellsSound130 : ∀ c∈certificate130.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch037.certificate455,MergedCutCells.Batch038.certificate456,MergedCutCells.Batch038.certificate457,MergedCutCells.Batch038.certificate458,MergedCutCells.Batch038.certificate459,MergedCutCells.Batch038.certificate460,MergedCutCells.Batch038.certificate461], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.sound455,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound456,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound457,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound460,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound461,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric130 : ∀ c∈certificate130.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch037.certificate455,MergedCutCells.Batch038.certificate456,MergedCutCells.Batch038.certificate457,MergedCutCells.Batch038.certificate458,MergedCutCells.Batch038.certificate459,MergedCutCells.Batch038.certificate460,MergedCutCells.Batch038.certificate461], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch037.numericValid455,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid456,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid457,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid460,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid461,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid130 : ∀ c∈certificate130.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch037.certificate455,MergedCutCells.Batch038.certificate456,MergedCutCells.Batch038.certificate457,MergedCutCells.Batch038.certificate458,MergedCutCells.Batch038.certificate459,MergedCutCells.Batch038.certificate460,MergedCutCells.Batch038.certificate461], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches130 : ∀ c∈certificate130.cells, c.population=certificate130.population := by
  change ∀ c∈[MergedCutCells.Batch037.certificate455,MergedCutCells.Batch038.certificate456,MergedCutCells.Batch038.certificate457,MergedCutCells.Batch038.certificate458,MergedCutCells.Batch038.certificate459,MergedCutCells.Batch038.certificate460,MergedCutCells.Batch038.certificate461], c.population=PopulationCertificates.Batch004.certificate86
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers130 {x : ℝ} (hx : certificate130.interval.Contains x) : ∃ c∈certificate130.cells, c.region.interval.Contains x := rat_cut_group_covers certificate130 numericValid130 hx

def certificate131 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate87,PopulationCertificates.Batch004.certificate87,[MergedCutCells.Batch038.certificate462,MergedCutCells.Batch038.certificate463,MergedCutCells.Batch038.certificate464],(75079853489752187/20000000000000000),none,(1/2),(269552147663010813/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid131 : certificate131.NumericValid := by decide +kernel
theorem cellsSound131 : ∀ c∈certificate131.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch038.certificate462,MergedCutCells.Batch038.certificate463,MergedCutCells.Batch038.certificate464], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound462,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound463,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.sound464,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric131 : ∀ c∈certificate131.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch038.certificate462,MergedCutCells.Batch038.certificate463,MergedCutCells.Batch038.certificate464], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid462,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid463,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch038.numericValid464,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid131 : ∀ c∈certificate131.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch038.certificate462,MergedCutCells.Batch038.certificate463,MergedCutCells.Batch038.certificate464], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches131 : ∀ c∈certificate131.cells, c.population=certificate131.population := by
  change ∀ c∈[MergedCutCells.Batch038.certificate462,MergedCutCells.Batch038.certificate463,MergedCutCells.Batch038.certificate464], c.population=PopulationCertificates.Batch004.certificate87
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers131 {x : ℝ} (hx : certificate131.interval.Contains x) : ∃ c∈certificate131.cells, c.region.interval.Contains x := rat_cut_group_covers certificate131 numericValid131 hx

end Cycle12.MergedCutGroups.Batch010
