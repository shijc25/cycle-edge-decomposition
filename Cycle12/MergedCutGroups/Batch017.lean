import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch006
import Cycle12.GeometryCertificates.Batch007
import Cycle12.MergedCutCells.Batch064
import Cycle12.MergedCutCells.Batch065
import Cycle12.MergedCutCells.Batch066
import Cycle12.MergedCutCells.Batch067
import Cycle12.MergedCutCells.Batch068
import Cycle12.PopulationCertificates.Batch006
import Cycle12.PopulationCertificates.Batch007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch017

def certificate204 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate136,PopulationCertificates.Batch006.certificate136,[MergedCutCells.Batch064.certificate774,MergedCutCells.Batch064.certificate775],(414714928481505079/500000000000000000),(some (871176641/1000000000)),(1/2),(406842582953840369/1000000000000000000),(some (608108598600115739/1000000000000000000)),(some (296776908670212357/1000000000000000000))⟩
theorem numericValid204 : certificate204.NumericValid := by decide +kernel
theorem cellsSound204 : ∀ c∈certificate204.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch064.certificate774,MergedCutCells.Batch064.certificate775], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound774,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound775,List.forall_mem_nil _⟩⟩
theorem cellsNumeric204 : ∀ c∈certificate204.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch064.certificate774,MergedCutCells.Batch064.certificate775], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid774,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid775,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid204 : ∀ c∈certificate204.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch064.certificate774,MergedCutCells.Batch064.certificate775], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid69,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid69,List.forall_mem_nil _⟩⟩
theorem populationMatches204 : ∀ c∈certificate204.cells, c.population=certificate204.population := by
  change ∀ c∈[MergedCutCells.Batch064.certificate774,MergedCutCells.Batch064.certificate775], c.population=PopulationCertificates.Batch006.certificate136
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers204 {x : ℝ} (hx : certificate204.interval.Contains x) : ∃ c∈certificate204.cells, c.region.interval.Contains x := rat_cut_group_covers certificate204 numericValid204 hx

def certificate205 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate136,PopulationCertificates.Batch006.certificate136,[MergedCutCells.Batch064.certificate776,MergedCutCells.Batch064.certificate777,MergedCutCells.Batch064.certificate778,MergedCutCells.Batch064.certificate779,MergedCutCells.Batch065.certificate780,MergedCutCells.Batch065.certificate781,MergedCutCells.Batch065.certificate782],(871176641/1000000000),none,(1/2),(298411464835451303/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid205 : certificate205.NumericValid := by decide +kernel
theorem cellsSound205 : ∀ c∈certificate205.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch064.certificate776,MergedCutCells.Batch064.certificate777,MergedCutCells.Batch064.certificate778,MergedCutCells.Batch064.certificate779,MergedCutCells.Batch065.certificate780,MergedCutCells.Batch065.certificate781,MergedCutCells.Batch065.certificate782], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound776,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound777,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound778,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.sound779,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound780,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound781,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound782,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric205 : ∀ c∈certificate205.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch064.certificate776,MergedCutCells.Batch064.certificate777,MergedCutCells.Batch064.certificate778,MergedCutCells.Batch064.certificate779,MergedCutCells.Batch065.certificate780,MergedCutCells.Batch065.certificate781,MergedCutCells.Batch065.certificate782], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid776,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid777,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid778,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch064.numericValid779,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid780,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid781,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid782,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid205 : ∀ c∈certificate205.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch064.certificate776,MergedCutCells.Batch064.certificate777,MergedCutCells.Batch064.certificate778,MergedCutCells.Batch064.certificate779,MergedCutCells.Batch065.certificate780,MergedCutCells.Batch065.certificate781,MergedCutCells.Batch065.certificate782], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches205 : ∀ c∈certificate205.cells, c.population=certificate205.population := by
  change ∀ c∈[MergedCutCells.Batch064.certificate776,MergedCutCells.Batch064.certificate777,MergedCutCells.Batch064.certificate778,MergedCutCells.Batch064.certificate779,MergedCutCells.Batch065.certificate780,MergedCutCells.Batch065.certificate781,MergedCutCells.Batch065.certificate782], c.population=PopulationCertificates.Batch006.certificate136
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers205 {x : ℝ} (hx : certificate205.interval.Contains x) : ∃ c∈certificate205.cells, c.region.interval.Contains x := rat_cut_group_covers certificate205 numericValid205 hx

def certificate206 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate137,PopulationCertificates.Batch006.certificate137,[MergedCutCells.Batch065.certificate783,MergedCutCells.Batch065.certificate784,MergedCutCells.Batch065.certificate785,MergedCutCells.Batch065.certificate786],(3754698975349443237/1000000000000000000),none,(1/2),(1056840894293179/1600000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid206 : certificate206.NumericValid := by decide +kernel
theorem cellsSound206 : ∀ c∈certificate206.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch065.certificate783,MergedCutCells.Batch065.certificate784,MergedCutCells.Batch065.certificate785,MergedCutCells.Batch065.certificate786], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound783,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound784,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound785,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound786,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric206 : ∀ c∈certificate206.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch065.certificate783,MergedCutCells.Batch065.certificate784,MergedCutCells.Batch065.certificate785,MergedCutCells.Batch065.certificate786], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid783,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid784,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid785,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid786,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid206 : ∀ c∈certificate206.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch065.certificate783,MergedCutCells.Batch065.certificate784,MergedCutCells.Batch065.certificate785,MergedCutCells.Batch065.certificate786], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches206 : ∀ c∈certificate206.cells, c.population=certificate206.population := by
  change ∀ c∈[MergedCutCells.Batch065.certificate783,MergedCutCells.Batch065.certificate784,MergedCutCells.Batch065.certificate785,MergedCutCells.Batch065.certificate786], c.population=PopulationCertificates.Batch006.certificate137
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers206 {x : ℝ} (hx : certificate206.interval.Contains x) : ∃ c∈certificate206.cells, c.region.interval.Contains x := rat_cut_group_covers certificate206 numericValid206 hx

def certificate207 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate138,PopulationCertificates.Batch006.certificate138,[MergedCutCells.Batch065.certificate787,MergedCutCells.Batch065.certificate788],(20831574280827227/25000000000000000),(some (875401041/1000000000)),(1/2),(423019971511864651/1000000000000000000),(some (38185458900325133/62500000000000000)),(some (150060826061701783/500000000000000000))⟩
theorem numericValid207 : certificate207.NumericValid := by decide +kernel
theorem cellsSound207 : ∀ c∈certificate207.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch065.certificate787,MergedCutCells.Batch065.certificate788], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound787,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound788,List.forall_mem_nil _⟩⟩
theorem cellsNumeric207 : ∀ c∈certificate207.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch065.certificate787,MergedCutCells.Batch065.certificate788], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid787,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid788,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid207 : ∀ c∈certificate207.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch065.certificate787,MergedCutCells.Batch065.certificate788], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid70,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid70,List.forall_mem_nil _⟩⟩
theorem populationMatches207 : ∀ c∈certificate207.cells, c.population=certificate207.population := by
  change ∀ c∈[MergedCutCells.Batch065.certificate787,MergedCutCells.Batch065.certificate788], c.population=PopulationCertificates.Batch006.certificate138
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers207 {x : ℝ} (hx : certificate207.interval.Contains x) : ∃ c∈certificate207.cells, c.region.interval.Contains x := rat_cut_group_covers certificate207 numericValid207 hx

def certificate208 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate138,PopulationCertificates.Batch006.certificate138,[MergedCutCells.Batch065.certificate789,MergedCutCells.Batch065.certificate790,MergedCutCells.Batch065.certificate791,MergedCutCells.Batch066.certificate792,MergedCutCells.Batch066.certificate793,MergedCutCells.Batch066.certificate794],(875401041/1000000000),none,(1/2),(301666516875756653/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid208 : certificate208.NumericValid := by decide +kernel
theorem cellsSound208 : ∀ c∈certificate208.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch065.certificate789,MergedCutCells.Batch065.certificate790,MergedCutCells.Batch065.certificate791,MergedCutCells.Batch066.certificate792,MergedCutCells.Batch066.certificate793,MergedCutCells.Batch066.certificate794], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound789,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound790,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.sound791,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound792,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound793,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound794,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric208 : ∀ c∈certificate208.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch065.certificate789,MergedCutCells.Batch065.certificate790,MergedCutCells.Batch065.certificate791,MergedCutCells.Batch066.certificate792,MergedCutCells.Batch066.certificate793,MergedCutCells.Batch066.certificate794], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid789,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid790,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch065.numericValid791,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid792,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid793,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid794,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid208 : ∀ c∈certificate208.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch065.certificate789,MergedCutCells.Batch065.certificate790,MergedCutCells.Batch065.certificate791,MergedCutCells.Batch066.certificate792,MergedCutCells.Batch066.certificate793,MergedCutCells.Batch066.certificate794], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches208 : ∀ c∈certificate208.cells, c.population=certificate208.population := by
  change ∀ c∈[MergedCutCells.Batch065.certificate789,MergedCutCells.Batch065.certificate790,MergedCutCells.Batch065.certificate791,MergedCutCells.Batch066.certificate792,MergedCutCells.Batch066.certificate793,MergedCutCells.Batch066.certificate794], c.population=PopulationCertificates.Batch006.certificate138
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers208 {x : ℝ} (hx : certificate208.interval.Contains x) : ∃ c∈certificate208.cells, c.region.interval.Contains x := rat_cut_group_covers certificate208 numericValid208 hx

def certificate209 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate139,PopulationCertificates.Batch006.certificate139,[MergedCutCells.Batch066.certificate795,MergedCutCells.Batch066.certificate796,MergedCutCells.Batch066.certificate797,MergedCutCells.Batch066.certificate798],(752214166047347937/200000000000000000),none,(1/2),(338137298008397757/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid209 : certificate209.NumericValid := by decide +kernel
theorem cellsSound209 : ∀ c∈certificate209.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch066.certificate795,MergedCutCells.Batch066.certificate796,MergedCutCells.Batch066.certificate797,MergedCutCells.Batch066.certificate798], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound795,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound796,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound797,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound798,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric209 : ∀ c∈certificate209.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch066.certificate795,MergedCutCells.Batch066.certificate796,MergedCutCells.Batch066.certificate797,MergedCutCells.Batch066.certificate798], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid795,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid796,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid797,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid798,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid209 : ∀ c∈certificate209.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch066.certificate795,MergedCutCells.Batch066.certificate796,MergedCutCells.Batch066.certificate797,MergedCutCells.Batch066.certificate798], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches209 : ∀ c∈certificate209.cells, c.population=certificate209.population := by
  change ∀ c∈[MergedCutCells.Batch066.certificate795,MergedCutCells.Batch066.certificate796,MergedCutCells.Batch066.certificate797,MergedCutCells.Batch066.certificate798], c.population=PopulationCertificates.Batch006.certificate139
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers209 {x : ℝ} (hx : certificate209.interval.Contains x) : ∃ c∈certificate209.cells, c.region.interval.Contains x := rat_cut_group_covers certificate209 numericValid209 hx

def certificate210 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate140,PopulationCertificates.Batch007.certificate140,[MergedCutCells.Batch066.certificate799,MergedCutCells.Batch066.certificate800],(414714929030923073/500000000000000000),(some (871176641/1000000000)),(1/2),(406146240864758109/1000000000000000000),(some (306930945803901863/500000000000000000)),(some (303573628541551123/1000000000000000000))⟩
theorem numericValid210 : certificate210.NumericValid := by decide +kernel
theorem cellsSound210 : ∀ c∈certificate210.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch066.certificate799,MergedCutCells.Batch066.certificate800], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound799,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound800,List.forall_mem_nil _⟩⟩
theorem cellsNumeric210 : ∀ c∈certificate210.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch066.certificate799,MergedCutCells.Batch066.certificate800], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid799,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid800,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid210 : ∀ c∈certificate210.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch066.certificate799,MergedCutCells.Batch066.certificate800], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid71,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid71,List.forall_mem_nil _⟩⟩
theorem populationMatches210 : ∀ c∈certificate210.cells, c.population=certificate210.population := by
  change ∀ c∈[MergedCutCells.Batch066.certificate799,MergedCutCells.Batch066.certificate800], c.population=PopulationCertificates.Batch007.certificate140
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers210 {x : ℝ} (hx : certificate210.interval.Contains x) : ∃ c∈certificate210.cells, c.region.interval.Contains x := rat_cut_group_covers certificate210 numericValid210 hx

def certificate211 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate140,PopulationCertificates.Batch007.certificate140,[MergedCutCells.Batch066.certificate801,MergedCutCells.Batch066.certificate802,MergedCutCells.Batch066.certificate803,MergedCutCells.Batch067.certificate804,MergedCutCells.Batch067.certificate805,MergedCutCells.Batch067.certificate806],(871176641/1000000000),none,(1/2),(30582595380838893/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid211 : certificate211.NumericValid := by decide +kernel
theorem cellsSound211 : ∀ c∈certificate211.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch066.certificate801,MergedCutCells.Batch066.certificate802,MergedCutCells.Batch066.certificate803,MergedCutCells.Batch067.certificate804,MergedCutCells.Batch067.certificate805,MergedCutCells.Batch067.certificate806], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound802,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.sound803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound804,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound806,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric211 : ∀ c∈certificate211.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch066.certificate801,MergedCutCells.Batch066.certificate802,MergedCutCells.Batch066.certificate803,MergedCutCells.Batch067.certificate804,MergedCutCells.Batch067.certificate805,MergedCutCells.Batch067.certificate806], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid802,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch066.numericValid803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid804,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid806,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid211 : ∀ c∈certificate211.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch066.certificate801,MergedCutCells.Batch066.certificate802,MergedCutCells.Batch066.certificate803,MergedCutCells.Batch067.certificate804,MergedCutCells.Batch067.certificate805,MergedCutCells.Batch067.certificate806], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches211 : ∀ c∈certificate211.cells, c.population=certificate211.population := by
  change ∀ c∈[MergedCutCells.Batch066.certificate801,MergedCutCells.Batch066.certificate802,MergedCutCells.Batch066.certificate803,MergedCutCells.Batch067.certificate804,MergedCutCells.Batch067.certificate805,MergedCutCells.Batch067.certificate806], c.population=PopulationCertificates.Batch007.certificate140
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers211 {x : ℝ} (hx : certificate211.interval.Contains x) : ∃ c∈certificate211.cells, c.region.interval.Contains x := rat_cut_group_covers certificate211 numericValid211 hx

def certificate212 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate141,PopulationCertificates.Batch007.certificate141,[MergedCutCells.Batch067.certificate807,MergedCutCells.Batch067.certificate808,MergedCutCells.Batch067.certificate809],(3769609743751020941/1000000000000000000),none,(1/2),(17227546802239083/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid212 : certificate212.NumericValid := by decide +kernel
theorem cellsSound212 : ∀ c∈certificate212.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch067.certificate807,MergedCutCells.Batch067.certificate808,MergedCutCells.Batch067.certificate809], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound808,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound809,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric212 : ∀ c∈certificate212.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch067.certificate807,MergedCutCells.Batch067.certificate808,MergedCutCells.Batch067.certificate809], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid808,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid809,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid212 : ∀ c∈certificate212.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch067.certificate807,MergedCutCells.Batch067.certificate808,MergedCutCells.Batch067.certificate809], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches212 : ∀ c∈certificate212.cells, c.population=certificate212.population := by
  change ∀ c∈[MergedCutCells.Batch067.certificate807,MergedCutCells.Batch067.certificate808,MergedCutCells.Batch067.certificate809], c.population=PopulationCertificates.Batch007.certificate141
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers212 {x : ℝ} (hx : certificate212.interval.Contains x) : ∃ c∈certificate212.cells, c.region.interval.Contains x := rat_cut_group_covers certificate212 numericValid212 hx

def certificate213 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate142,PopulationCertificates.Batch007.certificate142,[MergedCutCells.Batch067.certificate810,MergedCutCells.Batch067.certificate811],(208789721672771931/250000000000000000),(some (42800219/50000000)),(1/2),(436086559378561131/1000000000000000000),(some (153638995341725297/250000000000000000)),(some (304411539656241961/1000000000000000000))⟩
theorem numericValid213 : certificate213.NumericValid := by decide +kernel
theorem cellsSound213 : ∀ c∈certificate213.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch067.certificate810,MergedCutCells.Batch067.certificate811], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound810,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound811,List.forall_mem_nil _⟩⟩
theorem cellsNumeric213 : ∀ c∈certificate213.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch067.certificate810,MergedCutCells.Batch067.certificate811], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid810,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid811,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid213 : ∀ c∈certificate213.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch067.certificate810,MergedCutCells.Batch067.certificate811], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid72,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid72,List.forall_mem_nil _⟩⟩
theorem populationMatches213 : ∀ c∈certificate213.cells, c.population=certificate213.population := by
  change ∀ c∈[MergedCutCells.Batch067.certificate810,MergedCutCells.Batch067.certificate811], c.population=PopulationCertificates.Batch007.certificate142
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers213 {x : ℝ} (hx : certificate213.interval.Contains x) : ∃ c∈certificate213.cells, c.region.interval.Contains x := rat_cut_group_covers certificate213 numericValid213 hx

def certificate214 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate142,PopulationCertificates.Batch007.certificate142,[MergedCutCells.Batch067.certificate812,MergedCutCells.Batch067.certificate813,MergedCutCells.Batch067.certificate814,MergedCutCells.Batch067.certificate815,MergedCutCells.Batch068.certificate816,MergedCutCells.Batch068.certificate817,MergedCutCells.Batch068.certificate818],(42800219/50000000),none,(1/2),(61933633024338647/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid214 : certificate214.NumericValid := by decide +kernel
theorem cellsSound214 : ∀ c∈certificate214.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch067.certificate812,MergedCutCells.Batch067.certificate813,MergedCutCells.Batch067.certificate814,MergedCutCells.Batch067.certificate815,MergedCutCells.Batch068.certificate816,MergedCutCells.Batch068.certificate817,MergedCutCells.Batch068.certificate818], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound812,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound813,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound814,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.sound815,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound817,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound818,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric214 : ∀ c∈certificate214.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch067.certificate812,MergedCutCells.Batch067.certificate813,MergedCutCells.Batch067.certificate814,MergedCutCells.Batch067.certificate815,MergedCutCells.Batch068.certificate816,MergedCutCells.Batch068.certificate817,MergedCutCells.Batch068.certificate818], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid812,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid813,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid814,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch067.numericValid815,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid816,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid817,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid818,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid214 : ∀ c∈certificate214.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch067.certificate812,MergedCutCells.Batch067.certificate813,MergedCutCells.Batch067.certificate814,MergedCutCells.Batch067.certificate815,MergedCutCells.Batch068.certificate816,MergedCutCells.Batch068.certificate817,MergedCutCells.Batch068.certificate818], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches214 : ∀ c∈certificate214.cells, c.population=certificate214.population := by
  change ∀ c∈[MergedCutCells.Batch067.certificate812,MergedCutCells.Batch067.certificate813,MergedCutCells.Batch067.certificate814,MergedCutCells.Batch067.certificate815,MergedCutCells.Batch068.certificate816,MergedCutCells.Batch068.certificate817,MergedCutCells.Batch068.certificate818], c.population=PopulationCertificates.Batch007.certificate142
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers214 {x : ℝ} (hx : certificate214.interval.Contains x) : ∃ c∈certificate214.cells, c.region.interval.Contains x := rat_cut_group_covers certificate214 numericValid214 hx

def certificate215 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate143,PopulationCertificates.Batch007.certificate143,[MergedCutCells.Batch068.certificate819,MergedCutCells.Batch068.certificate820,MergedCutCells.Batch068.certificate821,MergedCutCells.Batch068.certificate822],(3776107616033287301/1000000000000000000),none,(1/2),(705658559784700789/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid215 : certificate215.NumericValid := by decide +kernel
theorem cellsSound215 : ∀ c∈certificate215.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch068.certificate819,MergedCutCells.Batch068.certificate820,MergedCutCells.Batch068.certificate821,MergedCutCells.Batch068.certificate822], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound819,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound820,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound821,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.sound822,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric215 : ∀ c∈certificate215.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch068.certificate819,MergedCutCells.Batch068.certificate820,MergedCutCells.Batch068.certificate821,MergedCutCells.Batch068.certificate822], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid819,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid820,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid821,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch068.numericValid822,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid215 : ∀ c∈certificate215.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch068.certificate819,MergedCutCells.Batch068.certificate820,MergedCutCells.Batch068.certificate821,MergedCutCells.Batch068.certificate822], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches215 : ∀ c∈certificate215.cells, c.population=certificate215.population := by
  change ∀ c∈[MergedCutCells.Batch068.certificate819,MergedCutCells.Batch068.certificate820,MergedCutCells.Batch068.certificate821,MergedCutCells.Batch068.certificate822], c.population=PopulationCertificates.Batch007.certificate143
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers215 {x : ℝ} (hx : certificate215.interval.Contains x) : ∃ c∈certificate215.cells, c.region.interval.Contains x := rat_cut_group_covers certificate215 numericValid215 hx

end Cycle12.MergedCutGroups.Batch017
