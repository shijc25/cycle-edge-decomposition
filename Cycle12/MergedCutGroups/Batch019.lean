import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch007
import Cycle12.MergedCutCells.Batch072
import Cycle12.MergedCutCells.Batch073
import Cycle12.MergedCutCells.Batch074
import Cycle12.MergedCutCells.Batch075
import Cycle12.MergedCutCells.Batch076
import Cycle12.PopulationCertificates.Batch007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch019

def certificate228 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate152,PopulationCertificates.Batch007.certificate152,[MergedCutCells.Batch072.certificate874,MergedCutCells.Batch072.certificate875,MergedCutCells.Batch073.certificate876,MergedCutCells.Batch073.certificate877,MergedCutCells.Batch073.certificate878,MergedCutCells.Batch073.certificate879,MergedCutCells.Batch073.certificate880,MergedCutCells.Batch073.certificate881],(843633377401672549/1000000000000000000),(some 64),(1/2),(338021507270246397/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (700997269895750717/500000000000000000))⟩
theorem numericValid228 : certificate228.NumericValid := by decide +kernel
theorem cellsSound228 : ∀ c∈certificate228.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch072.certificate874,MergedCutCells.Batch072.certificate875,MergedCutCells.Batch073.certificate876,MergedCutCells.Batch073.certificate877,MergedCutCells.Batch073.certificate878,MergedCutCells.Batch073.certificate879,MergedCutCells.Batch073.certificate880,MergedCutCells.Batch073.certificate881], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound874,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.sound875,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound876,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound877,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound879,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound880,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound881,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric228 : ∀ c∈certificate228.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch072.certificate874,MergedCutCells.Batch072.certificate875,MergedCutCells.Batch073.certificate876,MergedCutCells.Batch073.certificate877,MergedCutCells.Batch073.certificate878,MergedCutCells.Batch073.certificate879,MergedCutCells.Batch073.certificate880,MergedCutCells.Batch073.certificate881], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid874,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch072.numericValid875,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid876,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid877,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid878,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid879,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid880,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid881,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid228 : ∀ c∈certificate228.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch072.certificate874,MergedCutCells.Batch072.certificate875,MergedCutCells.Batch073.certificate876,MergedCutCells.Batch073.certificate877,MergedCutCells.Batch073.certificate878,MergedCutCells.Batch073.certificate879,MergedCutCells.Batch073.certificate880,MergedCutCells.Batch073.certificate881], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid77,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid77,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid77,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid77,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid77,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid77,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid77,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid77,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches228 : ∀ c∈certificate228.cells, c.population=certificate228.population := by
  change ∀ c∈[MergedCutCells.Batch072.certificate874,MergedCutCells.Batch072.certificate875,MergedCutCells.Batch073.certificate876,MergedCutCells.Batch073.certificate877,MergedCutCells.Batch073.certificate878,MergedCutCells.Batch073.certificate879,MergedCutCells.Batch073.certificate880,MergedCutCells.Batch073.certificate881], c.population=PopulationCertificates.Batch007.certificate152
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers228 {x : ℝ} (hx : certificate228.interval.Contains x) : ∃ c∈certificate228.cells, c.region.interval.Contains x := rat_cut_group_covers certificate228 numericValid228 hx

def certificate229 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate152,PopulationCertificates.Batch007.certificate152,[MergedCutCells.Batch073.certificate882],64,none,(1/2),(102612797900852939/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid229 : certificate229.NumericValid := by decide +kernel
theorem cellsSound229 : ∀ c∈certificate229.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch073.certificate882], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound882,List.forall_mem_nil _⟩
theorem cellsNumeric229 : ∀ c∈certificate229.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch073.certificate882], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid882,List.forall_mem_nil _⟩
theorem cellsEntropyValid229 : ∀ c∈certificate229.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch073.certificate882], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches229 : ∀ c∈certificate229.cells, c.population=certificate229.population := by
  change ∀ c∈[MergedCutCells.Batch073.certificate882], c.population=PopulationCertificates.Batch007.certificate152
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers229 {x : ℝ} (hx : certificate229.interval.Contains x) : ∃ c∈certificate229.cells, c.region.interval.Contains x := rat_cut_group_covers certificate229 numericValid229 hx

def certificate230 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate153,PopulationCertificates.Batch007.certificate153,[MergedCutCells.Batch073.certificate883,MergedCutCells.Batch073.certificate884,MergedCutCells.Batch073.certificate885,MergedCutCells.Batch073.certificate886],(3715948419915760893/1000000000000000000),none,(1/2),(660393700140790983/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid230 : certificate230.NumericValid := by decide +kernel
theorem cellsSound230 : ∀ c∈certificate230.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch073.certificate883,MergedCutCells.Batch073.certificate884,MergedCutCells.Batch073.certificate885,MergedCutCells.Batch073.certificate886], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound883,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound884,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound885,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound886,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric230 : ∀ c∈certificate230.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch073.certificate883,MergedCutCells.Batch073.certificate884,MergedCutCells.Batch073.certificate885,MergedCutCells.Batch073.certificate886], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid883,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid884,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid885,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid886,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid230 : ∀ c∈certificate230.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch073.certificate883,MergedCutCells.Batch073.certificate884,MergedCutCells.Batch073.certificate885,MergedCutCells.Batch073.certificate886], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches230 : ∀ c∈certificate230.cells, c.population=certificate230.population := by
  change ∀ c∈[MergedCutCells.Batch073.certificate883,MergedCutCells.Batch073.certificate884,MergedCutCells.Batch073.certificate885,MergedCutCells.Batch073.certificate886], c.population=PopulationCertificates.Batch007.certificate153
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers230 {x : ℝ} (hx : certificate230.interval.Contains x) : ∃ c∈certificate230.cells, c.region.interval.Contains x := rat_cut_group_covers certificate230 numericValid230 hx

def certificate231 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate154,PopulationCertificates.Batch007.certificate154,[MergedCutCells.Batch073.certificate887,MergedCutCells.Batch074.certificate888,MergedCutCells.Batch074.certificate889,MergedCutCells.Batch074.certificate890,MergedCutCells.Batch074.certificate891,MergedCutCells.Batch074.certificate892,MergedCutCells.Batch074.certificate893],(842927066034692153/1000000000000000000),(some 64),(1/2),(338823442372849087/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (703207085816960767/500000000000000000))⟩
theorem numericValid231 : certificate231.NumericValid := by decide +kernel
theorem cellsSound231 : ∀ c∈certificate231.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch073.certificate887,MergedCutCells.Batch074.certificate888,MergedCutCells.Batch074.certificate889,MergedCutCells.Batch074.certificate890,MergedCutCells.Batch074.certificate891,MergedCutCells.Batch074.certificate892,MergedCutCells.Batch074.certificate893], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.sound887,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound888,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound889,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound890,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound891,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound892,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound893,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric231 : ∀ c∈certificate231.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch073.certificate887,MergedCutCells.Batch074.certificate888,MergedCutCells.Batch074.certificate889,MergedCutCells.Batch074.certificate890,MergedCutCells.Batch074.certificate891,MergedCutCells.Batch074.certificate892,MergedCutCells.Batch074.certificate893], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch073.numericValid887,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid888,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid889,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid890,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid891,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid892,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid893,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid231 : ∀ c∈certificate231.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch073.certificate887,MergedCutCells.Batch074.certificate888,MergedCutCells.Batch074.certificate889,MergedCutCells.Batch074.certificate890,MergedCutCells.Batch074.certificate891,MergedCutCells.Batch074.certificate892,MergedCutCells.Batch074.certificate893], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid78,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid78,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid78,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid78,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid78,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid78,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid78,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches231 : ∀ c∈certificate231.cells, c.population=certificate231.population := by
  change ∀ c∈[MergedCutCells.Batch073.certificate887,MergedCutCells.Batch074.certificate888,MergedCutCells.Batch074.certificate889,MergedCutCells.Batch074.certificate890,MergedCutCells.Batch074.certificate891,MergedCutCells.Batch074.certificate892,MergedCutCells.Batch074.certificate893], c.population=PopulationCertificates.Batch007.certificate154
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers231 {x : ℝ} (hx : certificate231.interval.Contains x) : ∃ c∈certificate231.cells, c.region.interval.Contains x := rat_cut_group_covers certificate231 numericValid231 hx

def certificate232 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate154,PopulationCertificates.Batch007.certificate154,[MergedCutCells.Batch074.certificate894],64,none,(1/2),(414661006637210891/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid232 : certificate232.NumericValid := by decide +kernel
theorem cellsSound232 : ∀ c∈certificate232.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch074.certificate894], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound894,List.forall_mem_nil _⟩
theorem cellsNumeric232 : ∀ c∈certificate232.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch074.certificate894], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid894,List.forall_mem_nil _⟩
theorem cellsEntropyValid232 : ∀ c∈certificate232.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch074.certificate894], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches232 : ∀ c∈certificate232.cells, c.population=certificate232.population := by
  change ∀ c∈[MergedCutCells.Batch074.certificate894], c.population=PopulationCertificates.Batch007.certificate154
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers232 {x : ℝ} (hx : certificate232.interval.Contains x) : ∃ c∈certificate232.cells, c.region.interval.Contains x := rat_cut_group_covers certificate232 numericValid232 hx

def certificate233 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate155,PopulationCertificates.Batch007.certificate155,[MergedCutCells.Batch074.certificate895,MergedCutCells.Batch074.certificate896,MergedCutCells.Batch074.certificate897],(1861313903489883271/500000000000000000),none,(1/2),(337162282772592209/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid233 : certificate233.NumericValid := by decide +kernel
theorem cellsSound233 : ∀ c∈certificate233.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch074.certificate895,MergedCutCells.Batch074.certificate896,MergedCutCells.Batch074.certificate897], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound895,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound896,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound897,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric233 : ∀ c∈certificate233.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch074.certificate895,MergedCutCells.Batch074.certificate896,MergedCutCells.Batch074.certificate897], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid895,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid896,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid897,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid233 : ∀ c∈certificate233.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch074.certificate895,MergedCutCells.Batch074.certificate896,MergedCutCells.Batch074.certificate897], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches233 : ∀ c∈certificate233.cells, c.population=certificate233.population := by
  change ∀ c∈[MergedCutCells.Batch074.certificate895,MergedCutCells.Batch074.certificate896,MergedCutCells.Batch074.certificate897], c.population=PopulationCertificates.Batch007.certificate155
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers233 {x : ℝ} (hx : certificate233.interval.Contains x) : ∃ c∈certificate233.cells, c.region.interval.Contains x := rat_cut_group_covers certificate233 numericValid233 hx

def certificate234 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate156,PopulationCertificates.Batch007.certificate156,[MergedCutCells.Batch074.certificate898,MergedCutCells.Batch074.certificate899,MergedCutCells.Batch075.certificate900,MergedCutCells.Batch075.certificate901,MergedCutCells.Batch075.certificate902,MergedCutCells.Batch075.certificate903,MergedCutCells.Batch075.certificate904,MergedCutCells.Batch075.certificate905],(105409979924011561/125000000000000000),(some 64),(1/2),(349660311901885147/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1405337917440630993/1000000000000000000))⟩
theorem numericValid234 : certificate234.NumericValid := by decide +kernel
theorem cellsSound234 : ∀ c∈certificate234.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch074.certificate898,MergedCutCells.Batch074.certificate899,MergedCutCells.Batch075.certificate900,MergedCutCells.Batch075.certificate901,MergedCutCells.Batch075.certificate902,MergedCutCells.Batch075.certificate903,MergedCutCells.Batch075.certificate904,MergedCutCells.Batch075.certificate905], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound898,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.sound899,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound901,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound902,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound903,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound904,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound905,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric234 : ∀ c∈certificate234.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch074.certificate898,MergedCutCells.Batch074.certificate899,MergedCutCells.Batch075.certificate900,MergedCutCells.Batch075.certificate901,MergedCutCells.Batch075.certificate902,MergedCutCells.Batch075.certificate903,MergedCutCells.Batch075.certificate904,MergedCutCells.Batch075.certificate905], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid898,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch074.numericValid899,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid900,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid901,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid902,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid903,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid904,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid905,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid234 : ∀ c∈certificate234.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch074.certificate898,MergedCutCells.Batch074.certificate899,MergedCutCells.Batch075.certificate900,MergedCutCells.Batch075.certificate901,MergedCutCells.Batch075.certificate902,MergedCutCells.Batch075.certificate903,MergedCutCells.Batch075.certificate904,MergedCutCells.Batch075.certificate905], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid79,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid79,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid79,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid79,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid79,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid79,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid79,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid79,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches234 : ∀ c∈certificate234.cells, c.population=certificate234.population := by
  change ∀ c∈[MergedCutCells.Batch074.certificate898,MergedCutCells.Batch074.certificate899,MergedCutCells.Batch075.certificate900,MergedCutCells.Batch075.certificate901,MergedCutCells.Batch075.certificate902,MergedCutCells.Batch075.certificate903,MergedCutCells.Batch075.certificate904,MergedCutCells.Batch075.certificate905], c.population=PopulationCertificates.Batch007.certificate156
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers234 {x : ℝ} (hx : certificate234.interval.Contains x) : ∃ c∈certificate234.cells, c.region.interval.Contains x := rat_cut_group_covers certificate234 numericValid234 hx

def certificate235 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate156,PopulationCertificates.Batch007.certificate156,[MergedCutCells.Batch075.certificate906],64,none,(1/2),(852343370464087699/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid235 : certificate235.NumericValid := by decide +kernel
theorem cellsSound235 : ∀ c∈certificate235.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch075.certificate906], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound906,List.forall_mem_nil _⟩
theorem cellsNumeric235 : ∀ c∈certificate235.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch075.certificate906], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid906,List.forall_mem_nil _⟩
theorem cellsEntropyValid235 : ∀ c∈certificate235.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch075.certificate906], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches235 : ∀ c∈certificate235.cells, c.population=certificate235.population := by
  change ∀ c∈[MergedCutCells.Batch075.certificate906], c.population=PopulationCertificates.Batch007.certificate156
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers235 {x : ℝ} (hx : certificate235.interval.Contains x) : ∃ c∈certificate235.cells, c.region.interval.Contains x := rat_cut_group_covers certificate235 numericValid235 hx

def certificate236 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate157,PopulationCertificates.Batch007.certificate157,[MergedCutCells.Batch075.certificate907,MergedCutCells.Batch075.certificate908,MergedCutCells.Batch075.certificate909,MergedCutCells.Batch075.certificate910],(93234216871258459/25000000000000000),none,(1/2),(689967858652950827/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid236 : certificate236.NumericValid := by decide +kernel
theorem cellsSound236 : ∀ c∈certificate236.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch075.certificate907,MergedCutCells.Batch075.certificate908,MergedCutCells.Batch075.certificate909,MergedCutCells.Batch075.certificate910], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound908,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound909,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound910,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric236 : ∀ c∈certificate236.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch075.certificate907,MergedCutCells.Batch075.certificate908,MergedCutCells.Batch075.certificate909,MergedCutCells.Batch075.certificate910], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid908,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid909,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid910,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid236 : ∀ c∈certificate236.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch075.certificate907,MergedCutCells.Batch075.certificate908,MergedCutCells.Batch075.certificate909,MergedCutCells.Batch075.certificate910], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches236 : ∀ c∈certificate236.cells, c.population=certificate236.population := by
  change ∀ c∈[MergedCutCells.Batch075.certificate907,MergedCutCells.Batch075.certificate908,MergedCutCells.Batch075.certificate909,MergedCutCells.Batch075.certificate910], c.population=PopulationCertificates.Batch007.certificate157
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers236 {x : ℝ} (hx : certificate236.interval.Contains x) : ∃ c∈certificate236.cells, c.region.interval.Contains x := rat_cut_group_covers certificate236 numericValid236 hx

def certificate237 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate158,PopulationCertificates.Batch007.certificate158,[MergedCutCells.Batch075.certificate911,MergedCutCells.Batch076.certificate912,MergedCutCells.Batch076.certificate913,MergedCutCells.Batch076.certificate914,MergedCutCells.Batch076.certificate915,MergedCutCells.Batch076.certificate916,MergedCutCells.Batch076.certificate917],(416542967928879499/500000000000000000),(some 64),(1/2),(55456584718098761/200000000000000000),(some (69314718055994531/100000000000000000)),(some (1409508760660353869/1000000000000000000))⟩
theorem numericValid237 : certificate237.NumericValid := by decide +kernel
theorem cellsSound237 : ∀ c∈certificate237.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch075.certificate911,MergedCutCells.Batch076.certificate912,MergedCutCells.Batch076.certificate913,MergedCutCells.Batch076.certificate914,MergedCutCells.Batch076.certificate915,MergedCutCells.Batch076.certificate916,MergedCutCells.Batch076.certificate917], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.sound911,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound913,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound915,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound916,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound917,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric237 : ∀ c∈certificate237.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch075.certificate911,MergedCutCells.Batch076.certificate912,MergedCutCells.Batch076.certificate913,MergedCutCells.Batch076.certificate914,MergedCutCells.Batch076.certificate915,MergedCutCells.Batch076.certificate916,MergedCutCells.Batch076.certificate917], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch075.numericValid911,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid913,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid915,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid916,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid917,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid237 : ∀ c∈certificate237.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch075.certificate911,MergedCutCells.Batch076.certificate912,MergedCutCells.Batch076.certificate913,MergedCutCells.Batch076.certificate914,MergedCutCells.Batch076.certificate915,MergedCutCells.Batch076.certificate916,MergedCutCells.Batch076.certificate917], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid80,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid80,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid80,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid80,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid80,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid80,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid80,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches237 : ∀ c∈certificate237.cells, c.population=certificate237.population := by
  change ∀ c∈[MergedCutCells.Batch075.certificate911,MergedCutCells.Batch076.certificate912,MergedCutCells.Batch076.certificate913,MergedCutCells.Batch076.certificate914,MergedCutCells.Batch076.certificate915,MergedCutCells.Batch076.certificate916,MergedCutCells.Batch076.certificate917], c.population=PopulationCertificates.Batch007.certificate158
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers237 {x : ℝ} (hx : certificate237.interval.Contains x) : ∃ c∈certificate237.cells, c.region.interval.Contains x := rat_cut_group_covers certificate237 numericValid237 hx

def certificate238 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate158,PopulationCertificates.Batch007.certificate158,[MergedCutCells.Batch076.certificate918],64,none,(1/2),(387558213178846957/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid238 : certificate238.NumericValid := by decide +kernel
theorem cellsSound238 : ∀ c∈certificate238.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch076.certificate918], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound918,List.forall_mem_nil _⟩
theorem cellsNumeric238 : ∀ c∈certificate238.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch076.certificate918], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid918,List.forall_mem_nil _⟩
theorem cellsEntropyValid238 : ∀ c∈certificate238.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch076.certificate918], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches238 : ∀ c∈certificate238.cells, c.population=certificate238.population := by
  change ∀ c∈[MergedCutCells.Batch076.certificate918], c.population=PopulationCertificates.Batch007.certificate158
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers238 {x : ℝ} (hx : certificate238.interval.Contains x) : ∃ c∈certificate238.cells, c.region.interval.Contains x := rat_cut_group_covers certificate238 numericValid238 hx

def certificate239 : RatCutGroup := ⟨GeometryCertificates.Batch007.certificate159,PopulationCertificates.Batch007.certificate159,[MergedCutCells.Batch076.certificate919,MergedCutCells.Batch076.certificate920,MergedCutCells.Batch076.certificate921,MergedCutCells.Batch076.certificate922],(1899957685178174593/500000000000000000),none,(1/2),(174398529075800119/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid239 : certificate239.NumericValid := by decide +kernel
theorem cellsSound239 : ∀ c∈certificate239.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch076.certificate919,MergedCutCells.Batch076.certificate920,MergedCutCells.Batch076.certificate921,MergedCutCells.Batch076.certificate922], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound919,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound920,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound921,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound922,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric239 : ∀ c∈certificate239.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch076.certificate919,MergedCutCells.Batch076.certificate920,MergedCutCells.Batch076.certificate921,MergedCutCells.Batch076.certificate922], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid919,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid920,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid921,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid922,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid239 : ∀ c∈certificate239.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch076.certificate919,MergedCutCells.Batch076.certificate920,MergedCutCells.Batch076.certificate921,MergedCutCells.Batch076.certificate922], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches239 : ∀ c∈certificate239.cells, c.population=certificate239.population := by
  change ∀ c∈[MergedCutCells.Batch076.certificate919,MergedCutCells.Batch076.certificate920,MergedCutCells.Batch076.certificate921,MergedCutCells.Batch076.certificate922], c.population=PopulationCertificates.Batch007.certificate159
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers239 {x : ℝ} (hx : certificate239.interval.Contains x) : ∃ c∈certificate239.cells, c.region.interval.Contains x := rat_cut_group_covers certificate239 numericValid239 hx

end Cycle12.MergedCutGroups.Batch019
