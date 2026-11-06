import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch018
import Cycle12.MergedCutCells.Batch171
import Cycle12.MergedCutCells.Batch172
import Cycle12.MergedCutCells.Batch173
import Cycle12.MergedCutCells.Batch174
import Cycle12.PopulationCertificates.Batch018

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch046

def certificate552 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate368,PopulationCertificates.Batch018.certificate368,[MergedCutCells.Batch171.certificate2063,MergedCutCells.Batch172.certificate2064],(315231883792698741/500000000000000000),(some (23888427/20000000)),(1/2),(287862305635576581/1000000000000000000),(some (144474605247705149/1000000000000000000)),(some (513101226700353/15625000000000000))⟩
theorem numericValid552 : certificate552.NumericValid := by decide +kernel
theorem cellsSound552 : ∀ c∈certificate552.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2063,MergedCutCells.Batch172.certificate2064], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2063,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2064,List.forall_mem_nil _⟩⟩
theorem cellsNumeric552 : ∀ c∈certificate552.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2063,MergedCutCells.Batch172.certificate2064], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2063,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2064,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid552 : ∀ c∈certificate552.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2063,MergedCutCells.Batch172.certificate2064], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid185,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid185,List.forall_mem_nil _⟩⟩
theorem populationMatches552 : ∀ c∈certificate552.cells, c.population=certificate552.population := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2063,MergedCutCells.Batch172.certificate2064], c.population=PopulationCertificates.Batch018.certificate368
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers552 {x : ℝ} (hx : certificate552.interval.Contains x) : ∃ c∈certificate552.cells, c.region.interval.Contains x := rat_cut_group_covers certificate552 numericValid552 hx

def certificate553 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate368,PopulationCertificates.Batch018.certificate368,[MergedCutCells.Batch172.certificate2065,MergedCutCells.Batch172.certificate2066,MergedCutCells.Batch172.certificate2067,MergedCutCells.Batch172.certificate2068,MergedCutCells.Batch172.certificate2069],(23888427/20000000),none,(1/2),(275263905391669503/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid553 : certificate553.NumericValid := by decide +kernel
theorem cellsSound553 : ∀ c∈certificate553.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2065,MergedCutCells.Batch172.certificate2066,MergedCutCells.Batch172.certificate2067,MergedCutCells.Batch172.certificate2068,MergedCutCells.Batch172.certificate2069], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2065,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2066,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2067,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2069,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric553 : ∀ c∈certificate553.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2065,MergedCutCells.Batch172.certificate2066,MergedCutCells.Batch172.certificate2067,MergedCutCells.Batch172.certificate2068,MergedCutCells.Batch172.certificate2069], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2065,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2066,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2067,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2068,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2069,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid553 : ∀ c∈certificate553.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2065,MergedCutCells.Batch172.certificate2066,MergedCutCells.Batch172.certificate2067,MergedCutCells.Batch172.certificate2068,MergedCutCells.Batch172.certificate2069], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches553 : ∀ c∈certificate553.cells, c.population=certificate553.population := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2065,MergedCutCells.Batch172.certificate2066,MergedCutCells.Batch172.certificate2067,MergedCutCells.Batch172.certificate2068,MergedCutCells.Batch172.certificate2069], c.population=PopulationCertificates.Batch018.certificate368
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers553 {x : ℝ} (hx : certificate553.interval.Contains x) : ∃ c∈certificate553.cells, c.region.interval.Contains x := rat_cut_group_covers certificate553 numericValid553 hx

def certificate554 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate369,PopulationCertificates.Batch018.certificate369,[MergedCutCells.Batch172.certificate2070,MergedCutCells.Batch172.certificate2071],(5229569777229043149/1000000000000000000),none,(1/2),(394228899374981937/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid554 : certificate554.NumericValid := by decide +kernel
theorem cellsSound554 : ∀ c∈certificate554.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2070,MergedCutCells.Batch172.certificate2071], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2070,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2071,List.forall_mem_nil _⟩⟩
theorem cellsNumeric554 : ∀ c∈certificate554.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2070,MergedCutCells.Batch172.certificate2071], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2070,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2071,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid554 : ∀ c∈certificate554.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2070,MergedCutCells.Batch172.certificate2071], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches554 : ∀ c∈certificate554.cells, c.population=certificate554.population := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2070,MergedCutCells.Batch172.certificate2071], c.population=PopulationCertificates.Batch018.certificate369
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers554 {x : ℝ} (hx : certificate554.interval.Contains x) : ∃ c∈certificate554.cells, c.region.interval.Contains x := rat_cut_group_covers certificate554 numericValid554 hx

def certificate555 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate370,PopulationCertificates.Batch018.certificate370,[MergedCutCells.Batch172.certificate2072,MergedCutCells.Batch172.certificate2073,MergedCutCells.Batch172.certificate2074],(634989171441124529/1000000000000000000),(some (60295627/50000000)),(1/2),(286883954615879629/1000000000000000000),(some (155431848414078523/1000000000000000000)),(some (36126381730842419/1000000000000000000))⟩
theorem numericValid555 : certificate555.NumericValid := by decide +kernel
theorem cellsSound555 : ∀ c∈certificate555.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2072,MergedCutCells.Batch172.certificate2073,MergedCutCells.Batch172.certificate2074], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2072,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2074,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric555 : ∀ c∈certificate555.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2072,MergedCutCells.Batch172.certificate2073,MergedCutCells.Batch172.certificate2074], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2072,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2074,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid555 : ∀ c∈certificate555.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2072,MergedCutCells.Batch172.certificate2073,MergedCutCells.Batch172.certificate2074], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid186,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid186,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid186,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches555 : ∀ c∈certificate555.cells, c.population=certificate555.population := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2072,MergedCutCells.Batch172.certificate2073,MergedCutCells.Batch172.certificate2074], c.population=PopulationCertificates.Batch018.certificate370
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers555 {x : ℝ} (hx : certificate555.interval.Contains x) : ∃ c∈certificate555.cells, c.region.interval.Contains x := rat_cut_group_covers certificate555 numericValid555 hx

def certificate556 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate370,PopulationCertificates.Batch018.certificate370,[MergedCutCells.Batch172.certificate2075,MergedCutCells.Batch173.certificate2076,MergedCutCells.Batch173.certificate2077,MergedCutCells.Batch173.certificate2078],(60295627/50000000),none,(1/2),(275825923267168569/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid556 : certificate556.NumericValid := by decide +kernel
theorem cellsSound556 : ∀ c∈certificate556.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2075,MergedCutCells.Batch173.certificate2076,MergedCutCells.Batch173.certificate2077,MergedCutCells.Batch173.certificate2078], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.sound2075,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2077,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2078,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric556 : ∀ c∈certificate556.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2075,MergedCutCells.Batch173.certificate2076,MergedCutCells.Batch173.certificate2077,MergedCutCells.Batch173.certificate2078], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch172.numericValid2075,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2077,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2078,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid556 : ∀ c∈certificate556.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2075,MergedCutCells.Batch173.certificate2076,MergedCutCells.Batch173.certificate2077,MergedCutCells.Batch173.certificate2078], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches556 : ∀ c∈certificate556.cells, c.population=certificate556.population := by
  change ∀ c∈[MergedCutCells.Batch172.certificate2075,MergedCutCells.Batch173.certificate2076,MergedCutCells.Batch173.certificate2077,MergedCutCells.Batch173.certificate2078], c.population=PopulationCertificates.Batch018.certificate370
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers556 {x : ℝ} (hx : certificate556.interval.Contains x) : ∃ c∈certificate556.cells, c.region.interval.Contains x := rat_cut_group_covers certificate556 numericValid556 hx

def certificate557 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate371,PopulationCertificates.Batch018.certificate371,[MergedCutCells.Batch173.certificate2079,MergedCutCells.Batch173.certificate2080],(5184742592783593329/1000000000000000000),none,(1/2),(1953648112079552289/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid557 : certificate557.NumericValid := by decide +kernel
theorem cellsSound557 : ∀ c∈certificate557.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2079,MergedCutCells.Batch173.certificate2080], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2079,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2080,List.forall_mem_nil _⟩⟩
theorem cellsNumeric557 : ∀ c∈certificate557.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2079,MergedCutCells.Batch173.certificate2080], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2079,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2080,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid557 : ∀ c∈certificate557.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2079,MergedCutCells.Batch173.certificate2080], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches557 : ∀ c∈certificate557.cells, c.population=certificate557.population := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2079,MergedCutCells.Batch173.certificate2080], c.population=PopulationCertificates.Batch018.certificate371
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers557 {x : ℝ} (hx : certificate557.interval.Contains x) : ∃ c∈certificate557.cells, c.region.interval.Contains x := rat_cut_group_covers certificate557 numericValid557 hx

def certificate558 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate372,PopulationCertificates.Batch018.certificate372,[MergedCutCells.Batch173.certificate2081,MergedCutCells.Batch173.certificate2082,MergedCutCells.Batch173.certificate2083],(640516980691505541/1000000000000000000),(some (1185395967/1000000000)),(1/2),(144192703609359149/500000000000000000),(some (16569358608904861/100000000000000000)),(some (4911737147677521/125000000000000000))⟩
theorem numericValid558 : certificate558.NumericValid := by decide +kernel
theorem cellsSound558 : ∀ c∈certificate558.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2081,MergedCutCells.Batch173.certificate2082,MergedCutCells.Batch173.certificate2083], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2083,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric558 : ∀ c∈certificate558.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2081,MergedCutCells.Batch173.certificate2082,MergedCutCells.Batch173.certificate2083], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2083,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid558 : ∀ c∈certificate558.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2081,MergedCutCells.Batch173.certificate2082,MergedCutCells.Batch173.certificate2083], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid187,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid187,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid187,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches558 : ∀ c∈certificate558.cells, c.population=certificate558.population := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2081,MergedCutCells.Batch173.certificate2082,MergedCutCells.Batch173.certificate2083], c.population=PopulationCertificates.Batch018.certificate372
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers558 {x : ℝ} (hx : certificate558.interval.Contains x) : ∃ c∈certificate558.cells, c.region.interval.Contains x := rat_cut_group_covers certificate558 numericValid558 hx

def certificate559 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate372,PopulationCertificates.Batch018.certificate372,[MergedCutCells.Batch173.certificate2084,MergedCutCells.Batch173.certificate2085,MergedCutCells.Batch173.certificate2086,MergedCutCells.Batch173.certificate2087],(1185395967/1000000000),none,(1/2),(17271806465122631/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid559 : certificate559.NumericValid := by decide +kernel
theorem cellsSound559 : ∀ c∈certificate559.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2084,MergedCutCells.Batch173.certificate2085,MergedCutCells.Batch173.certificate2086,MergedCutCells.Batch173.certificate2087], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2084,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2085,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.sound2087,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric559 : ∀ c∈certificate559.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2084,MergedCutCells.Batch173.certificate2085,MergedCutCells.Batch173.certificate2086,MergedCutCells.Batch173.certificate2087], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2084,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2085,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch173.numericValid2087,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid559 : ∀ c∈certificate559.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2084,MergedCutCells.Batch173.certificate2085,MergedCutCells.Batch173.certificate2086,MergedCutCells.Batch173.certificate2087], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches559 : ∀ c∈certificate559.cells, c.population=certificate559.population := by
  change ∀ c∈[MergedCutCells.Batch173.certificate2084,MergedCutCells.Batch173.certificate2085,MergedCutCells.Batch173.certificate2086,MergedCutCells.Batch173.certificate2087], c.population=PopulationCertificates.Batch018.certificate372
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers559 {x : ℝ} (hx : certificate559.interval.Contains x) : ∃ c∈certificate559.cells, c.region.interval.Contains x := rat_cut_group_covers certificate559 numericValid559 hx

def certificate560 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate373,PopulationCertificates.Batch018.certificate373,[MergedCutCells.Batch174.certificate2088,MergedCutCells.Batch174.certificate2089],(5255340545974677743/1000000000000000000),none,(1/2),(2015459739698615881/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid560 : certificate560.NumericValid := by decide +kernel
theorem cellsSound560 : ∀ c∈certificate560.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2088,MergedCutCells.Batch174.certificate2089], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2088,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2089,List.forall_mem_nil _⟩⟩
theorem cellsNumeric560 : ∀ c∈certificate560.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2088,MergedCutCells.Batch174.certificate2089], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2088,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2089,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid560 : ∀ c∈certificate560.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2088,MergedCutCells.Batch174.certificate2089], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches560 : ∀ c∈certificate560.cells, c.population=certificate560.population := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2088,MergedCutCells.Batch174.certificate2089], c.population=PopulationCertificates.Batch018.certificate373
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers560 {x : ℝ} (hx : certificate560.interval.Contains x) : ∃ c∈certificate560.cells, c.region.interval.Contains x := rat_cut_group_covers certificate560 numericValid560 hx

def certificate561 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate374,PopulationCertificates.Batch018.certificate374,[MergedCutCells.Batch174.certificate2090,MergedCutCells.Batch174.certificate2091],(649196931814634863/1000000000000000000),(some (117392791/100000000)),(1/2),(60718321449932087/200000000000000000),(some (176433673551199963/1000000000000000000)),(some (42700553751522909/1000000000000000000))⟩
theorem numericValid561 : certificate561.NumericValid := by decide +kernel
theorem cellsSound561 : ∀ c∈certificate561.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2090,MergedCutCells.Batch174.certificate2091], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2090,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2091,List.forall_mem_nil _⟩⟩
theorem cellsNumeric561 : ∀ c∈certificate561.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2090,MergedCutCells.Batch174.certificate2091], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2090,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2091,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid561 : ∀ c∈certificate561.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2090,MergedCutCells.Batch174.certificate2091], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid188,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid188,List.forall_mem_nil _⟩⟩
theorem populationMatches561 : ∀ c∈certificate561.cells, c.population=certificate561.population := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2090,MergedCutCells.Batch174.certificate2091], c.population=PopulationCertificates.Batch018.certificate374
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers561 {x : ℝ} (hx : certificate561.interval.Contains x) : ∃ c∈certificate561.cells, c.region.interval.Contains x := rat_cut_group_covers certificate561 numericValid561 hx

def certificate562 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate374,PopulationCertificates.Batch018.certificate374,[MergedCutCells.Batch174.certificate2092,MergedCutCells.Batch174.certificate2093,MergedCutCells.Batch174.certificate2094,MergedCutCells.Batch174.certificate2095,MergedCutCells.Batch174.certificate2096],(117392791/100000000),none,(1/2),(14417174162758653/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid562 : certificate562.NumericValid := by decide +kernel
theorem cellsSound562 : ∀ c∈certificate562.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2092,MergedCutCells.Batch174.certificate2093,MergedCutCells.Batch174.certificate2094,MergedCutCells.Batch174.certificate2095,MergedCutCells.Batch174.certificate2096], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2092,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2093,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2095,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2096,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric562 : ∀ c∈certificate562.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2092,MergedCutCells.Batch174.certificate2093,MergedCutCells.Batch174.certificate2094,MergedCutCells.Batch174.certificate2095,MergedCutCells.Batch174.certificate2096], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2092,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2093,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2095,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2096,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid562 : ∀ c∈certificate562.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2092,MergedCutCells.Batch174.certificate2093,MergedCutCells.Batch174.certificate2094,MergedCutCells.Batch174.certificate2095,MergedCutCells.Batch174.certificate2096], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches562 : ∀ c∈certificate562.cells, c.population=certificate562.population := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2092,MergedCutCells.Batch174.certificate2093,MergedCutCells.Batch174.certificate2094,MergedCutCells.Batch174.certificate2095,MergedCutCells.Batch174.certificate2096], c.population=PopulationCertificates.Batch018.certificate374
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers562 {x : ℝ} (hx : certificate562.interval.Contains x) : ∃ c∈certificate562.cells, c.region.interval.Contains x := rat_cut_group_covers certificate562 numericValid562 hx

def certificate563 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate375,PopulationCertificates.Batch018.certificate375,[MergedCutCells.Batch174.certificate2097,MergedCutCells.Batch174.certificate2098],(5305075133442116517/1000000000000000000),none,(1/2),(1038613644813500713/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid563 : certificate563.NumericValid := by decide +kernel
theorem cellsSound563 : ∀ c∈certificate563.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2097,MergedCutCells.Batch174.certificate2098], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2097,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.sound2098,List.forall_mem_nil _⟩⟩
theorem cellsNumeric563 : ∀ c∈certificate563.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2097,MergedCutCells.Batch174.certificate2098], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2097,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch174.numericValid2098,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid563 : ∀ c∈certificate563.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2097,MergedCutCells.Batch174.certificate2098], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches563 : ∀ c∈certificate563.cells, c.population=certificate563.population := by
  change ∀ c∈[MergedCutCells.Batch174.certificate2097,MergedCutCells.Batch174.certificate2098], c.population=PopulationCertificates.Batch018.certificate375
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers563 {x : ℝ} (hx : certificate563.interval.Contains x) : ∃ c∈certificate563.cells, c.region.interval.Contains x := rat_cut_group_covers certificate563 numericValid563 hx

end Cycle12.MergedCutGroups.Batch046
