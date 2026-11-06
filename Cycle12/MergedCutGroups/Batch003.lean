import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch001
import Cycle12.MergedCutCells.Batch007
import Cycle12.MergedCutCells.Batch008
import Cycle12.MergedCutCells.Batch009
import Cycle12.MergedCutCells.Batch010
import Cycle12.PopulationCertificates.Batch001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch003

def certificate36 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate24,PopulationCertificates.Batch001.certificate24,[MergedCutCells.Batch007.certificate88,MergedCutCells.Batch007.certificate89],(76207426718585373/125000000000000000),(some (1245093699/1000000000)),(1/2),(241046384312169741/1000000000000000000),(some (32730442609533521/250000000000000000)),(some (28906929096128577/1000000000000000000))⟩
theorem numericValid36 : certificate36.NumericValid := by decide +kernel
theorem cellsSound36 : ∀ c∈certificate36.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch007.certificate88,MergedCutCells.Batch007.certificate89], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound88,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound89,List.forall_mem_nil _⟩⟩
theorem cellsNumeric36 : ∀ c∈certificate36.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch007.certificate88,MergedCutCells.Batch007.certificate89], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid88,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid89,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid36 : ∀ c∈certificate36.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch007.certificate88,MergedCutCells.Batch007.certificate89], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid13,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid13,List.forall_mem_nil _⟩⟩
theorem populationMatches36 : ∀ c∈certificate36.cells, c.population=certificate36.population := by
  change ∀ c∈[MergedCutCells.Batch007.certificate88,MergedCutCells.Batch007.certificate89], c.population=PopulationCertificates.Batch001.certificate24
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers36 {x : ℝ} (hx : certificate36.interval.Contains x) : ∃ c∈certificate36.cells, c.region.interval.Contains x := rat_cut_group_covers certificate36 numericValid36 hx

def certificate37 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate24,PopulationCertificates.Batch001.certificate24,[MergedCutCells.Batch007.certificate90,MergedCutCells.Batch007.certificate91,MergedCutCells.Batch007.certificate92,MergedCutCells.Batch007.certificate93],(1245093699/1000000000),none,(1/2),(46489948261787949/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid37 : certificate37.NumericValid := by decide +kernel
theorem cellsSound37 : ∀ c∈certificate37.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch007.certificate90,MergedCutCells.Batch007.certificate91,MergedCutCells.Batch007.certificate92,MergedCutCells.Batch007.certificate93], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound90,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound91,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound92,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound93,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric37 : ∀ c∈certificate37.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch007.certificate90,MergedCutCells.Batch007.certificate91,MergedCutCells.Batch007.certificate92,MergedCutCells.Batch007.certificate93], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid90,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid91,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid92,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid93,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid37 : ∀ c∈certificate37.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch007.certificate90,MergedCutCells.Batch007.certificate91,MergedCutCells.Batch007.certificate92,MergedCutCells.Batch007.certificate93], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches37 : ∀ c∈certificate37.cells, c.population=certificate37.population := by
  change ∀ c∈[MergedCutCells.Batch007.certificate90,MergedCutCells.Batch007.certificate91,MergedCutCells.Batch007.certificate92,MergedCutCells.Batch007.certificate93], c.population=PopulationCertificates.Batch001.certificate24
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers37 {x : ℝ} (hx : certificate37.interval.Contains x) : ∃ c∈certificate37.cells, c.region.interval.Contains x := rat_cut_group_covers certificate37 numericValid37 hx

def certificate38 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate25,PopulationCertificates.Batch001.certificate25,[MergedCutCells.Batch007.certificate94,MergedCutCells.Batch007.certificate95],(3374372767283928863/1000000000000000000),none,(1/2),(29887109870633463/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid38 : certificate38.NumericValid := by decide +kernel
theorem cellsSound38 : ∀ c∈certificate38.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch007.certificate94,MergedCutCells.Batch007.certificate95], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound94,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound95,List.forall_mem_nil _⟩⟩
theorem cellsNumeric38 : ∀ c∈certificate38.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch007.certificate94,MergedCutCells.Batch007.certificate95], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid94,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid95,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid38 : ∀ c∈certificate38.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch007.certificate94,MergedCutCells.Batch007.certificate95], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches38 : ∀ c∈certificate38.cells, c.population=certificate38.population := by
  change ∀ c∈[MergedCutCells.Batch007.certificate94,MergedCutCells.Batch007.certificate95], c.population=PopulationCertificates.Batch001.certificate25
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers38 {x : ℝ} (hx : certificate38.interval.Contains x) : ∃ c∈certificate38.cells, c.region.interval.Contains x := rat_cut_group_covers certificate38 numericValid38 hx

def certificate39 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate26,PopulationCertificates.Batch001.certificate26,[MergedCutCells.Batch008.certificate96,MergedCutCells.Batch008.certificate97],(307847250782034791/500000000000000000),(some (612523341/500000000)),(1/2),(47602387909780871/200000000000000000),(some (144981788658978511/1000000000000000000)),(some (32988514750136009/1000000000000000000))⟩
theorem numericValid39 : certificate39.NumericValid := by decide +kernel
theorem cellsSound39 : ∀ c∈certificate39.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch008.certificate96,MergedCutCells.Batch008.certificate97], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound96,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound97,List.forall_mem_nil _⟩⟩
theorem cellsNumeric39 : ∀ c∈certificate39.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate96,MergedCutCells.Batch008.certificate97], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid96,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid97,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid39 : ∀ c∈certificate39.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate96,MergedCutCells.Batch008.certificate97], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid14,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid14,List.forall_mem_nil _⟩⟩
theorem populationMatches39 : ∀ c∈certificate39.cells, c.population=certificate39.population := by
  change ∀ c∈[MergedCutCells.Batch008.certificate96,MergedCutCells.Batch008.certificate97], c.population=PopulationCertificates.Batch001.certificate26
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers39 {x : ℝ} (hx : certificate39.interval.Contains x) : ∃ c∈certificate39.cells, c.region.interval.Contains x := rat_cut_group_covers certificate39 numericValid39 hx

def certificate40 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate26,PopulationCertificates.Batch001.certificate26,[MergedCutCells.Batch008.certificate98,MergedCutCells.Batch008.certificate99,MergedCutCells.Batch008.certificate100,MergedCutCells.Batch008.certificate101],(612523341/500000000),none,(1/2),(114233578970495717/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid40 : certificate40.NumericValid := by decide +kernel
theorem cellsSound40 : ∀ c∈certificate40.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch008.certificate98,MergedCutCells.Batch008.certificate99,MergedCutCells.Batch008.certificate100,MergedCutCells.Batch008.certificate101], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound98,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound99,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound101,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric40 : ∀ c∈certificate40.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate98,MergedCutCells.Batch008.certificate99,MergedCutCells.Batch008.certificate100,MergedCutCells.Batch008.certificate101], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid98,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid99,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid101,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid40 : ∀ c∈certificate40.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate98,MergedCutCells.Batch008.certificate99,MergedCutCells.Batch008.certificate100,MergedCutCells.Batch008.certificate101], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches40 : ∀ c∈certificate40.cells, c.population=certificate40.population := by
  change ∀ c∈[MergedCutCells.Batch008.certificate98,MergedCutCells.Batch008.certificate99,MergedCutCells.Batch008.certificate100,MergedCutCells.Batch008.certificate101], c.population=PopulationCertificates.Batch001.certificate26
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers40 {x : ℝ} (hx : certificate40.interval.Contains x) : ∃ c∈certificate40.cells, c.region.interval.Contains x := rat_cut_group_covers certificate40 numericValid40 hx

def certificate41 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate27,PopulationCertificates.Batch001.certificate27,[MergedCutCells.Batch008.certificate102,MergedCutCells.Batch008.certificate103],(3411859671637580543/1000000000000000000),none,(1/2),(270268492956424973/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid41 : certificate41.NumericValid := by decide +kernel
theorem cellsSound41 : ∀ c∈certificate41.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch008.certificate102,MergedCutCells.Batch008.certificate103], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound102,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound103,List.forall_mem_nil _⟩⟩
theorem cellsNumeric41 : ∀ c∈certificate41.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate102,MergedCutCells.Batch008.certificate103], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid102,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid103,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid41 : ∀ c∈certificate41.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate102,MergedCutCells.Batch008.certificate103], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches41 : ∀ c∈certificate41.cells, c.population=certificate41.population := by
  change ∀ c∈[MergedCutCells.Batch008.certificate102,MergedCutCells.Batch008.certificate103], c.population=PopulationCertificates.Batch001.certificate27
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers41 {x : ℝ} (hx : certificate41.interval.Contains x) : ∃ c∈certificate41.cells, c.region.interval.Contains x := rat_cut_group_covers certificate41 numericValid41 hx

def certificate42 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate28,PopulationCertificates.Batch001.certificate28,[MergedCutCells.Batch008.certificate104,MergedCutCells.Batch008.certificate105],(622318900544206813/1000000000000000000),(some (605291289/500000000)),(1/2),(117618636143669179/500000000000000000),(some (19935844139962811/125000000000000000)),(some (1868390842057391/50000000000000000))⟩
theorem numericValid42 : certificate42.NumericValid := by decide +kernel
theorem cellsSound42 : ∀ c∈certificate42.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch008.certificate104,MergedCutCells.Batch008.certificate105], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound104,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound105,List.forall_mem_nil _⟩⟩
theorem cellsNumeric42 : ∀ c∈certificate42.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate104,MergedCutCells.Batch008.certificate105], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid104,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid105,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid42 : ∀ c∈certificate42.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate104,MergedCutCells.Batch008.certificate105], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid15,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid15,List.forall_mem_nil _⟩⟩
theorem populationMatches42 : ∀ c∈certificate42.cells, c.population=certificate42.population := by
  change ∀ c∈[MergedCutCells.Batch008.certificate104,MergedCutCells.Batch008.certificate105], c.population=PopulationCertificates.Batch001.certificate28
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers42 {x : ℝ} (hx : certificate42.interval.Contains x) : ∃ c∈certificate42.cells, c.region.interval.Contains x := rat_cut_group_covers certificate42 numericValid42 hx

def certificate43 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate28,PopulationCertificates.Batch001.certificate28,[MergedCutCells.Batch008.certificate106,MergedCutCells.Batch008.certificate107,MergedCutCells.Batch009.certificate108,MergedCutCells.Batch009.certificate109],(605291289/500000000),none,(1/2),(44860331323643169/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid43 : certificate43.NumericValid := by decide +kernel
theorem cellsSound43 : ∀ c∈certificate43.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch008.certificate106,MergedCutCells.Batch008.certificate107,MergedCutCells.Batch009.certificate108,MergedCutCells.Batch009.certificate109], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.sound107,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound109,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric43 : ∀ c∈certificate43.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate106,MergedCutCells.Batch008.certificate107,MergedCutCells.Batch009.certificate108,MergedCutCells.Batch009.certificate109], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch008.numericValid107,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid109,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid43 : ∀ c∈certificate43.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch008.certificate106,MergedCutCells.Batch008.certificate107,MergedCutCells.Batch009.certificate108,MergedCutCells.Batch009.certificate109], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches43 : ∀ c∈certificate43.cells, c.population=certificate43.population := by
  change ∀ c∈[MergedCutCells.Batch008.certificate106,MergedCutCells.Batch008.certificate107,MergedCutCells.Batch009.certificate108,MergedCutCells.Batch009.certificate109], c.population=PopulationCertificates.Batch001.certificate28
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers43 {x : ℝ} (hx : certificate43.interval.Contains x) : ∃ c∈certificate43.cells, c.region.interval.Contains x := rat_cut_group_covers certificate43 numericValid43 hx

def certificate44 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate29,PopulationCertificates.Batch001.certificate29,[MergedCutCells.Batch009.certificate110,MergedCutCells.Batch009.certificate111],(1725175270069206853/500000000000000000),none,(1/2),(302291948526529069/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid44 : certificate44.NumericValid := by decide +kernel
theorem cellsSound44 : ∀ c∈certificate44.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch009.certificate110,MergedCutCells.Batch009.certificate111], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound110,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound111,List.forall_mem_nil _⟩⟩
theorem cellsNumeric44 : ∀ c∈certificate44.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch009.certificate110,MergedCutCells.Batch009.certificate111], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid110,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid111,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid44 : ∀ c∈certificate44.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch009.certificate110,MergedCutCells.Batch009.certificate111], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches44 : ∀ c∈certificate44.cells, c.population=certificate44.population := by
  change ∀ c∈[MergedCutCells.Batch009.certificate110,MergedCutCells.Batch009.certificate111], c.population=PopulationCertificates.Batch001.certificate29
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers44 {x : ℝ} (hx : certificate44.interval.Contains x) : ∃ c∈certificate44.cells, c.region.interval.Contains x := rat_cut_group_covers certificate44 numericValid44 hx

def certificate45 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate30,PopulationCertificates.Batch001.certificate30,[MergedCutCells.Batch009.certificate112,MergedCutCells.Batch009.certificate113,MergedCutCells.Batch009.certificate114],(78672917866609029/125000000000000000),(some (596328671/500000000)),(1/2),(23331144250249701/100000000000000000),(some (34839944114314749/200000000000000000)),(some (5248030969926309/125000000000000000))⟩
theorem numericValid45 : certificate45.NumericValid := by decide +kernel
theorem cellsSound45 : ∀ c∈certificate45.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch009.certificate112,MergedCutCells.Batch009.certificate113,MergedCutCells.Batch009.certificate114], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound114,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric45 : ∀ c∈certificate45.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch009.certificate112,MergedCutCells.Batch009.certificate113,MergedCutCells.Batch009.certificate114], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid114,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid45 : ∀ c∈certificate45.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch009.certificate112,MergedCutCells.Batch009.certificate113,MergedCutCells.Batch009.certificate114], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid16,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid16,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid16,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches45 : ∀ c∈certificate45.cells, c.population=certificate45.population := by
  change ∀ c∈[MergedCutCells.Batch009.certificate112,MergedCutCells.Batch009.certificate113,MergedCutCells.Batch009.certificate114], c.population=PopulationCertificates.Batch001.certificate30
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers45 {x : ℝ} (hx : certificate45.interval.Contains x) : ∃ c∈certificate45.cells, c.region.interval.Contains x := rat_cut_group_covers certificate45 numericValid45 hx

def certificate46 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate30,PopulationCertificates.Batch001.certificate30,[MergedCutCells.Batch009.certificate115,MergedCutCells.Batch009.certificate116,MergedCutCells.Batch009.certificate117,MergedCutCells.Batch009.certificate118,MergedCutCells.Batch009.certificate119],(596328671/500000000),none,(1/2),(220007972814317113/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid46 : certificate46.NumericValid := by decide +kernel
theorem cellsSound46 : ∀ c∈certificate46.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch009.certificate115,MergedCutCells.Batch009.certificate116,MergedCutCells.Batch009.certificate117,MergedCutCells.Batch009.certificate118,MergedCutCells.Batch009.certificate119], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound115,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound116,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound117,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.sound119,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric46 : ∀ c∈certificate46.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch009.certificate115,MergedCutCells.Batch009.certificate116,MergedCutCells.Batch009.certificate117,MergedCutCells.Batch009.certificate118,MergedCutCells.Batch009.certificate119], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid115,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid116,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid117,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch009.numericValid119,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid46 : ∀ c∈certificate46.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch009.certificate115,MergedCutCells.Batch009.certificate116,MergedCutCells.Batch009.certificate117,MergedCutCells.Batch009.certificate118,MergedCutCells.Batch009.certificate119], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches46 : ∀ c∈certificate46.cells, c.population=certificate46.population := by
  change ∀ c∈[MergedCutCells.Batch009.certificate115,MergedCutCells.Batch009.certificate116,MergedCutCells.Batch009.certificate117,MergedCutCells.Batch009.certificate118,MergedCutCells.Batch009.certificate119], c.population=PopulationCertificates.Batch001.certificate30
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers46 {x : ℝ} (hx : certificate46.interval.Contains x) : ∃ c∈certificate46.cells, c.region.interval.Contains x := rat_cut_group_covers certificate46 numericValid46 hx

def certificate47 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate31,PopulationCertificates.Batch001.certificate31,[MergedCutCells.Batch010.certificate120,MergedCutCells.Batch010.certificate121],(3489881170794847273/1000000000000000000),none,(1/2),(67040622337005957/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid47 : certificate47.NumericValid := by decide +kernel
theorem cellsSound47 : ∀ c∈certificate47.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch010.certificate120,MergedCutCells.Batch010.certificate121], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound120,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound121,List.forall_mem_nil _⟩⟩
theorem cellsNumeric47 : ∀ c∈certificate47.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate120,MergedCutCells.Batch010.certificate121], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid120,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid121,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid47 : ∀ c∈certificate47.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate120,MergedCutCells.Batch010.certificate121], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches47 : ∀ c∈certificate47.cells, c.population=certificate47.population := by
  change ∀ c∈[MergedCutCells.Batch010.certificate120,MergedCutCells.Batch010.certificate121], c.population=PopulationCertificates.Batch001.certificate31
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers47 {x : ℝ} (hx : certificate47.interval.Contains x) : ∃ c∈certificate47.cells, c.region.interval.Contains x := rat_cut_group_covers certificate47 numericValid47 hx

end Cycle12.MergedCutGroups.Batch003
