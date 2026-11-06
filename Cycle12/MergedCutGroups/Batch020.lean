import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch008
import Cycle12.MergedCutCells.Batch076
import Cycle12.MergedCutCells.Batch077
import Cycle12.MergedCutCells.Batch078
import Cycle12.MergedCutCells.Batch079
import Cycle12.MergedCutCells.Batch080
import Cycle12.MergedCutCells.Batch081
import Cycle12.PopulationCertificates.Batch008

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch020

def certificate240 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate160,PopulationCertificates.Batch008.certificate160,[MergedCutCells.Batch076.certificate923,MergedCutCells.Batch077.certificate924,MergedCutCells.Batch077.certificate925,MergedCutCells.Batch077.certificate926,MergedCutCells.Batch077.certificate927,MergedCutCells.Batch077.certificate928,MergedCutCells.Batch077.certificate929,MergedCutCells.Batch077.certificate930],(832790380885074743/1000000000000000000),(some 64),(1/2),(290839645102868553/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (88156545591994433/62500000000000000))⟩
theorem numericValid240 : certificate240.NumericValid := by decide +kernel
theorem cellsSound240 : ∀ c∈certificate240.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch076.certificate923,MergedCutCells.Batch077.certificate924,MergedCutCells.Batch077.certificate925,MergedCutCells.Batch077.certificate926,MergedCutCells.Batch077.certificate927,MergedCutCells.Batch077.certificate928,MergedCutCells.Batch077.certificate929,MergedCutCells.Batch077.certificate930], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.sound923,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound925,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound926,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound927,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound928,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound930,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric240 : ∀ c∈certificate240.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch076.certificate923,MergedCutCells.Batch077.certificate924,MergedCutCells.Batch077.certificate925,MergedCutCells.Batch077.certificate926,MergedCutCells.Batch077.certificate927,MergedCutCells.Batch077.certificate928,MergedCutCells.Batch077.certificate929,MergedCutCells.Batch077.certificate930], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch076.numericValid923,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid925,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid926,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid927,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid928,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid930,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid240 : ∀ c∈certificate240.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch076.certificate923,MergedCutCells.Batch077.certificate924,MergedCutCells.Batch077.certificate925,MergedCutCells.Batch077.certificate926,MergedCutCells.Batch077.certificate927,MergedCutCells.Batch077.certificate928,MergedCutCells.Batch077.certificate929,MergedCutCells.Batch077.certificate930], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid81,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid81,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid81,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid81,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid81,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid81,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid81,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid81,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches240 : ∀ c∈certificate240.cells, c.population=certificate240.population := by
  change ∀ c∈[MergedCutCells.Batch076.certificate923,MergedCutCells.Batch077.certificate924,MergedCutCells.Batch077.certificate925,MergedCutCells.Batch077.certificate926,MergedCutCells.Batch077.certificate927,MergedCutCells.Batch077.certificate928,MergedCutCells.Batch077.certificate929,MergedCutCells.Batch077.certificate930], c.population=PopulationCertificates.Batch008.certificate160
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers240 {x : ℝ} (hx : certificate240.interval.Contains x) : ∃ c∈certificate240.cells, c.region.interval.Contains x := rat_cut_group_covers certificate240 numericValid240 hx

def certificate241 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate160,PopulationCertificates.Batch008.certificate160,[MergedCutCells.Batch077.certificate931],64,none,(1/2),(804071993938537917/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid241 : certificate241.NumericValid := by decide +kernel
theorem cellsSound241 : ∀ c∈certificate241.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch077.certificate931], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound931,List.forall_mem_nil _⟩
theorem cellsNumeric241 : ∀ c∈certificate241.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch077.certificate931], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid931,List.forall_mem_nil _⟩
theorem cellsEntropyValid241 : ∀ c∈certificate241.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch077.certificate931], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches241 : ∀ c∈certificate241.cells, c.population=certificate241.population := by
  change ∀ c∈[MergedCutCells.Batch077.certificate931], c.population=PopulationCertificates.Batch008.certificate160
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers241 {x : ℝ} (hx : certificate241.interval.Contains x) : ∃ c∈certificate241.cells, c.region.interval.Contains x := rat_cut_group_covers certificate241 numericValid241 hx

def certificate242 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate161,PopulationCertificates.Batch008.certificate161,[MergedCutCells.Batch077.certificate932,MergedCutCells.Batch077.certificate933,MergedCutCells.Batch077.certificate934,MergedCutCells.Batch077.certificate935],(1898174946371158641/500000000000000000),none,(1/2),(712537312432817003/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid242 : certificate242.NumericValid := by decide +kernel
theorem cellsSound242 : ∀ c∈certificate242.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch077.certificate932,MergedCutCells.Batch077.certificate933,MergedCutCells.Batch077.certificate934,MergedCutCells.Batch077.certificate935], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound932,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound934,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.sound935,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric242 : ∀ c∈certificate242.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch077.certificate932,MergedCutCells.Batch077.certificate933,MergedCutCells.Batch077.certificate934,MergedCutCells.Batch077.certificate935], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid932,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid934,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch077.numericValid935,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid242 : ∀ c∈certificate242.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch077.certificate932,MergedCutCells.Batch077.certificate933,MergedCutCells.Batch077.certificate934,MergedCutCells.Batch077.certificate935], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches242 : ∀ c∈certificate242.cells, c.population=certificate242.population := by
  change ∀ c∈[MergedCutCells.Batch077.certificate932,MergedCutCells.Batch077.certificate933,MergedCutCells.Batch077.certificate934,MergedCutCells.Batch077.certificate935], c.population=PopulationCertificates.Batch008.certificate161
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers242 {x : ℝ} (hx : certificate242.interval.Contains x) : ∃ c∈certificate242.cells, c.region.interval.Contains x := rat_cut_group_covers certificate242 numericValid242 hx

def certificate243 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate162,PopulationCertificates.Batch008.certificate162,[MergedCutCells.Batch078.certificate936,MergedCutCells.Batch078.certificate937,MergedCutCells.Batch078.certificate938,MergedCutCells.Batch078.certificate939,MergedCutCells.Batch078.certificate940,MergedCutCells.Batch078.certificate941,MergedCutCells.Batch078.certificate942,MergedCutCells.Batch078.certificate943],(416601262349090921/500000000000000000),(some 64),(1/2),(147558015905616737/500000000000000000),(some (69314718055994531/100000000000000000)),(some (1412891640987040193/1000000000000000000))⟩
theorem numericValid243 : certificate243.NumericValid := by decide +kernel
theorem cellsSound243 : ∀ c∈certificate243.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch078.certificate936,MergedCutCells.Batch078.certificate937,MergedCutCells.Batch078.certificate938,MergedCutCells.Batch078.certificate939,MergedCutCells.Batch078.certificate940,MergedCutCells.Batch078.certificate941,MergedCutCells.Batch078.certificate942,MergedCutCells.Batch078.certificate943], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound936,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound937,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound938,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound939,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound940,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound941,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound942,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound943,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric243 : ∀ c∈certificate243.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch078.certificate936,MergedCutCells.Batch078.certificate937,MergedCutCells.Batch078.certificate938,MergedCutCells.Batch078.certificate939,MergedCutCells.Batch078.certificate940,MergedCutCells.Batch078.certificate941,MergedCutCells.Batch078.certificate942,MergedCutCells.Batch078.certificate943], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid936,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid937,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid938,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid939,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid940,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid941,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid942,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid943,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid243 : ∀ c∈certificate243.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch078.certificate936,MergedCutCells.Batch078.certificate937,MergedCutCells.Batch078.certificate938,MergedCutCells.Batch078.certificate939,MergedCutCells.Batch078.certificate940,MergedCutCells.Batch078.certificate941,MergedCutCells.Batch078.certificate942,MergedCutCells.Batch078.certificate943], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid82,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid82,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid82,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid82,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid82,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid82,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid82,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid82,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches243 : ∀ c∈certificate243.cells, c.population=certificate243.population := by
  change ∀ c∈[MergedCutCells.Batch078.certificate936,MergedCutCells.Batch078.certificate937,MergedCutCells.Batch078.certificate938,MergedCutCells.Batch078.certificate939,MergedCutCells.Batch078.certificate940,MergedCutCells.Batch078.certificate941,MergedCutCells.Batch078.certificate942,MergedCutCells.Batch078.certificate943], c.population=PopulationCertificates.Batch008.certificate162
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers243 {x : ℝ} (hx : certificate243.interval.Contains x) : ∃ c∈certificate243.cells, c.region.interval.Contains x := rat_cut_group_covers certificate243 numericValid243 hx

def certificate244 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate162,PopulationCertificates.Batch008.certificate162,[MergedCutCells.Batch078.certificate944],64,none,(1/2),(810368234947961027/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid244 : certificate244.NumericValid := by decide +kernel
theorem cellsSound244 : ∀ c∈certificate244.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch078.certificate944], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound944,List.forall_mem_nil _⟩
theorem cellsNumeric244 : ∀ c∈certificate244.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch078.certificate944], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid944,List.forall_mem_nil _⟩
theorem cellsEntropyValid244 : ∀ c∈certificate244.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch078.certificate944], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches244 : ∀ c∈certificate244.cells, c.population=certificate244.population := by
  change ∀ c∈[MergedCutCells.Batch078.certificate944], c.population=PopulationCertificates.Batch008.certificate162
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers244 {x : ℝ} (hx : certificate244.interval.Contains x) : ∃ c∈certificate244.cells, c.region.interval.Contains x := rat_cut_group_covers certificate244 numericValid244 hx

def certificate245 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate163,PopulationCertificates.Batch008.certificate163,[MergedCutCells.Batch078.certificate945,MergedCutCells.Batch078.certificate946,MergedCutCells.Batch078.certificate947],(3809788386246167301/1000000000000000000),none,(1/2),(726859428563713417/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid245 : certificate245.NumericValid := by decide +kernel
theorem cellsSound245 : ∀ c∈certificate245.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch078.certificate945,MergedCutCells.Batch078.certificate946,MergedCutCells.Batch078.certificate947], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound945,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound946,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.sound947,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric245 : ∀ c∈certificate245.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch078.certificate945,MergedCutCells.Batch078.certificate946,MergedCutCells.Batch078.certificate947], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid945,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid946,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch078.numericValid947,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid245 : ∀ c∈certificate245.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch078.certificate945,MergedCutCells.Batch078.certificate946,MergedCutCells.Batch078.certificate947], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches245 : ∀ c∈certificate245.cells, c.population=certificate245.population := by
  change ∀ c∈[MergedCutCells.Batch078.certificate945,MergedCutCells.Batch078.certificate946,MergedCutCells.Batch078.certificate947], c.population=PopulationCertificates.Batch008.certificate163
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers245 {x : ℝ} (hx : certificate245.interval.Contains x) : ∃ c∈certificate245.cells, c.region.interval.Contains x := rat_cut_group_covers certificate245 numericValid245 hx

def certificate246 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate164,PopulationCertificates.Batch008.certificate164,[MergedCutCells.Batch079.certificate948,MergedCutCells.Batch079.certificate949,MergedCutCells.Batch079.certificate950,MergedCutCells.Batch079.certificate951,MergedCutCells.Batch079.certificate952,MergedCutCells.Batch079.certificate953,MergedCutCells.Batch079.certificate954],(8294301680008411/10000000000000000),(some 64),(1/2),(287458608619272327/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (177467299140754081/125000000000000000))⟩
theorem numericValid246 : certificate246.NumericValid := by decide +kernel
theorem cellsSound246 : ∀ c∈certificate246.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch079.certificate948,MergedCutCells.Batch079.certificate949,MergedCutCells.Batch079.certificate950,MergedCutCells.Batch079.certificate951,MergedCutCells.Batch079.certificate952,MergedCutCells.Batch079.certificate953,MergedCutCells.Batch079.certificate954], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound948,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound949,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound950,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound951,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound952,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound954,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric246 : ∀ c∈certificate246.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch079.certificate948,MergedCutCells.Batch079.certificate949,MergedCutCells.Batch079.certificate950,MergedCutCells.Batch079.certificate951,MergedCutCells.Batch079.certificate952,MergedCutCells.Batch079.certificate953,MergedCutCells.Batch079.certificate954], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid948,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid949,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid950,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid951,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid952,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid953,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid954,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid246 : ∀ c∈certificate246.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch079.certificate948,MergedCutCells.Batch079.certificate949,MergedCutCells.Batch079.certificate950,MergedCutCells.Batch079.certificate951,MergedCutCells.Batch079.certificate952,MergedCutCells.Batch079.certificate953,MergedCutCells.Batch079.certificate954], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid83,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid83,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid83,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid83,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid83,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid83,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid83,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches246 : ∀ c∈certificate246.cells, c.population=certificate246.population := by
  change ∀ c∈[MergedCutCells.Batch079.certificate948,MergedCutCells.Batch079.certificate949,MergedCutCells.Batch079.certificate950,MergedCutCells.Batch079.certificate951,MergedCutCells.Batch079.certificate952,MergedCutCells.Batch079.certificate953,MergedCutCells.Batch079.certificate954], c.population=PopulationCertificates.Batch008.certificate164
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers246 {x : ℝ} (hx : certificate246.interval.Contains x) : ∃ c∈certificate246.cells, c.region.interval.Contains x := rat_cut_group_covers certificate246 numericValid246 hx

def certificate247 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate164,PopulationCertificates.Batch008.certificate164,[MergedCutCells.Batch079.certificate955],64,none,(1/2),(808256048377254267/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid247 : certificate247.NumericValid := by decide +kernel
theorem cellsSound247 : ∀ c∈certificate247.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch079.certificate955], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound955,List.forall_mem_nil _⟩
theorem cellsNumeric247 : ∀ c∈certificate247.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch079.certificate955], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid955,List.forall_mem_nil _⟩
theorem cellsEntropyValid247 : ∀ c∈certificate247.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch079.certificate955], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches247 : ∀ c∈certificate247.cells, c.population=certificate247.population := by
  change ∀ c∈[MergedCutCells.Batch079.certificate955], c.population=PopulationCertificates.Batch008.certificate164
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers247 {x : ℝ} (hx : certificate247.interval.Contains x) : ∃ c∈certificate247.cells, c.region.interval.Contains x := rat_cut_group_covers certificate247 numericValid247 hx

def certificate248 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate165,PopulationCertificates.Batch008.certificate165,[MergedCutCells.Batch079.certificate956,MergedCutCells.Batch079.certificate957,MergedCutCells.Batch079.certificate958],(1864849949614433011/500000000000000000),none,(1/2),(77941487010091857/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid248 : certificate248.NumericValid := by decide +kernel
theorem cellsSound248 : ∀ c∈certificate248.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch079.certificate956,MergedCutCells.Batch079.certificate957,MergedCutCells.Batch079.certificate958], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound956,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound958,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric248 : ∀ c∈certificate248.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch079.certificate956,MergedCutCells.Batch079.certificate957,MergedCutCells.Batch079.certificate958], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid956,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid957,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid958,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid248 : ∀ c∈certificate248.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch079.certificate956,MergedCutCells.Batch079.certificate957,MergedCutCells.Batch079.certificate958], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches248 : ∀ c∈certificate248.cells, c.population=certificate248.population := by
  change ∀ c∈[MergedCutCells.Batch079.certificate956,MergedCutCells.Batch079.certificate957,MergedCutCells.Batch079.certificate958], c.population=PopulationCertificates.Batch008.certificate165
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers248 {x : ℝ} (hx : certificate248.interval.Contains x) : ∃ c∈certificate248.cells, c.region.interval.Contains x := rat_cut_group_covers certificate248 numericValid248 hx

def certificate249 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate166,PopulationCertificates.Batch008.certificate166,[MergedCutCells.Batch079.certificate959,MergedCutCells.Batch080.certificate960,MergedCutCells.Batch080.certificate961,MergedCutCells.Batch080.certificate962,MergedCutCells.Batch080.certificate963,MergedCutCells.Batch080.certificate964,MergedCutCells.Batch080.certificate965,MergedCutCells.Batch080.certificate966,MergedCutCells.Batch080.certificate967],(843649783794459247/1000000000000000000),(some 64),(1/2),(387279271127601129/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1414425235412442589/1000000000000000000))⟩
theorem numericValid249 : certificate249.NumericValid := by decide +kernel
theorem cellsSound249 : ∀ c∈certificate249.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch079.certificate959,MergedCutCells.Batch080.certificate960,MergedCutCells.Batch080.certificate961,MergedCutCells.Batch080.certificate962,MergedCutCells.Batch080.certificate963,MergedCutCells.Batch080.certificate964,MergedCutCells.Batch080.certificate965,MergedCutCells.Batch080.certificate966,MergedCutCells.Batch080.certificate967], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.sound959,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound960,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound961,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound962,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound963,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound965,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound966,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound967,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric249 : ∀ c∈certificate249.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch079.certificate959,MergedCutCells.Batch080.certificate960,MergedCutCells.Batch080.certificate961,MergedCutCells.Batch080.certificate962,MergedCutCells.Batch080.certificate963,MergedCutCells.Batch080.certificate964,MergedCutCells.Batch080.certificate965,MergedCutCells.Batch080.certificate966,MergedCutCells.Batch080.certificate967], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch079.numericValid959,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid960,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid961,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid962,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid963,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid964,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid965,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid966,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid967,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid249 : ∀ c∈certificate249.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch079.certificate959,MergedCutCells.Batch080.certificate960,MergedCutCells.Batch080.certificate961,MergedCutCells.Batch080.certificate962,MergedCutCells.Batch080.certificate963,MergedCutCells.Batch080.certificate964,MergedCutCells.Batch080.certificate965,MergedCutCells.Batch080.certificate966,MergedCutCells.Batch080.certificate967], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid84,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches249 : ∀ c∈certificate249.cells, c.population=certificate249.population := by
  change ∀ c∈[MergedCutCells.Batch079.certificate959,MergedCutCells.Batch080.certificate960,MergedCutCells.Batch080.certificate961,MergedCutCells.Batch080.certificate962,MergedCutCells.Batch080.certificate963,MergedCutCells.Batch080.certificate964,MergedCutCells.Batch080.certificate965,MergedCutCells.Batch080.certificate966,MergedCutCells.Batch080.certificate967], c.population=PopulationCertificates.Batch008.certificate166
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers249 {x : ℝ} (hx : certificate249.interval.Contains x) : ∃ c∈certificate249.cells, c.region.interval.Contains x := rat_cut_group_covers certificate249 numericValid249 hx

def certificate250 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate166,PopulationCertificates.Batch008.certificate166,[MergedCutCells.Batch080.certificate968],64,none,(1/2),(116667930898421643/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid250 : certificate250.NumericValid := by decide +kernel
theorem cellsSound250 : ∀ c∈certificate250.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch080.certificate968], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound968,List.forall_mem_nil _⟩
theorem cellsNumeric250 : ∀ c∈certificate250.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch080.certificate968], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid968,List.forall_mem_nil _⟩
theorem cellsEntropyValid250 : ∀ c∈certificate250.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch080.certificate968], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches250 : ∀ c∈certificate250.cells, c.population=certificate250.population := by
  change ∀ c∈[MergedCutCells.Batch080.certificate968], c.population=PopulationCertificates.Batch008.certificate166
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers250 {x : ℝ} (hx : certificate250.interval.Contains x) : ∃ c∈certificate250.cells, c.region.interval.Contains x := rat_cut_group_covers certificate250 numericValid250 hx

def certificate251 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate167,PopulationCertificates.Batch008.certificate167,[MergedCutCells.Batch080.certificate969,MergedCutCells.Batch080.certificate970,MergedCutCells.Batch080.certificate971,MergedCutCells.Batch081.certificate972],(917427616891112347/250000000000000000),none,(1/2),(324890497871747473/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid251 : certificate251.NumericValid := by decide +kernel
theorem cellsSound251 : ∀ c∈certificate251.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch080.certificate969,MergedCutCells.Batch080.certificate970,MergedCutCells.Batch080.certificate971,MergedCutCells.Batch081.certificate972], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound970,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.sound971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound972,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric251 : ∀ c∈certificate251.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch080.certificate969,MergedCutCells.Batch080.certificate970,MergedCutCells.Batch080.certificate971,MergedCutCells.Batch081.certificate972], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid969,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid970,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch080.numericValid971,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid972,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid251 : ∀ c∈certificate251.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch080.certificate969,MergedCutCells.Batch080.certificate970,MergedCutCells.Batch080.certificate971,MergedCutCells.Batch081.certificate972], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches251 : ∀ c∈certificate251.cells, c.population=certificate251.population := by
  change ∀ c∈[MergedCutCells.Batch080.certificate969,MergedCutCells.Batch080.certificate970,MergedCutCells.Batch080.certificate971,MergedCutCells.Batch081.certificate972], c.population=PopulationCertificates.Batch008.certificate167
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers251 {x : ℝ} (hx : certificate251.interval.Contains x) : ∃ c∈certificate251.cells, c.region.interval.Contains x := rat_cut_group_covers certificate251 numericValid251 hx

end Cycle12.MergedCutGroups.Batch020
