import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch026
import Cycle12.MergedCutCells.Batch242
import Cycle12.MergedCutCells.Batch243
import Cycle12.MergedCutCells.Batch244
import Cycle12.PopulationCertificates.Batch026

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch065

def certificate780 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate520,PopulationCertificates.Batch026.certificate520,[MergedCutCells.Batch242.certificate2907,MergedCutCells.Batch242.certificate2908],(296693843744298931/500000000000000000),(some (621274459/500000000)),(1/2),(126157221582986273/500000000000000000),(some (16653802895801137/250000000000000000)),(some (2473408530228587/200000000000000000))⟩
theorem numericValid780 : certificate780.NumericValid := by decide +kernel
theorem cellsSound780 : ∀ c∈certificate780.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2907,MergedCutCells.Batch242.certificate2908], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2908,List.forall_mem_nil _⟩⟩
theorem cellsNumeric780 : ∀ c∈certificate780.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2907,MergedCutCells.Batch242.certificate2908], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2907,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2908,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid780 : ∀ c∈certificate780.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2907,MergedCutCells.Batch242.certificate2908], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid261,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid261,List.forall_mem_nil _⟩⟩
theorem populationMatches780 : ∀ c∈certificate780.cells, c.population=certificate780.population := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2907,MergedCutCells.Batch242.certificate2908], c.population=PopulationCertificates.Batch026.certificate520
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers780 {x : ℝ} (hx : certificate780.interval.Contains x) : ∃ c∈certificate780.cells, c.region.interval.Contains x := rat_cut_group_covers certificate780 numericValid780 hx

def certificate781 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate520,PopulationCertificates.Batch026.certificate520,[MergedCutCells.Batch242.certificate2909,MergedCutCells.Batch242.certificate2910,MergedCutCells.Batch242.certificate2911],(621274459/500000000),none,(1/2),(49675580834368743/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid781 : certificate781.NumericValid := by decide +kernel
theorem cellsSound781 : ∀ c∈certificate781.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2909,MergedCutCells.Batch242.certificate2910,MergedCutCells.Batch242.certificate2911], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2909,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2910,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2911,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric781 : ∀ c∈certificate781.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2909,MergedCutCells.Batch242.certificate2910,MergedCutCells.Batch242.certificate2911], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2909,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2910,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2911,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid781 : ∀ c∈certificate781.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2909,MergedCutCells.Batch242.certificate2910,MergedCutCells.Batch242.certificate2911], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches781 : ∀ c∈certificate781.cells, c.population=certificate781.population := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2909,MergedCutCells.Batch242.certificate2910,MergedCutCells.Batch242.certificate2911], c.population=PopulationCertificates.Batch026.certificate520
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers781 {x : ℝ} (hx : certificate781.interval.Contains x) : ∃ c∈certificate781.cells, c.region.interval.Contains x := rat_cut_group_covers certificate781 numericValid781 hx

def certificate782 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate521,PopulationCertificates.Batch026.certificate521,[MergedCutCells.Batch242.certificate2912,MergedCutCells.Batch242.certificate2913],(1073010322479108783/125000000000000000),none,(1/2),(3408006364882044959/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid782 : certificate782.NumericValid := by decide +kernel
theorem cellsSound782 : ∀ c∈certificate782.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2912,MergedCutCells.Batch242.certificate2913], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2913,List.forall_mem_nil _⟩⟩
theorem cellsNumeric782 : ∀ c∈certificate782.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2912,MergedCutCells.Batch242.certificate2913], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2912,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2913,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid782 : ∀ c∈certificate782.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2912,MergedCutCells.Batch242.certificate2913], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches782 : ∀ c∈certificate782.cells, c.population=certificate782.population := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2912,MergedCutCells.Batch242.certificate2913], c.population=PopulationCertificates.Batch026.certificate521
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers782 {x : ℝ} (hx : certificate782.interval.Contains x) : ∃ c∈certificate782.cells, c.region.interval.Contains x := rat_cut_group_covers certificate782 numericValid782 hx

def certificate783 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate522,PopulationCertificates.Batch026.certificate522,[MergedCutCells.Batch242.certificate2914,MergedCutCells.Batch242.certificate2915],(298419710621056299/500000000000000000),(some (190357/156250)),(1/2),(128227159159956283/500000000000000000),(some (71843386774505107/1000000000000000000)),(some (13573807576887401/1000000000000000000))⟩
theorem numericValid783 : certificate783.NumericValid := by decide +kernel
theorem cellsSound783 : ∀ c∈certificate783.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2914,MergedCutCells.Batch242.certificate2915], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.sound2915,List.forall_mem_nil _⟩⟩
theorem cellsNumeric783 : ∀ c∈certificate783.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2914,MergedCutCells.Batch242.certificate2915], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2914,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch242.numericValid2915,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid783 : ∀ c∈certificate783.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2914,MergedCutCells.Batch242.certificate2915], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid262,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid262,List.forall_mem_nil _⟩⟩
theorem populationMatches783 : ∀ c∈certificate783.cells, c.population=certificate783.population := by
  change ∀ c∈[MergedCutCells.Batch242.certificate2914,MergedCutCells.Batch242.certificate2915], c.population=PopulationCertificates.Batch026.certificate522
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers783 {x : ℝ} (hx : certificate783.interval.Contains x) : ∃ c∈certificate783.cells, c.region.interval.Contains x := rat_cut_group_covers certificate783 numericValid783 hx

def certificate784 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate522,PopulationCertificates.Batch026.certificate522,[MergedCutCells.Batch243.certificate2916,MergedCutCells.Batch243.certificate2917,MergedCutCells.Batch243.certificate2918,MergedCutCells.Batch243.certificate2919],(190357/156250),none,(1/2),(25193606512060797/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid784 : certificate784.NumericValid := by decide +kernel
theorem cellsSound784 : ∀ c∈certificate784.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2916,MergedCutCells.Batch243.certificate2917,MergedCutCells.Batch243.certificate2918,MergedCutCells.Batch243.certificate2919], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2916,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2917,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2918,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2919,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric784 : ∀ c∈certificate784.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2916,MergedCutCells.Batch243.certificate2917,MergedCutCells.Batch243.certificate2918,MergedCutCells.Batch243.certificate2919], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2916,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2917,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2918,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2919,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid784 : ∀ c∈certificate784.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2916,MergedCutCells.Batch243.certificate2917,MergedCutCells.Batch243.certificate2918,MergedCutCells.Batch243.certificate2919], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches784 : ∀ c∈certificate784.cells, c.population=certificate784.population := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2916,MergedCutCells.Batch243.certificate2917,MergedCutCells.Batch243.certificate2918,MergedCutCells.Batch243.certificate2919], c.population=PopulationCertificates.Batch026.certificate522
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers784 {x : ℝ} (hx : certificate784.interval.Contains x) : ∃ c∈certificate784.cells, c.region.interval.Contains x := rat_cut_group_covers certificate784 numericValid784 hx

def certificate785 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate523,PopulationCertificates.Batch026.certificate523,[MergedCutCells.Batch243.certificate2920,MergedCutCells.Batch243.certificate2921],(4353332037583947943/500000000000000000),none,(1/2),(1745865606234443719/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid785 : certificate785.NumericValid := by decide +kernel
theorem cellsSound785 : ∀ c∈certificate785.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2920,MergedCutCells.Batch243.certificate2921], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2920,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2921,List.forall_mem_nil _⟩⟩
theorem cellsNumeric785 : ∀ c∈certificate785.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2920,MergedCutCells.Batch243.certificate2921], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2920,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2921,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid785 : ∀ c∈certificate785.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2920,MergedCutCells.Batch243.certificate2921], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches785 : ∀ c∈certificate785.cells, c.population=certificate785.population := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2920,MergedCutCells.Batch243.certificate2921], c.population=PopulationCertificates.Batch026.certificate523
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers785 {x : ℝ} (hx : certificate785.interval.Contains x) : ∃ c∈certificate785.cells, c.region.interval.Contains x := rat_cut_group_covers certificate785 numericValid785 hx

def certificate786 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate524,PopulationCertificates.Batch026.certificate524,[MergedCutCells.Batch243.certificate2922,MergedCutCells.Batch243.certificate2923],(600576015484649707/1000000000000000000),(some (612372399/500000000)),(1/2),(260425172052652073/1000000000000000000),(some (38837372409834951/500000000000000000)),(some (7475185015199797/500000000000000000))⟩
theorem numericValid786 : certificate786.NumericValid := by decide +kernel
theorem cellsSound786 : ∀ c∈certificate786.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2922,MergedCutCells.Batch243.certificate2923], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2922,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2923,List.forall_mem_nil _⟩⟩
theorem cellsNumeric786 : ∀ c∈certificate786.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2922,MergedCutCells.Batch243.certificate2923], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2922,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2923,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid786 : ∀ c∈certificate786.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2922,MergedCutCells.Batch243.certificate2923], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid263,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid263,List.forall_mem_nil _⟩⟩
theorem populationMatches786 : ∀ c∈certificate786.cells, c.population=certificate786.population := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2922,MergedCutCells.Batch243.certificate2923], c.population=PopulationCertificates.Batch026.certificate524
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers786 {x : ℝ} (hx : certificate786.interval.Contains x) : ∃ c∈certificate786.cells, c.region.interval.Contains x := rat_cut_group_covers certificate786 numericValid786 hx

def certificate787 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate524,PopulationCertificates.Batch026.certificate524,[MergedCutCells.Batch243.certificate2924,MergedCutCells.Batch243.certificate2925,MergedCutCells.Batch243.certificate2926],(612372399/500000000),none,(1/2),(255563368327420471/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid787 : certificate787.NumericValid := by decide +kernel
theorem cellsSound787 : ∀ c∈certificate787.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2924,MergedCutCells.Batch243.certificate2925,MergedCutCells.Batch243.certificate2926], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2925,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2926,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric787 : ∀ c∈certificate787.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2924,MergedCutCells.Batch243.certificate2925,MergedCutCells.Batch243.certificate2926], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2924,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2925,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2926,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid787 : ∀ c∈certificate787.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2924,MergedCutCells.Batch243.certificate2925,MergedCutCells.Batch243.certificate2926], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches787 : ∀ c∈certificate787.cells, c.population=certificate787.population := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2924,MergedCutCells.Batch243.certificate2925,MergedCutCells.Batch243.certificate2926], c.population=PopulationCertificates.Batch026.certificate524
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers787 {x : ℝ} (hx : certificate787.interval.Contains x) : ∃ c∈certificate787.cells, c.region.interval.Contains x := rat_cut_group_covers certificate787 numericValid787 hx

def certificate788 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate525,PopulationCertificates.Batch026.certificate525,[MergedCutCells.Batch243.certificate2927,MergedCutCells.Batch244.certificate2928],(4416050031998661749/500000000000000000),none,(1/2),(3577097393352604223/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid788 : certificate788.NumericValid := by decide +kernel
theorem cellsSound788 : ∀ c∈certificate788.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2927,MergedCutCells.Batch244.certificate2928], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.sound2927,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2928,List.forall_mem_nil _⟩⟩
theorem cellsNumeric788 : ∀ c∈certificate788.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2927,MergedCutCells.Batch244.certificate2928], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch243.numericValid2927,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2928,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid788 : ∀ c∈certificate788.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2927,MergedCutCells.Batch244.certificate2928], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches788 : ∀ c∈certificate788.cells, c.population=certificate788.population := by
  change ∀ c∈[MergedCutCells.Batch243.certificate2927,MergedCutCells.Batch244.certificate2928], c.population=PopulationCertificates.Batch026.certificate525
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers788 {x : ℝ} (hx : certificate788.interval.Contains x) : ∃ c∈certificate788.cells, c.region.interval.Contains x := rat_cut_group_covers certificate788 numericValid788 hx

def certificate789 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate526,PopulationCertificates.Batch026.certificate526,[MergedCutCells.Batch244.certificate2929,MergedCutCells.Batch244.certificate2930],(30220957676620169/50000000000000000),(some (602954831/500000000)),(1/2),(6632579144504503/25000000000000000),(some (83261796008482873/1000000000000000000)),(some (8149384047522589/500000000000000000))⟩
theorem numericValid789 : certificate789.NumericValid := by decide +kernel
theorem cellsSound789 : ∀ c∈certificate789.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2929,MergedCutCells.Batch244.certificate2930], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2930,List.forall_mem_nil _⟩⟩
theorem cellsNumeric789 : ∀ c∈certificate789.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2929,MergedCutCells.Batch244.certificate2930], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2929,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2930,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid789 : ∀ c∈certificate789.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2929,MergedCutCells.Batch244.certificate2930], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid264,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid264,List.forall_mem_nil _⟩⟩
theorem populationMatches789 : ∀ c∈certificate789.cells, c.population=certificate789.population := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2929,MergedCutCells.Batch244.certificate2930], c.population=PopulationCertificates.Batch026.certificate526
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers789 {x : ℝ} (hx : certificate789.interval.Contains x) : ∃ c∈certificate789.cells, c.region.interval.Contains x := rat_cut_group_covers certificate789 numericValid789 hx

def certificate790 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate526,PopulationCertificates.Batch026.certificate526,[MergedCutCells.Batch244.certificate2931,MergedCutCells.Batch244.certificate2932,MergedCutCells.Batch244.certificate2933,MergedCutCells.Batch244.certificate2934,MergedCutCells.Batch244.certificate2935],(602954831/500000000),none,(1/2),(259319957816592661/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid790 : certificate790.NumericValid := by decide +kernel
theorem cellsSound790 : ∀ c∈certificate790.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2931,MergedCutCells.Batch244.certificate2932,MergedCutCells.Batch244.certificate2933,MergedCutCells.Batch244.certificate2934,MergedCutCells.Batch244.certificate2935], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2931,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2932,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2934,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2935,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric790 : ∀ c∈certificate790.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2931,MergedCutCells.Batch244.certificate2932,MergedCutCells.Batch244.certificate2933,MergedCutCells.Batch244.certificate2934,MergedCutCells.Batch244.certificate2935], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2931,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2932,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2933,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2934,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2935,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid790 : ∀ c∈certificate790.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2931,MergedCutCells.Batch244.certificate2932,MergedCutCells.Batch244.certificate2933,MergedCutCells.Batch244.certificate2934,MergedCutCells.Batch244.certificate2935], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches790 : ∀ c∈certificate790.cells, c.population=certificate790.population := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2931,MergedCutCells.Batch244.certificate2932,MergedCutCells.Batch244.certificate2933,MergedCutCells.Batch244.certificate2934,MergedCutCells.Batch244.certificate2935], c.population=PopulationCertificates.Batch026.certificate526
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers790 {x : ℝ} (hx : certificate790.interval.Contains x) : ∃ c∈certificate790.cells, c.region.interval.Contains x := rat_cut_group_covers certificate790 numericValid790 hx

def certificate791 : RatCutGroup := ⟨GeometryCertificates.Batch026.certificate527,PopulationCertificates.Batch026.certificate527,[MergedCutCells.Batch244.certificate2936,MergedCutCells.Batch244.certificate2937],(1767539082226980097/200000000000000000),none,(1/2),(362823575854616167/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid791 : certificate791.NumericValid := by decide +kernel
theorem cellsSound791 : ∀ c∈certificate791.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2936,MergedCutCells.Batch244.certificate2937], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2936,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.sound2937,List.forall_mem_nil _⟩⟩
theorem cellsNumeric791 : ∀ c∈certificate791.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2936,MergedCutCells.Batch244.certificate2937], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2936,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch244.numericValid2937,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid791 : ∀ c∈certificate791.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2936,MergedCutCells.Batch244.certificate2937], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches791 : ∀ c∈certificate791.cells, c.population=certificate791.population := by
  change ∀ c∈[MergedCutCells.Batch244.certificate2936,MergedCutCells.Batch244.certificate2937], c.population=PopulationCertificates.Batch026.certificate527
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers791 {x : ℝ} (hx : certificate791.interval.Contains x) : ∃ c∈certificate791.cells, c.region.interval.Contains x := rat_cut_group_covers certificate791 numericValid791 hx

end Cycle12.MergedCutGroups.Batch065
