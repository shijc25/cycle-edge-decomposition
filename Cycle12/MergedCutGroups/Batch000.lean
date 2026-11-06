import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch000
import Cycle12.MergedCutCells.Batch000
import Cycle12.MergedCutCells.Batch001
import Cycle12.MergedCutCells.Batch002
import Cycle12.PopulationCertificates.Batch000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch000

def certificate0 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate0,PopulationCertificates.Batch000.certificate0,[MergedCutCells.Batch000.certificate0,MergedCutCells.Batch000.certificate1],(526754133773041959/1000000000000000000),(some (1309610447/1000000000)),(1/2),(132302451142289787/1000000000000000000),(some (10366822029258913/1000000000000000000)),(some (682378239891701/500000000000000000))⟩
theorem numericValid0 : certificate0.NumericValid := by decide +kernel
theorem cellsSound0 : ∀ c∈certificate0.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch000.certificate0,MergedCutCells.Batch000.certificate1], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound0,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound1,List.forall_mem_nil _⟩⟩
theorem cellsNumeric0 : ∀ c∈certificate0.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate0,MergedCutCells.Batch000.certificate1], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid0,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid1,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid0 : ∀ c∈certificate0.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate0,MergedCutCells.Batch000.certificate1], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid0,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid0,List.forall_mem_nil _⟩⟩
theorem populationMatches0 : ∀ c∈certificate0.cells, c.population=certificate0.population := by
  change ∀ c∈[MergedCutCells.Batch000.certificate0,MergedCutCells.Batch000.certificate1], c.population=PopulationCertificates.Batch000.certificate0
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers0 {x : ℝ} (hx : certificate0.interval.Contains x) : ∃ c∈certificate0.cells, c.region.interval.Contains x := rat_cut_group_covers certificate0 numericValid0 hx

def certificate1 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate0,PopulationCertificates.Batch000.certificate0,[MergedCutCells.Batch000.certificate2,MergedCutCells.Batch000.certificate3,MergedCutCells.Batch000.certificate4],(1309610447/1000000000),none,(1/2),(65929795097944263/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1 : certificate1.NumericValid := by decide +kernel
theorem cellsSound1 : ∀ c∈certificate1.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch000.certificate2,MergedCutCells.Batch000.certificate3,MergedCutCells.Batch000.certificate4], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound2,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound3,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound4,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1 : ∀ c∈certificate1.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate2,MergedCutCells.Batch000.certificate3,MergedCutCells.Batch000.certificate4], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid2,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid3,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid4,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1 : ∀ c∈certificate1.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate2,MergedCutCells.Batch000.certificate3,MergedCutCells.Batch000.certificate4], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1 : ∀ c∈certificate1.cells, c.population=certificate1.population := by
  change ∀ c∈[MergedCutCells.Batch000.certificate2,MergedCutCells.Batch000.certificate3,MergedCutCells.Batch000.certificate4], c.population=PopulationCertificates.Batch000.certificate0
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1 {x : ℝ} (hx : certificate1.interval.Contains x) : ∃ c∈certificate1.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1 numericValid1 hx

def certificate2 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate1,PopulationCertificates.Batch000.certificate1,[MergedCutCells.Batch000.certificate5,MergedCutCells.Batch000.certificate6],(3396530379125543999/1000000000000000000),none,(1/2),(15292040964488061/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid2 : certificate2.NumericValid := by decide +kernel
theorem cellsSound2 : ∀ c∈certificate2.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch000.certificate5,MergedCutCells.Batch000.certificate6], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound5,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound6,List.forall_mem_nil _⟩⟩
theorem cellsNumeric2 : ∀ c∈certificate2.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate5,MergedCutCells.Batch000.certificate6], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid5,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid6,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid2 : ∀ c∈certificate2.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate5,MergedCutCells.Batch000.certificate6], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches2 : ∀ c∈certificate2.cells, c.population=certificate2.population := by
  change ∀ c∈[MergedCutCells.Batch000.certificate5,MergedCutCells.Batch000.certificate6], c.population=PopulationCertificates.Batch000.certificate1
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers2 {x : ℝ} (hx : certificate2.interval.Contains x) : ∃ c∈certificate2.cells, c.region.interval.Contains x := rat_cut_group_covers certificate2 numericValid2 hx

def certificate3 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate2,PopulationCertificates.Batch000.certificate2,[MergedCutCells.Batch000.certificate7,MergedCutCells.Batch000.certificate8],(127245632834735863/250000000000000000),(some (649702233/500000000)),(1/2),(39294127764886041/500000000000000000),(some (2848917518928521/500000000000000000)),(some (172008488548027/250000000000000000))⟩
theorem numericValid3 : certificate3.NumericValid := by decide +kernel
theorem cellsSound3 : ∀ c∈certificate3.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch000.certificate7,MergedCutCells.Batch000.certificate8], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound7,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound8,List.forall_mem_nil _⟩⟩
theorem cellsNumeric3 : ∀ c∈certificate3.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate7,MergedCutCells.Batch000.certificate8], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid7,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid8,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid3 : ∀ c∈certificate3.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate7,MergedCutCells.Batch000.certificate8], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid2,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid2,List.forall_mem_nil _⟩⟩
theorem populationMatches3 : ∀ c∈certificate3.cells, c.population=certificate3.population := by
  change ∀ c∈[MergedCutCells.Batch000.certificate7,MergedCutCells.Batch000.certificate8], c.population=PopulationCertificates.Batch000.certificate2
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers3 {x : ℝ} (hx : certificate3.interval.Contains x) : ∃ c∈certificate3.cells, c.region.interval.Contains x := rat_cut_group_covers certificate3 numericValid3 hx

def certificate4 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate2,PopulationCertificates.Batch000.certificate2,[MergedCutCells.Batch000.certificate9,MergedCutCells.Batch000.certificate10,MergedCutCells.Batch000.certificate11],(649702233/500000000),none,(1/2),(39170222563158317/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid4 : certificate4.NumericValid := by decide +kernel
theorem cellsSound4 : ∀ c∈certificate4.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch000.certificate9,MergedCutCells.Batch000.certificate10,MergedCutCells.Batch000.certificate11], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound9,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound10,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.sound11,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric4 : ∀ c∈certificate4.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate9,MergedCutCells.Batch000.certificate10,MergedCutCells.Batch000.certificate11], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid9,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid10,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch000.numericValid11,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid4 : ∀ c∈certificate4.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch000.certificate9,MergedCutCells.Batch000.certificate10,MergedCutCells.Batch000.certificate11], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches4 : ∀ c∈certificate4.cells, c.population=certificate4.population := by
  change ∀ c∈[MergedCutCells.Batch000.certificate9,MergedCutCells.Batch000.certificate10,MergedCutCells.Batch000.certificate11], c.population=PopulationCertificates.Batch000.certificate2
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers4 {x : ℝ} (hx : certificate4.interval.Contains x) : ∃ c∈certificate4.cells, c.region.interval.Contains x := rat_cut_group_covers certificate4 numericValid4 hx

def certificate5 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate3,PopulationCertificates.Batch000.certificate3,[MergedCutCells.Batch001.certificate12,MergedCutCells.Batch001.certificate13],(4881034354796982317/1000000000000000000),none,(1/2),(590814516901912601/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid5 : certificate5.NumericValid := by decide +kernel
theorem cellsSound5 : ∀ c∈certificate5.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch001.certificate12,MergedCutCells.Batch001.certificate13], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound12,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound13,List.forall_mem_nil _⟩⟩
theorem cellsNumeric5 : ∀ c∈certificate5.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate12,MergedCutCells.Batch001.certificate13], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid12,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid13,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid5 : ∀ c∈certificate5.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate12,MergedCutCells.Batch001.certificate13], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches5 : ∀ c∈certificate5.cells, c.population=certificate5.population := by
  change ∀ c∈[MergedCutCells.Batch001.certificate12,MergedCutCells.Batch001.certificate13], c.population=PopulationCertificates.Batch000.certificate3
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers5 {x : ℝ} (hx : certificate5.interval.Contains x) : ∃ c∈certificate5.cells, c.region.interval.Contains x := rat_cut_group_covers certificate5 numericValid5 hx

def certificate6 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate4,PopulationCertificates.Batch000.certificate4,[MergedCutCells.Batch001.certificate14,MergedCutCells.Batch001.certificate15],(568640786208774967/1000000000000000000),(some (1312491441/1000000000)),(1/2),(278893336885000097/1000000000000000000),(some (16945392946271123/1000000000000000000)),(some (60293605624453/25000000000000000))⟩
theorem numericValid6 : certificate6.NumericValid := by decide +kernel
theorem cellsSound6 : ∀ c∈certificate6.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch001.certificate14,MergedCutCells.Batch001.certificate15], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound14,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound15,List.forall_mem_nil _⟩⟩
theorem cellsNumeric6 : ∀ c∈certificate6.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate14,MergedCutCells.Batch001.certificate15], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid14,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid15,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid6 : ∀ c∈certificate6.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate14,MergedCutCells.Batch001.certificate15], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid3,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid3,List.forall_mem_nil _⟩⟩
theorem populationMatches6 : ∀ c∈certificate6.cells, c.population=certificate6.population := by
  change ∀ c∈[MergedCutCells.Batch001.certificate14,MergedCutCells.Batch001.certificate15], c.population=PopulationCertificates.Batch000.certificate4
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers6 {x : ℝ} (hx : certificate6.interval.Contains x) : ∃ c∈certificate6.cells, c.region.interval.Contains x := rat_cut_group_covers certificate6 numericValid6 hx

def certificate7 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate4,PopulationCertificates.Batch000.certificate4,[MergedCutCells.Batch001.certificate16,MergedCutCells.Batch001.certificate17,MergedCutCells.Batch001.certificate18],(1312491441/1000000000),none,(1/2),(138854341844570393/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid7 : certificate7.NumericValid := by decide +kernel
theorem cellsSound7 : ∀ c∈certificate7.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch001.certificate16,MergedCutCells.Batch001.certificate17,MergedCutCells.Batch001.certificate18], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound16,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound17,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound18,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric7 : ∀ c∈certificate7.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate16,MergedCutCells.Batch001.certificate17,MergedCutCells.Batch001.certificate18], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid16,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid17,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid18,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid7 : ∀ c∈certificate7.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate16,MergedCutCells.Batch001.certificate17,MergedCutCells.Batch001.certificate18], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches7 : ∀ c∈certificate7.cells, c.population=certificate7.population := by
  change ∀ c∈[MergedCutCells.Batch001.certificate16,MergedCutCells.Batch001.certificate17,MergedCutCells.Batch001.certificate18], c.population=PopulationCertificates.Batch000.certificate4
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers7 {x : ℝ} (hx : certificate7.interval.Contains x) : ∃ c∈certificate7.cells, c.region.interval.Contains x := rat_cut_group_covers certificate7 numericValid7 hx

def certificate8 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate5,PopulationCertificates.Batch000.certificate5,[MergedCutCells.Batch001.certificate19,MergedCutCells.Batch001.certificate20],(3248235977562722423/1000000000000000000),none,(1/2),(19995601932044001/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid8 : certificate8.NumericValid := by decide +kernel
theorem cellsSound8 : ∀ c∈certificate8.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch001.certificate19,MergedCutCells.Batch001.certificate20], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound19,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound20,List.forall_mem_nil _⟩⟩
theorem cellsNumeric8 : ∀ c∈certificate8.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate19,MergedCutCells.Batch001.certificate20], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid19,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid20,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid8 : ∀ c∈certificate8.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate19,MergedCutCells.Batch001.certificate20], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches8 : ∀ c∈certificate8.cells, c.population=certificate8.population := by
  change ∀ c∈[MergedCutCells.Batch001.certificate19,MergedCutCells.Batch001.certificate20], c.population=PopulationCertificates.Batch000.certificate5
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers8 {x : ℝ} (hx : certificate8.interval.Contains x) : ∃ c∈certificate8.cells, c.region.interval.Contains x := rat_cut_group_covers certificate8 numericValid8 hx

def certificate9 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate6,PopulationCertificates.Batch000.certificate6,[MergedCutCells.Batch001.certificate21,MergedCutCells.Batch001.certificate22],(285221416227561743/500000000000000000),(some (1315913273/1000000000)),(1/2),(275924382801026929/1000000000000000000),(some (3098869330448189/125000000000000000)),(some (3768010709861431/1000000000000000000))⟩
theorem numericValid9 : certificate9.NumericValid := by decide +kernel
theorem cellsSound9 : ∀ c∈certificate9.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch001.certificate21,MergedCutCells.Batch001.certificate22], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound21,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound22,List.forall_mem_nil _⟩⟩
theorem cellsNumeric9 : ∀ c∈certificate9.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate21,MergedCutCells.Batch001.certificate22], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid21,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid22,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid9 : ∀ c∈certificate9.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate21,MergedCutCells.Batch001.certificate22], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid4,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid4,List.forall_mem_nil _⟩⟩
theorem populationMatches9 : ∀ c∈certificate9.cells, c.population=certificate9.population := by
  change ∀ c∈[MergedCutCells.Batch001.certificate21,MergedCutCells.Batch001.certificate22], c.population=PopulationCertificates.Batch000.certificate6
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers9 {x : ℝ} (hx : certificate9.interval.Contains x) : ∃ c∈certificate9.cells, c.region.interval.Contains x := rat_cut_group_covers certificate9 numericValid9 hx

def certificate10 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate6,PopulationCertificates.Batch000.certificate6,[MergedCutCells.Batch001.certificate23,MergedCutCells.Batch002.certificate24,MergedCutCells.Batch002.certificate25],(1315913273/1000000000),none,(1/2),(274860770125611531/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid10 : certificate10.NumericValid := by decide +kernel
theorem cellsSound10 : ∀ c∈certificate10.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch001.certificate23,MergedCutCells.Batch002.certificate24,MergedCutCells.Batch002.certificate25], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.sound23,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound24,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound25,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric10 : ∀ c∈certificate10.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate23,MergedCutCells.Batch002.certificate24,MergedCutCells.Batch002.certificate25], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch001.numericValid23,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid24,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid25,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid10 : ∀ c∈certificate10.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch001.certificate23,MergedCutCells.Batch002.certificate24,MergedCutCells.Batch002.certificate25], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches10 : ∀ c∈certificate10.cells, c.population=certificate10.population := by
  change ∀ c∈[MergedCutCells.Batch001.certificate23,MergedCutCells.Batch002.certificate24,MergedCutCells.Batch002.certificate25], c.population=PopulationCertificates.Batch000.certificate6
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers10 {x : ℝ} (hx : certificate10.interval.Contains x) : ∃ c∈certificate10.cells, c.region.interval.Contains x := rat_cut_group_covers certificate10 numericValid10 hx

def certificate11 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate7,PopulationCertificates.Batch000.certificate7,[MergedCutCells.Batch002.certificate26,MergedCutCells.Batch002.certificate27],(3278349187592359123/1000000000000000000),none,(1/2),(48856603403948443/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid11 : certificate11.NumericValid := by decide +kernel
theorem cellsSound11 : ∀ c∈certificate11.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch002.certificate26,MergedCutCells.Batch002.certificate27], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound26,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound27,List.forall_mem_nil _⟩⟩
theorem cellsNumeric11 : ∀ c∈certificate11.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate26,MergedCutCells.Batch002.certificate27], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid26,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid27,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid11 : ∀ c∈certificate11.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate26,MergedCutCells.Batch002.certificate27], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches11 : ∀ c∈certificate11.cells, c.population=certificate11.population := by
  change ∀ c∈[MergedCutCells.Batch002.certificate26,MergedCutCells.Batch002.certificate27], c.population=PopulationCertificates.Batch000.certificate7
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers11 {x : ℝ} (hx : certificate11.interval.Contains x) : ∃ c∈certificate11.cells, c.region.interval.Contains x := rat_cut_group_covers certificate11 numericValid11 hx

end Cycle12.MergedCutGroups.Batch000
