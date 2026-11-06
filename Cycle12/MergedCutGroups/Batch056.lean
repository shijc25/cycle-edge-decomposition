import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch022
import Cycle12.MergedCutCells.Batch212
import Cycle12.MergedCutCells.Batch213
import Cycle12.MergedCutCells.Batch214
import Cycle12.MergedCutCells.Batch215
import Cycle12.MergedCutCells.Batch216
import Cycle12.PopulationCertificates.Batch022

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch056

def certificate672 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate448,PopulationCertificates.Batch022.certificate448,[MergedCutCells.Batch212.certificate2552,MergedCutCells.Batch212.certificate2553],(907989179049195641/1000000000000000000),(some (3054771/3125000)),(1/2),(322045426435068037/200000000000000000),(some (140918970382904507/250000000000000000)),(some (7850750751799163/31250000000000000))⟩
theorem numericValid672 : certificate672.NumericValid := by decide +kernel
theorem cellsSound672 : ∀ c∈certificate672.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2552,MergedCutCells.Batch212.certificate2553], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2552,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2553,List.forall_mem_nil _⟩⟩
theorem cellsNumeric672 : ∀ c∈certificate672.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2552,MergedCutCells.Batch212.certificate2553], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2552,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2553,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid672 : ∀ c∈certificate672.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2552,MergedCutCells.Batch212.certificate2553], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid225,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid225,List.forall_mem_nil _⟩⟩
theorem populationMatches672 : ∀ c∈certificate672.cells, c.population=certificate672.population := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2552,MergedCutCells.Batch212.certificate2553], c.population=PopulationCertificates.Batch022.certificate448
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers672 {x : ℝ} (hx : certificate672.interval.Contains x) : ∃ c∈certificate672.cells, c.region.interval.Contains x := rat_cut_group_covers certificate672 numericValid672 hx

def certificate673 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate448,PopulationCertificates.Batch022.certificate448,[MergedCutCells.Batch212.certificate2554,MergedCutCells.Batch212.certificate2555,MergedCutCells.Batch213.certificate2556,MergedCutCells.Batch213.certificate2557,MergedCutCells.Batch213.certificate2558,MergedCutCells.Batch213.certificate2559,MergedCutCells.Batch213.certificate2560],(3054771/3125000),none,(1/2),(1524072464261919413/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid673 : certificate673.NumericValid := by decide +kernel
theorem cellsSound673 : ∀ c∈certificate673.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2554,MergedCutCells.Batch212.certificate2555,MergedCutCells.Batch213.certificate2556,MergedCutCells.Batch213.certificate2557,MergedCutCells.Batch213.certificate2558,MergedCutCells.Batch213.certificate2559,MergedCutCells.Batch213.certificate2560], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2554,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2555,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2556,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2558,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2560,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric673 : ∀ c∈certificate673.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2554,MergedCutCells.Batch212.certificate2555,MergedCutCells.Batch213.certificate2556,MergedCutCells.Batch213.certificate2557,MergedCutCells.Batch213.certificate2558,MergedCutCells.Batch213.certificate2559,MergedCutCells.Batch213.certificate2560], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2554,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2555,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2556,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2558,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2560,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid673 : ∀ c∈certificate673.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2554,MergedCutCells.Batch212.certificate2555,MergedCutCells.Batch213.certificate2556,MergedCutCells.Batch213.certificate2557,MergedCutCells.Batch213.certificate2558,MergedCutCells.Batch213.certificate2559,MergedCutCells.Batch213.certificate2560], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches673 : ∀ c∈certificate673.cells, c.population=certificate673.population := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2554,MergedCutCells.Batch212.certificate2555,MergedCutCells.Batch213.certificate2556,MergedCutCells.Batch213.certificate2557,MergedCutCells.Batch213.certificate2558,MergedCutCells.Batch213.certificate2559,MergedCutCells.Batch213.certificate2560], c.population=PopulationCertificates.Batch022.certificate448
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers673 {x : ℝ} (hx : certificate673.interval.Contains x) : ∃ c∈certificate673.cells, c.region.interval.Contains x := rat_cut_group_covers certificate673 numericValid673 hx

def certificate674 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate449,PopulationCertificates.Batch022.certificate449,[MergedCutCells.Batch213.certificate2561,MergedCutCells.Batch213.certificate2562,MergedCutCells.Batch213.certificate2563,MergedCutCells.Batch213.certificate2564],(5145515082482123857/1000000000000000000),none,(1/2),(3879698087520305993/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid674 : certificate674.NumericValid := by decide +kernel
theorem cellsSound674 : ∀ c∈certificate674.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2561,MergedCutCells.Batch213.certificate2562,MergedCutCells.Batch213.certificate2563,MergedCutCells.Batch213.certificate2564], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2561,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2562,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2563,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2564,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric674 : ∀ c∈certificate674.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2561,MergedCutCells.Batch213.certificate2562,MergedCutCells.Batch213.certificate2563,MergedCutCells.Batch213.certificate2564], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2561,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2562,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2563,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2564,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid674 : ∀ c∈certificate674.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2561,MergedCutCells.Batch213.certificate2562,MergedCutCells.Batch213.certificate2563,MergedCutCells.Batch213.certificate2564], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches674 : ∀ c∈certificate674.cells, c.population=certificate674.population := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2561,MergedCutCells.Batch213.certificate2562,MergedCutCells.Batch213.certificate2563,MergedCutCells.Batch213.certificate2564], c.population=PopulationCertificates.Batch022.certificate449
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers674 {x : ℝ} (hx : certificate674.interval.Contains x) : ∃ c∈certificate674.cells, c.region.interval.Contains x := rat_cut_group_covers certificate674 numericValid674 hx

def certificate675 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate450,PopulationCertificates.Batch022.certificate450,[MergedCutCells.Batch213.certificate2565,MergedCutCells.Batch213.certificate2566],(912548605155016873/1000000000000000000),(some (245587499/250000000)),(1/2),(836132773497370033/500000000000000000),(some (568720795341341907/1000000000000000000)),(some (127948212791773477/500000000000000000))⟩
theorem numericValid675 : certificate675.NumericValid := by decide +kernel
theorem cellsSound675 : ∀ c∈certificate675.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2565,MergedCutCells.Batch213.certificate2566], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2566,List.forall_mem_nil _⟩⟩
theorem cellsNumeric675 : ∀ c∈certificate675.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2565,MergedCutCells.Batch213.certificate2566], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2566,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid675 : ∀ c∈certificate675.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2565,MergedCutCells.Batch213.certificate2566], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid226,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid226,List.forall_mem_nil _⟩⟩
theorem populationMatches675 : ∀ c∈certificate675.cells, c.population=certificate675.population := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2565,MergedCutCells.Batch213.certificate2566], c.population=PopulationCertificates.Batch022.certificate450
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers675 {x : ℝ} (hx : certificate675.interval.Contains x) : ∃ c∈certificate675.cells, c.region.interval.Contains x := rat_cut_group_covers certificate675 numericValid675 hx

def certificate676 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate450,PopulationCertificates.Batch022.certificate450,[MergedCutCells.Batch213.certificate2567,MergedCutCells.Batch214.certificate2568,MergedCutCells.Batch214.certificate2569,MergedCutCells.Batch214.certificate2570,MergedCutCells.Batch214.certificate2571,MergedCutCells.Batch214.certificate2572],(245587499/250000000),none,(1/2),(1581349226825694381/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid676 : certificate676.NumericValid := by decide +kernel
theorem cellsSound676 : ∀ c∈certificate676.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2567,MergedCutCells.Batch214.certificate2568,MergedCutCells.Batch214.certificate2569,MergedCutCells.Batch214.certificate2570,MergedCutCells.Batch214.certificate2571,MergedCutCells.Batch214.certificate2572], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.sound2567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2568,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2569,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2571,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2572,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric676 : ∀ c∈certificate676.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2567,MergedCutCells.Batch214.certificate2568,MergedCutCells.Batch214.certificate2569,MergedCutCells.Batch214.certificate2570,MergedCutCells.Batch214.certificate2571,MergedCutCells.Batch214.certificate2572], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch213.numericValid2567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2568,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2569,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2571,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2572,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid676 : ∀ c∈certificate676.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2567,MergedCutCells.Batch214.certificate2568,MergedCutCells.Batch214.certificate2569,MergedCutCells.Batch214.certificate2570,MergedCutCells.Batch214.certificate2571,MergedCutCells.Batch214.certificate2572], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches676 : ∀ c∈certificate676.cells, c.population=certificate676.population := by
  change ∀ c∈[MergedCutCells.Batch213.certificate2567,MergedCutCells.Batch214.certificate2568,MergedCutCells.Batch214.certificate2569,MergedCutCells.Batch214.certificate2570,MergedCutCells.Batch214.certificate2571,MergedCutCells.Batch214.certificate2572], c.population=PopulationCertificates.Batch022.certificate450
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers676 {x : ℝ} (hx : certificate676.interval.Contains x) : ∃ c∈certificate676.cells, c.region.interval.Contains x := rat_cut_group_covers certificate676 numericValid676 hx

def certificate677 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate451,PopulationCertificates.Batch022.certificate451,[MergedCutCells.Batch214.certificate2573,MergedCutCells.Batch214.certificate2574,MergedCutCells.Batch214.certificate2575,MergedCutCells.Batch214.certificate2576],(1284104197680929531/250000000000000000),none,(1/2),(493116741701802893/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid677 : certificate677.NumericValid := by decide +kernel
theorem cellsSound677 : ∀ c∈certificate677.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2573,MergedCutCells.Batch214.certificate2574,MergedCutCells.Batch214.certificate2575,MergedCutCells.Batch214.certificate2576], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2573,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2574,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2575,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2576,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric677 : ∀ c∈certificate677.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2573,MergedCutCells.Batch214.certificate2574,MergedCutCells.Batch214.certificate2575,MergedCutCells.Batch214.certificate2576], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2573,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2574,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2575,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2576,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid677 : ∀ c∈certificate677.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2573,MergedCutCells.Batch214.certificate2574,MergedCutCells.Batch214.certificate2575,MergedCutCells.Batch214.certificate2576], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches677 : ∀ c∈certificate677.cells, c.population=certificate677.population := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2573,MergedCutCells.Batch214.certificate2574,MergedCutCells.Batch214.certificate2575,MergedCutCells.Batch214.certificate2576], c.population=PopulationCertificates.Batch022.certificate451
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers677 {x : ℝ} (hx : certificate677.interval.Contains x) : ∃ c∈certificate677.cells, c.region.interval.Contains x := rat_cut_group_covers certificate677 numericValid677 hx

def certificate678 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate452,PopulationCertificates.Batch022.certificate452,[MergedCutCells.Batch214.certificate2577,MergedCutCells.Batch214.certificate2578],(915128588044111733/1000000000000000000),(some (197015819/200000000)),(1/2),(1709261848707064477/1000000000000000000),(some (574341720424585277/1000000000000000000)),(some (261232106247669603/1000000000000000000))⟩
theorem numericValid678 : certificate678.NumericValid := by decide +kernel
theorem cellsSound678 : ∀ c∈certificate678.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2577,MergedCutCells.Batch214.certificate2578], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2577,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2578,List.forall_mem_nil _⟩⟩
theorem cellsNumeric678 : ∀ c∈certificate678.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2577,MergedCutCells.Batch214.certificate2578], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2577,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2578,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid678 : ∀ c∈certificate678.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2577,MergedCutCells.Batch214.certificate2578], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid227,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid227,List.forall_mem_nil _⟩⟩
theorem populationMatches678 : ∀ c∈certificate678.cells, c.population=certificate678.population := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2577,MergedCutCells.Batch214.certificate2578], c.population=PopulationCertificates.Batch022.certificate452
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers678 {x : ℝ} (hx : certificate678.interval.Contains x) : ∃ c∈certificate678.cells, c.region.interval.Contains x := rat_cut_group_covers certificate678 numericValid678 hx

def certificate679 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate452,PopulationCertificates.Batch022.certificate452,[MergedCutCells.Batch214.certificate2579,MergedCutCells.Batch215.certificate2580,MergedCutCells.Batch215.certificate2581,MergedCutCells.Batch215.certificate2582,MergedCutCells.Batch215.certificate2583,MergedCutCells.Batch215.certificate2584],(197015819/200000000),none,(1/2),(810612267971431097/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid679 : certificate679.NumericValid := by decide +kernel
theorem cellsSound679 : ∀ c∈certificate679.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2579,MergedCutCells.Batch215.certificate2580,MergedCutCells.Batch215.certificate2581,MergedCutCells.Batch215.certificate2582,MergedCutCells.Batch215.certificate2583,MergedCutCells.Batch215.certificate2584], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.sound2579,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2580,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2581,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2583,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2584,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric679 : ∀ c∈certificate679.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2579,MergedCutCells.Batch215.certificate2580,MergedCutCells.Batch215.certificate2581,MergedCutCells.Batch215.certificate2582,MergedCutCells.Batch215.certificate2583,MergedCutCells.Batch215.certificate2584], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch214.numericValid2579,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2580,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2581,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2582,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2583,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2584,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid679 : ∀ c∈certificate679.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2579,MergedCutCells.Batch215.certificate2580,MergedCutCells.Batch215.certificate2581,MergedCutCells.Batch215.certificate2582,MergedCutCells.Batch215.certificate2583,MergedCutCells.Batch215.certificate2584], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches679 : ∀ c∈certificate679.cells, c.population=certificate679.population := by
  change ∀ c∈[MergedCutCells.Batch214.certificate2579,MergedCutCells.Batch215.certificate2580,MergedCutCells.Batch215.certificate2581,MergedCutCells.Batch215.certificate2582,MergedCutCells.Batch215.certificate2583,MergedCutCells.Batch215.certificate2584], c.population=PopulationCertificates.Batch022.certificate452
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers679 {x : ℝ} (hx : certificate679.interval.Contains x) : ∃ c∈certificate679.cells, c.region.interval.Contains x := rat_cut_group_covers certificate679 numericValid679 hx

def certificate680 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate453,PopulationCertificates.Batch022.certificate453,[MergedCutCells.Batch215.certificate2585,MergedCutCells.Batch215.certificate2586,MergedCutCells.Batch215.certificate2587,MergedCutCells.Batch215.certificate2588],(634123955301402821/125000000000000000),none,(1/2),(392868640312067479/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid680 : certificate680.NumericValid := by decide +kernel
theorem cellsSound680 : ∀ c∈certificate680.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2585,MergedCutCells.Batch215.certificate2586,MergedCutCells.Batch215.certificate2587,MergedCutCells.Batch215.certificate2588], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2585,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2586,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2587,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2588,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric680 : ∀ c∈certificate680.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2585,MergedCutCells.Batch215.certificate2586,MergedCutCells.Batch215.certificate2587,MergedCutCells.Batch215.certificate2588], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2585,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2586,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2587,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2588,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid680 : ∀ c∈certificate680.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2585,MergedCutCells.Batch215.certificate2586,MergedCutCells.Batch215.certificate2587,MergedCutCells.Batch215.certificate2588], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches680 : ∀ c∈certificate680.cells, c.population=certificate680.population := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2585,MergedCutCells.Batch215.certificate2586,MergedCutCells.Batch215.certificate2587,MergedCutCells.Batch215.certificate2588], c.population=PopulationCertificates.Batch022.certificate453
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers680 {x : ℝ} (hx : certificate680.interval.Contains x) : ∃ c∈certificate680.cells, c.region.interval.Contains x := rat_cut_group_covers certificate680 numericValid680 hx

def certificate681 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate454,PopulationCertificates.Batch022.certificate454,[MergedCutCells.Batch215.certificate2589,MergedCutCells.Batch215.certificate2590],(923342549539317877/1000000000000000000),(some (242497747/250000000)),(1/2),(449353570278274563/250000000000000000),(some (577227346531689103/1000000000000000000)),(some (52805461933532023/200000000000000000))⟩
theorem numericValid681 : certificate681.NumericValid := by decide +kernel
theorem cellsSound681 : ∀ c∈certificate681.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2589,MergedCutCells.Batch215.certificate2590], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2590,List.forall_mem_nil _⟩⟩
theorem cellsNumeric681 : ∀ c∈certificate681.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2589,MergedCutCells.Batch215.certificate2590], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2589,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2590,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid681 : ∀ c∈certificate681.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2589,MergedCutCells.Batch215.certificate2590], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid228,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid228,List.forall_mem_nil _⟩⟩
theorem populationMatches681 : ∀ c∈certificate681.cells, c.population=certificate681.population := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2589,MergedCutCells.Batch215.certificate2590], c.population=PopulationCertificates.Batch022.certificate454
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers681 {x : ℝ} (hx : certificate681.interval.Contains x) : ∃ c∈certificate681.cells, c.region.interval.Contains x := rat_cut_group_covers certificate681 numericValid681 hx

def certificate682 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate454,PopulationCertificates.Batch022.certificate454,[MergedCutCells.Batch215.certificate2591,MergedCutCells.Batch216.certificate2592,MergedCutCells.Batch216.certificate2593,MergedCutCells.Batch216.certificate2594,MergedCutCells.Batch216.certificate2595,MergedCutCells.Batch216.certificate2596,MergedCutCells.Batch216.certificate2597],(242497747/250000000),none,(1/2),(83942692240915189/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid682 : certificate682.NumericValid := by decide +kernel
theorem cellsSound682 : ∀ c∈certificate682.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2591,MergedCutCells.Batch216.certificate2592,MergedCutCells.Batch216.certificate2593,MergedCutCells.Batch216.certificate2594,MergedCutCells.Batch216.certificate2595,MergedCutCells.Batch216.certificate2596,MergedCutCells.Batch216.certificate2597], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.sound2591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2593,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2594,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2596,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2597,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric682 : ∀ c∈certificate682.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2591,MergedCutCells.Batch216.certificate2592,MergedCutCells.Batch216.certificate2593,MergedCutCells.Batch216.certificate2594,MergedCutCells.Batch216.certificate2595,MergedCutCells.Batch216.certificate2596,MergedCutCells.Batch216.certificate2597], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch215.numericValid2591,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2592,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2593,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2594,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2595,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2596,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2597,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid682 : ∀ c∈certificate682.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2591,MergedCutCells.Batch216.certificate2592,MergedCutCells.Batch216.certificate2593,MergedCutCells.Batch216.certificate2594,MergedCutCells.Batch216.certificate2595,MergedCutCells.Batch216.certificate2596,MergedCutCells.Batch216.certificate2597], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches682 : ∀ c∈certificate682.cells, c.population=certificate682.population := by
  change ∀ c∈[MergedCutCells.Batch215.certificate2591,MergedCutCells.Batch216.certificate2592,MergedCutCells.Batch216.certificate2593,MergedCutCells.Batch216.certificate2594,MergedCutCells.Batch216.certificate2595,MergedCutCells.Batch216.certificate2596,MergedCutCells.Batch216.certificate2597], c.population=PopulationCertificates.Batch022.certificate454
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers682 {x : ℝ} (hx : certificate682.interval.Contains x) : ∃ c∈certificate682.cells, c.region.interval.Contains x := rat_cut_group_covers certificate682 numericValid682 hx

def certificate683 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate455,PopulationCertificates.Batch022.certificate455,[MergedCutCells.Batch216.certificate2598,MergedCutCells.Batch216.certificate2599,MergedCutCells.Batch216.certificate2600],(2531943457363765793/500000000000000000),none,(1/2),(3994595730356778981/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid683 : certificate683.NumericValid := by decide +kernel
theorem cellsSound683 : ∀ c∈certificate683.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2598,MergedCutCells.Batch216.certificate2599,MergedCutCells.Batch216.certificate2600], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2599,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.sound2600,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric683 : ∀ c∈certificate683.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2598,MergedCutCells.Batch216.certificate2599,MergedCutCells.Batch216.certificate2600], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2598,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2599,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch216.numericValid2600,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid683 : ∀ c∈certificate683.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2598,MergedCutCells.Batch216.certificate2599,MergedCutCells.Batch216.certificate2600], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches683 : ∀ c∈certificate683.cells, c.population=certificate683.population := by
  change ∀ c∈[MergedCutCells.Batch216.certificate2598,MergedCutCells.Batch216.certificate2599,MergedCutCells.Batch216.certificate2600], c.population=PopulationCertificates.Batch022.certificate455
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers683 {x : ℝ} (hx : certificate683.interval.Contains x) : ∃ c∈certificate683.cells, c.region.interval.Contains x := rat_cut_group_covers certificate683 numericValid683 hx

end Cycle12.MergedCutGroups.Batch056
