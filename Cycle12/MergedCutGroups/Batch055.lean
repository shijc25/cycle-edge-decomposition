import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch022
import Cycle12.MergedCutCells.Batch208
import Cycle12.MergedCutCells.Batch209
import Cycle12.MergedCutCells.Batch210
import Cycle12.MergedCutCells.Batch211
import Cycle12.MergedCutCells.Batch212
import Cycle12.PopulationCertificates.Batch022

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch055

def certificate660 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate440,PopulationCertificates.Batch022.certificate440,[MergedCutCells.Batch208.certificate2500,MergedCutCells.Batch208.certificate2501],(883901523125844273/1000000000000000000),(some (195068593/200000000)),(1/2),(1311467175659059253/1000000000000000000),(some (529299966928714459/1000000000000000000)),(some (27737274475923557/125000000000000000))⟩
theorem numericValid660 : certificate660.NumericValid := by decide +kernel
theorem cellsSound660 : ∀ c∈certificate660.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2500,MergedCutCells.Batch208.certificate2501], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2500,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2501,List.forall_mem_nil _⟩⟩
theorem cellsNumeric660 : ∀ c∈certificate660.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2500,MergedCutCells.Batch208.certificate2501], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2500,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2501,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid660 : ∀ c∈certificate660.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2500,MergedCutCells.Batch208.certificate2501], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid221,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid221,List.forall_mem_nil _⟩⟩
theorem populationMatches660 : ∀ c∈certificate660.cells, c.population=certificate660.population := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2500,MergedCutCells.Batch208.certificate2501], c.population=PopulationCertificates.Batch022.certificate440
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers660 {x : ℝ} (hx : certificate660.interval.Contains x) : ∃ c∈certificate660.cells, c.region.interval.Contains x := rat_cut_group_covers certificate660 numericValid660 hx

def certificate661 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate440,PopulationCertificates.Batch022.certificate440,[MergedCutCells.Batch208.certificate2502,MergedCutCells.Batch208.certificate2503,MergedCutCells.Batch208.certificate2504,MergedCutCells.Batch208.certificate2505,MergedCutCells.Batch208.certificate2506,MergedCutCells.Batch208.certificate2507,MergedCutCells.Batch209.certificate2508],(195068593/200000000),none,(1/2),(151988956115187127/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid661 : certificate661.NumericValid := by decide +kernel
theorem cellsSound661 : ∀ c∈certificate661.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2502,MergedCutCells.Batch208.certificate2503,MergedCutCells.Batch208.certificate2504,MergedCutCells.Batch208.certificate2505,MergedCutCells.Batch208.certificate2506,MergedCutCells.Batch208.certificate2507,MergedCutCells.Batch209.certificate2508], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2504,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2505,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.sound2507,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2508,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric661 : ∀ c∈certificate661.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2502,MergedCutCells.Batch208.certificate2503,MergedCutCells.Batch208.certificate2504,MergedCutCells.Batch208.certificate2505,MergedCutCells.Batch208.certificate2506,MergedCutCells.Batch208.certificate2507,MergedCutCells.Batch209.certificate2508], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2504,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2505,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch208.numericValid2507,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2508,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid661 : ∀ c∈certificate661.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2502,MergedCutCells.Batch208.certificate2503,MergedCutCells.Batch208.certificate2504,MergedCutCells.Batch208.certificate2505,MergedCutCells.Batch208.certificate2506,MergedCutCells.Batch208.certificate2507,MergedCutCells.Batch209.certificate2508], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches661 : ∀ c∈certificate661.cells, c.population=certificate661.population := by
  change ∀ c∈[MergedCutCells.Batch208.certificate2502,MergedCutCells.Batch208.certificate2503,MergedCutCells.Batch208.certificate2504,MergedCutCells.Batch208.certificate2505,MergedCutCells.Batch208.certificate2506,MergedCutCells.Batch208.certificate2507,MergedCutCells.Batch209.certificate2508], c.population=PopulationCertificates.Batch022.certificate440
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers661 {x : ℝ} (hx : certificate661.interval.Contains x) : ∃ c∈certificate661.cells, c.region.interval.Contains x := rat_cut_group_covers certificate661 numericValid661 hx

def certificate662 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate441,PopulationCertificates.Batch022.certificate441,[MergedCutCells.Batch209.certificate2509,MergedCutCells.Batch209.certificate2510,MergedCutCells.Batch209.certificate2511,MergedCutCells.Batch209.certificate2512],(21446358079377297/4000000000000000),none,(1/2),(3686502654664367899/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid662 : certificate662.NumericValid := by decide +kernel
theorem cellsSound662 : ∀ c∈certificate662.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2509,MergedCutCells.Batch209.certificate2510,MergedCutCells.Batch209.certificate2511,MergedCutCells.Batch209.certificate2512], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2509,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2510,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2512,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric662 : ∀ c∈certificate662.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2509,MergedCutCells.Batch209.certificate2510,MergedCutCells.Batch209.certificate2511,MergedCutCells.Batch209.certificate2512], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2509,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2510,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2512,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid662 : ∀ c∈certificate662.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2509,MergedCutCells.Batch209.certificate2510,MergedCutCells.Batch209.certificate2511,MergedCutCells.Batch209.certificate2512], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches662 : ∀ c∈certificate662.cells, c.population=certificate662.population := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2509,MergedCutCells.Batch209.certificate2510,MergedCutCells.Batch209.certificate2511,MergedCutCells.Batch209.certificate2512], c.population=PopulationCertificates.Batch022.certificate441
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers662 {x : ℝ} (hx : certificate662.interval.Contains x) : ∃ c∈certificate662.cells, c.region.interval.Contains x := rat_cut_group_covers certificate662 numericValid662 hx

def certificate663 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate442,PopulationCertificates.Batch022.certificate442,[MergedCutCells.Batch209.certificate2513,MergedCutCells.Batch209.certificate2514],(886129957040676547/1000000000000000000),(some (977745337/1000000000)),(1/2),(1331332054460966381/1000000000000000000),(some (33749266335990587/62500000000000000)),(some (28823749839926329/125000000000000000))⟩
theorem numericValid663 : certificate663.NumericValid := by decide +kernel
theorem cellsSound663 : ∀ c∈certificate663.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2513,MergedCutCells.Batch209.certificate2514], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2513,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2514,List.forall_mem_nil _⟩⟩
theorem cellsNumeric663 : ∀ c∈certificate663.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2513,MergedCutCells.Batch209.certificate2514], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2513,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2514,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid663 : ∀ c∈certificate663.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2513,MergedCutCells.Batch209.certificate2514], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid222,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid222,List.forall_mem_nil _⟩⟩
theorem populationMatches663 : ∀ c∈certificate663.cells, c.population=certificate663.population := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2513,MergedCutCells.Batch209.certificate2514], c.population=PopulationCertificates.Batch022.certificate442
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers663 {x : ℝ} (hx : certificate663.interval.Contains x) : ∃ c∈certificate663.cells, c.region.interval.Contains x := rat_cut_group_covers certificate663 numericValid663 hx

def certificate664 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate442,PopulationCertificates.Batch022.certificate442,[MergedCutCells.Batch209.certificate2515,MergedCutCells.Batch209.certificate2516,MergedCutCells.Batch209.certificate2517,MergedCutCells.Batch209.certificate2518,MergedCutCells.Batch209.certificate2519,MergedCutCells.Batch210.certificate2520,MergedCutCells.Batch210.certificate2521],(977745337/1000000000),none,(1/2),(250173461924633759/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid664 : certificate664.NumericValid := by decide +kernel
theorem cellsSound664 : ∀ c∈certificate664.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2515,MergedCutCells.Batch209.certificate2516,MergedCutCells.Batch209.certificate2517,MergedCutCells.Batch209.certificate2518,MergedCutCells.Batch209.certificate2519,MergedCutCells.Batch210.certificate2520,MergedCutCells.Batch210.certificate2521], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2515,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2516,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2517,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2518,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.sound2519,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2520,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2521,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric664 : ∀ c∈certificate664.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2515,MergedCutCells.Batch209.certificate2516,MergedCutCells.Batch209.certificate2517,MergedCutCells.Batch209.certificate2518,MergedCutCells.Batch209.certificate2519,MergedCutCells.Batch210.certificate2520,MergedCutCells.Batch210.certificate2521], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2515,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2516,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2517,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2518,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch209.numericValid2519,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2520,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2521,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid664 : ∀ c∈certificate664.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2515,MergedCutCells.Batch209.certificate2516,MergedCutCells.Batch209.certificate2517,MergedCutCells.Batch209.certificate2518,MergedCutCells.Batch209.certificate2519,MergedCutCells.Batch210.certificate2520,MergedCutCells.Batch210.certificate2521], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches664 : ∀ c∈certificate664.cells, c.population=certificate664.population := by
  change ∀ c∈[MergedCutCells.Batch209.certificate2515,MergedCutCells.Batch209.certificate2516,MergedCutCells.Batch209.certificate2517,MergedCutCells.Batch209.certificate2518,MergedCutCells.Batch209.certificate2519,MergedCutCells.Batch210.certificate2520,MergedCutCells.Batch210.certificate2521], c.population=PopulationCertificates.Batch022.certificate442
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers664 {x : ℝ} (hx : certificate664.interval.Contains x) : ∃ c∈certificate664.cells, c.region.interval.Contains x := rat_cut_group_covers certificate664 numericValid664 hx

def certificate665 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate443,PopulationCertificates.Batch022.certificate443,[MergedCutCells.Batch210.certificate2522,MergedCutCells.Batch210.certificate2523,MergedCutCells.Batch210.certificate2524,MergedCutCells.Batch210.certificate2525],(2628934007397505761/500000000000000000),none,(1/2),(906424104576008567/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid665 : certificate665.NumericValid := by decide +kernel
theorem cellsSound665 : ∀ c∈certificate665.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2522,MergedCutCells.Batch210.certificate2523,MergedCutCells.Batch210.certificate2524,MergedCutCells.Batch210.certificate2525], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2522,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2523,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2525,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric665 : ∀ c∈certificate665.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2522,MergedCutCells.Batch210.certificate2523,MergedCutCells.Batch210.certificate2524,MergedCutCells.Batch210.certificate2525], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2522,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2523,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2525,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid665 : ∀ c∈certificate665.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2522,MergedCutCells.Batch210.certificate2523,MergedCutCells.Batch210.certificate2524,MergedCutCells.Batch210.certificate2525], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches665 : ∀ c∈certificate665.cells, c.population=certificate665.population := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2522,MergedCutCells.Batch210.certificate2523,MergedCutCells.Batch210.certificate2524,MergedCutCells.Batch210.certificate2525], c.population=PopulationCertificates.Batch022.certificate443
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers665 {x : ℝ} (hx : certificate665.interval.Contains x) : ∃ c∈certificate665.cells, c.region.interval.Contains x := rat_cut_group_covers certificate665 numericValid665 hx

def certificate666 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate444,PopulationCertificates.Batch022.certificate444,[MergedCutCells.Batch210.certificate2526,MergedCutCells.Batch210.certificate2527],(35728209531388453/40000000000000000),(some (15405179/15625000)),(1/2),(11044585651113649/7812500000000000),(some (110140191926538269/200000000000000000)),(some (9586859399530847/40000000000000000))⟩
theorem numericValid666 : certificate666.NumericValid := by decide +kernel
theorem cellsSound666 : ∀ c∈certificate666.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2526,MergedCutCells.Batch210.certificate2527], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2526,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2527,List.forall_mem_nil _⟩⟩
theorem cellsNumeric666 : ∀ c∈certificate666.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2526,MergedCutCells.Batch210.certificate2527], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2526,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2527,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid666 : ∀ c∈certificate666.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2526,MergedCutCells.Batch210.certificate2527], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid223,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid223,List.forall_mem_nil _⟩⟩
theorem populationMatches666 : ∀ c∈certificate666.cells, c.population=certificate666.population := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2526,MergedCutCells.Batch210.certificate2527], c.population=PopulationCertificates.Batch022.certificate444
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers666 {x : ℝ} (hx : certificate666.interval.Contains x) : ∃ c∈certificate666.cells, c.region.interval.Contains x := rat_cut_group_covers certificate666 numericValid666 hx

def certificate667 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate444,PopulationCertificates.Batch022.certificate444,[MergedCutCells.Batch210.certificate2528,MergedCutCells.Batch210.certificate2529,MergedCutCells.Batch210.certificate2530,MergedCutCells.Batch210.certificate2531,MergedCutCells.Batch211.certificate2532,MergedCutCells.Batch211.certificate2533,MergedCutCells.Batch211.certificate2534],(15405179/15625000),none,(1/2),(1342026343243607433/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid667 : certificate667.NumericValid := by decide +kernel
theorem cellsSound667 : ∀ c∈certificate667.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2528,MergedCutCells.Batch210.certificate2529,MergedCutCells.Batch210.certificate2530,MergedCutCells.Batch210.certificate2531,MergedCutCells.Batch211.certificate2532,MergedCutCells.Batch211.certificate2533,MergedCutCells.Batch211.certificate2534], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2529,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2530,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.sound2531,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2532,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2533,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2534,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric667 : ∀ c∈certificate667.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2528,MergedCutCells.Batch210.certificate2529,MergedCutCells.Batch210.certificate2530,MergedCutCells.Batch210.certificate2531,MergedCutCells.Batch211.certificate2532,MergedCutCells.Batch211.certificate2533,MergedCutCells.Batch211.certificate2534], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2529,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2530,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch210.numericValid2531,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2532,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2533,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2534,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid667 : ∀ c∈certificate667.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2528,MergedCutCells.Batch210.certificate2529,MergedCutCells.Batch210.certificate2530,MergedCutCells.Batch210.certificate2531,MergedCutCells.Batch211.certificate2532,MergedCutCells.Batch211.certificate2533,MergedCutCells.Batch211.certificate2534], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches667 : ∀ c∈certificate667.cells, c.population=certificate667.population := by
  change ∀ c∈[MergedCutCells.Batch210.certificate2528,MergedCutCells.Batch210.certificate2529,MergedCutCells.Batch210.certificate2530,MergedCutCells.Batch210.certificate2531,MergedCutCells.Batch211.certificate2532,MergedCutCells.Batch211.certificate2533,MergedCutCells.Batch211.certificate2534], c.population=PopulationCertificates.Batch022.certificate444
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers667 {x : ℝ} (hx : certificate667.interval.Contains x) : ∃ c∈certificate667.cells, c.region.interval.Contains x := rat_cut_group_covers certificate667 numericValid667 hx

def certificate668 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate445,PopulationCertificates.Batch022.certificate445,[MergedCutCells.Batch211.certificate2535,MergedCutCells.Batch211.certificate2536,MergedCutCells.Batch211.certificate2537],(5265550567563335607/1000000000000000000),none,(1/2),(3745699164417890133/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid668 : certificate668.NumericValid := by decide +kernel
theorem cellsSound668 : ∀ c∈certificate668.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2535,MergedCutCells.Batch211.certificate2536,MergedCutCells.Batch211.certificate2537], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2535,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2536,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2537,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric668 : ∀ c∈certificate668.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2535,MergedCutCells.Batch211.certificate2536,MergedCutCells.Batch211.certificate2537], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2535,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2536,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2537,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid668 : ∀ c∈certificate668.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2535,MergedCutCells.Batch211.certificate2536,MergedCutCells.Batch211.certificate2537], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches668 : ∀ c∈certificate668.cells, c.population=certificate668.population := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2535,MergedCutCells.Batch211.certificate2536,MergedCutCells.Batch211.certificate2537], c.population=PopulationCertificates.Batch022.certificate445
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers668 {x : ℝ} (hx : certificate668.interval.Contains x) : ∃ c∈certificate668.cells, c.region.interval.Contains x := rat_cut_group_covers certificate668 numericValid668 hx

def certificate669 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate446,PopulationCertificates.Batch022.certificate446,[MergedCutCells.Batch211.certificate2538,MergedCutCells.Batch211.certificate2539],(902727381757623223/1000000000000000000),(some (194391981/200000000)),(1/2),(1521621450791567809/1000000000000000000),(some (111760910293819869/200000000000000000)),(some (49362214008355409/200000000000000000))⟩
theorem numericValid669 : certificate669.NumericValid := by decide +kernel
theorem cellsSound669 : ∀ c∈certificate669.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2538,MergedCutCells.Batch211.certificate2539], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2538,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2539,List.forall_mem_nil _⟩⟩
theorem cellsNumeric669 : ∀ c∈certificate669.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2538,MergedCutCells.Batch211.certificate2539], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2538,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2539,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid669 : ∀ c∈certificate669.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2538,MergedCutCells.Batch211.certificate2539], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid224,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy011.valid224,List.forall_mem_nil _⟩⟩
theorem populationMatches669 : ∀ c∈certificate669.cells, c.population=certificate669.population := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2538,MergedCutCells.Batch211.certificate2539], c.population=PopulationCertificates.Batch022.certificate446
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers669 {x : ℝ} (hx : certificate669.interval.Contains x) : ∃ c∈certificate669.cells, c.region.interval.Contains x := rat_cut_group_covers certificate669 numericValid669 hx

def certificate670 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate446,PopulationCertificates.Batch022.certificate446,[MergedCutCells.Batch211.certificate2540,MergedCutCells.Batch211.certificate2541,MergedCutCells.Batch211.certificate2542,MergedCutCells.Batch211.certificate2543,MergedCutCells.Batch212.certificate2544,MergedCutCells.Batch212.certificate2545,MergedCutCells.Batch212.certificate2546,MergedCutCells.Batch212.certificate2547],(194391981/200000000),none,(1/2),(1427245865717695919/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid670 : certificate670.NumericValid := by decide +kernel
theorem cellsSound670 : ∀ c∈certificate670.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2540,MergedCutCells.Batch211.certificate2541,MergedCutCells.Batch211.certificate2542,MergedCutCells.Batch211.certificate2543,MergedCutCells.Batch212.certificate2544,MergedCutCells.Batch212.certificate2545,MergedCutCells.Batch212.certificate2546,MergedCutCells.Batch212.certificate2547], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2540,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2541,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2542,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.sound2543,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2544,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2545,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2546,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2547,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric670 : ∀ c∈certificate670.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2540,MergedCutCells.Batch211.certificate2541,MergedCutCells.Batch211.certificate2542,MergedCutCells.Batch211.certificate2543,MergedCutCells.Batch212.certificate2544,MergedCutCells.Batch212.certificate2545,MergedCutCells.Batch212.certificate2546,MergedCutCells.Batch212.certificate2547], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2540,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2541,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2542,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch211.numericValid2543,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2544,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2545,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2546,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2547,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid670 : ∀ c∈certificate670.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2540,MergedCutCells.Batch211.certificate2541,MergedCutCells.Batch211.certificate2542,MergedCutCells.Batch211.certificate2543,MergedCutCells.Batch212.certificate2544,MergedCutCells.Batch212.certificate2545,MergedCutCells.Batch212.certificate2546,MergedCutCells.Batch212.certificate2547], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches670 : ∀ c∈certificate670.cells, c.population=certificate670.population := by
  change ∀ c∈[MergedCutCells.Batch211.certificate2540,MergedCutCells.Batch211.certificate2541,MergedCutCells.Batch211.certificate2542,MergedCutCells.Batch211.certificate2543,MergedCutCells.Batch212.certificate2544,MergedCutCells.Batch212.certificate2545,MergedCutCells.Batch212.certificate2546,MergedCutCells.Batch212.certificate2547], c.population=PopulationCertificates.Batch022.certificate446
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers670 {x : ℝ} (hx : certificate670.interval.Contains x) : ∃ c∈certificate670.cells, c.region.interval.Contains x := rat_cut_group_covers certificate670 numericValid670 hx

def certificate671 : RatCutGroup := ⟨GeometryCertificates.Batch022.certificate447,PopulationCertificates.Batch022.certificate447,[MergedCutCells.Batch212.certificate2548,MergedCutCells.Batch212.certificate2549,MergedCutCells.Batch212.certificate2550,MergedCutCells.Batch212.certificate2551],(20752237869756561/4000000000000000),none,(1/2),(1895459620192631457/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid671 : certificate671.NumericValid := by decide +kernel
theorem cellsSound671 : ∀ c∈certificate671.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2548,MergedCutCells.Batch212.certificate2549,MergedCutCells.Batch212.certificate2550,MergedCutCells.Batch212.certificate2551], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2548,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2549,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2550,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.sound2551,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric671 : ∀ c∈certificate671.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2548,MergedCutCells.Batch212.certificate2549,MergedCutCells.Batch212.certificate2550,MergedCutCells.Batch212.certificate2551], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2548,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2549,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2550,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch212.numericValid2551,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid671 : ∀ c∈certificate671.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2548,MergedCutCells.Batch212.certificate2549,MergedCutCells.Batch212.certificate2550,MergedCutCells.Batch212.certificate2551], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches671 : ∀ c∈certificate671.cells, c.population=certificate671.population := by
  change ∀ c∈[MergedCutCells.Batch212.certificate2548,MergedCutCells.Batch212.certificate2549,MergedCutCells.Batch212.certificate2550,MergedCutCells.Batch212.certificate2551], c.population=PopulationCertificates.Batch022.certificate447
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers671 {x : ℝ} (hx : certificate671.interval.Contains x) : ∃ c∈certificate671.cells, c.region.interval.Contains x := rat_cut_group_covers certificate671 numericValid671 hx

end Cycle12.MergedCutGroups.Batch055
