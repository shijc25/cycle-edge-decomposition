import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch042
import Cycle12.MergedCutCells.Batch364
import Cycle12.MergedCutCells.Batch365
import Cycle12.MergedCutCells.Batch366
import Cycle12.PopulationCertificates.Batch042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch106

def certificate1272 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate850,PopulationCertificates.Batch042.certificate850,[MergedCutCells.Batch364.certificate4373,MergedCutCells.Batch364.certificate4374,MergedCutCells.Batch364.certificate4375],(170378532288158213/250000000000000000),none,(1/40),(137358050260800337/1000000000000000000),none,none⟩
theorem numericValid1272 : certificate1272.NumericValid := by decide +kernel
theorem cellsSound1272 : ∀ c∈certificate1272.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4373,MergedCutCells.Batch364.certificate4374,MergedCutCells.Batch364.certificate4375], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4373,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4375,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1272 : ∀ c∈certificate1272.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4373,MergedCutCells.Batch364.certificate4374,MergedCutCells.Batch364.certificate4375], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4373,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4375,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1272 : ∀ c∈certificate1272.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4373,MergedCutCells.Batch364.certificate4374,MergedCutCells.Batch364.certificate4375], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid441,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid442,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid443,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1272 : ∀ c∈certificate1272.cells, c.population=certificate1272.population := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4373,MergedCutCells.Batch364.certificate4374,MergedCutCells.Batch364.certificate4375], c.population=PopulationCertificates.Batch042.certificate850
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1272 {x : ℝ} (hx : certificate1272.interval.Contains x) : ∃ c∈certificate1272.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1272 numericValid1272 hx

def certificate1273 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate851,PopulationCertificates.Batch042.certificate851,[MergedCutCells.Batch364.certificate4376,MergedCutCells.Batch364.certificate4377],(290180298795897327/500000000000000000),(some (1276126907/1000000000)),(1/2),(367517575436159083/1000000000000000000),(some (1773717888278223/1000000000000000000)),(some (184840772540153/1000000000000000000))⟩
theorem numericValid1273 : certificate1273.NumericValid := by decide +kernel
theorem cellsSound1273 : ∀ c∈certificate1273.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4376,MergedCutCells.Batch364.certificate4377], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4377,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1273 : ∀ c∈certificate1273.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4376,MergedCutCells.Batch364.certificate4377], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4377,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1273 : ∀ c∈certificate1273.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4376,MergedCutCells.Batch364.certificate4377], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid444,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid444,List.forall_mem_nil _⟩⟩
theorem populationMatches1273 : ∀ c∈certificate1273.cells, c.population=certificate1273.population := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4376,MergedCutCells.Batch364.certificate4377], c.population=PopulationCertificates.Batch042.certificate851
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1273 {x : ℝ} (hx : certificate1273.interval.Contains x) : ∃ c∈certificate1273.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1273 numericValid1273 hx

def certificate1274 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate851,PopulationCertificates.Batch042.certificate851,[MergedCutCells.Batch364.certificate4378,MergedCutCells.Batch364.certificate4379,MergedCutCells.Batch365.certificate4380],(1276126907/1000000000),none,(1/2),(918762188964881/2500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1274 : certificate1274.NumericValid := by decide +kernel
theorem cellsSound1274 : ∀ c∈certificate1274.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4378,MergedCutCells.Batch364.certificate4379,MergedCutCells.Batch365.certificate4380], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4378,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.sound4379,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4380,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1274 : ∀ c∈certificate1274.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4378,MergedCutCells.Batch364.certificate4379,MergedCutCells.Batch365.certificate4380], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4378,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch364.numericValid4379,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4380,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1274 : ∀ c∈certificate1274.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4378,MergedCutCells.Batch364.certificate4379,MergedCutCells.Batch365.certificate4380], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1274 : ∀ c∈certificate1274.cells, c.population=certificate1274.population := by
  change ∀ c∈[MergedCutCells.Batch364.certificate4378,MergedCutCells.Batch364.certificate4379,MergedCutCells.Batch365.certificate4380], c.population=PopulationCertificates.Batch042.certificate851
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1274 {x : ℝ} (hx : certificate1274.interval.Contains x) : ∃ c∈certificate1274.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1274 numericValid1274 hx

def certificate1275 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate852,PopulationCertificates.Batch042.certificate852,[MergedCutCells.Batch365.certificate4381,MergedCutCells.Batch365.certificate4382],(8032331799323036389/500000000000000000),none,(1/2),(262407316934197613/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1275 : certificate1275.NumericValid := by decide +kernel
theorem cellsSound1275 : ∀ c∈certificate1275.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4381,MergedCutCells.Batch365.certificate4382], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4381,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4382,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1275 : ∀ c∈certificate1275.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4381,MergedCutCells.Batch365.certificate4382], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4381,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4382,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1275 : ∀ c∈certificate1275.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4381,MergedCutCells.Batch365.certificate4382], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1275 : ∀ c∈certificate1275.cells, c.population=certificate1275.population := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4381,MergedCutCells.Batch365.certificate4382], c.population=PopulationCertificates.Batch042.certificate852
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1275 {x : ℝ} (hx : certificate1275.interval.Contains x) : ∃ c∈certificate1275.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1275 numericValid1275 hx

def certificate1276 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate853,PopulationCertificates.Batch042.certificate853,[MergedCutCells.Batch365.certificate4383,MergedCutCells.Batch365.certificate4384,MergedCutCells.Batch365.certificate4385],(342072052619594827/500000000000000000),none,(1/40),(143737708694100737/1000000000000000000),none,none⟩
theorem numericValid1276 : certificate1276.NumericValid := by decide +kernel
theorem cellsSound1276 : ∀ c∈certificate1276.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4383,MergedCutCells.Batch365.certificate4384,MergedCutCells.Batch365.certificate4385], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4385,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1276 : ∀ c∈certificate1276.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4383,MergedCutCells.Batch365.certificate4384,MergedCutCells.Batch365.certificate4385], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4385,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1276 : ∀ c∈certificate1276.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4383,MergedCutCells.Batch365.certificate4384,MergedCutCells.Batch365.certificate4385], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid445,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid446,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid447,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1276 : ∀ c∈certificate1276.cells, c.population=certificate1276.population := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4383,MergedCutCells.Batch365.certificate4384,MergedCutCells.Batch365.certificate4385], c.population=PopulationCertificates.Batch042.certificate853
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1276 {x : ℝ} (hx : certificate1276.interval.Contains x) : ∃ c∈certificate1276.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1276 numericValid1276 hx

def certificate1277 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate854,PopulationCertificates.Batch042.certificate854,[MergedCutCells.Batch365.certificate4386,MergedCutCells.Batch365.certificate4387],(116268116098219351/200000000000000000),(some (127792047/100000000)),(1/2),(384338207369636977/1000000000000000000),(some (1033076377828153/500000000000000000)),(some (219212044929871/1000000000000000000))⟩
theorem numericValid1277 : certificate1277.NumericValid := by decide +kernel
theorem cellsSound1277 : ∀ c∈certificate1277.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4386,MergedCutCells.Batch365.certificate4387], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4386,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4387,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1277 : ∀ c∈certificate1277.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4386,MergedCutCells.Batch365.certificate4387], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4386,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4387,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1277 : ∀ c∈certificate1277.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4386,MergedCutCells.Batch365.certificate4387], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid448,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid448,List.forall_mem_nil _⟩⟩
theorem populationMatches1277 : ∀ c∈certificate1277.cells, c.population=certificate1277.population := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4386,MergedCutCells.Batch365.certificate4387], c.population=PopulationCertificates.Batch042.certificate854
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1277 {x : ℝ} (hx : certificate1277.interval.Contains x) : ∃ c∈certificate1277.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1277 numericValid1277 hx

def certificate1278 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate854,PopulationCertificates.Batch042.certificate854,[MergedCutCells.Batch365.certificate4388,MergedCutCells.Batch365.certificate4389,MergedCutCells.Batch365.certificate4390],(127792047/100000000),none,(1/2),(24025538855675017/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1278 : certificate1278.NumericValid := by decide +kernel
theorem cellsSound1278 : ∀ c∈certificate1278.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4388,MergedCutCells.Batch365.certificate4389,MergedCutCells.Batch365.certificate4390], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4388,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4389,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4390,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1278 : ∀ c∈certificate1278.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4388,MergedCutCells.Batch365.certificate4389,MergedCutCells.Batch365.certificate4390], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4388,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4389,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4390,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1278 : ∀ c∈certificate1278.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4388,MergedCutCells.Batch365.certificate4389,MergedCutCells.Batch365.certificate4390], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1278 : ∀ c∈certificate1278.cells, c.population=certificate1278.population := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4388,MergedCutCells.Batch365.certificate4389,MergedCutCells.Batch365.certificate4390], c.population=PopulationCertificates.Batch042.certificate854
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1278 {x : ℝ} (hx : certificate1278.interval.Contains x) : ∃ c∈certificate1278.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1278 numericValid1278 hx

def certificate1279 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate855,PopulationCertificates.Batch042.certificate855,[MergedCutCells.Batch365.certificate4391,MergedCutCells.Batch366.certificate4392],(8122098535421185937/500000000000000000),none,(1/2),(4297928419283098053/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1279 : certificate1279.NumericValid := by decide +kernel
theorem cellsSound1279 : ∀ c∈certificate1279.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4391,MergedCutCells.Batch366.certificate4392], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.sound4391,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4392,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1279 : ∀ c∈certificate1279.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4391,MergedCutCells.Batch366.certificate4392], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch365.numericValid4391,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4392,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1279 : ∀ c∈certificate1279.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4391,MergedCutCells.Batch366.certificate4392], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1279 : ∀ c∈certificate1279.cells, c.population=certificate1279.population := by
  change ∀ c∈[MergedCutCells.Batch365.certificate4391,MergedCutCells.Batch366.certificate4392], c.population=PopulationCertificates.Batch042.certificate855
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1279 {x : ℝ} (hx : certificate1279.interval.Contains x) : ∃ c∈certificate1279.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1279 numericValid1279 hx

def certificate1280 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate856,PopulationCertificates.Batch042.certificate856,[MergedCutCells.Batch366.certificate4393,MergedCutCells.Batch366.certificate4394,MergedCutCells.Batch366.certificate4395],(27472086024370111/40000000000000000),none,(1/40),(150297215755685857/1000000000000000000),none,none⟩
theorem numericValid1280 : certificate1280.NumericValid := by decide +kernel
theorem cellsSound1280 : ∀ c∈certificate1280.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4393,MergedCutCells.Batch366.certificate4394,MergedCutCells.Batch366.certificate4395], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4393,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4394,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4395,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1280 : ∀ c∈certificate1280.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4393,MergedCutCells.Batch366.certificate4394,MergedCutCells.Batch366.certificate4395], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4393,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4394,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4395,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1280 : ∀ c∈certificate1280.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4393,MergedCutCells.Batch366.certificate4394,MergedCutCells.Batch366.certificate4395], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid449,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid450,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid451,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1280 : ∀ c∈certificate1280.cells, c.population=certificate1280.population := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4393,MergedCutCells.Batch366.certificate4394,MergedCutCells.Batch366.certificate4395], c.population=PopulationCertificates.Batch042.certificate856
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1280 {x : ℝ} (hx : certificate1280.interval.Contains x) : ∃ c∈certificate1280.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1280 numericValid1280 hx

def certificate1281 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate857,PopulationCertificates.Batch042.certificate857,[MergedCutCells.Batch366.certificate4396,MergedCutCells.Batch366.certificate4397],(147039682077721603/250000000000000000),(some (259146439/200000000)),(1/2),(408720813773732627/1000000000000000000),(some (75110290790907/31250000000000000)),(some (259673852371707/1000000000000000000))⟩
theorem numericValid1281 : certificate1281.NumericValid := by decide +kernel
theorem cellsSound1281 : ∀ c∈certificate1281.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4396,MergedCutCells.Batch366.certificate4397], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4397,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1281 : ∀ c∈certificate1281.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4396,MergedCutCells.Batch366.certificate4397], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4397,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1281 : ∀ c∈certificate1281.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4396,MergedCutCells.Batch366.certificate4397], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid452,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy022.valid452,List.forall_mem_nil _⟩⟩
theorem populationMatches1281 : ∀ c∈certificate1281.cells, c.population=certificate1281.population := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4396,MergedCutCells.Batch366.certificate4397], c.population=PopulationCertificates.Batch042.certificate857
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1281 {x : ℝ} (hx : certificate1281.interval.Contains x) : ∃ c∈certificate1281.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1281 numericValid1281 hx

def certificate1282 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate857,PopulationCertificates.Batch042.certificate857,[MergedCutCells.Batch366.certificate4398,MergedCutCells.Batch366.certificate4399,MergedCutCells.Batch366.certificate4400],(259146439/200000000),none,(1/2),(25422853790809419/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1282 : certificate1282.NumericValid := by decide +kernel
theorem cellsSound1282 : ∀ c∈certificate1282.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4398,MergedCutCells.Batch366.certificate4399,MergedCutCells.Batch366.certificate4400], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4398,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4399,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4400,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1282 : ∀ c∈certificate1282.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4398,MergedCutCells.Batch366.certificate4399,MergedCutCells.Batch366.certificate4400], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4398,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4399,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4400,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1282 : ∀ c∈certificate1282.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4398,MergedCutCells.Batch366.certificate4399,MergedCutCells.Batch366.certificate4400], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1282 : ∀ c∈certificate1282.cells, c.population=certificate1282.population := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4398,MergedCutCells.Batch366.certificate4399,MergedCutCells.Batch366.certificate4400], c.population=PopulationCertificates.Batch042.certificate857
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1282 {x : ℝ} (hx : certificate1282.interval.Contains x) : ∃ c∈certificate1282.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1282 numericValid1282 hx

def certificate1283 : RatCutGroup := ⟨GeometryCertificates.Batch042.certificate858,PopulationCertificates.Batch042.certificate858,[MergedCutCells.Batch366.certificate4401,MergedCutCells.Batch366.certificate4402],(8213594690952650247/500000000000000000),none,(1/2),(4380978244596439071/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1283 : certificate1283.NumericValid := by decide +kernel
theorem cellsSound1283 : ∀ c∈certificate1283.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4401,MergedCutCells.Batch366.certificate4402], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4401,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.sound4402,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1283 : ∀ c∈certificate1283.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4401,MergedCutCells.Batch366.certificate4402], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4401,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch366.numericValid4402,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1283 : ∀ c∈certificate1283.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4401,MergedCutCells.Batch366.certificate4402], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1283 : ∀ c∈certificate1283.cells, c.population=certificate1283.population := by
  change ∀ c∈[MergedCutCells.Batch366.certificate4401,MergedCutCells.Batch366.certificate4402], c.population=PopulationCertificates.Batch042.certificate858
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1283 {x : ℝ} (hx : certificate1283.interval.Contains x) : ∃ c∈certificate1283.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1283 numericValid1283 hx

end Cycle12.MergedCutGroups.Batch106
