import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch002
import Cycle12.GeometryCertificates.Batch003
import Cycle12.MergedCutCells.Batch021
import Cycle12.MergedCutCells.Batch022
import Cycle12.MergedCutCells.Batch023
import Cycle12.MergedCutCells.Batch024
import Cycle12.MergedCutCells.Batch025
import Cycle12.PopulationCertificates.Batch002
import Cycle12.PopulationCertificates.Batch003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch007

def certificate84 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate56,PopulationCertificates.Batch002.certificate56,[MergedCutCells.Batch021.certificate263,MergedCutCells.Batch022.certificate264,MergedCutCells.Batch022.certificate265],(715214767482681063/1000000000000000000),(some (1033749823/1000000000)),(1/2),(169938436571496611/1000000000000000000),(some (187849195985687547/500000000000000000)),(some (62224965631189079/500000000000000000))⟩
theorem numericValid84 : certificate84.NumericValid := by decide +kernel
theorem cellsSound84 : ∀ c∈certificate84.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch021.certificate263,MergedCutCells.Batch022.certificate264,MergedCutCells.Batch022.certificate265], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound263,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound264,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound265,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric84 : ∀ c∈certificate84.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch021.certificate263,MergedCutCells.Batch022.certificate264,MergedCutCells.Batch022.certificate265], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid263,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid264,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid265,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid84 : ∀ c∈certificate84.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch021.certificate263,MergedCutCells.Batch022.certificate264,MergedCutCells.Batch022.certificate265], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid29,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid29,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid29,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches84 : ∀ c∈certificate84.cells, c.population=certificate84.population := by
  change ∀ c∈[MergedCutCells.Batch021.certificate263,MergedCutCells.Batch022.certificate264,MergedCutCells.Batch022.certificate265], c.population=PopulationCertificates.Batch002.certificate56
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers84 {x : ℝ} (hx : certificate84.interval.Contains x) : ∃ c∈certificate84.cells, c.region.interval.Contains x := rat_cut_group_covers certificate84 numericValid84 hx

def certificate85 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate56,PopulationCertificates.Batch002.certificate56,[MergedCutCells.Batch022.certificate266,MergedCutCells.Batch022.certificate267,MergedCutCells.Batch022.certificate268,MergedCutCells.Batch022.certificate269,MergedCutCells.Batch022.certificate270,MergedCutCells.Batch022.certificate271],(1033749823/1000000000),none,(1/2),(70186035426345501/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid85 : certificate85.NumericValid := by decide +kernel
theorem cellsSound85 : ∀ c∈certificate85.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch022.certificate266,MergedCutCells.Batch022.certificate267,MergedCutCells.Batch022.certificate268,MergedCutCells.Batch022.certificate269,MergedCutCells.Batch022.certificate270,MergedCutCells.Batch022.certificate271], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound266,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound267,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound268,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound270,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound271,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric85 : ∀ c∈certificate85.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch022.certificate266,MergedCutCells.Batch022.certificate267,MergedCutCells.Batch022.certificate268,MergedCutCells.Batch022.certificate269,MergedCutCells.Batch022.certificate270,MergedCutCells.Batch022.certificate271], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid266,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid267,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid268,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid270,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid271,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid85 : ∀ c∈certificate85.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch022.certificate266,MergedCutCells.Batch022.certificate267,MergedCutCells.Batch022.certificate268,MergedCutCells.Batch022.certificate269,MergedCutCells.Batch022.certificate270,MergedCutCells.Batch022.certificate271], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches85 : ∀ c∈certificate85.cells, c.population=certificate85.population := by
  change ∀ c∈[MergedCutCells.Batch022.certificate266,MergedCutCells.Batch022.certificate267,MergedCutCells.Batch022.certificate268,MergedCutCells.Batch022.certificate269,MergedCutCells.Batch022.certificate270,MergedCutCells.Batch022.certificate271], c.population=PopulationCertificates.Batch002.certificate56
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers85 {x : ℝ} (hx : certificate85.interval.Contains x) : ∃ c∈certificate85.cells, c.region.interval.Contains x := rat_cut_group_covers certificate85 numericValid85 hx

def certificate86 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate57,PopulationCertificates.Batch002.certificate57,[MergedCutCells.Batch022.certificate272,MergedCutCells.Batch022.certificate273,MergedCutCells.Batch022.certificate274],(114666105452015811/31250000000000000),none,(1/2),(397071627997883903/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid86 : certificate86.NumericValid := by decide +kernel
theorem cellsSound86 : ∀ c∈certificate86.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch022.certificate272,MergedCutCells.Batch022.certificate273,MergedCutCells.Batch022.certificate274], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound272,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound273,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound274,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric86 : ∀ c∈certificate86.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch022.certificate272,MergedCutCells.Batch022.certificate273,MergedCutCells.Batch022.certificate274], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid272,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid273,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid274,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid86 : ∀ c∈certificate86.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch022.certificate272,MergedCutCells.Batch022.certificate273,MergedCutCells.Batch022.certificate274], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches86 : ∀ c∈certificate86.cells, c.population=certificate86.population := by
  change ∀ c∈[MergedCutCells.Batch022.certificate272,MergedCutCells.Batch022.certificate273,MergedCutCells.Batch022.certificate274], c.population=PopulationCertificates.Batch002.certificate57
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers86 {x : ℝ} (hx : certificate86.interval.Contains x) : ∃ c∈certificate86.cells, c.region.interval.Contains x := rat_cut_group_covers certificate86 numericValid86 hx

def certificate87 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate58,PopulationCertificates.Batch002.certificate58,[MergedCutCells.Batch022.certificate275,MergedCutCells.Batch023.certificate276,MergedCutCells.Batch023.certificate277],(721744456875391567/1000000000000000000),(some (63693333/62500000)),(1/2),(21733976091665587/125000000000000000),(some (78091952030646461/200000000000000000)),(some (66076682449900601/500000000000000000))⟩
theorem numericValid87 : certificate87.NumericValid := by decide +kernel
theorem cellsSound87 : ∀ c∈certificate87.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch022.certificate275,MergedCutCells.Batch023.certificate276,MergedCutCells.Batch023.certificate277], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.sound275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound276,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound277,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric87 : ∀ c∈certificate87.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch022.certificate275,MergedCutCells.Batch023.certificate276,MergedCutCells.Batch023.certificate277], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch022.numericValid275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid276,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid277,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid87 : ∀ c∈certificate87.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch022.certificate275,MergedCutCells.Batch023.certificate276,MergedCutCells.Batch023.certificate277], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid30,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid30,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid30,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches87 : ∀ c∈certificate87.cells, c.population=certificate87.population := by
  change ∀ c∈[MergedCutCells.Batch022.certificate275,MergedCutCells.Batch023.certificate276,MergedCutCells.Batch023.certificate277], c.population=PopulationCertificates.Batch002.certificate58
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers87 {x : ℝ} (hx : certificate87.interval.Contains x) : ∃ c∈certificate87.cells, c.region.interval.Contains x := rat_cut_group_covers certificate87 numericValid87 hx

def certificate88 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate58,PopulationCertificates.Batch002.certificate58,[MergedCutCells.Batch023.certificate278,MergedCutCells.Batch023.certificate279,MergedCutCells.Batch023.certificate280,MergedCutCells.Batch023.certificate281,MergedCutCells.Batch023.certificate282,MergedCutCells.Batch023.certificate283],(63693333/62500000),none,(1/2),(16689418279196199/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid88 : certificate88.NumericValid := by decide +kernel
theorem cellsSound88 : ∀ c∈certificate88.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch023.certificate278,MergedCutCells.Batch023.certificate279,MergedCutCells.Batch023.certificate280,MergedCutCells.Batch023.certificate281,MergedCutCells.Batch023.certificate282,MergedCutCells.Batch023.certificate283], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound278,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound279,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound280,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound281,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound282,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound283,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric88 : ∀ c∈certificate88.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch023.certificate278,MergedCutCells.Batch023.certificate279,MergedCutCells.Batch023.certificate280,MergedCutCells.Batch023.certificate281,MergedCutCells.Batch023.certificate282,MergedCutCells.Batch023.certificate283], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid278,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid279,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid280,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid281,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid282,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid283,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid88 : ∀ c∈certificate88.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch023.certificate278,MergedCutCells.Batch023.certificate279,MergedCutCells.Batch023.certificate280,MergedCutCells.Batch023.certificate281,MergedCutCells.Batch023.certificate282,MergedCutCells.Batch023.certificate283], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches88 : ∀ c∈certificate88.cells, c.population=certificate88.population := by
  change ∀ c∈[MergedCutCells.Batch023.certificate278,MergedCutCells.Batch023.certificate279,MergedCutCells.Batch023.certificate280,MergedCutCells.Batch023.certificate281,MergedCutCells.Batch023.certificate282,MergedCutCells.Batch023.certificate283], c.population=PopulationCertificates.Batch002.certificate58
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers88 {x : ℝ} (hx : certificate88.interval.Contains x) : ∃ c∈certificate88.cells, c.region.interval.Contains x := rat_cut_group_covers certificate88 numericValid88 hx

def certificate89 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate59,PopulationCertificates.Batch002.certificate59,[MergedCutCells.Batch023.certificate284,MergedCutCells.Batch023.certificate285,MergedCutCells.Batch023.certificate286],(7219664673498009/1953125000000000),none,(1/2),(26713783633415473/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid89 : certificate89.NumericValid := by decide +kernel
theorem cellsSound89 : ∀ c∈certificate89.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch023.certificate284,MergedCutCells.Batch023.certificate285,MergedCutCells.Batch023.certificate286], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound284,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound286,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric89 : ∀ c∈certificate89.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch023.certificate284,MergedCutCells.Batch023.certificate285,MergedCutCells.Batch023.certificate286], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid284,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid286,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid89 : ∀ c∈certificate89.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch023.certificate284,MergedCutCells.Batch023.certificate285,MergedCutCells.Batch023.certificate286], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches89 : ∀ c∈certificate89.cells, c.population=certificate89.population := by
  change ∀ c∈[MergedCutCells.Batch023.certificate284,MergedCutCells.Batch023.certificate285,MergedCutCells.Batch023.certificate286], c.population=PopulationCertificates.Batch002.certificate59
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers89 {x : ℝ} (hx : certificate89.interval.Contains x) : ∃ c∈certificate89.cells, c.region.interval.Contains x := rat_cut_group_covers certificate89 numericValid89 hx

def certificate90 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate60,PopulationCertificates.Batch003.certificate60,[MergedCutCells.Batch023.certificate287,MergedCutCells.Batch024.certificate288,MergedCutCells.Batch024.certificate289],(45659412274176207/62500000000000000),(some (31423347/31250000)),(1/2),(17835420681111493/100000000000000000),(some (202787138615312427/500000000000000000)),(some (70168365037842959/500000000000000000))⟩
theorem numericValid90 : certificate90.NumericValid := by decide +kernel
theorem cellsSound90 : ∀ c∈certificate90.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch023.certificate287,MergedCutCells.Batch024.certificate288,MergedCutCells.Batch024.certificate289], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.sound287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound288,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound289,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric90 : ∀ c∈certificate90.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch023.certificate287,MergedCutCells.Batch024.certificate288,MergedCutCells.Batch024.certificate289], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch023.numericValid287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid288,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid289,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid90 : ∀ c∈certificate90.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch023.certificate287,MergedCutCells.Batch024.certificate288,MergedCutCells.Batch024.certificate289], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid31,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid31,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid31,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches90 : ∀ c∈certificate90.cells, c.population=certificate90.population := by
  change ∀ c∈[MergedCutCells.Batch023.certificate287,MergedCutCells.Batch024.certificate288,MergedCutCells.Batch024.certificate289], c.population=PopulationCertificates.Batch003.certificate60
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers90 {x : ℝ} (hx : certificate90.interval.Contains x) : ∃ c∈certificate90.cells, c.region.interval.Contains x := rat_cut_group_covers certificate90 numericValid90 hx

def certificate91 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate60,PopulationCertificates.Batch003.certificate60,[MergedCutCells.Batch024.certificate290,MergedCutCells.Batch024.certificate291,MergedCutCells.Batch024.certificate292,MergedCutCells.Batch024.certificate293,MergedCutCells.Batch024.certificate294,MergedCutCells.Batch024.certificate295,MergedCutCells.Batch024.certificate296],(31423347/31250000),none,(1/2),(26985198492239719/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid91 : certificate91.NumericValid := by decide +kernel
theorem cellsSound91 : ∀ c∈certificate91.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch024.certificate290,MergedCutCells.Batch024.certificate291,MergedCutCells.Batch024.certificate292,MergedCutCells.Batch024.certificate293,MergedCutCells.Batch024.certificate294,MergedCutCells.Batch024.certificate295,MergedCutCells.Batch024.certificate296], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound290,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound292,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound294,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound296,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric91 : ∀ c∈certificate91.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch024.certificate290,MergedCutCells.Batch024.certificate291,MergedCutCells.Batch024.certificate292,MergedCutCells.Batch024.certificate293,MergedCutCells.Batch024.certificate294,MergedCutCells.Batch024.certificate295,MergedCutCells.Batch024.certificate296], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid290,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid292,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid294,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid296,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid91 : ∀ c∈certificate91.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch024.certificate290,MergedCutCells.Batch024.certificate291,MergedCutCells.Batch024.certificate292,MergedCutCells.Batch024.certificate293,MergedCutCells.Batch024.certificate294,MergedCutCells.Batch024.certificate295,MergedCutCells.Batch024.certificate296], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches91 : ∀ c∈certificate91.cells, c.population=certificate91.population := by
  change ∀ c∈[MergedCutCells.Batch024.certificate290,MergedCutCells.Batch024.certificate291,MergedCutCells.Batch024.certificate292,MergedCutCells.Batch024.certificate293,MergedCutCells.Batch024.certificate294,MergedCutCells.Batch024.certificate295,MergedCutCells.Batch024.certificate296], c.population=PopulationCertificates.Batch003.certificate60
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers91 {x : ℝ} (hx : certificate91.interval.Contains x) : ∃ c∈certificate91.cells, c.region.interval.Contains x := rat_cut_group_covers certificate91 numericValid91 hx

def certificate92 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate61,PopulationCertificates.Batch003.certificate61,[MergedCutCells.Batch024.certificate297,MergedCutCells.Batch024.certificate298,MergedCutCells.Batch024.certificate299],(374156723765451957/100000000000000000),none,(1/2),(236411756415655723/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid92 : certificate92.NumericValid := by decide +kernel
theorem cellsSound92 : ∀ c∈certificate92.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch024.certificate297,MergedCutCells.Batch024.certificate298,MergedCutCells.Batch024.certificate299], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound297,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound298,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.sound299,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric92 : ∀ c∈certificate92.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch024.certificate297,MergedCutCells.Batch024.certificate298,MergedCutCells.Batch024.certificate299], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid297,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid298,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch024.numericValid299,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid92 : ∀ c∈certificate92.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch024.certificate297,MergedCutCells.Batch024.certificate298,MergedCutCells.Batch024.certificate299], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches92 : ∀ c∈certificate92.cells, c.population=certificate92.population := by
  change ∀ c∈[MergedCutCells.Batch024.certificate297,MergedCutCells.Batch024.certificate298,MergedCutCells.Batch024.certificate299], c.population=PopulationCertificates.Batch003.certificate61
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers92 {x : ℝ} (hx : certificate92.interval.Contains x) : ∃ c∈certificate92.cells, c.region.interval.Contains x := rat_cut_group_covers certificate92 numericValid92 hx

def certificate93 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate62,PopulationCertificates.Batch003.certificate62,[MergedCutCells.Batch025.certificate300,MergedCutCells.Batch025.certificate301,MergedCutCells.Batch025.certificate302],(183273783951490377/250000000000000000),(some (504399447/500000000)),(1/2),(91342835979586571/500000000000000000),(some (413611130007074621/1000000000000000000)),(some (5792653962209363/40000000000000000))⟩
theorem numericValid93 : certificate93.NumericValid := by decide +kernel
theorem cellsSound93 : ∀ c∈certificate93.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch025.certificate300,MergedCutCells.Batch025.certificate301,MergedCutCells.Batch025.certificate302], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound300,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound301,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound302,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric93 : ∀ c∈certificate93.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch025.certificate300,MergedCutCells.Batch025.certificate301,MergedCutCells.Batch025.certificate302], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid300,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid301,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid302,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid93 : ∀ c∈certificate93.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch025.certificate300,MergedCutCells.Batch025.certificate301,MergedCutCells.Batch025.certificate302], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid32,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid32,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid32,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches93 : ∀ c∈certificate93.cells, c.population=certificate93.population := by
  change ∀ c∈[MergedCutCells.Batch025.certificate300,MergedCutCells.Batch025.certificate301,MergedCutCells.Batch025.certificate302], c.population=PopulationCertificates.Batch003.certificate62
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers93 {x : ℝ} (hx : certificate93.interval.Contains x) : ∃ c∈certificate93.cells, c.region.interval.Contains x := rat_cut_group_covers certificate93 numericValid93 hx

def certificate94 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate62,PopulationCertificates.Batch003.certificate62,[MergedCutCells.Batch025.certificate303,MergedCutCells.Batch025.certificate304,MergedCutCells.Batch025.certificate305,MergedCutCells.Batch025.certificate306,MergedCutCells.Batch025.certificate307,MergedCutCells.Batch025.certificate308],(504399447/500000000),none,(1/2),(73183042517758373/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid94 : certificate94.NumericValid := by decide +kernel
theorem cellsSound94 : ∀ c∈certificate94.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch025.certificate303,MergedCutCells.Batch025.certificate304,MergedCutCells.Batch025.certificate305,MergedCutCells.Batch025.certificate306,MergedCutCells.Batch025.certificate307,MergedCutCells.Batch025.certificate308], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound303,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound304,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound305,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound306,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound307,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound308,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric94 : ∀ c∈certificate94.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch025.certificate303,MergedCutCells.Batch025.certificate304,MergedCutCells.Batch025.certificate305,MergedCutCells.Batch025.certificate306,MergedCutCells.Batch025.certificate307,MergedCutCells.Batch025.certificate308], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid303,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid304,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid305,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid306,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid307,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid308,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid94 : ∀ c∈certificate94.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch025.certificate303,MergedCutCells.Batch025.certificate304,MergedCutCells.Batch025.certificate305,MergedCutCells.Batch025.certificate306,MergedCutCells.Batch025.certificate307,MergedCutCells.Batch025.certificate308], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches94 : ∀ c∈certificate94.cells, c.population=certificate94.population := by
  change ∀ c∈[MergedCutCells.Batch025.certificate303,MergedCutCells.Batch025.certificate304,MergedCutCells.Batch025.certificate305,MergedCutCells.Batch025.certificate306,MergedCutCells.Batch025.certificate307,MergedCutCells.Batch025.certificate308], c.population=PopulationCertificates.Batch003.certificate62
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers94 {x : ℝ} (hx : certificate94.interval.Contains x) : ∃ c∈certificate94.cells, c.region.interval.Contains x := rat_cut_group_covers certificate94 numericValid94 hx

def certificate95 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate63,PopulationCertificates.Batch003.certificate63,[MergedCutCells.Batch025.certificate309,MergedCutCells.Batch025.certificate310,MergedCutCells.Batch025.certificate311],(1839516645824970237/500000000000000000),none,(1/2),(82443717406585167/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid95 : certificate95.NumericValid := by decide +kernel
theorem cellsSound95 : ∀ c∈certificate95.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch025.certificate309,MergedCutCells.Batch025.certificate310,MergedCutCells.Batch025.certificate311], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.sound311,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric95 : ∀ c∈certificate95.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch025.certificate309,MergedCutCells.Batch025.certificate310,MergedCutCells.Batch025.certificate311], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch025.numericValid311,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid95 : ∀ c∈certificate95.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch025.certificate309,MergedCutCells.Batch025.certificate310,MergedCutCells.Batch025.certificate311], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches95 : ∀ c∈certificate95.cells, c.population=certificate95.population := by
  change ∀ c∈[MergedCutCells.Batch025.certificate309,MergedCutCells.Batch025.certificate310,MergedCutCells.Batch025.certificate311], c.population=PopulationCertificates.Batch003.certificate63
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers95 {x : ℝ} (hx : certificate95.interval.Contains x) : ∃ c∈certificate95.cells, c.region.interval.Contains x := rat_cut_group_covers certificate95 numericValid95 hx

end Cycle12.MergedCutGroups.Batch007
