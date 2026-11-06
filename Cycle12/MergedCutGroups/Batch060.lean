import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch024
import Cycle12.MergedCutCells.Batch229
import Cycle12.MergedCutCells.Batch230
import Cycle12.MergedCutCells.Batch231
import Cycle12.MergedCutCells.Batch232
import Cycle12.PopulationCertificates.Batch024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch060

def certificate720 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate480,PopulationCertificates.Batch024.certificate480,[MergedCutCells.Batch229.certificate2752,MergedCutCells.Batch229.certificate2753,MergedCutCells.Batch229.certificate2754,MergedCutCells.Batch229.certificate2755,MergedCutCells.Batch229.certificate2756,MergedCutCells.Batch229.certificate2757,MergedCutCells.Batch229.certificate2758,MergedCutCells.Batch229.certificate2759],(973255164165863973/1000000000000000000),(some 64),(1/2),(2495191306233087157/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (677063933453944777/500000000000000000))⟩
theorem numericValid720 : certificate720.NumericValid := by decide +kernel
theorem cellsSound720 : ∀ c∈certificate720.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch229.certificate2752,MergedCutCells.Batch229.certificate2753,MergedCutCells.Batch229.certificate2754,MergedCutCells.Batch229.certificate2755,MergedCutCells.Batch229.certificate2756,MergedCutCells.Batch229.certificate2757,MergedCutCells.Batch229.certificate2758,MergedCutCells.Batch229.certificate2759], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2752,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2753,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2755,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2757,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.sound2759,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric720 : ∀ c∈certificate720.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch229.certificate2752,MergedCutCells.Batch229.certificate2753,MergedCutCells.Batch229.certificate2754,MergedCutCells.Batch229.certificate2755,MergedCutCells.Batch229.certificate2756,MergedCutCells.Batch229.certificate2757,MergedCutCells.Batch229.certificate2758,MergedCutCells.Batch229.certificate2759], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2752,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2753,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2754,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2755,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2756,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2757,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2758,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch229.numericValid2759,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid720 : ∀ c∈certificate720.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch229.certificate2752,MergedCutCells.Batch229.certificate2753,MergedCutCells.Batch229.certificate2754,MergedCutCells.Batch229.certificate2755,MergedCutCells.Batch229.certificate2756,MergedCutCells.Batch229.certificate2757,MergedCutCells.Batch229.certificate2758,MergedCutCells.Batch229.certificate2759], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid241,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid241,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid241,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid241,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid241,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid241,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid241,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid241,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches720 : ∀ c∈certificate720.cells, c.population=certificate720.population := by
  change ∀ c∈[MergedCutCells.Batch229.certificate2752,MergedCutCells.Batch229.certificate2753,MergedCutCells.Batch229.certificate2754,MergedCutCells.Batch229.certificate2755,MergedCutCells.Batch229.certificate2756,MergedCutCells.Batch229.certificate2757,MergedCutCells.Batch229.certificate2758,MergedCutCells.Batch229.certificate2759], c.population=PopulationCertificates.Batch024.certificate480
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers720 {x : ℝ} (hx : certificate720.interval.Contains x) : ∃ c∈certificate720.cells, c.region.interval.Contains x := rat_cut_group_covers certificate720 numericValid720 hx

def certificate721 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate480,PopulationCertificates.Batch024.certificate480,[MergedCutCells.Batch230.certificate2760],64,none,(1/2),(3412786121935834513/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid721 : certificate721.NumericValid := by decide +kernel
theorem cellsSound721 : ∀ c∈certificate721.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2760], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2760,List.forall_mem_nil _⟩
theorem cellsNumeric721 : ∀ c∈certificate721.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2760], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2760,List.forall_mem_nil _⟩
theorem cellsEntropyValid721 : ∀ c∈certificate721.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2760], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches721 : ∀ c∈certificate721.cells, c.population=certificate721.population := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2760], c.population=PopulationCertificates.Batch024.certificate480
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers721 {x : ℝ} (hx : certificate721.interval.Contains x) : ∃ c∈certificate721.cells, c.region.interval.Contains x := rat_cut_group_covers certificate721 numericValid721 hx

def certificate722 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate481,PopulationCertificates.Batch024.certificate481,[MergedCutCells.Batch230.certificate2761,MergedCutCells.Batch230.certificate2762,MergedCutCells.Batch230.certificate2763,MergedCutCells.Batch230.certificate2764],(4704124681020422783/1000000000000000000),none,(1/2),(287312010764651433/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid722 : certificate722.NumericValid := by decide +kernel
theorem cellsSound722 : ∀ c∈certificate722.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2761,MergedCutCells.Batch230.certificate2762,MergedCutCells.Batch230.certificate2763,MergedCutCells.Batch230.certificate2764], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2761,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2762,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2763,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2764,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric722 : ∀ c∈certificate722.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2761,MergedCutCells.Batch230.certificate2762,MergedCutCells.Batch230.certificate2763,MergedCutCells.Batch230.certificate2764], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2761,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2762,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2763,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2764,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid722 : ∀ c∈certificate722.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2761,MergedCutCells.Batch230.certificate2762,MergedCutCells.Batch230.certificate2763,MergedCutCells.Batch230.certificate2764], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches722 : ∀ c∈certificate722.cells, c.population=certificate722.population := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2761,MergedCutCells.Batch230.certificate2762,MergedCutCells.Batch230.certificate2763,MergedCutCells.Batch230.certificate2764], c.population=PopulationCertificates.Batch024.certificate481
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers722 {x : ℝ} (hx : certificate722.interval.Contains x) : ∃ c∈certificate722.cells, c.region.interval.Contains x := rat_cut_group_covers certificate722 numericValid722 hx

def certificate723 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate482,PopulationCertificates.Batch024.certificate482,[MergedCutCells.Batch230.certificate2765,MergedCutCells.Batch230.certificate2766,MergedCutCells.Batch230.certificate2767,MergedCutCells.Batch230.certificate2768,MergedCutCells.Batch230.certificate2769,MergedCutCells.Batch230.certificate2770,MergedCutCells.Batch230.certificate2771,MergedCutCells.Batch231.certificate2772],(48765067213997411/50000000000000000),(some 64),(1/2),(258034105618073437/100000000000000000),(some (69314718055994531/100000000000000000)),(some (54224146449144577/40000000000000000))⟩
theorem numericValid723 : certificate723.NumericValid := by decide +kernel
theorem cellsSound723 : ∀ c∈certificate723.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2765,MergedCutCells.Batch230.certificate2766,MergedCutCells.Batch230.certificate2767,MergedCutCells.Batch230.certificate2768,MergedCutCells.Batch230.certificate2769,MergedCutCells.Batch230.certificate2770,MergedCutCells.Batch230.certificate2771,MergedCutCells.Batch231.certificate2772], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2765,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2766,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2767,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2768,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2769,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2770,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.sound2771,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2772,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric723 : ∀ c∈certificate723.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2765,MergedCutCells.Batch230.certificate2766,MergedCutCells.Batch230.certificate2767,MergedCutCells.Batch230.certificate2768,MergedCutCells.Batch230.certificate2769,MergedCutCells.Batch230.certificate2770,MergedCutCells.Batch230.certificate2771,MergedCutCells.Batch231.certificate2772], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2765,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2766,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2767,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2768,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2769,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2770,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch230.numericValid2771,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2772,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid723 : ∀ c∈certificate723.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2765,MergedCutCells.Batch230.certificate2766,MergedCutCells.Batch230.certificate2767,MergedCutCells.Batch230.certificate2768,MergedCutCells.Batch230.certificate2769,MergedCutCells.Batch230.certificate2770,MergedCutCells.Batch230.certificate2771,MergedCutCells.Batch231.certificate2772], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid242,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid242,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid242,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid242,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid242,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid242,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid242,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid242,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches723 : ∀ c∈certificate723.cells, c.population=certificate723.population := by
  change ∀ c∈[MergedCutCells.Batch230.certificate2765,MergedCutCells.Batch230.certificate2766,MergedCutCells.Batch230.certificate2767,MergedCutCells.Batch230.certificate2768,MergedCutCells.Batch230.certificate2769,MergedCutCells.Batch230.certificate2770,MergedCutCells.Batch230.certificate2771,MergedCutCells.Batch231.certificate2772], c.population=PopulationCertificates.Batch024.certificate482
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers723 {x : ℝ} (hx : certificate723.interval.Contains x) : ∃ c∈certificate723.cells, c.region.interval.Contains x := rat_cut_group_covers certificate723 numericValid723 hx

def certificate724 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate482,PopulationCertificates.Batch024.certificate482,[MergedCutCells.Batch231.certificate2773],64,none,(1/2),(706804780999062673/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid724 : certificate724.NumericValid := by decide +kernel
theorem cellsSound724 : ∀ c∈certificate724.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2773], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2773,List.forall_mem_nil _⟩
theorem cellsNumeric724 : ∀ c∈certificate724.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2773], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2773,List.forall_mem_nil _⟩
theorem cellsEntropyValid724 : ∀ c∈certificate724.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2773], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches724 : ∀ c∈certificate724.cells, c.population=certificate724.population := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2773], c.population=PopulationCertificates.Batch024.certificate482
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers724 {x : ℝ} (hx : certificate724.interval.Contains x) : ∃ c∈certificate724.cells, c.region.interval.Contains x := rat_cut_group_covers certificate724 numericValid724 hx

def certificate725 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate483,PopulationCertificates.Batch024.certificate483,[MergedCutCells.Batch231.certificate2774,MergedCutCells.Batch231.certificate2775,MergedCutCells.Batch231.certificate2776,MergedCutCells.Batch231.certificate2777],(1156566038511704029/250000000000000000),none,(1/2),(2314723971122881623/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid725 : certificate725.NumericValid := by decide +kernel
theorem cellsSound725 : ∀ c∈certificate725.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2774,MergedCutCells.Batch231.certificate2775,MergedCutCells.Batch231.certificate2776,MergedCutCells.Batch231.certificate2777], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2774,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2775,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2776,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2777,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric725 : ∀ c∈certificate725.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2774,MergedCutCells.Batch231.certificate2775,MergedCutCells.Batch231.certificate2776,MergedCutCells.Batch231.certificate2777], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2774,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2775,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2776,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2777,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid725 : ∀ c∈certificate725.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2774,MergedCutCells.Batch231.certificate2775,MergedCutCells.Batch231.certificate2776,MergedCutCells.Batch231.certificate2777], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches725 : ∀ c∈certificate725.cells, c.population=certificate725.population := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2774,MergedCutCells.Batch231.certificate2775,MergedCutCells.Batch231.certificate2776,MergedCutCells.Batch231.certificate2777], c.population=PopulationCertificates.Batch024.certificate483
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers725 {x : ℝ} (hx : certificate725.interval.Contains x) : ∃ c∈certificate725.cells, c.region.interval.Contains x := rat_cut_group_covers certificate725 numericValid725 hx

def certificate726 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate484,PopulationCertificates.Batch024.certificate484,[MergedCutCells.Batch231.certificate2778,MergedCutCells.Batch231.certificate2779],(572908247735206181/1000000000000000000),(some (663189157/500000000)),(1/2),(303229611556218821/1000000000000000000),(some (2102384543579347/500000000000000000)),(some (121862068682651/250000000000000000))⟩
theorem numericValid726 : certificate726.NumericValid := by decide +kernel
theorem cellsSound726 : ∀ c∈certificate726.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2778,MergedCutCells.Batch231.certificate2779], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2778,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2779,List.forall_mem_nil _⟩⟩
theorem cellsNumeric726 : ∀ c∈certificate726.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2778,MergedCutCells.Batch231.certificate2779], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2778,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2779,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid726 : ∀ c∈certificate726.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2778,MergedCutCells.Batch231.certificate2779], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid243,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid243,List.forall_mem_nil _⟩⟩
theorem populationMatches726 : ∀ c∈certificate726.cells, c.population=certificate726.population := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2778,MergedCutCells.Batch231.certificate2779], c.population=PopulationCertificates.Batch024.certificate484
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers726 {x : ℝ} (hx : certificate726.interval.Contains x) : ∃ c∈certificate726.cells, c.region.interval.Contains x := rat_cut_group_covers certificate726 numericValid726 hx

def certificate727 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate484,PopulationCertificates.Batch024.certificate484,[MergedCutCells.Batch231.certificate2780,MergedCutCells.Batch231.certificate2781,MergedCutCells.Batch231.certificate2782],(663189157/500000000),none,(1/2),(15156643958549851/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid727 : certificate727.NumericValid := by decide +kernel
theorem cellsSound727 : ∀ c∈certificate727.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2780,MergedCutCells.Batch231.certificate2781,MergedCutCells.Batch231.certificate2782], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2780,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2781,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2782,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric727 : ∀ c∈certificate727.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2780,MergedCutCells.Batch231.certificate2781,MergedCutCells.Batch231.certificate2782], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2780,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2781,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2782,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid727 : ∀ c∈certificate727.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2780,MergedCutCells.Batch231.certificate2781,MergedCutCells.Batch231.certificate2782], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches727 : ∀ c∈certificate727.cells, c.population=certificate727.population := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2780,MergedCutCells.Batch231.certificate2781,MergedCutCells.Batch231.certificate2782], c.population=PopulationCertificates.Batch024.certificate484
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers727 {x : ℝ} (hx : certificate727.interval.Contains x) : ∃ c∈certificate727.cells, c.region.interval.Contains x := rat_cut_group_covers certificate727 numericValid727 hx

def certificate728 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate485,PopulationCertificates.Batch024.certificate485,[MergedCutCells.Batch231.certificate2783,MergedCutCells.Batch232.certificate2784],(7250213697956392521/1000000000000000000),none,(1/2),(245129135385415361/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid728 : certificate728.NumericValid := by decide +kernel
theorem cellsSound728 : ∀ c∈certificate728.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2783,MergedCutCells.Batch232.certificate2784], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.sound2783,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2784,List.forall_mem_nil _⟩⟩
theorem cellsNumeric728 : ∀ c∈certificate728.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2783,MergedCutCells.Batch232.certificate2784], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch231.numericValid2783,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2784,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid728 : ∀ c∈certificate728.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2783,MergedCutCells.Batch232.certificate2784], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches728 : ∀ c∈certificate728.cells, c.population=certificate728.population := by
  change ∀ c∈[MergedCutCells.Batch231.certificate2783,MergedCutCells.Batch232.certificate2784], c.population=PopulationCertificates.Batch024.certificate485
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers728 {x : ℝ} (hx : certificate728.interval.Contains x) : ∃ c∈certificate728.cells, c.region.interval.Contains x := rat_cut_group_covers certificate728 numericValid728 hx

def certificate729 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate486,PopulationCertificates.Batch024.certificate486,[MergedCutCells.Batch232.certificate2785,MergedCutCells.Batch232.certificate2786],(143780299544425427/250000000000000000),(some (1330588209/1000000000)),(1/2),(152937003790386409/500000000000000000),(some (1564877147966139/250000000000000000)),(some (765758354021977/1000000000000000000))⟩
theorem numericValid729 : certificate729.NumericValid := by decide +kernel
theorem cellsSound729 : ∀ c∈certificate729.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2785,MergedCutCells.Batch232.certificate2786], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2785,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2786,List.forall_mem_nil _⟩⟩
theorem cellsNumeric729 : ∀ c∈certificate729.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2785,MergedCutCells.Batch232.certificate2786], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2785,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2786,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid729 : ∀ c∈certificate729.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2785,MergedCutCells.Batch232.certificate2786], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid244,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid244,List.forall_mem_nil _⟩⟩
theorem populationMatches729 : ∀ c∈certificate729.cells, c.population=certificate729.population := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2785,MergedCutCells.Batch232.certificate2786], c.population=PopulationCertificates.Batch024.certificate486
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers729 {x : ℝ} (hx : certificate729.interval.Contains x) : ∃ c∈certificate729.cells, c.region.interval.Contains x := rat_cut_group_covers certificate729 numericValid729 hx

def certificate730 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate486,PopulationCertificates.Batch024.certificate486,[MergedCutCells.Batch232.certificate2787,MergedCutCells.Batch232.certificate2788,MergedCutCells.Batch232.certificate2789],(1330588209/1000000000),none,(1/2),(15285510147554623/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid730 : certificate730.NumericValid := by decide +kernel
theorem cellsSound730 : ∀ c∈certificate730.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2787,MergedCutCells.Batch232.certificate2788,MergedCutCells.Batch232.certificate2789], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2787,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2788,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2789,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric730 : ∀ c∈certificate730.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2787,MergedCutCells.Batch232.certificate2788,MergedCutCells.Batch232.certificate2789], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2787,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2788,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2789,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid730 : ∀ c∈certificate730.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2787,MergedCutCells.Batch232.certificate2788,MergedCutCells.Batch232.certificate2789], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches730 : ∀ c∈certificate730.cells, c.population=certificate730.population := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2787,MergedCutCells.Batch232.certificate2788,MergedCutCells.Batch232.certificate2789], c.population=PopulationCertificates.Batch024.certificate486
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers730 {x : ℝ} (hx : certificate730.interval.Contains x) : ∃ c∈certificate730.cells, c.region.interval.Contains x := rat_cut_group_covers certificate730 numericValid730 hx

def certificate731 : RatCutGroup := ⟨GeometryCertificates.Batch024.certificate487,PopulationCertificates.Batch024.certificate487,[MergedCutCells.Batch232.certificate2790,MergedCutCells.Batch232.certificate2791],(7340418926741313407/1000000000000000000),none,(1/2),(2514475716671789493/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid731 : certificate731.NumericValid := by decide +kernel
theorem cellsSound731 : ∀ c∈certificate731.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2790,MergedCutCells.Batch232.certificate2791], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2790,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.sound2791,List.forall_mem_nil _⟩⟩
theorem cellsNumeric731 : ∀ c∈certificate731.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2790,MergedCutCells.Batch232.certificate2791], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2790,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch232.numericValid2791,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid731 : ∀ c∈certificate731.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2790,MergedCutCells.Batch232.certificate2791], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches731 : ∀ c∈certificate731.cells, c.population=certificate731.population := by
  change ∀ c∈[MergedCutCells.Batch232.certificate2790,MergedCutCells.Batch232.certificate2791], c.population=PopulationCertificates.Batch024.certificate487
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers731 {x : ℝ} (hx : certificate731.interval.Contains x) : ∃ c∈certificate731.cells, c.region.interval.Contains x := rat_cut_group_covers certificate731 numericValid731 hx

end Cycle12.MergedCutGroups.Batch060
