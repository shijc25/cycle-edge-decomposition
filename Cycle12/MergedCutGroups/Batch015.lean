import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch006
import Cycle12.MergedCutCells.Batch056
import Cycle12.MergedCutCells.Batch057
import Cycle12.MergedCutCells.Batch058
import Cycle12.MergedCutCells.Batch059
import Cycle12.MergedCutCells.Batch060
import Cycle12.PopulationCertificates.Batch006

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch015

def certificate180 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate120,PopulationCertificates.Batch006.certificate120,[MergedCutCells.Batch056.certificate674,MergedCutCells.Batch056.certificate675],(25301837210755213/31250000000000000),(some (893700359/1000000000)),(1/2),(10047221737324121/31250000000000000),(some (23418250017730003/40000000000000000)),(some (136110929950737707/500000000000000000))⟩
theorem numericValid180 : certificate180.NumericValid := by decide +kernel
theorem cellsSound180 : ∀ c∈certificate180.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch056.certificate674,MergedCutCells.Batch056.certificate675], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound675,List.forall_mem_nil _⟩⟩
theorem cellsNumeric180 : ∀ c∈certificate180.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch056.certificate674,MergedCutCells.Batch056.certificate675], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid675,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid180 : ∀ c∈certificate180.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch056.certificate674,MergedCutCells.Batch056.certificate675], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid61,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid61,List.forall_mem_nil _⟩⟩
theorem populationMatches180 : ∀ c∈certificate180.cells, c.population=certificate180.population := by
  change ∀ c∈[MergedCutCells.Batch056.certificate674,MergedCutCells.Batch056.certificate675], c.population=PopulationCertificates.Batch006.certificate120
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers180 {x : ℝ} (hx : certificate180.interval.Contains x) : ∃ c∈certificate180.cells, c.region.interval.Contains x := rat_cut_group_covers certificate180 numericValid180 hx

def certificate181 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate120,PopulationCertificates.Batch006.certificate120,[MergedCutCells.Batch056.certificate676,MergedCutCells.Batch056.certificate677,MergedCutCells.Batch056.certificate678,MergedCutCells.Batch056.certificate679,MergedCutCells.Batch056.certificate680,MergedCutCells.Batch056.certificate681],(893700359/1000000000),none,(1/2),(258875225450326151/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid181 : certificate181.NumericValid := by decide +kernel
theorem cellsSound181 : ∀ c∈certificate181.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch056.certificate676,MergedCutCells.Batch056.certificate677,MergedCutCells.Batch056.certificate678,MergedCutCells.Batch056.certificate679,MergedCutCells.Batch056.certificate680,MergedCutCells.Batch056.certificate681], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound676,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound677,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound678,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound680,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound681,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric181 : ∀ c∈certificate181.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch056.certificate676,MergedCutCells.Batch056.certificate677,MergedCutCells.Batch056.certificate678,MergedCutCells.Batch056.certificate679,MergedCutCells.Batch056.certificate680,MergedCutCells.Batch056.certificate681], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid676,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid677,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid678,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid680,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid681,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid181 : ∀ c∈certificate181.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch056.certificate676,MergedCutCells.Batch056.certificate677,MergedCutCells.Batch056.certificate678,MergedCutCells.Batch056.certificate679,MergedCutCells.Batch056.certificate680,MergedCutCells.Batch056.certificate681], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches181 : ∀ c∈certificate181.cells, c.population=certificate181.population := by
  change ∀ c∈[MergedCutCells.Batch056.certificate676,MergedCutCells.Batch056.certificate677,MergedCutCells.Batch056.certificate678,MergedCutCells.Batch056.certificate679,MergedCutCells.Batch056.certificate680,MergedCutCells.Batch056.certificate681], c.population=PopulationCertificates.Batch006.certificate120
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers181 {x : ℝ} (hx : certificate181.interval.Contains x) : ∃ c∈certificate181.cells, c.region.interval.Contains x := rat_cut_group_covers certificate181 numericValid181 hx

def certificate182 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate121,PopulationCertificates.Batch006.certificate121,[MergedCutCells.Batch056.certificate682,MergedCutCells.Batch056.certificate683,MergedCutCells.Batch057.certificate684],(3785037519171510523/1000000000000000000),none,(1/2),(26152678184721703/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid182 : certificate182.NumericValid := by decide +kernel
theorem cellsSound182 : ∀ c∈certificate182.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch056.certificate682,MergedCutCells.Batch056.certificate683,MergedCutCells.Batch057.certificate684], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.sound683,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound684,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric182 : ∀ c∈certificate182.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch056.certificate682,MergedCutCells.Batch056.certificate683,MergedCutCells.Batch057.certificate684], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch056.numericValid683,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid684,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid182 : ∀ c∈certificate182.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch056.certificate682,MergedCutCells.Batch056.certificate683,MergedCutCells.Batch057.certificate684], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches182 : ∀ c∈certificate182.cells, c.population=certificate182.population := by
  change ∀ c∈[MergedCutCells.Batch056.certificate682,MergedCutCells.Batch056.certificate683,MergedCutCells.Batch057.certificate684], c.population=PopulationCertificates.Batch006.certificate121
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers182 {x : ℝ} (hx : certificate182.interval.Contains x) : ∃ c∈certificate182.cells, c.region.interval.Contains x := rat_cut_group_covers certificate182 numericValid182 hx

def certificate183 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate122,PopulationCertificates.Batch006.certificate122,[MergedCutCells.Batch057.certificate685,MergedCutCells.Batch057.certificate686],(820316492135015269/1000000000000000000),(some (883186871/1000000000)),(1/2),(184351421851994571/500000000000000000),(some (586142529951949029/1000000000000000000)),(some (136460496359518109/500000000000000000))⟩
theorem numericValid183 : certificate183.NumericValid := by decide +kernel
theorem cellsSound183 : ∀ c∈certificate183.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch057.certificate685,MergedCutCells.Batch057.certificate686], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound685,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound686,List.forall_mem_nil _⟩⟩
theorem cellsNumeric183 : ∀ c∈certificate183.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch057.certificate685,MergedCutCells.Batch057.certificate686], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid685,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid686,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid183 : ∀ c∈certificate183.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch057.certificate685,MergedCutCells.Batch057.certificate686], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid62,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid62,List.forall_mem_nil _⟩⟩
theorem populationMatches183 : ∀ c∈certificate183.cells, c.population=certificate183.population := by
  change ∀ c∈[MergedCutCells.Batch057.certificate685,MergedCutCells.Batch057.certificate686], c.population=PopulationCertificates.Batch006.certificate122
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers183 {x : ℝ} (hx : certificate183.interval.Contains x) : ∃ c∈certificate183.cells, c.region.interval.Contains x := rat_cut_group_covers certificate183 numericValid183 hx

def certificate184 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate122,PopulationCertificates.Batch006.certificate122,[MergedCutCells.Batch057.certificate687,MergedCutCells.Batch057.certificate688,MergedCutCells.Batch057.certificate689,MergedCutCells.Batch057.certificate690,MergedCutCells.Batch057.certificate691,MergedCutCells.Batch057.certificate692,MergedCutCells.Batch057.certificate693],(883186871/1000000000),none,(1/2),(263510522201321489/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid184 : certificate184.NumericValid := by decide +kernel
theorem cellsSound184 : ∀ c∈certificate184.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch057.certificate687,MergedCutCells.Batch057.certificate688,MergedCutCells.Batch057.certificate689,MergedCutCells.Batch057.certificate690,MergedCutCells.Batch057.certificate691,MergedCutCells.Batch057.certificate692,MergedCutCells.Batch057.certificate693], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound687,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound688,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound689,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound690,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound691,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound692,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound693,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric184 : ∀ c∈certificate184.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch057.certificate687,MergedCutCells.Batch057.certificate688,MergedCutCells.Batch057.certificate689,MergedCutCells.Batch057.certificate690,MergedCutCells.Batch057.certificate691,MergedCutCells.Batch057.certificate692,MergedCutCells.Batch057.certificate693], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid687,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid688,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid689,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid690,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid691,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid692,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid693,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid184 : ∀ c∈certificate184.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch057.certificate687,MergedCutCells.Batch057.certificate688,MergedCutCells.Batch057.certificate689,MergedCutCells.Batch057.certificate690,MergedCutCells.Batch057.certificate691,MergedCutCells.Batch057.certificate692,MergedCutCells.Batch057.certificate693], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches184 : ∀ c∈certificate184.cells, c.population=certificate184.population := by
  change ∀ c∈[MergedCutCells.Batch057.certificate687,MergedCutCells.Batch057.certificate688,MergedCutCells.Batch057.certificate689,MergedCutCells.Batch057.certificate690,MergedCutCells.Batch057.certificate691,MergedCutCells.Batch057.certificate692,MergedCutCells.Batch057.certificate693], c.population=PopulationCertificates.Batch006.certificate122
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers184 {x : ℝ} (hx : certificate184.interval.Contains x) : ∃ c∈certificate184.cells, c.region.interval.Contains x := rat_cut_group_covers certificate184 numericValid184 hx

def certificate185 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate123,PopulationCertificates.Batch006.certificate123,[MergedCutCells.Batch057.certificate694,MergedCutCells.Batch057.certificate695,MergedCutCells.Batch058.certificate696,MergedCutCells.Batch058.certificate697],(3793125823660242777/1000000000000000000),none,(1/2),(668260505099088539/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid185 : certificate185.NumericValid := by decide +kernel
theorem cellsSound185 : ∀ c∈certificate185.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch057.certificate694,MergedCutCells.Batch057.certificate695,MergedCutCells.Batch058.certificate696,MergedCutCells.Batch058.certificate697], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound694,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.sound695,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound697,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric185 : ∀ c∈certificate185.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch057.certificate694,MergedCutCells.Batch057.certificate695,MergedCutCells.Batch058.certificate696,MergedCutCells.Batch058.certificate697], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid694,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch057.numericValid695,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid697,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid185 : ∀ c∈certificate185.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch057.certificate694,MergedCutCells.Batch057.certificate695,MergedCutCells.Batch058.certificate696,MergedCutCells.Batch058.certificate697], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches185 : ∀ c∈certificate185.cells, c.population=certificate185.population := by
  change ∀ c∈[MergedCutCells.Batch057.certificate694,MergedCutCells.Batch057.certificate695,MergedCutCells.Batch058.certificate696,MergedCutCells.Batch058.certificate697], c.population=PopulationCertificates.Batch006.certificate123
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers185 {x : ℝ} (hx : certificate185.interval.Contains x) : ∃ c∈certificate185.cells, c.region.interval.Contains x := rat_cut_group_covers certificate185 numericValid185 hx

def certificate186 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate124,PopulationCertificates.Batch006.certificate124,[MergedCutCells.Batch058.certificate698,MergedCutCells.Batch058.certificate699],(412413547014760389/500000000000000000),(some (866396687/1000000000)),(1/2),(190458951199703107/500000000000000000),(some (590466260250291603/1000000000000000000)),(some (69346172255492957/250000000000000000))⟩
theorem numericValid186 : certificate186.NumericValid := by decide +kernel
theorem cellsSound186 : ∀ c∈certificate186.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch058.certificate698,MergedCutCells.Batch058.certificate699], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound699,List.forall_mem_nil _⟩⟩
theorem cellsNumeric186 : ∀ c∈certificate186.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch058.certificate698,MergedCutCells.Batch058.certificate699], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid699,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid186 : ∀ c∈certificate186.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch058.certificate698,MergedCutCells.Batch058.certificate699], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid63,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid63,List.forall_mem_nil _⟩⟩
theorem populationMatches186 : ∀ c∈certificate186.cells, c.population=certificate186.population := by
  change ∀ c∈[MergedCutCells.Batch058.certificate698,MergedCutCells.Batch058.certificate699], c.population=PopulationCertificates.Batch006.certificate124
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers186 {x : ℝ} (hx : certificate186.interval.Contains x) : ∃ c∈certificate186.cells, c.region.interval.Contains x := rat_cut_group_covers certificate186 numericValid186 hx

def certificate187 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate124,PopulationCertificates.Batch006.certificate124,[MergedCutCells.Batch058.certificate700,MergedCutCells.Batch058.certificate701,MergedCutCells.Batch058.certificate702,MergedCutCells.Batch058.certificate703,MergedCutCells.Batch058.certificate704,MergedCutCells.Batch058.certificate705,MergedCutCells.Batch058.certificate706,MergedCutCells.Batch058.certificate707],(866396687/1000000000),none,(1/2),(257498149009804773/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid187 : certificate187.NumericValid := by decide +kernel
theorem cellsSound187 : ∀ c∈certificate187.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch058.certificate700,MergedCutCells.Batch058.certificate701,MergedCutCells.Batch058.certificate702,MergedCutCells.Batch058.certificate703,MergedCutCells.Batch058.certificate704,MergedCutCells.Batch058.certificate705,MergedCutCells.Batch058.certificate706,MergedCutCells.Batch058.certificate707], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound700,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound701,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound702,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound703,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound704,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound705,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound706,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.sound707,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric187 : ∀ c∈certificate187.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch058.certificate700,MergedCutCells.Batch058.certificate701,MergedCutCells.Batch058.certificate702,MergedCutCells.Batch058.certificate703,MergedCutCells.Batch058.certificate704,MergedCutCells.Batch058.certificate705,MergedCutCells.Batch058.certificate706,MergedCutCells.Batch058.certificate707], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid700,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid701,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid702,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid703,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid704,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid705,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid706,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch058.numericValid707,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid187 : ∀ c∈certificate187.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch058.certificate700,MergedCutCells.Batch058.certificate701,MergedCutCells.Batch058.certificate702,MergedCutCells.Batch058.certificate703,MergedCutCells.Batch058.certificate704,MergedCutCells.Batch058.certificate705,MergedCutCells.Batch058.certificate706,MergedCutCells.Batch058.certificate707], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches187 : ∀ c∈certificate187.cells, c.population=certificate187.population := by
  change ∀ c∈[MergedCutCells.Batch058.certificate700,MergedCutCells.Batch058.certificate701,MergedCutCells.Batch058.certificate702,MergedCutCells.Batch058.certificate703,MergedCutCells.Batch058.certificate704,MergedCutCells.Batch058.certificate705,MergedCutCells.Batch058.certificate706,MergedCutCells.Batch058.certificate707], c.population=PopulationCertificates.Batch006.certificate124
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers187 {x : ℝ} (hx : certificate187.interval.Contains x) : ∃ c∈certificate187.cells, c.region.interval.Contains x := rat_cut_group_covers certificate187 numericValid187 hx

def certificate188 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate125,PopulationCertificates.Batch006.certificate125,[MergedCutCells.Batch059.certificate708,MergedCutCells.Batch059.certificate709,MergedCutCells.Batch059.certificate710,MergedCutCells.Batch059.certificate711],(1849003878437226449/500000000000000000),none,(1/2),(8520512867691141/15625000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid188 : certificate188.NumericValid := by decide +kernel
theorem cellsSound188 : ∀ c∈certificate188.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch059.certificate708,MergedCutCells.Batch059.certificate709,MergedCutCells.Batch059.certificate710,MergedCutCells.Batch059.certificate711], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound708,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound709,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound711,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric188 : ∀ c∈certificate188.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch059.certificate708,MergedCutCells.Batch059.certificate709,MergedCutCells.Batch059.certificate710,MergedCutCells.Batch059.certificate711], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid708,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid709,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid711,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid188 : ∀ c∈certificate188.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch059.certificate708,MergedCutCells.Batch059.certificate709,MergedCutCells.Batch059.certificate710,MergedCutCells.Batch059.certificate711], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches188 : ∀ c∈certificate188.cells, c.population=certificate188.population := by
  change ∀ c∈[MergedCutCells.Batch059.certificate708,MergedCutCells.Batch059.certificate709,MergedCutCells.Batch059.certificate710,MergedCutCells.Batch059.certificate711], c.population=PopulationCertificates.Batch006.certificate125
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers188 {x : ℝ} (hx : certificate188.interval.Contains x) : ∃ c∈certificate188.cells, c.region.interval.Contains x := rat_cut_group_covers certificate188 numericValid188 hx

def certificate189 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate126,PopulationCertificates.Batch006.certificate126,[MergedCutCells.Batch059.certificate712,MergedCutCells.Batch059.certificate713],(829429857802049283/1000000000000000000),(some (27231867/31250000)),(1/2),(406992542807550849/1000000000000000000),(some (593274575688838049/1000000000000000000)),(some (140170226952360613/500000000000000000))⟩
theorem numericValid189 : certificate189.NumericValid := by decide +kernel
theorem cellsSound189 : ∀ c∈certificate189.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch059.certificate712,MergedCutCells.Batch059.certificate713], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound713,List.forall_mem_nil _⟩⟩
theorem cellsNumeric189 : ∀ c∈certificate189.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch059.certificate712,MergedCutCells.Batch059.certificate713], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid713,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid189 : ∀ c∈certificate189.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch059.certificate712,MergedCutCells.Batch059.certificate713], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid64,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy003.valid64,List.forall_mem_nil _⟩⟩
theorem populationMatches189 : ∀ c∈certificate189.cells, c.population=certificate189.population := by
  change ∀ c∈[MergedCutCells.Batch059.certificate712,MergedCutCells.Batch059.certificate713], c.population=PopulationCertificates.Batch006.certificate126
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers189 {x : ℝ} (hx : certificate189.interval.Contains x) : ∃ c∈certificate189.cells, c.region.interval.Contains x := rat_cut_group_covers certificate189 numericValid189 hx

def certificate190 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate126,PopulationCertificates.Batch006.certificate126,[MergedCutCells.Batch059.certificate714,MergedCutCells.Batch059.certificate715,MergedCutCells.Batch059.certificate716,MergedCutCells.Batch059.certificate717,MergedCutCells.Batch059.certificate718,MergedCutCells.Batch059.certificate719,MergedCutCells.Batch060.certificate720],(27231867/31250000),none,(1/2),(273561143348569433/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid190 : certificate190.NumericValid := by decide +kernel
theorem cellsSound190 : ∀ c∈certificate190.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch059.certificate714,MergedCutCells.Batch059.certificate715,MergedCutCells.Batch059.certificate716,MergedCutCells.Batch059.certificate717,MergedCutCells.Batch059.certificate718,MergedCutCells.Batch059.certificate719,MergedCutCells.Batch060.certificate720], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound715,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound716,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound717,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound718,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.sound719,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound720,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric190 : ∀ c∈certificate190.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch059.certificate714,MergedCutCells.Batch059.certificate715,MergedCutCells.Batch059.certificate716,MergedCutCells.Batch059.certificate717,MergedCutCells.Batch059.certificate718,MergedCutCells.Batch059.certificate719,MergedCutCells.Batch060.certificate720], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid715,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid716,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid717,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid718,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch059.numericValid719,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid720,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid190 : ∀ c∈certificate190.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch059.certificate714,MergedCutCells.Batch059.certificate715,MergedCutCells.Batch059.certificate716,MergedCutCells.Batch059.certificate717,MergedCutCells.Batch059.certificate718,MergedCutCells.Batch059.certificate719,MergedCutCells.Batch060.certificate720], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches190 : ∀ c∈certificate190.cells, c.population=certificate190.population := by
  change ∀ c∈[MergedCutCells.Batch059.certificate714,MergedCutCells.Batch059.certificate715,MergedCutCells.Batch059.certificate716,MergedCutCells.Batch059.certificate717,MergedCutCells.Batch059.certificate718,MergedCutCells.Batch059.certificate719,MergedCutCells.Batch060.certificate720], c.population=PopulationCertificates.Batch006.certificate126
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers190 {x : ℝ} (hx : certificate190.interval.Contains x) : ∃ c∈certificate190.cells, c.region.interval.Contains x := rat_cut_group_covers certificate190 numericValid190 hx

def certificate191 : RatCutGroup := ⟨GeometryCertificates.Batch006.certificate127,PopulationCertificates.Batch006.certificate127,[MergedCutCells.Batch060.certificate721,MergedCutCells.Batch060.certificate722,MergedCutCells.Batch060.certificate723,MergedCutCells.Batch060.certificate724],(1858757643112766289/500000000000000000),none,(1/2),(588965126570905639/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid191 : certificate191.NumericValid := by decide +kernel
theorem cellsSound191 : ∀ c∈certificate191.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch060.certificate721,MergedCutCells.Batch060.certificate722,MergedCutCells.Batch060.certificate723,MergedCutCells.Batch060.certificate724], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound721,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound722,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound723,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.sound724,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric191 : ∀ c∈certificate191.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch060.certificate721,MergedCutCells.Batch060.certificate722,MergedCutCells.Batch060.certificate723,MergedCutCells.Batch060.certificate724], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid721,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid722,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid723,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch060.numericValid724,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid191 : ∀ c∈certificate191.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch060.certificate721,MergedCutCells.Batch060.certificate722,MergedCutCells.Batch060.certificate723,MergedCutCells.Batch060.certificate724], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches191 : ∀ c∈certificate191.cells, c.population=certificate191.population := by
  change ∀ c∈[MergedCutCells.Batch060.certificate721,MergedCutCells.Batch060.certificate722,MergedCutCells.Batch060.certificate723,MergedCutCells.Batch060.certificate724], c.population=PopulationCertificates.Batch006.certificate127
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers191 {x : ℝ} (hx : certificate191.interval.Contains x) : ∃ c∈certificate191.cells, c.region.interval.Contains x := rat_cut_group_covers certificate191 numericValid191 hx

end Cycle12.MergedCutGroups.Batch015
