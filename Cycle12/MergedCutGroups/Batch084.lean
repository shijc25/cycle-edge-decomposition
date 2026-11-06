import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch033
import Cycle12.MergedCutCells.Batch308
import Cycle12.MergedCutCells.Batch309
import Cycle12.MergedCutCells.Batch310
import Cycle12.MergedCutCells.Batch311
import Cycle12.PopulationCertificates.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch084

def certificate1008 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate672,PopulationCertificates.Batch033.certificate672,[MergedCutCells.Batch308.certificate3707,MergedCutCells.Batch309.certificate3708],(572311289295840601/1000000000000000000),(some (1287438351/1000000000)),(1/2),(263763768808751293/1000000000000000000),(some (1156747131335541/200000000000000000)),(some (139969150142541/200000000000000000))⟩
theorem numericValid1008 : certificate1008.NumericValid := by decide +kernel
theorem cellsSound1008 : ∀ c∈certificate1008.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3707,MergedCutCells.Batch309.certificate3708], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3707,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3708,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1008 : ∀ c∈certificate1008.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3707,MergedCutCells.Batch309.certificate3708], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3707,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3708,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1008 : ∀ c∈certificate1008.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3707,MergedCutCells.Batch309.certificate3708], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid337,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid337,List.forall_mem_nil _⟩⟩
theorem populationMatches1008 : ∀ c∈certificate1008.cells, c.population=certificate1008.population := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3707,MergedCutCells.Batch309.certificate3708], c.population=PopulationCertificates.Batch033.certificate672
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1008 {x : ℝ} (hx : certificate1008.interval.Contains x) : ∃ c∈certificate1008.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1008 numericValid1008 hx

def certificate1009 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate672,PopulationCertificates.Batch033.certificate672,[MergedCutCells.Batch309.certificate3709,MergedCutCells.Batch309.certificate3710,MergedCutCells.Batch309.certificate3711],(1287438351/1000000000),none,(1/2),(131846854301371429/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1009 : certificate1009.NumericValid := by decide +kernel
theorem cellsSound1009 : ∀ c∈certificate1009.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3709,MergedCutCells.Batch309.certificate3710,MergedCutCells.Batch309.certificate3711], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3709,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3711,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1009 : ∀ c∈certificate1009.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3709,MergedCutCells.Batch309.certificate3710,MergedCutCells.Batch309.certificate3711], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3709,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3710,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3711,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1009 : ∀ c∈certificate1009.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3709,MergedCutCells.Batch309.certificate3710,MergedCutCells.Batch309.certificate3711], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1009 : ∀ c∈certificate1009.cells, c.population=certificate1009.population := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3709,MergedCutCells.Batch309.certificate3710,MergedCutCells.Batch309.certificate3711], c.population=PopulationCertificates.Batch033.certificate672
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1009 {x : ℝ} (hx : certificate1009.interval.Contains x) : ∃ c∈certificate1009.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1009 numericValid1009 hx

def certificate1010 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate673,PopulationCertificates.Batch033.certificate673,[MergedCutCells.Batch309.certificate3712,MergedCutCells.Batch309.certificate3713],(15986693708051214293/1000000000000000000),none,(1/2),(4081965590412692159/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1010 : certificate1010.NumericValid := by decide +kernel
theorem cellsSound1010 : ∀ c∈certificate1010.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3712,MergedCutCells.Batch309.certificate3713], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3713,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1010 : ∀ c∈certificate1010.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3712,MergedCutCells.Batch309.certificate3713], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3712,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3713,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1010 : ∀ c∈certificate1010.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3712,MergedCutCells.Batch309.certificate3713], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1010 : ∀ c∈certificate1010.cells, c.population=certificate1010.population := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3712,MergedCutCells.Batch309.certificate3713], c.population=PopulationCertificates.Batch033.certificate673
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1010 {x : ℝ} (hx : certificate1010.interval.Contains x) : ∃ c∈certificate1010.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1010 numericValid1010 hx

def certificate1011 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate674,PopulationCertificates.Batch033.certificate674,[MergedCutCells.Batch309.certificate3714,MergedCutCells.Batch309.certificate3715],(571490514192422669/1000000000000000000),(some (1285909139/1000000000)),(1/2),(49990282100006703/200000000000000000),(some (6366982297166191/1000000000000000000)),(some (156151995450157/200000000000000000))⟩
theorem numericValid1011 : certificate1011.NumericValid := by decide +kernel
theorem cellsSound1011 : ∀ c∈certificate1011.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3714,MergedCutCells.Batch309.certificate3715], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3715,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1011 : ∀ c∈certificate1011.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3714,MergedCutCells.Batch309.certificate3715], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3714,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3715,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1011 : ∀ c∈certificate1011.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3714,MergedCutCells.Batch309.certificate3715], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid338,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid338,List.forall_mem_nil _⟩⟩
theorem populationMatches1011 : ∀ c∈certificate1011.cells, c.population=certificate1011.population := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3714,MergedCutCells.Batch309.certificate3715], c.population=PopulationCertificates.Batch033.certificate674
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1011 {x : ℝ} (hx : certificate1011.interval.Contains x) : ∃ c∈certificate1011.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1011 numericValid1011 hx

def certificate1012 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate674,PopulationCertificates.Batch033.certificate674,[MergedCutCells.Batch309.certificate3716,MergedCutCells.Batch309.certificate3717,MergedCutCells.Batch309.certificate3718],(1285909139/1000000000),none,(1/2),(975735472201819/3906250000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1012 : certificate1012.NumericValid := by decide +kernel
theorem cellsSound1012 : ∀ c∈certificate1012.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3716,MergedCutCells.Batch309.certificate3717,MergedCutCells.Batch309.certificate3718], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3716,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3717,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3718,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1012 : ∀ c∈certificate1012.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3716,MergedCutCells.Batch309.certificate3717,MergedCutCells.Batch309.certificate3718], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3716,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3717,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3718,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1012 : ∀ c∈certificate1012.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3716,MergedCutCells.Batch309.certificate3717,MergedCutCells.Batch309.certificate3718], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1012 : ∀ c∈certificate1012.cells, c.population=certificate1012.population := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3716,MergedCutCells.Batch309.certificate3717,MergedCutCells.Batch309.certificate3718], c.population=PopulationCertificates.Batch033.certificate674
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1012 {x : ℝ} (hx : certificate1012.interval.Contains x) : ∃ c∈certificate1012.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1012 numericValid1012 hx

def certificate1013 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate675,PopulationCertificates.Batch033.certificate675,[MergedCutCells.Batch309.certificate3719,MergedCutCells.Batch310.certificate3720],(648251116319971077/40000000000000000),none,(1/2),(4122174822523816401/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1013 : certificate1013.NumericValid := by decide +kernel
theorem cellsSound1013 : ∀ c∈certificate1013.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3719,MergedCutCells.Batch310.certificate3720], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.sound3719,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3720,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1013 : ∀ c∈certificate1013.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3719,MergedCutCells.Batch310.certificate3720], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch309.numericValid3719,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3720,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1013 : ∀ c∈certificate1013.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3719,MergedCutCells.Batch310.certificate3720], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1013 : ∀ c∈certificate1013.cells, c.population=certificate1013.population := by
  change ∀ c∈[MergedCutCells.Batch309.certificate3719,MergedCutCells.Batch310.certificate3720], c.population=PopulationCertificates.Batch033.certificate675
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1013 {x : ℝ} (hx : certificate1013.interval.Contains x) : ∃ c∈certificate1013.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1013 numericValid1013 hx

def certificate1014 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate676,PopulationCertificates.Batch033.certificate676,[MergedCutCells.Batch310.certificate3721,MergedCutCells.Batch310.certificate3722],(568903271503288541/1000000000000000000),(some (128108629/100000000)),(1/2),(248992177853145753/1000000000000000000),(some (53819457658939/7812500000000000)),(some (427088509004189/500000000000000000))⟩
theorem numericValid1014 : certificate1014.NumericValid := by decide +kernel
theorem cellsSound1014 : ∀ c∈certificate1014.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3721,MergedCutCells.Batch310.certificate3722], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3721,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3722,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1014 : ∀ c∈certificate1014.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3721,MergedCutCells.Batch310.certificate3722], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3721,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3722,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1014 : ∀ c∈certificate1014.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3721,MergedCutCells.Batch310.certificate3722], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid339,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid339,List.forall_mem_nil _⟩⟩
theorem populationMatches1014 : ∀ c∈certificate1014.cells, c.population=certificate1014.population := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3721,MergedCutCells.Batch310.certificate3722], c.population=PopulationCertificates.Batch033.certificate676
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1014 {x : ℝ} (hx : certificate1014.interval.Contains x) : ∃ c∈certificate1014.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1014 numericValid1014 hx

def certificate1015 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate676,PopulationCertificates.Batch033.certificate676,[MergedCutCells.Batch310.certificate3723,MergedCutCells.Batch310.certificate3724,MergedCutCells.Batch310.certificate3725],(128108629/100000000),none,(1/2),(248685906629875489/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1015 : certificate1015.NumericValid := by decide +kernel
theorem cellsSound1015 : ∀ c∈certificate1015.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3723,MergedCutCells.Batch310.certificate3724,MergedCutCells.Batch310.certificate3725], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3723,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3724,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3725,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1015 : ∀ c∈certificate1015.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3723,MergedCutCells.Batch310.certificate3724,MergedCutCells.Batch310.certificate3725], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3723,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3724,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3725,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1015 : ∀ c∈certificate1015.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3723,MergedCutCells.Batch310.certificate3724,MergedCutCells.Batch310.certificate3725], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1015 : ∀ c∈certificate1015.cells, c.population=certificate1015.population := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3723,MergedCutCells.Batch310.certificate3724,MergedCutCells.Batch310.certificate3725], c.population=PopulationCertificates.Batch033.certificate676
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1015 {x : ℝ} (hx : certificate1015.interval.Contains x) : ∃ c∈certificate1015.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1015 numericValid1015 hx

def certificate1016 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate677,PopulationCertificates.Batch033.certificate677,[MergedCutCells.Batch310.certificate3726,MergedCutCells.Batch310.certificate3727],(3247576877984794851/200000000000000000),none,(1/2),(2075865006267290361/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1016 : certificate1016.NumericValid := by decide +kernel
theorem cellsSound1016 : ∀ c∈certificate1016.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3726,MergedCutCells.Batch310.certificate3727], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3726,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3727,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1016 : ∀ c∈certificate1016.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3726,MergedCutCells.Batch310.certificate3727], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3726,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3727,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1016 : ∀ c∈certificate1016.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3726,MergedCutCells.Batch310.certificate3727], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1016 : ∀ c∈certificate1016.cells, c.population=certificate1016.population := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3726,MergedCutCells.Batch310.certificate3727], c.population=PopulationCertificates.Batch033.certificate677
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1016 {x : ℝ} (hx : certificate1016.interval.Contains x) : ∃ c∈certificate1016.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1016 numericValid1016 hx

def certificate1017 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate678,PopulationCertificates.Batch033.certificate678,[MergedCutCells.Batch310.certificate3728,MergedCutCells.Batch310.certificate3729],(568267816759111399/1000000000000000000),(some (319975293/250000000)),(1/2),(123213566226027329/500000000000000000),(some (1867854790501791/250000000000000000)),(some (937189209163793/1000000000000000000))⟩
theorem numericValid1017 : certificate1017.NumericValid := by decide +kernel
theorem cellsSound1017 : ∀ c∈certificate1017.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3728,MergedCutCells.Batch310.certificate3729], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3728,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3729,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1017 : ∀ c∈certificate1017.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3728,MergedCutCells.Batch310.certificate3729], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3728,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3729,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1017 : ∀ c∈certificate1017.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3728,MergedCutCells.Batch310.certificate3729], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid340,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid340,List.forall_mem_nil _⟩⟩
theorem populationMatches1017 : ∀ c∈certificate1017.cells, c.population=certificate1017.population := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3728,MergedCutCells.Batch310.certificate3729], c.population=PopulationCertificates.Batch033.certificate678
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1017 {x : ℝ} (hx : certificate1017.interval.Contains x) : ∃ c∈certificate1017.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1017 numericValid1017 hx

def certificate1018 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate678,PopulationCertificates.Batch033.certificate678,[MergedCutCells.Batch310.certificate3730,MergedCutCells.Batch310.certificate3731,MergedCutCells.Batch311.certificate3732],(319975293/250000000),none,(1/2),(246181843958942019/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1018 : certificate1018.NumericValid := by decide +kernel
theorem cellsSound1018 : ∀ c∈certificate1018.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3730,MergedCutCells.Batch310.certificate3731,MergedCutCells.Batch311.certificate3732], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3730,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.sound3731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3732,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1018 : ∀ c∈certificate1018.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3730,MergedCutCells.Batch310.certificate3731,MergedCutCells.Batch311.certificate3732], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3730,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch310.numericValid3731,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3732,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1018 : ∀ c∈certificate1018.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3730,MergedCutCells.Batch310.certificate3731,MergedCutCells.Batch311.certificate3732], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1018 : ∀ c∈certificate1018.cells, c.population=certificate1018.population := by
  change ∀ c∈[MergedCutCells.Batch310.certificate3730,MergedCutCells.Batch310.certificate3731,MergedCutCells.Batch311.certificate3732], c.population=PopulationCertificates.Batch033.certificate678
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1018 {x : ℝ} (hx : certificate1018.interval.Contains x) : ∃ c∈certificate1018.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1018 numericValid1018 hx

def certificate1019 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate679,PopulationCertificates.Batch033.certificate679,[MergedCutCells.Batch311.certificate3733,MergedCutCells.Batch311.certificate3734],(16389297360015867223/1000000000000000000),none,(1/2),(4191982881283105809/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1019 : certificate1019.NumericValid := by decide +kernel
theorem cellsSound1019 : ∀ c∈certificate1019.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3733,MergedCutCells.Batch311.certificate3734], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3733,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.sound3734,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1019 : ∀ c∈certificate1019.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3733,MergedCutCells.Batch311.certificate3734], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3733,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch311.numericValid3734,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1019 : ∀ c∈certificate1019.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3733,MergedCutCells.Batch311.certificate3734], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1019 : ∀ c∈certificate1019.cells, c.population=certificate1019.population := by
  change ∀ c∈[MergedCutCells.Batch311.certificate3733,MergedCutCells.Batch311.certificate3734], c.population=PopulationCertificates.Batch033.certificate679
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1019 {x : ℝ} (hx : certificate1019.interval.Contains x) : ∃ c∈certificate1019.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1019 numericValid1019 hx

end Cycle12.MergedCutGroups.Batch084
