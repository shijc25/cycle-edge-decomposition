import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch030
import Cycle12.GeometryCertificates.Batch031
import Cycle12.MergedCutCells.Batch283
import Cycle12.MergedCutCells.Batch284
import Cycle12.MergedCutCells.Batch285
import Cycle12.MergedCutCells.Batch286
import Cycle12.MergedCutCells.Batch287
import Cycle12.PopulationCertificates.Batch030
import Cycle12.PopulationCertificates.Batch031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch077

def certificate924 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate616,PopulationCertificates.Batch030.certificate616,[MergedCutCells.Batch283.certificate3403,MergedCutCells.Batch283.certificate3404,MergedCutCells.Batch283.certificate3405],(174859359354817931/200000000000000000),(some (1091690757/1000000000)),(1/2),(14663972168476289/8000000000000000),(some (175064979501851733/500000000000000000)),(some (111736201072270221/1000000000000000000))⟩
theorem numericValid924 : certificate924.NumericValid := by decide +kernel
theorem cellsSound924 : ∀ c∈certificate924.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3403,MergedCutCells.Batch283.certificate3404,MergedCutCells.Batch283.certificate3405], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3403,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3404,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3405,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric924 : ∀ c∈certificate924.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3403,MergedCutCells.Batch283.certificate3404,MergedCutCells.Batch283.certificate3405], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3403,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3404,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3405,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid924 : ∀ c∈certificate924.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3403,MergedCutCells.Batch283.certificate3404,MergedCutCells.Batch283.certificate3405], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid309,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid309,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid309,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches924 : ∀ c∈certificate924.cells, c.population=certificate924.population := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3403,MergedCutCells.Batch283.certificate3404,MergedCutCells.Batch283.certificate3405], c.population=PopulationCertificates.Batch030.certificate616
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers924 {x : ℝ} (hx : certificate924.interval.Contains x) : ∃ c∈certificate924.cells, c.region.interval.Contains x := rat_cut_group_covers certificate924 numericValid924 hx

def certificate925 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate616,PopulationCertificates.Batch030.certificate616,[MergedCutCells.Batch283.certificate3406,MergedCutCells.Batch283.certificate3407,MergedCutCells.Batch284.certificate3408,MergedCutCells.Batch284.certificate3409,MergedCutCells.Batch284.certificate3410,MergedCutCells.Batch284.certificate3411],(1091690757/1000000000),none,(1/2),(90113817608499523/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid925 : certificate925.NumericValid := by decide +kernel
theorem cellsSound925 : ∀ c∈certificate925.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3406,MergedCutCells.Batch283.certificate3407,MergedCutCells.Batch284.certificate3408,MergedCutCells.Batch284.certificate3409,MergedCutCells.Batch284.certificate3410,MergedCutCells.Batch284.certificate3411], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3406,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.sound3407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3408,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3409,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3410,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3411,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric925 : ∀ c∈certificate925.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3406,MergedCutCells.Batch283.certificate3407,MergedCutCells.Batch284.certificate3408,MergedCutCells.Batch284.certificate3409,MergedCutCells.Batch284.certificate3410,MergedCutCells.Batch284.certificate3411], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3406,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch283.numericValid3407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3408,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3409,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3410,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3411,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid925 : ∀ c∈certificate925.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3406,MergedCutCells.Batch283.certificate3407,MergedCutCells.Batch284.certificate3408,MergedCutCells.Batch284.certificate3409,MergedCutCells.Batch284.certificate3410,MergedCutCells.Batch284.certificate3411], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches925 : ∀ c∈certificate925.cells, c.population=certificate925.population := by
  change ∀ c∈[MergedCutCells.Batch283.certificate3406,MergedCutCells.Batch283.certificate3407,MergedCutCells.Batch284.certificate3408,MergedCutCells.Batch284.certificate3409,MergedCutCells.Batch284.certificate3410,MergedCutCells.Batch284.certificate3411], c.population=PopulationCertificates.Batch030.certificate616
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers925 {x : ℝ} (hx : certificate925.interval.Contains x) : ∃ c∈certificate925.cells, c.region.interval.Contains x := rat_cut_group_covers certificate925 numericValid925 hx

def certificate926 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate617,PopulationCertificates.Batch030.certificate617,[MergedCutCells.Batch284.certificate3412,MergedCutCells.Batch284.certificate3413,MergedCutCells.Batch284.certificate3414,MergedCutCells.Batch284.certificate3415],(9364803868152555641/1000000000000000000),none,(1/2),(465537730647493123/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid926 : certificate926.NumericValid := by decide +kernel
theorem cellsSound926 : ∀ c∈certificate926.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3412,MergedCutCells.Batch284.certificate3413,MergedCutCells.Batch284.certificate3414,MergedCutCells.Batch284.certificate3415], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3413,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3414,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3415,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric926 : ∀ c∈certificate926.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3412,MergedCutCells.Batch284.certificate3413,MergedCutCells.Batch284.certificate3414,MergedCutCells.Batch284.certificate3415], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3413,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3414,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3415,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid926 : ∀ c∈certificate926.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3412,MergedCutCells.Batch284.certificate3413,MergedCutCells.Batch284.certificate3414,MergedCutCells.Batch284.certificate3415], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches926 : ∀ c∈certificate926.cells, c.population=certificate926.population := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3412,MergedCutCells.Batch284.certificate3413,MergedCutCells.Batch284.certificate3414,MergedCutCells.Batch284.certificate3415], c.population=PopulationCertificates.Batch030.certificate617
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers926 {x : ℝ} (hx : certificate926.interval.Contains x) : ∃ c∈certificate926.cells, c.region.interval.Contains x := rat_cut_group_covers certificate926 numericValid926 hx

def certificate927 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate618,PopulationCertificates.Batch030.certificate618,[MergedCutCells.Batch284.certificate3416,MergedCutCells.Batch284.certificate3417,MergedCutCells.Batch284.certificate3418],(110099269560618441/125000000000000000),(some (68711411/62500000)),(1/2),(1907459469525988537/1000000000000000000),(some (177248954493211967/500000000000000000)),(some (711587355682637/6250000000000000))⟩
theorem numericValid927 : certificate927.NumericValid := by decide +kernel
theorem cellsSound927 : ∀ c∈certificate927.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3416,MergedCutCells.Batch284.certificate3417,MergedCutCells.Batch284.certificate3418], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3416,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3417,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3418,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric927 : ∀ c∈certificate927.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3416,MergedCutCells.Batch284.certificate3417,MergedCutCells.Batch284.certificate3418], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3416,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3417,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3418,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid927 : ∀ c∈certificate927.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3416,MergedCutCells.Batch284.certificate3417,MergedCutCells.Batch284.certificate3418], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid310,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid310,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid310,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches927 : ∀ c∈certificate927.cells, c.population=certificate927.population := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3416,MergedCutCells.Batch284.certificate3417,MergedCutCells.Batch284.certificate3418], c.population=PopulationCertificates.Batch030.certificate618
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers927 {x : ℝ} (hx : certificate927.interval.Contains x) : ∃ c∈certificate927.cells, c.region.interval.Contains x := rat_cut_group_covers certificate927 numericValid927 hx

def certificate928 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate618,PopulationCertificates.Batch030.certificate618,[MergedCutCells.Batch284.certificate3419,MergedCutCells.Batch285.certificate3420,MergedCutCells.Batch285.certificate3421,MergedCutCells.Batch285.certificate3422,MergedCutCells.Batch285.certificate3423,MergedCutCells.Batch285.certificate3424],(68711411/62500000),none,(1/2),(934682577932174597/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid928 : certificate928.NumericValid := by decide +kernel
theorem cellsSound928 : ∀ c∈certificate928.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3419,MergedCutCells.Batch285.certificate3420,MergedCutCells.Batch285.certificate3421,MergedCutCells.Batch285.certificate3422,MergedCutCells.Batch285.certificate3423,MergedCutCells.Batch285.certificate3424], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.sound3419,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3420,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3421,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3422,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3423,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3424,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric928 : ∀ c∈certificate928.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3419,MergedCutCells.Batch285.certificate3420,MergedCutCells.Batch285.certificate3421,MergedCutCells.Batch285.certificate3422,MergedCutCells.Batch285.certificate3423,MergedCutCells.Batch285.certificate3424], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch284.numericValid3419,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3420,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3421,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3422,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3423,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3424,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid928 : ∀ c∈certificate928.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3419,MergedCutCells.Batch285.certificate3420,MergedCutCells.Batch285.certificate3421,MergedCutCells.Batch285.certificate3422,MergedCutCells.Batch285.certificate3423,MergedCutCells.Batch285.certificate3424], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches928 : ∀ c∈certificate928.cells, c.population=certificate928.population := by
  change ∀ c∈[MergedCutCells.Batch284.certificate3419,MergedCutCells.Batch285.certificate3420,MergedCutCells.Batch285.certificate3421,MergedCutCells.Batch285.certificate3422,MergedCutCells.Batch285.certificate3423,MergedCutCells.Batch285.certificate3424], c.population=PopulationCertificates.Batch030.certificate618
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers928 {x : ℝ} (hx : certificate928.interval.Contains x) : ∃ c∈certificate928.cells, c.region.interval.Contains x := rat_cut_group_covers certificate928 numericValid928 hx

def certificate929 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate619,PopulationCertificates.Batch030.certificate619,[MergedCutCells.Batch285.certificate3425,MergedCutCells.Batch285.certificate3426,MergedCutCells.Batch285.certificate3427,MergedCutCells.Batch285.certificate3428],(1853001115189166351/200000000000000000),none,(1/2),(3753817603113227969/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid929 : certificate929.NumericValid := by decide +kernel
theorem cellsSound929 : ∀ c∈certificate929.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch285.certificate3425,MergedCutCells.Batch285.certificate3426,MergedCutCells.Batch285.certificate3427,MergedCutCells.Batch285.certificate3428], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3426,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3428,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric929 : ∀ c∈certificate929.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch285.certificate3425,MergedCutCells.Batch285.certificate3426,MergedCutCells.Batch285.certificate3427,MergedCutCells.Batch285.certificate3428], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3426,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3428,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid929 : ∀ c∈certificate929.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch285.certificate3425,MergedCutCells.Batch285.certificate3426,MergedCutCells.Batch285.certificate3427,MergedCutCells.Batch285.certificate3428], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches929 : ∀ c∈certificate929.cells, c.population=certificate929.population := by
  change ∀ c∈[MergedCutCells.Batch285.certificate3425,MergedCutCells.Batch285.certificate3426,MergedCutCells.Batch285.certificate3427,MergedCutCells.Batch285.certificate3428], c.population=PopulationCertificates.Batch030.certificate619
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers929 {x : ℝ} (hx : certificate929.interval.Contains x) : ∃ c∈certificate929.cells, c.region.interval.Contains x := rat_cut_group_covers certificate929 numericValid929 hx

def certificate930 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate620,PopulationCertificates.Batch031.certificate620,[MergedCutCells.Batch285.certificate3429,MergedCutCells.Batch285.certificate3430,MergedCutCells.Batch285.certificate3431],(221609600622349331/250000000000000000),(some (221212413/200000000)),(1/2),(494755970916985553/250000000000000000),(some (71776620966051713/200000000000000000)),(some (116002132788897637/1000000000000000000))⟩
theorem numericValid930 : certificate930.NumericValid := by decide +kernel
theorem cellsSound930 : ∀ c∈certificate930.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch285.certificate3429,MergedCutCells.Batch285.certificate3430,MergedCutCells.Batch285.certificate3431], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3429,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3430,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.sound3431,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric930 : ∀ c∈certificate930.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch285.certificate3429,MergedCutCells.Batch285.certificate3430,MergedCutCells.Batch285.certificate3431], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3429,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3430,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch285.numericValid3431,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid930 : ∀ c∈certificate930.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch285.certificate3429,MergedCutCells.Batch285.certificate3430,MergedCutCells.Batch285.certificate3431], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid311,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid311,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid311,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches930 : ∀ c∈certificate930.cells, c.population=certificate930.population := by
  change ∀ c∈[MergedCutCells.Batch285.certificate3429,MergedCutCells.Batch285.certificate3430,MergedCutCells.Batch285.certificate3431], c.population=PopulationCertificates.Batch031.certificate620
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers930 {x : ℝ} (hx : certificate930.interval.Contains x) : ∃ c∈certificate930.cells, c.region.interval.Contains x := rat_cut_group_covers certificate930 numericValid930 hx

def certificate931 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate620,PopulationCertificates.Batch031.certificate620,[MergedCutCells.Batch286.certificate3432,MergedCutCells.Batch286.certificate3433,MergedCutCells.Batch286.certificate3434,MergedCutCells.Batch286.certificate3435,MergedCutCells.Batch286.certificate3436],(221212413/200000000),none,(1/2),(1939344238334860681/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid931 : certificate931.NumericValid := by decide +kernel
theorem cellsSound931 : ∀ c∈certificate931.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3432,MergedCutCells.Batch286.certificate3433,MergedCutCells.Batch286.certificate3434,MergedCutCells.Batch286.certificate3435,MergedCutCells.Batch286.certificate3436], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3433,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3434,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3435,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3436,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric931 : ∀ c∈certificate931.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3432,MergedCutCells.Batch286.certificate3433,MergedCutCells.Batch286.certificate3434,MergedCutCells.Batch286.certificate3435,MergedCutCells.Batch286.certificate3436], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3433,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3434,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3435,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3436,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid931 : ∀ c∈certificate931.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3432,MergedCutCells.Batch286.certificate3433,MergedCutCells.Batch286.certificate3434,MergedCutCells.Batch286.certificate3435,MergedCutCells.Batch286.certificate3436], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches931 : ∀ c∈certificate931.cells, c.population=certificate931.population := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3432,MergedCutCells.Batch286.certificate3433,MergedCutCells.Batch286.certificate3434,MergedCutCells.Batch286.certificate3435,MergedCutCells.Batch286.certificate3436], c.population=PopulationCertificates.Batch031.certificate620
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers931 {x : ℝ} (hx : certificate931.interval.Contains x) : ∃ c∈certificate931.cells, c.region.interval.Contains x := rat_cut_group_covers certificate931 numericValid931 hx

def certificate932 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate621,PopulationCertificates.Batch031.certificate621,[MergedCutCells.Batch286.certificate3437,MergedCutCells.Batch286.certificate3438,MergedCutCells.Batch286.certificate3439,MergedCutCells.Batch286.certificate3440],(4628932340323177627/500000000000000000),none,(1/2),(76054763980539649/10000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid932 : certificate932.NumericValid := by decide +kernel
theorem cellsSound932 : ∀ c∈certificate932.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3437,MergedCutCells.Batch286.certificate3438,MergedCutCells.Batch286.certificate3439,MergedCutCells.Batch286.certificate3440], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3437,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3439,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3440,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric932 : ∀ c∈certificate932.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3437,MergedCutCells.Batch286.certificate3438,MergedCutCells.Batch286.certificate3439,MergedCutCells.Batch286.certificate3440], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3437,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3439,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3440,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid932 : ∀ c∈certificate932.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3437,MergedCutCells.Batch286.certificate3438,MergedCutCells.Batch286.certificate3439,MergedCutCells.Batch286.certificate3440], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches932 : ∀ c∈certificate932.cells, c.population=certificate932.population := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3437,MergedCutCells.Batch286.certificate3438,MergedCutCells.Batch286.certificate3439,MergedCutCells.Batch286.certificate3440], c.population=PopulationCertificates.Batch031.certificate621
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers932 {x : ℝ} (hx : certificate932.interval.Contains x) : ∃ c∈certificate932.cells, c.region.interval.Contains x := rat_cut_group_covers certificate932 numericValid932 hx

def certificate933 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate622,PopulationCertificates.Batch031.certificate622,[MergedCutCells.Batch286.certificate3441,MergedCutCells.Batch286.certificate3442,MergedCutCells.Batch286.certificate3443],(891508134325996669/1000000000000000000),(some (111205979/100000000)),(1/2),(512458545659559319/250000000000000000),(some (181620495596530147/500000000000000000)),(some (29539772764097847/250000000000000000))⟩
theorem numericValid933 : certificate933.NumericValid := by decide +kernel
theorem cellsSound933 : ∀ c∈certificate933.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3441,MergedCutCells.Batch286.certificate3442,MergedCutCells.Batch286.certificate3443], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3441,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3442,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.sound3443,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric933 : ∀ c∈certificate933.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3441,MergedCutCells.Batch286.certificate3442,MergedCutCells.Batch286.certificate3443], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3441,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3442,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch286.numericValid3443,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid933 : ∀ c∈certificate933.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3441,MergedCutCells.Batch286.certificate3442,MergedCutCells.Batch286.certificate3443], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid312,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid312,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid312,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches933 : ∀ c∈certificate933.cells, c.population=certificate933.population := by
  change ∀ c∈[MergedCutCells.Batch286.certificate3441,MergedCutCells.Batch286.certificate3442,MergedCutCells.Batch286.certificate3443], c.population=PopulationCertificates.Batch031.certificate622
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers933 {x : ℝ} (hx : certificate933.interval.Contains x) : ∃ c∈certificate933.cells, c.region.interval.Contains x := rat_cut_group_covers certificate933 numericValid933 hx

def certificate934 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate622,PopulationCertificates.Batch031.certificate622,[MergedCutCells.Batch287.certificate3444,MergedCutCells.Batch287.certificate3445,MergedCutCells.Batch287.certificate3446,MergedCutCells.Batch287.certificate3447,MergedCutCells.Batch287.certificate3448,MergedCutCells.Batch287.certificate3449],(111205979/100000000),none,(1/2),(201421599047054227/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid934 : certificate934.NumericValid := by decide +kernel
theorem cellsSound934 : ∀ c∈certificate934.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3444,MergedCutCells.Batch287.certificate3445,MergedCutCells.Batch287.certificate3446,MergedCutCells.Batch287.certificate3447,MergedCutCells.Batch287.certificate3448,MergedCutCells.Batch287.certificate3449], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3444,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3445,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3446,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3447,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3448,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3449,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric934 : ∀ c∈certificate934.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3444,MergedCutCells.Batch287.certificate3445,MergedCutCells.Batch287.certificate3446,MergedCutCells.Batch287.certificate3447,MergedCutCells.Batch287.certificate3448,MergedCutCells.Batch287.certificate3449], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3444,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3445,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3446,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3447,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3448,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3449,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid934 : ∀ c∈certificate934.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3444,MergedCutCells.Batch287.certificate3445,MergedCutCells.Batch287.certificate3446,MergedCutCells.Batch287.certificate3447,MergedCutCells.Batch287.certificate3448,MergedCutCells.Batch287.certificate3449], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches934 : ∀ c∈certificate934.cells, c.population=certificate934.population := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3444,MergedCutCells.Batch287.certificate3445,MergedCutCells.Batch287.certificate3446,MergedCutCells.Batch287.certificate3447,MergedCutCells.Batch287.certificate3448,MergedCutCells.Batch287.certificate3449], c.population=PopulationCertificates.Batch031.certificate622
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers934 {x : ℝ} (hx : certificate934.interval.Contains x) : ∃ c∈certificate934.cells, c.region.interval.Contains x := rat_cut_group_covers certificate934 numericValid934 hx

def certificate935 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate623,PopulationCertificates.Batch031.certificate623,[MergedCutCells.Batch287.certificate3450,MergedCutCells.Batch287.certificate3451,MergedCutCells.Batch287.certificate3452],(9159607737915775943/1000000000000000000),none,(1/2),(3831972699404990639/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid935 : certificate935.NumericValid := by decide +kernel
theorem cellsSound935 : ∀ c∈certificate935.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3450,MergedCutCells.Batch287.certificate3451,MergedCutCells.Batch287.certificate3452], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3450,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3451,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3452,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric935 : ∀ c∈certificate935.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3450,MergedCutCells.Batch287.certificate3451,MergedCutCells.Batch287.certificate3452], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3450,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3451,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3452,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid935 : ∀ c∈certificate935.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3450,MergedCutCells.Batch287.certificate3451,MergedCutCells.Batch287.certificate3452], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches935 : ∀ c∈certificate935.cells, c.population=certificate935.population := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3450,MergedCutCells.Batch287.certificate3451,MergedCutCells.Batch287.certificate3452], c.population=PopulationCertificates.Batch031.certificate623
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers935 {x : ℝ} (hx : certificate935.interval.Contains x) : ∃ c∈certificate935.cells, c.region.interval.Contains x := rat_cut_group_covers certificate935 numericValid935 hx

end Cycle12.MergedCutGroups.Batch077
