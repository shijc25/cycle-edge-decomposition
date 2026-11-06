import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch030
import Cycle12.MergedCutCells.Batch275
import Cycle12.MergedCutCells.Batch276
import Cycle12.MergedCutCells.Batch277
import Cycle12.MergedCutCells.Batch278
import Cycle12.MergedCutCells.Batch279
import Cycle12.PopulationCertificates.Batch030

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch075

def certificate900 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate600,PopulationCertificates.Batch030.certificate600,[MergedCutCells.Batch275.certificate3306,MergedCutCells.Batch275.certificate3307,MergedCutCells.Batch275.certificate3308],(166376665384277347/200000000000000000),(some (545650769/500000000)),(1/2),(10706518599132323/8000000000000000),(some (159575987085434333/500000000000000000)),(some (48659503022969541/500000000000000000))⟩
theorem numericValid900 : certificate900.NumericValid := by decide +kernel
theorem cellsSound900 : ∀ c∈certificate900.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3306,MergedCutCells.Batch275.certificate3307,MergedCutCells.Batch275.certificate3308], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3306,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3307,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3308,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric900 : ∀ c∈certificate900.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3306,MergedCutCells.Batch275.certificate3307,MergedCutCells.Batch275.certificate3308], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3306,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3307,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3308,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid900 : ∀ c∈certificate900.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3306,MergedCutCells.Batch275.certificate3307,MergedCutCells.Batch275.certificate3308], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid301,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid301,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid301,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches900 : ∀ c∈certificate900.cells, c.population=certificate900.population := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3306,MergedCutCells.Batch275.certificate3307,MergedCutCells.Batch275.certificate3308], c.population=PopulationCertificates.Batch030.certificate600
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers900 {x : ℝ} (hx : certificate900.interval.Contains x) : ∃ c∈certificate900.cells, c.region.interval.Contains x := rat_cut_group_covers certificate900 numericValid900 hx

def certificate901 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate600,PopulationCertificates.Batch030.certificate600,[MergedCutCells.Batch275.certificate3309,MergedCutCells.Batch275.certificate3310,MergedCutCells.Batch275.certificate3311,MergedCutCells.Batch276.certificate3312,MergedCutCells.Batch276.certificate3313,MergedCutCells.Batch276.certificate3314],(545650769/500000000),none,(1/2),(3268622505018751/2500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid901 : certificate901.NumericValid := by decide +kernel
theorem cellsSound901 : ∀ c∈certificate901.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3309,MergedCutCells.Batch275.certificate3310,MergedCutCells.Batch275.certificate3311,MergedCutCells.Batch276.certificate3312,MergedCutCells.Batch276.certificate3313,MergedCutCells.Batch276.certificate3314], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.sound3311,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3312,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3313,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3314,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric901 : ∀ c∈certificate901.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3309,MergedCutCells.Batch275.certificate3310,MergedCutCells.Batch275.certificate3311,MergedCutCells.Batch276.certificate3312,MergedCutCells.Batch276.certificate3313,MergedCutCells.Batch276.certificate3314], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch275.numericValid3311,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3312,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3313,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3314,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid901 : ∀ c∈certificate901.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3309,MergedCutCells.Batch275.certificate3310,MergedCutCells.Batch275.certificate3311,MergedCutCells.Batch276.certificate3312,MergedCutCells.Batch276.certificate3313,MergedCutCells.Batch276.certificate3314], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches901 : ∀ c∈certificate901.cells, c.population=certificate901.population := by
  change ∀ c∈[MergedCutCells.Batch275.certificate3309,MergedCutCells.Batch275.certificate3310,MergedCutCells.Batch275.certificate3311,MergedCutCells.Batch276.certificate3312,MergedCutCells.Batch276.certificate3313,MergedCutCells.Batch276.certificate3314], c.population=PopulationCertificates.Batch030.certificate600
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers901 {x : ℝ} (hx : certificate901.interval.Contains x) : ∃ c∈certificate901.cells, c.region.interval.Contains x := rat_cut_group_covers certificate901 numericValid901 hx

def certificate902 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate601,PopulationCertificates.Batch030.certificate601,[MergedCutCells.Batch276.certificate3315,MergedCutCells.Batch276.certificate3316,MergedCutCells.Batch276.certificate3317],(4866691573994780971/500000000000000000),none,(1/2),(1702464462210349771/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid902 : certificate902.NumericValid := by decide +kernel
theorem cellsSound902 : ∀ c∈certificate902.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3315,MergedCutCells.Batch276.certificate3316,MergedCutCells.Batch276.certificate3317], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3315,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3316,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3317,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric902 : ∀ c∈certificate902.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3315,MergedCutCells.Batch276.certificate3316,MergedCutCells.Batch276.certificate3317], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3315,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3316,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3317,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid902 : ∀ c∈certificate902.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3315,MergedCutCells.Batch276.certificate3316,MergedCutCells.Batch276.certificate3317], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches902 : ∀ c∈certificate902.cells, c.population=certificate902.population := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3315,MergedCutCells.Batch276.certificate3316,MergedCutCells.Batch276.certificate3317], c.population=PopulationCertificates.Batch030.certificate601
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers902 {x : ℝ} (hx : certificate902.interval.Contains x) : ∃ c∈certificate902.cells, c.region.interval.Contains x := rat_cut_group_covers certificate902 numericValid902 hx

def certificate903 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate602,PopulationCertificates.Batch030.certificate602,[MergedCutCells.Batch276.certificate3318,MergedCutCells.Batch276.certificate3319,MergedCutCells.Batch276.certificate3320],(419695908699871597/500000000000000000),(some (1100533289/1000000000)),(1/2),(1425884078277386199/1000000000000000000),(some (64673849579141539/200000000000000000)),(some (99221585519392613/1000000000000000000))⟩
theorem numericValid903 : certificate903.NumericValid := by decide +kernel
theorem cellsSound903 : ∀ c∈certificate903.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3318,MergedCutCells.Batch276.certificate3319,MergedCutCells.Batch276.certificate3320], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3318,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3319,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3320,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric903 : ∀ c∈certificate903.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3318,MergedCutCells.Batch276.certificate3319,MergedCutCells.Batch276.certificate3320], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3318,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3319,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3320,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid903 : ∀ c∈certificate903.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3318,MergedCutCells.Batch276.certificate3319,MergedCutCells.Batch276.certificate3320], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid302,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid302,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid302,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches903 : ∀ c∈certificate903.cells, c.population=certificate903.population := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3318,MergedCutCells.Batch276.certificate3319,MergedCutCells.Batch276.certificate3320], c.population=PopulationCertificates.Batch030.certificate602
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers903 {x : ℝ} (hx : certificate903.interval.Contains x) : ∃ c∈certificate903.cells, c.region.interval.Contains x := rat_cut_group_covers certificate903 numericValid903 hx

def certificate904 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate602,PopulationCertificates.Batch030.certificate602,[MergedCutCells.Batch276.certificate3321,MergedCutCells.Batch276.certificate3322,MergedCutCells.Batch276.certificate3323,MergedCutCells.Batch277.certificate3324,MergedCutCells.Batch277.certificate3325],(1100533289/1000000000),none,(1/2),(69762460760669509/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid904 : certificate904.NumericValid := by decide +kernel
theorem cellsSound904 : ∀ c∈certificate904.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3321,MergedCutCells.Batch276.certificate3322,MergedCutCells.Batch276.certificate3323,MergedCutCells.Batch277.certificate3324,MergedCutCells.Batch277.certificate3325], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3321,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.sound3323,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3324,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3325,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric904 : ∀ c∈certificate904.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3321,MergedCutCells.Batch276.certificate3322,MergedCutCells.Batch276.certificate3323,MergedCutCells.Batch277.certificate3324,MergedCutCells.Batch277.certificate3325], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3321,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch276.numericValid3323,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3324,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3325,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid904 : ∀ c∈certificate904.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3321,MergedCutCells.Batch276.certificate3322,MergedCutCells.Batch276.certificate3323,MergedCutCells.Batch277.certificate3324,MergedCutCells.Batch277.certificate3325], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches904 : ∀ c∈certificate904.cells, c.population=certificate904.population := by
  change ∀ c∈[MergedCutCells.Batch276.certificate3321,MergedCutCells.Batch276.certificate3322,MergedCutCells.Batch276.certificate3323,MergedCutCells.Batch277.certificate3324,MergedCutCells.Batch277.certificate3325], c.population=PopulationCertificates.Batch030.certificate602
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers904 {x : ℝ} (hx : certificate904.interval.Contains x) : ∃ c∈certificate904.cells, c.region.interval.Contains x := rat_cut_group_covers certificate904 numericValid904 hx

def certificate905 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate603,PopulationCertificates.Batch030.certificate603,[MergedCutCells.Batch277.certificate3326,MergedCutCells.Batch277.certificate3327,MergedCutCells.Batch277.certificate3328],(9713003383763258499/1000000000000000000),none,(1/2),(1742103822344547879/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid905 : certificate905.NumericValid := by decide +kernel
theorem cellsSound905 : ∀ c∈certificate905.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3326,MergedCutCells.Batch277.certificate3327,MergedCutCells.Batch277.certificate3328], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3326,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3327,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3328,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric905 : ∀ c∈certificate905.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3326,MergedCutCells.Batch277.certificate3327,MergedCutCells.Batch277.certificate3328], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3326,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3327,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3328,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid905 : ∀ c∈certificate905.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3326,MergedCutCells.Batch277.certificate3327,MergedCutCells.Batch277.certificate3328], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches905 : ∀ c∈certificate905.cells, c.population=certificate905.population := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3326,MergedCutCells.Batch277.certificate3327,MergedCutCells.Batch277.certificate3328], c.population=PopulationCertificates.Batch030.certificate603
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers905 {x : ℝ} (hx : certificate905.interval.Contains x) : ∃ c∈certificate905.cells, c.region.interval.Contains x := rat_cut_group_covers certificate905 numericValid905 hx

def certificate906 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate604,PopulationCertificates.Batch030.certificate604,[MergedCutCells.Batch277.certificate3329,MergedCutCells.Batch277.certificate3330,MergedCutCells.Batch277.certificate3331],(169165261090208317/200000000000000000),(some (135190699/125000000)),(1/2),(1492632602922206257/1000000000000000000),(some (326145407152363893/1000000000000000000)),(some (3140128943942533/31250000000000000))⟩
theorem numericValid906 : certificate906.NumericValid := by decide +kernel
theorem cellsSound906 : ∀ c∈certificate906.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3329,MergedCutCells.Batch277.certificate3330,MergedCutCells.Batch277.certificate3331], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3329,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3331,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric906 : ∀ c∈certificate906.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3329,MergedCutCells.Batch277.certificate3330,MergedCutCells.Batch277.certificate3331], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3329,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3331,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid906 : ∀ c∈certificate906.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3329,MergedCutCells.Batch277.certificate3330,MergedCutCells.Batch277.certificate3331], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid303,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid303,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid303,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches906 : ∀ c∈certificate906.cells, c.population=certificate906.population := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3329,MergedCutCells.Batch277.certificate3330,MergedCutCells.Batch277.certificate3331], c.population=PopulationCertificates.Batch030.certificate604
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers906 {x : ℝ} (hx : certificate906.interval.Contains x) : ∃ c∈certificate906.cells, c.region.interval.Contains x := rat_cut_group_covers certificate906 numericValid906 hx

def certificate907 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate604,PopulationCertificates.Batch030.certificate604,[MergedCutCells.Batch277.certificate3332,MergedCutCells.Batch277.certificate3333,MergedCutCells.Batch277.certificate3334,MergedCutCells.Batch277.certificate3335,MergedCutCells.Batch278.certificate3336,MergedCutCells.Batch278.certificate3337,MergedCutCells.Batch278.certificate3338],(135190699/125000000),none,(1/2),(1454833962703275259/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid907 : certificate907.NumericValid := by decide +kernel
theorem cellsSound907 : ∀ c∈certificate907.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3332,MergedCutCells.Batch277.certificate3333,MergedCutCells.Batch277.certificate3334,MergedCutCells.Batch277.certificate3335,MergedCutCells.Batch278.certificate3336,MergedCutCells.Batch278.certificate3337,MergedCutCells.Batch278.certificate3338], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3332,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3333,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.sound3335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3336,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3337,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3338,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric907 : ∀ c∈certificate907.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3332,MergedCutCells.Batch277.certificate3333,MergedCutCells.Batch277.certificate3334,MergedCutCells.Batch277.certificate3335,MergedCutCells.Batch278.certificate3336,MergedCutCells.Batch278.certificate3337,MergedCutCells.Batch278.certificate3338], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3332,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3333,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch277.numericValid3335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3336,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3337,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3338,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid907 : ∀ c∈certificate907.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3332,MergedCutCells.Batch277.certificate3333,MergedCutCells.Batch277.certificate3334,MergedCutCells.Batch277.certificate3335,MergedCutCells.Batch278.certificate3336,MergedCutCells.Batch278.certificate3337,MergedCutCells.Batch278.certificate3338], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches907 : ∀ c∈certificate907.cells, c.population=certificate907.population := by
  change ∀ c∈[MergedCutCells.Batch277.certificate3332,MergedCutCells.Batch277.certificate3333,MergedCutCells.Batch277.certificate3334,MergedCutCells.Batch277.certificate3335,MergedCutCells.Batch278.certificate3336,MergedCutCells.Batch278.certificate3337,MergedCutCells.Batch278.certificate3338], c.population=PopulationCertificates.Batch030.certificate604
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers907 {x : ℝ} (hx : certificate907.interval.Contains x) : ∃ c∈certificate907.cells, c.region.interval.Contains x := rat_cut_group_covers certificate907 numericValid907 hx

def certificate908 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate605,PopulationCertificates.Batch030.certificate605,[MergedCutCells.Batch278.certificate3339,MergedCutCells.Batch278.certificate3340,MergedCutCells.Batch278.certificate3341],(9606376526945960059/1000000000000000000),none,(1/2),(1753900190708581337/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid908 : certificate908.NumericValid := by decide +kernel
theorem cellsSound908 : ∀ c∈certificate908.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3339,MergedCutCells.Batch278.certificate3340,MergedCutCells.Batch278.certificate3341], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3339,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3341,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric908 : ∀ c∈certificate908.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3339,MergedCutCells.Batch278.certificate3340,MergedCutCells.Batch278.certificate3341], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3339,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3341,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid908 : ∀ c∈certificate908.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3339,MergedCutCells.Batch278.certificate3340,MergedCutCells.Batch278.certificate3341], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches908 : ∀ c∈certificate908.cells, c.population=certificate908.population := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3339,MergedCutCells.Batch278.certificate3340,MergedCutCells.Batch278.certificate3341], c.population=PopulationCertificates.Batch030.certificate605
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers908 {x : ℝ} (hx : certificate908.interval.Contains x) : ∃ c∈certificate908.cells, c.region.interval.Contains x := rat_cut_group_covers certificate908 numericValid908 hx

def certificate909 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate606,PopulationCertificates.Batch030.certificate606,[MergedCutCells.Batch278.certificate3342,MergedCutCells.Batch278.certificate3343,MergedCutCells.Batch278.certificate3344],(212089092834173381/250000000000000000),(some (542288309/500000000)),(1/2),(76347582529389909/50000000000000000),(some (330145653351543997/1000000000000000000)),(some (10231761387322933/100000000000000000))⟩
theorem numericValid909 : certificate909.NumericValid := by decide +kernel
theorem cellsSound909 : ∀ c∈certificate909.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3342,MergedCutCells.Batch278.certificate3343,MergedCutCells.Batch278.certificate3344], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3342,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3343,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3344,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric909 : ∀ c∈certificate909.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3342,MergedCutCells.Batch278.certificate3343,MergedCutCells.Batch278.certificate3344], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3342,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3343,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3344,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid909 : ∀ c∈certificate909.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3342,MergedCutCells.Batch278.certificate3343,MergedCutCells.Batch278.certificate3344], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid304,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid304,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid304,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches909 : ∀ c∈certificate909.cells, c.population=certificate909.population := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3342,MergedCutCells.Batch278.certificate3343,MergedCutCells.Batch278.certificate3344], c.population=PopulationCertificates.Batch030.certificate606
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers909 {x : ℝ} (hx : certificate909.interval.Contains x) : ∃ c∈certificate909.cells, c.region.interval.Contains x := rat_cut_group_covers certificate909 numericValid909 hx

def certificate910 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate606,PopulationCertificates.Batch030.certificate606,[MergedCutCells.Batch278.certificate3345,MergedCutCells.Batch278.certificate3346,MergedCutCells.Batch278.certificate3347,MergedCutCells.Batch279.certificate3348,MergedCutCells.Batch279.certificate3349,MergedCutCells.Batch279.certificate3350],(542288309/500000000),none,(1/2),(748550857221949757/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid910 : certificate910.NumericValid := by decide +kernel
theorem cellsSound910 : ∀ c∈certificate910.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3345,MergedCutCells.Batch278.certificate3346,MergedCutCells.Batch278.certificate3347,MergedCutCells.Batch279.certificate3348,MergedCutCells.Batch279.certificate3349,MergedCutCells.Batch279.certificate3350], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3345,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3346,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.sound3347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3348,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3349,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3350,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric910 : ∀ c∈certificate910.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3345,MergedCutCells.Batch278.certificate3346,MergedCutCells.Batch278.certificate3347,MergedCutCells.Batch279.certificate3348,MergedCutCells.Batch279.certificate3349,MergedCutCells.Batch279.certificate3350], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3345,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3346,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch278.numericValid3347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3348,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3349,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3350,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid910 : ∀ c∈certificate910.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3345,MergedCutCells.Batch278.certificate3346,MergedCutCells.Batch278.certificate3347,MergedCutCells.Batch279.certificate3348,MergedCutCells.Batch279.certificate3349,MergedCutCells.Batch279.certificate3350], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches910 : ∀ c∈certificate910.cells, c.population=certificate910.population := by
  change ∀ c∈[MergedCutCells.Batch278.certificate3345,MergedCutCells.Batch278.certificate3346,MergedCutCells.Batch278.certificate3347,MergedCutCells.Batch279.certificate3348,MergedCutCells.Batch279.certificate3349,MergedCutCells.Batch279.certificate3350], c.population=PopulationCertificates.Batch030.certificate606
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers910 {x : ℝ} (hx : certificate910.interval.Contains x) : ∃ c∈certificate910.cells, c.region.interval.Contains x := rat_cut_group_covers certificate910 numericValid910 hx

def certificate911 : RatCutGroup := ⟨GeometryCertificates.Batch030.certificate607,PopulationCertificates.Batch030.certificate607,[MergedCutCells.Batch279.certificate3351,MergedCutCells.Batch279.certificate3352,MergedCutCells.Batch279.certificate3353,MergedCutCells.Batch279.certificate3354],(9643510346704288107/1000000000000000000),none,(1/2),(3553738991070302197/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid911 : certificate911.NumericValid := by decide +kernel
theorem cellsSound911 : ∀ c∈certificate911.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3351,MergedCutCells.Batch279.certificate3352,MergedCutCells.Batch279.certificate3353,MergedCutCells.Batch279.certificate3354], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3352,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3353,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.sound3354,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric911 : ∀ c∈certificate911.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3351,MergedCutCells.Batch279.certificate3352,MergedCutCells.Batch279.certificate3353,MergedCutCells.Batch279.certificate3354], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3352,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3353,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch279.numericValid3354,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid911 : ∀ c∈certificate911.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3351,MergedCutCells.Batch279.certificate3352,MergedCutCells.Batch279.certificate3353,MergedCutCells.Batch279.certificate3354], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches911 : ∀ c∈certificate911.cells, c.population=certificate911.population := by
  change ∀ c∈[MergedCutCells.Batch279.certificate3351,MergedCutCells.Batch279.certificate3352,MergedCutCells.Batch279.certificate3353,MergedCutCells.Batch279.certificate3354], c.population=PopulationCertificates.Batch030.certificate607
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers911 {x : ℝ} (hx : certificate911.interval.Contains x) : ∃ c∈certificate911.cells, c.region.interval.Contains x := rat_cut_group_covers certificate911 numericValid911 hx

end Cycle12.MergedCutGroups.Batch075
