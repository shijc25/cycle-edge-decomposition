import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch028
import Cycle12.GeometryCertificates.Batch029
import Cycle12.MergedCutCells.Batch263
import Cycle12.MergedCutCells.Batch264
import Cycle12.MergedCutCells.Batch265
import Cycle12.MergedCutCells.Batch266
import Cycle12.MergedCutCells.Batch267
import Cycle12.PopulationCertificates.Batch028
import Cycle12.PopulationCertificates.Batch029

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch072

def certificate864 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate576,PopulationCertificates.Batch028.certificate576,[MergedCutCells.Batch263.certificate3163,MergedCutCells.Batch263.certificate3164],(11874188398143493/15625000000000000),(some (109959709/100000000)),(1/2),(386332211115928019/500000000000000000),(some (256956412042058967/1000000000000000000)),(some (35643703776955837/500000000000000000))⟩
theorem numericValid864 : certificate864.NumericValid := by decide +kernel
theorem cellsSound864 : ∀ c∈certificate864.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3163,MergedCutCells.Batch263.certificate3164], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3164,List.forall_mem_nil _⟩⟩
theorem cellsNumeric864 : ∀ c∈certificate864.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3163,MergedCutCells.Batch263.certificate3164], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3164,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid864 : ∀ c∈certificate864.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3163,MergedCutCells.Batch263.certificate3164], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid289,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid289,List.forall_mem_nil _⟩⟩
theorem populationMatches864 : ∀ c∈certificate864.cells, c.population=certificate864.population := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3163,MergedCutCells.Batch263.certificate3164], c.population=PopulationCertificates.Batch028.certificate576
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers864 {x : ℝ} (hx : certificate864.interval.Contains x) : ∃ c∈certificate864.cells, c.region.interval.Contains x := rat_cut_group_covers certificate864 numericValid864 hx

def certificate865 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate576,PopulationCertificates.Batch028.certificate576,[MergedCutCells.Batch263.certificate3165,MergedCutCells.Batch263.certificate3166,MergedCutCells.Batch263.certificate3167,MergedCutCells.Batch264.certificate3168,MergedCutCells.Batch264.certificate3169,MergedCutCells.Batch264.certificate3170],(109959709/100000000),none,(1/2),(37597034693442107/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid865 : certificate865.NumericValid := by decide +kernel
theorem cellsSound865 : ∀ c∈certificate865.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3165,MergedCutCells.Batch263.certificate3166,MergedCutCells.Batch263.certificate3167,MergedCutCells.Batch264.certificate3168,MergedCutCells.Batch264.certificate3169,MergedCutCells.Batch264.certificate3170], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3166,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3167,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3170,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric865 : ∀ c∈certificate865.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3165,MergedCutCells.Batch263.certificate3166,MergedCutCells.Batch263.certificate3167,MergedCutCells.Batch264.certificate3168,MergedCutCells.Batch264.certificate3169,MergedCutCells.Batch264.certificate3170], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3166,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3167,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3170,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid865 : ∀ c∈certificate865.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3165,MergedCutCells.Batch263.certificate3166,MergedCutCells.Batch263.certificate3167,MergedCutCells.Batch264.certificate3168,MergedCutCells.Batch264.certificate3169,MergedCutCells.Batch264.certificate3170], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches865 : ∀ c∈certificate865.cells, c.population=certificate865.population := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3165,MergedCutCells.Batch263.certificate3166,MergedCutCells.Batch263.certificate3167,MergedCutCells.Batch264.certificate3168,MergedCutCells.Batch264.certificate3169,MergedCutCells.Batch264.certificate3170], c.population=PopulationCertificates.Batch028.certificate576
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers865 {x : ℝ} (hx : certificate865.interval.Contains x) : ∃ c∈certificate865.cells, c.region.interval.Contains x := rat_cut_group_covers certificate865 numericValid865 hx

def certificate866 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate577,PopulationCertificates.Batch028.certificate577,[MergedCutCells.Batch264.certificate3171,MergedCutCells.Batch264.certificate3172,MergedCutCells.Batch264.certificate3173,MergedCutCells.Batch264.certificate3174],(10026317706723052973/1000000000000000000),none,(1/2),(1171955057834569501/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid866 : certificate866.NumericValid := by decide +kernel
theorem cellsSound866 : ∀ c∈certificate866.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3171,MergedCutCells.Batch264.certificate3172,MergedCutCells.Batch264.certificate3173,MergedCutCells.Batch264.certificate3174], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3173,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3174,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric866 : ∀ c∈certificate866.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3171,MergedCutCells.Batch264.certificate3172,MergedCutCells.Batch264.certificate3173,MergedCutCells.Batch264.certificate3174], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3173,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3174,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid866 : ∀ c∈certificate866.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3171,MergedCutCells.Batch264.certificate3172,MergedCutCells.Batch264.certificate3173,MergedCutCells.Batch264.certificate3174], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches866 : ∀ c∈certificate866.cells, c.population=certificate866.population := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3171,MergedCutCells.Batch264.certificate3172,MergedCutCells.Batch264.certificate3173,MergedCutCells.Batch264.certificate3174], c.population=PopulationCertificates.Batch028.certificate577
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers866 {x : ℝ} (hx : certificate866.interval.Contains x) : ∃ c∈certificate866.cells, c.region.interval.Contains x := rat_cut_group_covers certificate866 numericValid866 hx

def certificate867 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate578,PopulationCertificates.Batch028.certificate578,[MergedCutCells.Batch264.certificate3175,MergedCutCells.Batch264.certificate3176,MergedCutCells.Batch264.certificate3177],(384619563701752801/500000000000000000),(some (555957067/500000000)),(1/2),(831136220788132213/1000000000000000000),(some (132698487382552309/500000000000000000)),(some (582870173971899/7812500000000000))⟩
theorem numericValid867 : certificate867.NumericValid := by decide +kernel
theorem cellsSound867 : ∀ c∈certificate867.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3175,MergedCutCells.Batch264.certificate3176,MergedCutCells.Batch264.certificate3177], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3176,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3177,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric867 : ∀ c∈certificate867.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3175,MergedCutCells.Batch264.certificate3176,MergedCutCells.Batch264.certificate3177], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3176,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3177,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid867 : ∀ c∈certificate867.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3175,MergedCutCells.Batch264.certificate3176,MergedCutCells.Batch264.certificate3177], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid290,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid290,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid290,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches867 : ∀ c∈certificate867.cells, c.population=certificate867.population := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3175,MergedCutCells.Batch264.certificate3176,MergedCutCells.Batch264.certificate3177], c.population=PopulationCertificates.Batch028.certificate578
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers867 {x : ℝ} (hx : certificate867.interval.Contains x) : ∃ c∈certificate867.cells, c.region.interval.Contains x := rat_cut_group_covers certificate867 numericValid867 hx

def certificate868 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate578,PopulationCertificates.Batch028.certificate578,[MergedCutCells.Batch264.certificate3178,MergedCutCells.Batch264.certificate3179,MergedCutCells.Batch265.certificate3180,MergedCutCells.Batch265.certificate3181,MergedCutCells.Batch265.certificate3182],(555957067/500000000),none,(1/2),(808758169017689551/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid868 : certificate868.NumericValid := by decide +kernel
theorem cellsSound868 : ∀ c∈certificate868.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3178,MergedCutCells.Batch264.certificate3179,MergedCutCells.Batch265.certificate3180,MergedCutCells.Batch265.certificate3181,MergedCutCells.Batch265.certificate3182], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3178,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.sound3179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3182,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric868 : ∀ c∈certificate868.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3178,MergedCutCells.Batch264.certificate3179,MergedCutCells.Batch265.certificate3180,MergedCutCells.Batch265.certificate3181,MergedCutCells.Batch265.certificate3182], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3178,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch264.numericValid3179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3182,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid868 : ∀ c∈certificate868.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3178,MergedCutCells.Batch264.certificate3179,MergedCutCells.Batch265.certificate3180,MergedCutCells.Batch265.certificate3181,MergedCutCells.Batch265.certificate3182], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches868 : ∀ c∈certificate868.cells, c.population=certificate868.population := by
  change ∀ c∈[MergedCutCells.Batch264.certificate3178,MergedCutCells.Batch264.certificate3179,MergedCutCells.Batch265.certificate3180,MergedCutCells.Batch265.certificate3181,MergedCutCells.Batch265.certificate3182], c.population=PopulationCertificates.Batch028.certificate578
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers868 {x : ℝ} (hx : certificate868.interval.Contains x) : ∃ c∈certificate868.cells, c.region.interval.Contains x := rat_cut_group_covers certificate868 numericValid868 hx

def certificate869 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate579,PopulationCertificates.Batch028.certificate579,[MergedCutCells.Batch265.certificate3183,MergedCutCells.Batch265.certificate3184,MergedCutCells.Batch265.certificate3185],(4988942145967276989/500000000000000000),none,(1/2),(5958912909192337987/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid869 : certificate869.NumericValid := by decide +kernel
theorem cellsSound869 : ∀ c∈certificate869.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3183,MergedCutCells.Batch265.certificate3184,MergedCutCells.Batch265.certificate3185], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3184,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3185,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric869 : ∀ c∈certificate869.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3183,MergedCutCells.Batch265.certificate3184,MergedCutCells.Batch265.certificate3185], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3184,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3185,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid869 : ∀ c∈certificate869.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3183,MergedCutCells.Batch265.certificate3184,MergedCutCells.Batch265.certificate3185], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches869 : ∀ c∈certificate869.cells, c.population=certificate869.population := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3183,MergedCutCells.Batch265.certificate3184,MergedCutCells.Batch265.certificate3185], c.population=PopulationCertificates.Batch028.certificate579
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers869 {x : ℝ} (hx : certificate869.interval.Contains x) : ∃ c∈certificate869.cells, c.region.interval.Contains x := rat_cut_group_covers certificate869 numericValid869 hx

def certificate870 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate580,PopulationCertificates.Batch029.certificate580,[MergedCutCells.Batch265.certificate3186,MergedCutCells.Batch265.certificate3187],(386815213765820029/500000000000000000),(some (1092740557/1000000000)),(1/2),(87616478895680819/100000000000000000),(some (267995292869182493/1000000000000000000)),(some (18910589108701557/250000000000000000))⟩
theorem numericValid870 : certificate870.NumericValid := by decide +kernel
theorem cellsSound870 : ∀ c∈certificate870.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3186,MergedCutCells.Batch265.certificate3187], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3186,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3187,List.forall_mem_nil _⟩⟩
theorem cellsNumeric870 : ∀ c∈certificate870.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3186,MergedCutCells.Batch265.certificate3187], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3186,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3187,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid870 : ∀ c∈certificate870.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3186,MergedCutCells.Batch265.certificate3187], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid291,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid291,List.forall_mem_nil _⟩⟩
theorem populationMatches870 : ∀ c∈certificate870.cells, c.population=certificate870.population := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3186,MergedCutCells.Batch265.certificate3187], c.population=PopulationCertificates.Batch029.certificate580
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers870 {x : ℝ} (hx : certificate870.interval.Contains x) : ∃ c∈certificate870.cells, c.region.interval.Contains x := rat_cut_group_covers certificate870 numericValid870 hx

def certificate871 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate580,PopulationCertificates.Batch029.certificate580,[MergedCutCells.Batch265.certificate3188,MergedCutCells.Batch265.certificate3189,MergedCutCells.Batch265.certificate3190,MergedCutCells.Batch265.certificate3191,MergedCutCells.Batch266.certificate3192,MergedCutCells.Batch266.certificate3193,MergedCutCells.Batch266.certificate3194],(1092740557/1000000000),none,(1/2),(859592534577685351/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid871 : certificate871.NumericValid := by decide +kernel
theorem cellsSound871 : ∀ c∈certificate871.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3188,MergedCutCells.Batch265.certificate3189,MergedCutCells.Batch265.certificate3190,MergedCutCells.Batch265.certificate3191,MergedCutCells.Batch266.certificate3192,MergedCutCells.Batch266.certificate3193,MergedCutCells.Batch266.certificate3194], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3189,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.sound3191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3192,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3194,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric871 : ∀ c∈certificate871.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3188,MergedCutCells.Batch265.certificate3189,MergedCutCells.Batch265.certificate3190,MergedCutCells.Batch265.certificate3191,MergedCutCells.Batch266.certificate3192,MergedCutCells.Batch266.certificate3193,MergedCutCells.Batch266.certificate3194], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3189,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch265.numericValid3191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3192,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3194,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid871 : ∀ c∈certificate871.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3188,MergedCutCells.Batch265.certificate3189,MergedCutCells.Batch265.certificate3190,MergedCutCells.Batch265.certificate3191,MergedCutCells.Batch266.certificate3192,MergedCutCells.Batch266.certificate3193,MergedCutCells.Batch266.certificate3194], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches871 : ∀ c∈certificate871.cells, c.population=certificate871.population := by
  change ∀ c∈[MergedCutCells.Batch265.certificate3188,MergedCutCells.Batch265.certificate3189,MergedCutCells.Batch265.certificate3190,MergedCutCells.Batch265.certificate3191,MergedCutCells.Batch266.certificate3192,MergedCutCells.Batch266.certificate3193,MergedCutCells.Batch266.certificate3194], c.population=PopulationCertificates.Batch029.certificate580
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers871 {x : ℝ} (hx : certificate871.interval.Contains x) : ∃ c∈certificate871.cells, c.region.interval.Contains x := rat_cut_group_covers certificate871 numericValid871 hx

def certificate872 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate581,PopulationCertificates.Batch029.certificate581,[MergedCutCells.Batch266.certificate3195,MergedCutCells.Batch266.certificate3196,MergedCutCells.Batch266.certificate3197],(4991273796655721359/500000000000000000),none,(1/2),(6086497049930446989/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid872 : certificate872.NumericValid := by decide +kernel
theorem cellsSound872 : ∀ c∈certificate872.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3195,MergedCutCells.Batch266.certificate3196,MergedCutCells.Batch266.certificate3197], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3196,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3197,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric872 : ∀ c∈certificate872.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3195,MergedCutCells.Batch266.certificate3196,MergedCutCells.Batch266.certificate3197], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3196,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3197,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid872 : ∀ c∈certificate872.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3195,MergedCutCells.Batch266.certificate3196,MergedCutCells.Batch266.certificate3197], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches872 : ∀ c∈certificate872.cells, c.population=certificate872.population := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3195,MergedCutCells.Batch266.certificate3196,MergedCutCells.Batch266.certificate3197], c.population=PopulationCertificates.Batch029.certificate581
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers872 {x : ℝ} (hx : certificate872.interval.Contains x) : ∃ c∈certificate872.cells, c.region.interval.Contains x := rat_cut_group_covers certificate872 numericValid872 hx

def certificate873 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate582,PopulationCertificates.Batch029.certificate582,[MergedCutCells.Batch266.certificate3198,MergedCutCells.Batch266.certificate3199,MergedCutCells.Batch266.certificate3200],(390006902866512773/500000000000000000),(some (275262277/250000000)),(1/2),(457411784212087653/500000000000000000),(some (136155643267941193/500000000000000000)),(some (77375146218873251/1000000000000000000))⟩
theorem numericValid873 : certificate873.NumericValid := by decide +kernel
theorem cellsSound873 : ∀ c∈certificate873.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3198,MergedCutCells.Batch266.certificate3199,MergedCutCells.Batch266.certificate3200], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3198,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3200,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric873 : ∀ c∈certificate873.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3198,MergedCutCells.Batch266.certificate3199,MergedCutCells.Batch266.certificate3200], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3198,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3200,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid873 : ∀ c∈certificate873.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3198,MergedCutCells.Batch266.certificate3199,MergedCutCells.Batch266.certificate3200], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid292,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid292,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid292,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches873 : ∀ c∈certificate873.cells, c.population=certificate873.population := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3198,MergedCutCells.Batch266.certificate3199,MergedCutCells.Batch266.certificate3200], c.population=PopulationCertificates.Batch029.certificate582
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers873 {x : ℝ} (hx : certificate873.interval.Contains x) : ∃ c∈certificate873.cells, c.region.interval.Contains x := rat_cut_group_covers certificate873 numericValid873 hx

def certificate874 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate582,PopulationCertificates.Batch029.certificate582,[MergedCutCells.Batch266.certificate3201,MergedCutCells.Batch266.certificate3202,MergedCutCells.Batch266.certificate3203,MergedCutCells.Batch267.certificate3204,MergedCutCells.Batch267.certificate3205,MergedCutCells.Batch267.certificate3206],(275262277/250000000),none,(1/2),(55585631533552757/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid874 : certificate874.NumericValid := by decide +kernel
theorem cellsSound874 : ∀ c∈certificate874.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3201,MergedCutCells.Batch266.certificate3202,MergedCutCells.Batch266.certificate3203,MergedCutCells.Batch267.certificate3204,MergedCutCells.Batch267.certificate3205,MergedCutCells.Batch267.certificate3206], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3202,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.sound3203,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3205,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3206,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric874 : ∀ c∈certificate874.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3201,MergedCutCells.Batch266.certificate3202,MergedCutCells.Batch266.certificate3203,MergedCutCells.Batch267.certificate3204,MergedCutCells.Batch267.certificate3205,MergedCutCells.Batch267.certificate3206], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3202,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch266.numericValid3203,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3205,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3206,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid874 : ∀ c∈certificate874.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3201,MergedCutCells.Batch266.certificate3202,MergedCutCells.Batch266.certificate3203,MergedCutCells.Batch267.certificate3204,MergedCutCells.Batch267.certificate3205,MergedCutCells.Batch267.certificate3206], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches874 : ∀ c∈certificate874.cells, c.population=certificate874.population := by
  change ∀ c∈[MergedCutCells.Batch266.certificate3201,MergedCutCells.Batch266.certificate3202,MergedCutCells.Batch266.certificate3203,MergedCutCells.Batch267.certificate3204,MergedCutCells.Batch267.certificate3205,MergedCutCells.Batch267.certificate3206], c.population=PopulationCertificates.Batch029.certificate582
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers874 {x : ℝ} (hx : certificate874.interval.Contains x) : ∃ c∈certificate874.cells, c.region.interval.Contains x := rat_cut_group_covers certificate874 numericValid874 hx

def certificate875 : RatCutGroup := ⟨GeometryCertificates.Batch029.certificate583,PopulationCertificates.Batch029.certificate583,[MergedCutCells.Batch267.certificate3207,MergedCutCells.Batch267.certificate3208,MergedCutCells.Batch267.certificate3209],(2504075166044100399/250000000000000000),none,(1/2),(6159613682338050011/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid875 : certificate875.NumericValid := by decide +kernel
theorem cellsSound875 : ∀ c∈certificate875.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3207,MergedCutCells.Batch267.certificate3208,MergedCutCells.Batch267.certificate3209], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3208,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.sound3209,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric875 : ∀ c∈certificate875.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3207,MergedCutCells.Batch267.certificate3208,MergedCutCells.Batch267.certificate3209], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3208,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch267.numericValid3209,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid875 : ∀ c∈certificate875.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3207,MergedCutCells.Batch267.certificate3208,MergedCutCells.Batch267.certificate3209], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches875 : ∀ c∈certificate875.cells, c.population=certificate875.population := by
  change ∀ c∈[MergedCutCells.Batch267.certificate3207,MergedCutCells.Batch267.certificate3208,MergedCutCells.Batch267.certificate3209], c.population=PopulationCertificates.Batch029.certificate583
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers875 {x : ℝ} (hx : certificate875.interval.Contains x) : ∃ c∈certificate875.cells, c.region.interval.Contains x := rat_cut_group_covers certificate875 numericValid875 hx

end Cycle12.MergedCutGroups.Batch072
