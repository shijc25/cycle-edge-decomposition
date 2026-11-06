import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch028
import Cycle12.MergedCutCells.Batch256
import Cycle12.MergedCutCells.Batch257
import Cycle12.MergedCutCells.Batch258
import Cycle12.MergedCutCells.Batch259
import Cycle12.PopulationCertificates.Batch028

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch070

def certificate840 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate560,PopulationCertificates.Batch028.certificate560,[MergedCutCells.Batch256.certificate3072,MergedCutCells.Batch256.certificate3073,MergedCutCells.Batch256.certificate3074],(695529929719077861/1000000000000000000),(some (1137049359/1000000000)),(1/2),(93596184449986847/200000000000000000),(some (49394148977091079/250000000000000000)),(some (49681576696995347/1000000000000000000))⟩
theorem numericValid840 : certificate840.NumericValid := by decide +kernel
theorem cellsSound840 : ∀ c∈certificate840.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3072,MergedCutCells.Batch256.certificate3073,MergedCutCells.Batch256.certificate3074], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3072,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3074,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric840 : ∀ c∈certificate840.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3072,MergedCutCells.Batch256.certificate3073,MergedCutCells.Batch256.certificate3074], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3072,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3074,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid840 : ∀ c∈certificate840.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3072,MergedCutCells.Batch256.certificate3073,MergedCutCells.Batch256.certificate3074], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid281,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid281,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid281,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches840 : ∀ c∈certificate840.cells, c.population=certificate840.population := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3072,MergedCutCells.Batch256.certificate3073,MergedCutCells.Batch256.certificate3074], c.population=PopulationCertificates.Batch028.certificate560
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers840 {x : ℝ} (hx : certificate840.interval.Contains x) : ∃ c∈certificate840.cells, c.region.interval.Contains x := rat_cut_group_covers certificate840 numericValid840 hx

def certificate841 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate560,PopulationCertificates.Batch028.certificate560,[MergedCutCells.Batch256.certificate3075,MergedCutCells.Batch256.certificate3076,MergedCutCells.Batch256.certificate3077,MergedCutCells.Batch256.certificate3078],(1137049359/1000000000),none,(1/2),(22603395568415959/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid841 : certificate841.NumericValid := by decide +kernel
theorem cellsSound841 : ∀ c∈certificate841.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3075,MergedCutCells.Batch256.certificate3076,MergedCutCells.Batch256.certificate3077,MergedCutCells.Batch256.certificate3078], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3075,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3077,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3078,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric841 : ∀ c∈certificate841.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3075,MergedCutCells.Batch256.certificate3076,MergedCutCells.Batch256.certificate3077,MergedCutCells.Batch256.certificate3078], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3075,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3077,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3078,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid841 : ∀ c∈certificate841.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3075,MergedCutCells.Batch256.certificate3076,MergedCutCells.Batch256.certificate3077,MergedCutCells.Batch256.certificate3078], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches841 : ∀ c∈certificate841.cells, c.population=certificate841.population := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3075,MergedCutCells.Batch256.certificate3076,MergedCutCells.Batch256.certificate3077,MergedCutCells.Batch256.certificate3078], c.population=PopulationCertificates.Batch028.certificate560
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers841 {x : ℝ} (hx : certificate841.interval.Contains x) : ∃ c∈certificate841.cells, c.region.interval.Contains x := rat_cut_group_covers certificate841 numericValid841 hx

def certificate842 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate561,PopulationCertificates.Batch028.certificate561,[MergedCutCells.Batch256.certificate3079,MergedCutCells.Batch256.certificate3080],(4974961364710269939/500000000000000000),none,(1/2),(1263998434948575269/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid842 : certificate842.NumericValid := by decide +kernel
theorem cellsSound842 : ∀ c∈certificate842.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3079,MergedCutCells.Batch256.certificate3080], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3079,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3080,List.forall_mem_nil _⟩⟩
theorem cellsNumeric842 : ∀ c∈certificate842.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3079,MergedCutCells.Batch256.certificate3080], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3079,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3080,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid842 : ∀ c∈certificate842.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3079,MergedCutCells.Batch256.certificate3080], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches842 : ∀ c∈certificate842.cells, c.population=certificate842.population := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3079,MergedCutCells.Batch256.certificate3080], c.population=PopulationCertificates.Batch028.certificate561
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers842 {x : ℝ} (hx : certificate842.interval.Contains x) : ∃ c∈certificate842.cells, c.region.interval.Contains x := rat_cut_group_covers certificate842 numericValid842 hx

def certificate843 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate562,PopulationCertificates.Batch028.certificate562,[MergedCutCells.Batch256.certificate3081,MergedCutCells.Batch256.certificate3082,MergedCutCells.Batch256.certificate3083],(704373297403367031/1000000000000000000),(some (56247297/50000000)),(1/2),(126077050198263333/250000000000000000),(some (51119519918987541/250000000000000000)),(some (26019902489636641/500000000000000000))⟩
theorem numericValid843 : certificate843.NumericValid := by decide +kernel
theorem cellsSound843 : ∀ c∈certificate843.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3081,MergedCutCells.Batch256.certificate3082,MergedCutCells.Batch256.certificate3083], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.sound3083,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric843 : ∀ c∈certificate843.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3081,MergedCutCells.Batch256.certificate3082,MergedCutCells.Batch256.certificate3083], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch256.numericValid3083,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid843 : ∀ c∈certificate843.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3081,MergedCutCells.Batch256.certificate3082,MergedCutCells.Batch256.certificate3083], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid282,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid282,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid282,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches843 : ∀ c∈certificate843.cells, c.population=certificate843.population := by
  change ∀ c∈[MergedCutCells.Batch256.certificate3081,MergedCutCells.Batch256.certificate3082,MergedCutCells.Batch256.certificate3083], c.population=PopulationCertificates.Batch028.certificate562
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers843 {x : ℝ} (hx : certificate843.interval.Contains x) : ∃ c∈certificate843.cells, c.region.interval.Contains x := rat_cut_group_covers certificate843 numericValid843 hx

def certificate844 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate562,PopulationCertificates.Batch028.certificate562,[MergedCutCells.Batch257.certificate3084,MergedCutCells.Batch257.certificate3085,MergedCutCells.Batch257.certificate3086,MergedCutCells.Batch257.certificate3087,MergedCutCells.Batch257.certificate3088],(56247297/50000000),none,(1/2),(487867315436349497/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid844 : certificate844.NumericValid := by decide +kernel
theorem cellsSound844 : ∀ c∈certificate844.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3084,MergedCutCells.Batch257.certificate3085,MergedCutCells.Batch257.certificate3086,MergedCutCells.Batch257.certificate3087,MergedCutCells.Batch257.certificate3088], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3084,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3085,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3087,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3088,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric844 : ∀ c∈certificate844.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3084,MergedCutCells.Batch257.certificate3085,MergedCutCells.Batch257.certificate3086,MergedCutCells.Batch257.certificate3087,MergedCutCells.Batch257.certificate3088], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3084,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3085,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3087,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3088,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid844 : ∀ c∈certificate844.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3084,MergedCutCells.Batch257.certificate3085,MergedCutCells.Batch257.certificate3086,MergedCutCells.Batch257.certificate3087,MergedCutCells.Batch257.certificate3088], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches844 : ∀ c∈certificate844.cells, c.population=certificate844.population := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3084,MergedCutCells.Batch257.certificate3085,MergedCutCells.Batch257.certificate3086,MergedCutCells.Batch257.certificate3087,MergedCutCells.Batch257.certificate3088], c.population=PopulationCertificates.Batch028.certificate562
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers844 {x : ℝ} (hx : certificate844.interval.Contains x) : ∃ c∈certificate844.cells, c.region.interval.Contains x := rat_cut_group_covers certificate844 numericValid844 hx

def certificate845 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate563,PopulationCertificates.Batch028.certificate563,[MergedCutCells.Batch257.certificate3089,MergedCutCells.Batch257.certificate3090],(9920695515166500201/1000000000000000000),none,(1/2),(40158736708948137/7812500000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid845 : certificate845.NumericValid := by decide +kernel
theorem cellsSound845 : ∀ c∈certificate845.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3089,MergedCutCells.Batch257.certificate3090], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3089,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3090,List.forall_mem_nil _⟩⟩
theorem cellsNumeric845 : ∀ c∈certificate845.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3089,MergedCutCells.Batch257.certificate3090], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3089,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3090,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid845 : ∀ c∈certificate845.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3089,MergedCutCells.Batch257.certificate3090], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches845 : ∀ c∈certificate845.cells, c.population=certificate845.population := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3089,MergedCutCells.Batch257.certificate3090], c.population=PopulationCertificates.Batch028.certificate563
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers845 {x : ℝ} (hx : certificate845.interval.Contains x) : ∃ c∈certificate845.cells, c.region.interval.Contains x := rat_cut_group_covers certificate845 numericValid845 hx

def certificate846 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate564,PopulationCertificates.Batch028.certificate564,[MergedCutCells.Batch257.certificate3091,MergedCutCells.Batch257.certificate3092,MergedCutCells.Batch257.certificate3093],(356832924358324177/500000000000000000),(some (1138237023/1000000000)),(1/2),(542203912656342519/1000000000000000000),(some (8501909151008189/40000000000000000)),(some (5484730426157351/100000000000000000))⟩
theorem numericValid846 : certificate846.NumericValid := by decide +kernel
theorem cellsSound846 : ∀ c∈certificate846.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3091,MergedCutCells.Batch257.certificate3092,MergedCutCells.Batch257.certificate3093], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3091,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3092,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3093,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric846 : ∀ c∈certificate846.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3091,MergedCutCells.Batch257.certificate3092,MergedCutCells.Batch257.certificate3093], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3091,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3092,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3093,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid846 : ∀ c∈certificate846.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3091,MergedCutCells.Batch257.certificate3092,MergedCutCells.Batch257.certificate3093], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid283,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid283,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid283,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches846 : ∀ c∈certificate846.cells, c.population=certificate846.population := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3091,MergedCutCells.Batch257.certificate3092,MergedCutCells.Batch257.certificate3093], c.population=PopulationCertificates.Batch028.certificate564
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers846 {x : ℝ} (hx : certificate846.interval.Contains x) : ∃ c∈certificate846.cells, c.region.interval.Contains x := rat_cut_group_covers certificate846 numericValid846 hx

def certificate847 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate564,PopulationCertificates.Batch028.certificate564,[MergedCutCells.Batch257.certificate3094,MergedCutCells.Batch257.certificate3095,MergedCutCells.Batch258.certificate3096,MergedCutCells.Batch258.certificate3097],(1138237023/1000000000),none,(1/2),(524657823120588387/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid847 : certificate847.NumericValid := by decide +kernel
theorem cellsSound847 : ∀ c∈certificate847.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3094,MergedCutCells.Batch257.certificate3095,MergedCutCells.Batch258.certificate3096,MergedCutCells.Batch258.certificate3097], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.sound3095,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3096,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3097,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric847 : ∀ c∈certificate847.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3094,MergedCutCells.Batch257.certificate3095,MergedCutCells.Batch258.certificate3096,MergedCutCells.Batch258.certificate3097], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch257.numericValid3095,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3096,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3097,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid847 : ∀ c∈certificate847.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3094,MergedCutCells.Batch257.certificate3095,MergedCutCells.Batch258.certificate3096,MergedCutCells.Batch258.certificate3097], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches847 : ∀ c∈certificate847.cells, c.population=certificate847.population := by
  change ∀ c∈[MergedCutCells.Batch257.certificate3094,MergedCutCells.Batch257.certificate3095,MergedCutCells.Batch258.certificate3096,MergedCutCells.Batch258.certificate3097], c.population=PopulationCertificates.Batch028.certificate564
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers847 {x : ℝ} (hx : certificate847.interval.Contains x) : ∃ c∈certificate847.cells, c.region.interval.Contains x := rat_cut_group_covers certificate847 numericValid847 hx

def certificate848 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate565,PopulationCertificates.Batch028.certificate565,[MergedCutCells.Batch258.certificate3098,MergedCutCells.Batch258.certificate3099],(9894663936877018079/1000000000000000000),none,(1/2),(1306779719079912417/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid848 : certificate848.NumericValid := by decide +kernel
theorem cellsSound848 : ∀ c∈certificate848.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3098,MergedCutCells.Batch258.certificate3099], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3098,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3099,List.forall_mem_nil _⟩⟩
theorem cellsNumeric848 : ∀ c∈certificate848.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3098,MergedCutCells.Batch258.certificate3099], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3098,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3099,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid848 : ∀ c∈certificate848.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3098,MergedCutCells.Batch258.certificate3099], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches848 : ∀ c∈certificate848.cells, c.population=certificate848.population := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3098,MergedCutCells.Batch258.certificate3099], c.population=PopulationCertificates.Batch028.certificate565
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers848 {x : ℝ} (hx : certificate848.interval.Contains x) : ∃ c∈certificate848.cells, c.region.interval.Contains x := rat_cut_group_covers certificate848 numericValid848 hx

def certificate849 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate566,PopulationCertificates.Batch028.certificate566,[MergedCutCells.Batch258.certificate3100,MergedCutCells.Batch258.certificate3101,MergedCutCells.Batch258.certificate3102],(360266041971624549/500000000000000000),(some (2807403/2500000)),(1/2),(567081803518169841/1000000000000000000),(some (54882748587713087/250000000000000000)),(some (57320774346407921/1000000000000000000))⟩
theorem numericValid849 : certificate849.NumericValid := by decide +kernel
theorem cellsSound849 : ∀ c∈certificate849.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3100,MergedCutCells.Batch258.certificate3101,MergedCutCells.Batch258.certificate3102], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3101,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3102,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric849 : ∀ c∈certificate849.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3100,MergedCutCells.Batch258.certificate3101,MergedCutCells.Batch258.certificate3102], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3101,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3102,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid849 : ∀ c∈certificate849.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3100,MergedCutCells.Batch258.certificate3101,MergedCutCells.Batch258.certificate3102], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid284,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid284,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid284,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches849 : ∀ c∈certificate849.cells, c.population=certificate849.population := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3100,MergedCutCells.Batch258.certificate3101,MergedCutCells.Batch258.certificate3102], c.population=PopulationCertificates.Batch028.certificate566
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers849 {x : ℝ} (hx : certificate849.interval.Contains x) : ∃ c∈certificate849.cells, c.region.interval.Contains x := rat_cut_group_covers certificate849 numericValid849 hx

def certificate850 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate566,PopulationCertificates.Batch028.certificate566,[MergedCutCells.Batch258.certificate3103,MergedCutCells.Batch258.certificate3104,MergedCutCells.Batch258.certificate3105,MergedCutCells.Batch258.certificate3106,MergedCutCells.Batch258.certificate3107],(2807403/2500000),none,(1/2),(6851133652867897/12500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid850 : certificate850.NumericValid := by decide +kernel
theorem cellsSound850 : ∀ c∈certificate850.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3103,MergedCutCells.Batch258.certificate3104,MergedCutCells.Batch258.certificate3105,MergedCutCells.Batch258.certificate3106,MergedCutCells.Batch258.certificate3107], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3103,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3104,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3105,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.sound3107,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric850 : ∀ c∈certificate850.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3103,MergedCutCells.Batch258.certificate3104,MergedCutCells.Batch258.certificate3105,MergedCutCells.Batch258.certificate3106,MergedCutCells.Batch258.certificate3107], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3103,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3104,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3105,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch258.numericValid3107,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid850 : ∀ c∈certificate850.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3103,MergedCutCells.Batch258.certificate3104,MergedCutCells.Batch258.certificate3105,MergedCutCells.Batch258.certificate3106,MergedCutCells.Batch258.certificate3107], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches850 : ∀ c∈certificate850.cells, c.population=certificate850.population := by
  change ∀ c∈[MergedCutCells.Batch258.certificate3103,MergedCutCells.Batch258.certificate3104,MergedCutCells.Batch258.certificate3105,MergedCutCells.Batch258.certificate3106,MergedCutCells.Batch258.certificate3107], c.population=PopulationCertificates.Batch028.certificate566
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers850 {x : ℝ} (hx : certificate850.interval.Contains x) : ∃ c∈certificate850.cells, c.region.interval.Contains x := rat_cut_group_covers certificate850 numericValid850 hx

def certificate851 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate567,PopulationCertificates.Batch028.certificate567,[MergedCutCells.Batch259.certificate3108,MergedCutCells.Batch259.certificate3109,MergedCutCells.Batch259.certificate3110],(100295051192647949/10000000000000000),none,(1/2),(5356535663152212829/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid851 : certificate851.NumericValid := by decide +kernel
theorem cellsSound851 : ∀ c∈certificate851.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3108,MergedCutCells.Batch259.certificate3109,MergedCutCells.Batch259.certificate3110], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3109,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3110,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric851 : ∀ c∈certificate851.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3108,MergedCutCells.Batch259.certificate3109,MergedCutCells.Batch259.certificate3110], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3109,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3110,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid851 : ∀ c∈certificate851.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3108,MergedCutCells.Batch259.certificate3109,MergedCutCells.Batch259.certificate3110], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches851 : ∀ c∈certificate851.cells, c.population=certificate851.population := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3108,MergedCutCells.Batch259.certificate3109,MergedCutCells.Batch259.certificate3110], c.population=PopulationCertificates.Batch028.certificate567
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers851 {x : ℝ} (hx : certificate851.interval.Contains x) : ∃ c∈certificate851.cells, c.region.interval.Contains x := rat_cut_group_covers certificate851 numericValid851 hx

end Cycle12.MergedCutGroups.Batch070
