import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch027
import Cycle12.MergedCutCells.Batch250
import Cycle12.MergedCutCells.Batch251
import Cycle12.MergedCutCells.Batch252
import Cycle12.PopulationCertificates.Batch027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch068

def certificate816 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate544,PopulationCertificates.Batch027.certificate544,[MergedCutCells.Batch250.certificate3001,MergedCutCells.Batch250.certificate3002],(642947278449139453/1000000000000000000),(some (46415577/40000000)),(1/2),(321141958009973893/1000000000000000000),(some (35125617762393383/250000000000000000)),(some (31670672145636623/1000000000000000000))⟩
theorem numericValid816 : certificate816.NumericValid := by decide +kernel
theorem cellsSound816 : ∀ c∈certificate816.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3001,MergedCutCells.Batch250.certificate3002], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3001,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3002,List.forall_mem_nil _⟩⟩
theorem cellsNumeric816 : ∀ c∈certificate816.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3001,MergedCutCells.Batch250.certificate3002], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3001,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3002,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid816 : ∀ c∈certificate816.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3001,MergedCutCells.Batch250.certificate3002], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid273,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid273,List.forall_mem_nil _⟩⟩
theorem populationMatches816 : ∀ c∈certificate816.cells, c.population=certificate816.population := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3001,MergedCutCells.Batch250.certificate3002], c.population=PopulationCertificates.Batch027.certificate544
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers816 {x : ℝ} (hx : certificate816.interval.Contains x) : ∃ c∈certificate816.cells, c.region.interval.Contains x := rat_cut_group_covers certificate816 numericValid816 hx

def certificate817 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate544,PopulationCertificates.Batch027.certificate544,[MergedCutCells.Batch250.certificate3003,MergedCutCells.Batch250.certificate3004,MergedCutCells.Batch250.certificate3005,MergedCutCells.Batch250.certificate3006,MergedCutCells.Batch250.certificate3007],(46415577/40000000),none,(1/2),(310757963976864681/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid817 : certificate817.NumericValid := by decide +kernel
theorem cellsSound817 : ∀ c∈certificate817.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3003,MergedCutCells.Batch250.certificate3004,MergedCutCells.Batch250.certificate3005,MergedCutCells.Batch250.certificate3006,MergedCutCells.Batch250.certificate3007], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3003,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3004,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3005,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3006,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3007,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric817 : ∀ c∈certificate817.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3003,MergedCutCells.Batch250.certificate3004,MergedCutCells.Batch250.certificate3005,MergedCutCells.Batch250.certificate3006,MergedCutCells.Batch250.certificate3007], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3003,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3004,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3005,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3006,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3007,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid817 : ∀ c∈certificate817.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3003,MergedCutCells.Batch250.certificate3004,MergedCutCells.Batch250.certificate3005,MergedCutCells.Batch250.certificate3006,MergedCutCells.Batch250.certificate3007], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches817 : ∀ c∈certificate817.cells, c.population=certificate817.population := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3003,MergedCutCells.Batch250.certificate3004,MergedCutCells.Batch250.certificate3005,MergedCutCells.Batch250.certificate3006,MergedCutCells.Batch250.certificate3007], c.population=PopulationCertificates.Batch027.certificate544
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers817 {x : ℝ} (hx : certificate817.interval.Contains x) : ∃ c∈certificate817.cells, c.region.interval.Contains x := rat_cut_group_covers certificate817 numericValid817 hx

def certificate818 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate545,PopulationCertificates.Batch027.certificate545,[MergedCutCells.Batch250.certificate3008,MergedCutCells.Batch250.certificate3009],(9558409571558448327/1000000000000000000),none,(1/2),(4342847664366684611/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid818 : certificate818.NumericValid := by decide +kernel
theorem cellsSound818 : ∀ c∈certificate818.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3008,MergedCutCells.Batch250.certificate3009], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3008,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3009,List.forall_mem_nil _⟩⟩
theorem cellsNumeric818 : ∀ c∈certificate818.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3008,MergedCutCells.Batch250.certificate3009], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3008,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3009,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid818 : ∀ c∈certificate818.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3008,MergedCutCells.Batch250.certificate3009], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches818 : ∀ c∈certificate818.cells, c.population=certificate818.population := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3008,MergedCutCells.Batch250.certificate3009], c.population=PopulationCertificates.Batch027.certificate545
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers818 {x : ℝ} (hx : certificate818.interval.Contains x) : ∃ c∈certificate818.cells, c.region.interval.Contains x := rat_cut_group_covers certificate818 numericValid818 hx

def certificate819 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate546,PopulationCertificates.Batch027.certificate546,[MergedCutCells.Batch250.certificate3010,MergedCutCells.Batch250.certificate3011,MergedCutCells.Batch251.certificate3012],(647664819333490669/1000000000000000000),(some (1167807411/1000000000)),(1/2),(327131448247648457/1000000000000000000),(some (147775343227229999/1000000000000000000)),(some (33818659020504217/1000000000000000000))⟩
theorem numericValid819 : certificate819.NumericValid := by decide +kernel
theorem cellsSound819 : ∀ c∈certificate819.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3010,MergedCutCells.Batch250.certificate3011,MergedCutCells.Batch251.certificate3012], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3010,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.sound3011,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3012,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric819 : ∀ c∈certificate819.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3010,MergedCutCells.Batch250.certificate3011,MergedCutCells.Batch251.certificate3012], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3010,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch250.numericValid3011,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3012,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid819 : ∀ c∈certificate819.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3010,MergedCutCells.Batch250.certificate3011,MergedCutCells.Batch251.certificate3012], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid274,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid274,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid274,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches819 : ∀ c∈certificate819.cells, c.population=certificate819.population := by
  change ∀ c∈[MergedCutCells.Batch250.certificate3010,MergedCutCells.Batch250.certificate3011,MergedCutCells.Batch251.certificate3012], c.population=PopulationCertificates.Batch027.certificate546
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers819 {x : ℝ} (hx : certificate819.interval.Contains x) : ∃ c∈certificate819.cells, c.region.interval.Contains x := rat_cut_group_covers certificate819 numericValid819 hx

def certificate820 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate546,PopulationCertificates.Batch027.certificate546,[MergedCutCells.Batch251.certificate3013,MergedCutCells.Batch251.certificate3014,MergedCutCells.Batch251.certificate3015,MergedCutCells.Batch251.certificate3016],(1167807411/1000000000),none,(1/2),(315843993630019371/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid820 : certificate820.NumericValid := by decide +kernel
theorem cellsSound820 : ∀ c∈certificate820.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3013,MergedCutCells.Batch251.certificate3014,MergedCutCells.Batch251.certificate3015,MergedCutCells.Batch251.certificate3016], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3013,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3014,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3015,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3016,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric820 : ∀ c∈certificate820.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3013,MergedCutCells.Batch251.certificate3014,MergedCutCells.Batch251.certificate3015,MergedCutCells.Batch251.certificate3016], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3013,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3014,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3015,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3016,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid820 : ∀ c∈certificate820.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3013,MergedCutCells.Batch251.certificate3014,MergedCutCells.Batch251.certificate3015,MergedCutCells.Batch251.certificate3016], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches820 : ∀ c∈certificate820.cells, c.population=certificate820.population := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3013,MergedCutCells.Batch251.certificate3014,MergedCutCells.Batch251.certificate3015,MergedCutCells.Batch251.certificate3016], c.population=PopulationCertificates.Batch027.certificate546
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers820 {x : ℝ} (hx : certificate820.interval.Contains x) : ∃ c∈certificate820.cells, c.region.interval.Contains x := rat_cut_group_covers certificate820 numericValid820 hx

def certificate821 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate547,PopulationCertificates.Batch027.certificate547,[MergedCutCells.Batch251.certificate3017,MergedCutCells.Batch251.certificate3018],(9585934797911637177/1000000000000000000),none,(1/2),(4410935300205689633/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid821 : certificate821.NumericValid := by decide +kernel
theorem cellsSound821 : ∀ c∈certificate821.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3017,MergedCutCells.Batch251.certificate3018], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3017,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3018,List.forall_mem_nil _⟩⟩
theorem cellsNumeric821 : ∀ c∈certificate821.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3017,MergedCutCells.Batch251.certificate3018], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3017,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3018,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid821 : ∀ c∈certificate821.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3017,MergedCutCells.Batch251.certificate3018], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches821 : ∀ c∈certificate821.cells, c.population=certificate821.population := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3017,MergedCutCells.Batch251.certificate3018], c.population=PopulationCertificates.Batch027.certificate547
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers821 {x : ℝ} (hx : certificate821.interval.Contains x) : ∃ c∈certificate821.cells, c.region.interval.Contains x := rat_cut_group_covers certificate821 numericValid821 hx

def certificate822 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate548,PopulationCertificates.Batch027.certificate548,[MergedCutCells.Batch251.certificate3019,MergedCutCells.Batch251.certificate3020],(130797860343600663/200000000000000000),(some (1152713183/1000000000)),(1/2),(172814130297859893/500000000000000000),(some (154337546296826723/1000000000000000000)),(some (35793638544097477/1000000000000000000))⟩
theorem numericValid822 : certificate822.NumericValid := by decide +kernel
theorem cellsSound822 : ∀ c∈certificate822.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3019,MergedCutCells.Batch251.certificate3020], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3019,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3020,List.forall_mem_nil _⟩⟩
theorem cellsNumeric822 : ∀ c∈certificate822.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3019,MergedCutCells.Batch251.certificate3020], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3019,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3020,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid822 : ∀ c∈certificate822.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3019,MergedCutCells.Batch251.certificate3020], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid275,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid275,List.forall_mem_nil _⟩⟩
theorem populationMatches822 : ∀ c∈certificate822.cells, c.population=certificate822.population := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3019,MergedCutCells.Batch251.certificate3020], c.population=PopulationCertificates.Batch027.certificate548
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers822 {x : ℝ} (hx : certificate822.interval.Contains x) : ∃ c∈certificate822.cells, c.region.interval.Contains x := rat_cut_group_covers certificate822 numericValid822 hx

def certificate823 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate548,PopulationCertificates.Batch027.certificate548,[MergedCutCells.Batch251.certificate3021,MergedCutCells.Batch251.certificate3022,MergedCutCells.Batch251.certificate3023,MergedCutCells.Batch252.certificate3024],(1152713183/1000000000),none,(1/2),(8346949460953229/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid823 : certificate823.NumericValid := by decide +kernel
theorem cellsSound823 : ∀ c∈certificate823.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3021,MergedCutCells.Batch251.certificate3022,MergedCutCells.Batch251.certificate3023,MergedCutCells.Batch252.certificate3024], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3021,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3022,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.sound3023,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3024,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric823 : ∀ c∈certificate823.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3021,MergedCutCells.Batch251.certificate3022,MergedCutCells.Batch251.certificate3023,MergedCutCells.Batch252.certificate3024], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3021,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3022,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch251.numericValid3023,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3024,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid823 : ∀ c∈certificate823.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3021,MergedCutCells.Batch251.certificate3022,MergedCutCells.Batch251.certificate3023,MergedCutCells.Batch252.certificate3024], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches823 : ∀ c∈certificate823.cells, c.population=certificate823.population := by
  change ∀ c∈[MergedCutCells.Batch251.certificate3021,MergedCutCells.Batch251.certificate3022,MergedCutCells.Batch251.certificate3023,MergedCutCells.Batch252.certificate3024], c.population=PopulationCertificates.Batch027.certificate548
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers823 {x : ℝ} (hx : certificate823.interval.Contains x) : ∃ c∈certificate823.cells, c.region.interval.Contains x := rat_cut_group_covers certificate823 numericValid823 hx

def certificate824 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate549,PopulationCertificates.Batch027.certificate549,[MergedCutCells.Batch252.certificate3025,MergedCutCells.Batch252.certificate3026],(2425348173596243839/250000000000000000),none,(1/2),(2258965817737720689/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid824 : certificate824.NumericValid := by decide +kernel
theorem cellsSound824 : ∀ c∈certificate824.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3025,MergedCutCells.Batch252.certificate3026], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3025,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3026,List.forall_mem_nil _⟩⟩
theorem cellsNumeric824 : ∀ c∈certificate824.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3025,MergedCutCells.Batch252.certificate3026], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3025,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3026,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid824 : ∀ c∈certificate824.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3025,MergedCutCells.Batch252.certificate3026], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches824 : ∀ c∈certificate824.cells, c.population=certificate824.population := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3025,MergedCutCells.Batch252.certificate3026], c.population=PopulationCertificates.Batch027.certificate549
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers824 {x : ℝ} (hx : certificate824.interval.Contains x) : ∃ c∈certificate824.cells, c.region.interval.Contains x := rat_cut_group_covers certificate824 numericValid824 hx

def certificate825 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate550,PopulationCertificates.Batch027.certificate550,[MergedCutCells.Batch252.certificate3027,MergedCutCells.Batch252.certificate3028,MergedCutCells.Batch252.certificate3029],(13216478364072951/20000000000000000),(some (581631681/500000000)),(1/2),(36483977116865191/100000000000000000),(some (161809973567831191/1000000000000000000)),(some (9521273035897943/250000000000000000))⟩
theorem numericValid825 : certificate825.NumericValid := by decide +kernel
theorem cellsSound825 : ∀ c∈certificate825.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3027,MergedCutCells.Batch252.certificate3028,MergedCutCells.Batch252.certificate3029], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3028,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3029,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric825 : ∀ c∈certificate825.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3027,MergedCutCells.Batch252.certificate3028,MergedCutCells.Batch252.certificate3029], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3028,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3029,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid825 : ∀ c∈certificate825.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3027,MergedCutCells.Batch252.certificate3028,MergedCutCells.Batch252.certificate3029], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid276,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid276,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy013.valid276,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches825 : ∀ c∈certificate825.cells, c.population=certificate825.population := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3027,MergedCutCells.Batch252.certificate3028,MergedCutCells.Batch252.certificate3029], c.population=PopulationCertificates.Batch027.certificate550
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers825 {x : ℝ} (hx : certificate825.interval.Contains x) : ∃ c∈certificate825.cells, c.region.interval.Contains x := rat_cut_group_covers certificate825 numericValid825 hx

def certificate826 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate550,PopulationCertificates.Batch027.certificate550,[MergedCutCells.Batch252.certificate3030,MergedCutCells.Batch252.certificate3031,MergedCutCells.Batch252.certificate3032,MergedCutCells.Batch252.certificate3033],(581631681/500000000),none,(1/2),(14090815810660753/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid826 : certificate826.NumericValid := by decide +kernel
theorem cellsSound826 : ∀ c∈certificate826.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3030,MergedCutCells.Batch252.certificate3031,MergedCutCells.Batch252.certificate3032,MergedCutCells.Batch252.certificate3033], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3030,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3031,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3032,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3033,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric826 : ∀ c∈certificate826.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3030,MergedCutCells.Batch252.certificate3031,MergedCutCells.Batch252.certificate3032,MergedCutCells.Batch252.certificate3033], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3030,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3031,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3032,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3033,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid826 : ∀ c∈certificate826.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3030,MergedCutCells.Batch252.certificate3031,MergedCutCells.Batch252.certificate3032,MergedCutCells.Batch252.certificate3033], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches826 : ∀ c∈certificate826.cells, c.population=certificate826.population := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3030,MergedCutCells.Batch252.certificate3031,MergedCutCells.Batch252.certificate3032,MergedCutCells.Batch252.certificate3033], c.population=PopulationCertificates.Batch027.certificate550
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers826 {x : ℝ} (hx : certificate826.interval.Contains x) : ∃ c∈certificate826.cells, c.region.interval.Contains x := rat_cut_group_covers certificate826 numericValid826 hx

def certificate827 : RatCutGroup := ⟨GeometryCertificates.Batch027.certificate551,PopulationCertificates.Batch027.certificate551,[MergedCutCells.Batch252.certificate3034,MergedCutCells.Batch252.certificate3035],(9695420361871502517/1000000000000000000),none,(1/2),(4589380545153354791/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid827 : certificate827.NumericValid := by decide +kernel
theorem cellsSound827 : ∀ c∈certificate827.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3034,MergedCutCells.Batch252.certificate3035], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3034,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.sound3035,List.forall_mem_nil _⟩⟩
theorem cellsNumeric827 : ∀ c∈certificate827.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3034,MergedCutCells.Batch252.certificate3035], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3034,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch252.numericValid3035,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid827 : ∀ c∈certificate827.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3034,MergedCutCells.Batch252.certificate3035], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches827 : ∀ c∈certificate827.cells, c.population=certificate827.population := by
  change ∀ c∈[MergedCutCells.Batch252.certificate3034,MergedCutCells.Batch252.certificate3035], c.population=PopulationCertificates.Batch027.certificate551
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers827 {x : ℝ} (hx : certificate827.interval.Contains x) : ∃ c∈certificate827.cells, c.region.interval.Contains x := rat_cut_group_covers certificate827 numericValid827 hx

end Cycle12.MergedCutGroups.Batch068
