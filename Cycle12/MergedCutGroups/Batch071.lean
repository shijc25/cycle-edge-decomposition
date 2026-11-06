import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch028
import Cycle12.MergedCutCells.Batch259
import Cycle12.MergedCutCells.Batch260
import Cycle12.MergedCutCells.Batch261
import Cycle12.MergedCutCells.Batch262
import Cycle12.MergedCutCells.Batch263
import Cycle12.PopulationCertificates.Batch028

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch071

def certificate852 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate568,PopulationCertificates.Batch028.certificate568,[MergedCutCells.Batch259.certificate3111,MergedCutCells.Batch259.certificate3112,MergedCutCells.Batch259.certificate3113],(729723912019545669/1000000000000000000),(some (1108280233/1000000000)),(1/2),(38032627712910213/62500000000000000),(some (56656434475510789/250000000000000000)),(some (59875833746068471/1000000000000000000))⟩
theorem numericValid852 : certificate852.NumericValid := by decide +kernel
theorem cellsSound852 : ∀ c∈certificate852.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3111,MergedCutCells.Batch259.certificate3112,MergedCutCells.Batch259.certificate3113], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3111,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3113,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric852 : ∀ c∈certificate852.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3111,MergedCutCells.Batch259.certificate3112,MergedCutCells.Batch259.certificate3113], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3111,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3113,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid852 : ∀ c∈certificate852.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3111,MergedCutCells.Batch259.certificate3112,MergedCutCells.Batch259.certificate3113], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid285,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid285,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid285,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches852 : ∀ c∈certificate852.cells, c.population=certificate852.population := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3111,MergedCutCells.Batch259.certificate3112,MergedCutCells.Batch259.certificate3113], c.population=PopulationCertificates.Batch028.certificate568
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers852 {x : ℝ} (hx : certificate852.interval.Contains x) : ∃ c∈certificate852.cells, c.region.interval.Contains x := rat_cut_group_covers certificate852 numericValid852 hx

def certificate853 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate568,PopulationCertificates.Batch028.certificate568,[MergedCutCells.Batch259.certificate3114,MergedCutCells.Batch259.certificate3115,MergedCutCells.Batch259.certificate3116,MergedCutCells.Batch259.certificate3117,MergedCutCells.Batch259.certificate3118,MergedCutCells.Batch259.certificate3119,MergedCutCells.Batch260.certificate3120],(1108280233/1000000000),none,(1/2),(585048886138245197/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid853 : certificate853.NumericValid := by decide +kernel
theorem cellsSound853 : ∀ c∈certificate853.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3114,MergedCutCells.Batch259.certificate3115,MergedCutCells.Batch259.certificate3116,MergedCutCells.Batch259.certificate3117,MergedCutCells.Batch259.certificate3118,MergedCutCells.Batch259.certificate3119,MergedCutCells.Batch260.certificate3120], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3114,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3115,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3116,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3117,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.sound3119,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3120,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric853 : ∀ c∈certificate853.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3114,MergedCutCells.Batch259.certificate3115,MergedCutCells.Batch259.certificate3116,MergedCutCells.Batch259.certificate3117,MergedCutCells.Batch259.certificate3118,MergedCutCells.Batch259.certificate3119,MergedCutCells.Batch260.certificate3120], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3114,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3115,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3116,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3117,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch259.numericValid3119,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3120,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid853 : ∀ c∈certificate853.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3114,MergedCutCells.Batch259.certificate3115,MergedCutCells.Batch259.certificate3116,MergedCutCells.Batch259.certificate3117,MergedCutCells.Batch259.certificate3118,MergedCutCells.Batch259.certificate3119,MergedCutCells.Batch260.certificate3120], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches853 : ∀ c∈certificate853.cells, c.population=certificate853.population := by
  change ∀ c∈[MergedCutCells.Batch259.certificate3114,MergedCutCells.Batch259.certificate3115,MergedCutCells.Batch259.certificate3116,MergedCutCells.Batch259.certificate3117,MergedCutCells.Batch259.certificate3118,MergedCutCells.Batch259.certificate3119,MergedCutCells.Batch260.certificate3120], c.population=PopulationCertificates.Batch028.certificate568
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers853 {x : ℝ} (hx : certificate853.interval.Contains x) : ∃ c∈certificate853.cells, c.region.interval.Contains x := rat_cut_group_covers certificate853 numericValid853 hx

def certificate854 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate569,PopulationCertificates.Batch028.certificate569,[MergedCutCells.Batch260.certificate3121,MergedCutCells.Batch260.certificate3122,MergedCutCells.Batch260.certificate3123,MergedCutCells.Batch260.certificate3124],(5004058123042717313/500000000000000000),none,(1/2),(170221654039356907/31250000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid854 : certificate854.NumericValid := by decide +kernel
theorem cellsSound854 : ∀ c∈certificate854.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3121,MergedCutCells.Batch260.certificate3122,MergedCutCells.Batch260.certificate3123,MergedCutCells.Batch260.certificate3124], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3124,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric854 : ∀ c∈certificate854.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3121,MergedCutCells.Batch260.certificate3122,MergedCutCells.Batch260.certificate3123,MergedCutCells.Batch260.certificate3124], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3124,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid854 : ∀ c∈certificate854.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3121,MergedCutCells.Batch260.certificate3122,MergedCutCells.Batch260.certificate3123,MergedCutCells.Batch260.certificate3124], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches854 : ∀ c∈certificate854.cells, c.population=certificate854.population := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3121,MergedCutCells.Batch260.certificate3122,MergedCutCells.Batch260.certificate3123,MergedCutCells.Batch260.certificate3124], c.population=PopulationCertificates.Batch028.certificate569
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers854 {x : ℝ} (hx : certificate854.interval.Contains x) : ∃ c∈certificate854.cells, c.region.interval.Contains x := rat_cut_group_covers certificate854 numericValid854 hx

def certificate855 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate570,PopulationCertificates.Batch028.certificate570,[MergedCutCells.Batch260.certificate3125,MergedCutCells.Batch260.certificate3126],(368100564453181901/500000000000000000),(some (1119772341/1000000000)),(1/2),(20001864829554897/31250000000000000),(some (117355231921309679/500000000000000000)),(some (62839649500036041/1000000000000000000))⟩
theorem numericValid855 : certificate855.NumericValid := by decide +kernel
theorem cellsSound855 : ∀ c∈certificate855.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3125,MergedCutCells.Batch260.certificate3126], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3126,List.forall_mem_nil _⟩⟩
theorem cellsNumeric855 : ∀ c∈certificate855.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3125,MergedCutCells.Batch260.certificate3126], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3126,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid855 : ∀ c∈certificate855.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3125,MergedCutCells.Batch260.certificate3126], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid286,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid286,List.forall_mem_nil _⟩⟩
theorem populationMatches855 : ∀ c∈certificate855.cells, c.population=certificate855.population := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3125,MergedCutCells.Batch260.certificate3126], c.population=PopulationCertificates.Batch028.certificate570
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers855 {x : ℝ} (hx : certificate855.interval.Contains x) : ∃ c∈certificate855.cells, c.region.interval.Contains x := rat_cut_group_covers certificate855 numericValid855 hx

def certificate856 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate570,PopulationCertificates.Batch028.certificate570,[MergedCutCells.Batch260.certificate3127,MergedCutCells.Batch260.certificate3128,MergedCutCells.Batch260.certificate3129,MergedCutCells.Batch260.certificate3130,MergedCutCells.Batch260.certificate3131,MergedCutCells.Batch261.certificate3132],(1119772341/1000000000),none,(1/2),(622491850881488937/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid856 : certificate856.NumericValid := by decide +kernel
theorem cellsSound856 : ∀ c∈certificate856.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3127,MergedCutCells.Batch260.certificate3128,MergedCutCells.Batch260.certificate3129,MergedCutCells.Batch260.certificate3130,MergedCutCells.Batch260.certificate3131,MergedCutCells.Batch261.certificate3132], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3127,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3128,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3130,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.sound3131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3132,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric856 : ∀ c∈certificate856.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3127,MergedCutCells.Batch260.certificate3128,MergedCutCells.Batch260.certificate3129,MergedCutCells.Batch260.certificate3130,MergedCutCells.Batch260.certificate3131,MergedCutCells.Batch261.certificate3132], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3127,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3128,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3130,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch260.numericValid3131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3132,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid856 : ∀ c∈certificate856.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3127,MergedCutCells.Batch260.certificate3128,MergedCutCells.Batch260.certificate3129,MergedCutCells.Batch260.certificate3130,MergedCutCells.Batch260.certificate3131,MergedCutCells.Batch261.certificate3132], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches856 : ∀ c∈certificate856.cells, c.population=certificate856.population := by
  change ∀ c∈[MergedCutCells.Batch260.certificate3127,MergedCutCells.Batch260.certificate3128,MergedCutCells.Batch260.certificate3129,MergedCutCells.Batch260.certificate3130,MergedCutCells.Batch260.certificate3131,MergedCutCells.Batch261.certificate3132], c.population=PopulationCertificates.Batch028.certificate570
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers856 {x : ℝ} (hx : certificate856.interval.Contains x) : ∃ c∈certificate856.cells, c.region.interval.Contains x := rat_cut_group_covers certificate856 numericValid856 hx

def certificate857 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate571,PopulationCertificates.Batch028.certificate571,[MergedCutCells.Batch261.certificate3133,MergedCutCells.Batch261.certificate3134,MergedCutCells.Batch261.certificate3135,MergedCutCells.Batch261.certificate3136],(9989895199785492037/1000000000000000000),none,(1/2),(86507832904957733/15625000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid857 : certificate857.NumericValid := by decide +kernel
theorem cellsSound857 : ∀ c∈certificate857.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3133,MergedCutCells.Batch261.certificate3134,MergedCutCells.Batch261.certificate3135,MergedCutCells.Batch261.certificate3136], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3134,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3136,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric857 : ∀ c∈certificate857.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3133,MergedCutCells.Batch261.certificate3134,MergedCutCells.Batch261.certificate3135,MergedCutCells.Batch261.certificate3136], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3134,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3136,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid857 : ∀ c∈certificate857.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3133,MergedCutCells.Batch261.certificate3134,MergedCutCells.Batch261.certificate3135,MergedCutCells.Batch261.certificate3136], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches857 : ∀ c∈certificate857.cells, c.population=certificate857.population := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3133,MergedCutCells.Batch261.certificate3134,MergedCutCells.Batch261.certificate3135,MergedCutCells.Batch261.certificate3136], c.population=PopulationCertificates.Batch028.certificate571
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers857 {x : ℝ} (hx : certificate857.interval.Contains x) : ∃ c∈certificate857.cells, c.region.interval.Contains x := rat_cut_group_covers certificate857 numericValid857 hx

def certificate858 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate572,PopulationCertificates.Batch028.certificate572,[MergedCutCells.Batch261.certificate3137,MergedCutCells.Batch261.certificate3138,MergedCutCells.Batch261.certificate3139],(743270032984973733/1000000000000000000),(some (220408983/200000000)),(1/2),(169615706319404903/250000000000000000),(some (120793720651210083/500000000000000000)),(some (65404959426181037/1000000000000000000))⟩
theorem numericValid858 : certificate858.NumericValid := by decide +kernel
theorem cellsSound858 : ∀ c∈certificate858.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3137,MergedCutCells.Batch261.certificate3138,MergedCutCells.Batch261.certificate3139], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3137,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3138,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3139,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric858 : ∀ c∈certificate858.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3137,MergedCutCells.Batch261.certificate3138,MergedCutCells.Batch261.certificate3139], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3137,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3138,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3139,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid858 : ∀ c∈certificate858.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3137,MergedCutCells.Batch261.certificate3138,MergedCutCells.Batch261.certificate3139], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid287,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid287,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid287,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches858 : ∀ c∈certificate858.cells, c.population=certificate858.population := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3137,MergedCutCells.Batch261.certificate3138,MergedCutCells.Batch261.certificate3139], c.population=PopulationCertificates.Batch028.certificate572
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers858 {x : ℝ} (hx : certificate858.interval.Contains x) : ∃ c∈certificate858.cells, c.region.interval.Contains x := rat_cut_group_covers certificate858 numericValid858 hx

def certificate859 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate572,PopulationCertificates.Batch028.certificate572,[MergedCutCells.Batch261.certificate3140,MergedCutCells.Batch261.certificate3141,MergedCutCells.Batch261.certificate3142,MergedCutCells.Batch261.certificate3143,MergedCutCells.Batch262.certificate3144,MergedCutCells.Batch262.certificate3145,MergedCutCells.Batch262.certificate3146],(220408983/200000000),none,(1/2),(659204091484084257/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid859 : certificate859.NumericValid := by decide +kernel
theorem cellsSound859 : ∀ c∈certificate859.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3140,MergedCutCells.Batch261.certificate3141,MergedCutCells.Batch261.certificate3142,MergedCutCells.Batch261.certificate3143,MergedCutCells.Batch262.certificate3144,MergedCutCells.Batch262.certificate3145,MergedCutCells.Batch262.certificate3146], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3141,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.sound3143,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3145,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3146,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric859 : ∀ c∈certificate859.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3140,MergedCutCells.Batch261.certificate3141,MergedCutCells.Batch261.certificate3142,MergedCutCells.Batch261.certificate3143,MergedCutCells.Batch262.certificate3144,MergedCutCells.Batch262.certificate3145,MergedCutCells.Batch262.certificate3146], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3141,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch261.numericValid3143,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3145,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3146,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid859 : ∀ c∈certificate859.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3140,MergedCutCells.Batch261.certificate3141,MergedCutCells.Batch261.certificate3142,MergedCutCells.Batch261.certificate3143,MergedCutCells.Batch262.certificate3144,MergedCutCells.Batch262.certificate3145,MergedCutCells.Batch262.certificate3146], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches859 : ∀ c∈certificate859.cells, c.population=certificate859.population := by
  change ∀ c∈[MergedCutCells.Batch261.certificate3140,MergedCutCells.Batch261.certificate3141,MergedCutCells.Batch261.certificate3142,MergedCutCells.Batch261.certificate3143,MergedCutCells.Batch262.certificate3144,MergedCutCells.Batch262.certificate3145,MergedCutCells.Batch262.certificate3146], c.population=PopulationCertificates.Batch028.certificate572
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers859 {x : ℝ} (hx : certificate859.interval.Contains x) : ∃ c∈certificate859.cells, c.region.interval.Contains x := rat_cut_group_covers certificate859 numericValid859 hx

def certificate860 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate573,PopulationCertificates.Batch028.certificate573,[MergedCutCells.Batch262.certificate3147,MergedCutCells.Batch262.certificate3148,MergedCutCells.Batch262.certificate3149,MergedCutCells.Batch262.certificate3150],(10091016912222790751/1000000000000000000),none,(1/2),(1416942676542158887/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid860 : certificate860.NumericValid := by decide +kernel
theorem cellsSound860 : ∀ c∈certificate860.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3147,MergedCutCells.Batch262.certificate3148,MergedCutCells.Batch262.certificate3149,MergedCutCells.Batch262.certificate3150], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3147,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3150,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric860 : ∀ c∈certificate860.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3147,MergedCutCells.Batch262.certificate3148,MergedCutCells.Batch262.certificate3149,MergedCutCells.Batch262.certificate3150], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3147,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3150,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid860 : ∀ c∈certificate860.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3147,MergedCutCells.Batch262.certificate3148,MergedCutCells.Batch262.certificate3149,MergedCutCells.Batch262.certificate3150], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches860 : ∀ c∈certificate860.cells, c.population=certificate860.population := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3147,MergedCutCells.Batch262.certificate3148,MergedCutCells.Batch262.certificate3149,MergedCutCells.Batch262.certificate3150], c.population=PopulationCertificates.Batch028.certificate573
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers860 {x : ℝ} (hx : certificate860.interval.Contains x) : ∃ c∈certificate860.cells, c.region.interval.Contains x := rat_cut_group_covers certificate860 numericValid860 hx

def certificate861 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate574,PopulationCertificates.Batch028.certificate574,[MergedCutCells.Batch262.certificate3151,MergedCutCells.Batch262.certificate3152,MergedCutCells.Batch262.certificate3153],(753000709587762163/1000000000000000000),(some (223525067/200000000)),(1/2),(14660104801237819/20000000000000000),(some (250066580322876719/1000000000000000000)),(some (536129640116737/7812500000000000))⟩
theorem numericValid861 : certificate861.NumericValid := by decide +kernel
theorem cellsSound861 : ∀ c∈certificate861.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3151,MergedCutCells.Batch262.certificate3152,MergedCutCells.Batch262.certificate3153], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3151,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3153,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric861 : ∀ c∈certificate861.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3151,MergedCutCells.Batch262.certificate3152,MergedCutCells.Batch262.certificate3153], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3151,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3153,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid861 : ∀ c∈certificate861.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3151,MergedCutCells.Batch262.certificate3152,MergedCutCells.Batch262.certificate3153], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid288,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid288,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy014.valid288,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches861 : ∀ c∈certificate861.cells, c.population=certificate861.population := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3151,MergedCutCells.Batch262.certificate3152,MergedCutCells.Batch262.certificate3153], c.population=PopulationCertificates.Batch028.certificate574
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers861 {x : ℝ} (hx : certificate861.interval.Contains x) : ∃ c∈certificate861.cells, c.region.interval.Contains x := rat_cut_group_covers certificate861 numericValid861 hx

def certificate862 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate574,PopulationCertificates.Batch028.certificate574,[MergedCutCells.Batch262.certificate3154,MergedCutCells.Batch262.certificate3155,MergedCutCells.Batch263.certificate3156,MergedCutCells.Batch263.certificate3157,MergedCutCells.Batch263.certificate3158,MergedCutCells.Batch263.certificate3159],(223525067/200000000),none,(1/2),(89119872566315933/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid862 : certificate862.NumericValid := by decide +kernel
theorem cellsSound862 : ∀ c∈certificate862.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3154,MergedCutCells.Batch262.certificate3155,MergedCutCells.Batch263.certificate3156,MergedCutCells.Batch263.certificate3157,MergedCutCells.Batch263.certificate3158,MergedCutCells.Batch263.certificate3159], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3154,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.sound3155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3157,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3159,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric862 : ∀ c∈certificate862.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3154,MergedCutCells.Batch262.certificate3155,MergedCutCells.Batch263.certificate3156,MergedCutCells.Batch263.certificate3157,MergedCutCells.Batch263.certificate3158,MergedCutCells.Batch263.certificate3159], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3154,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch262.numericValid3155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3157,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3159,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid862 : ∀ c∈certificate862.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3154,MergedCutCells.Batch262.certificate3155,MergedCutCells.Batch263.certificate3156,MergedCutCells.Batch263.certificate3157,MergedCutCells.Batch263.certificate3158,MergedCutCells.Batch263.certificate3159], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches862 : ∀ c∈certificate862.cells, c.population=certificate862.population := by
  change ∀ c∈[MergedCutCells.Batch262.certificate3154,MergedCutCells.Batch262.certificate3155,MergedCutCells.Batch263.certificate3156,MergedCutCells.Batch263.certificate3157,MergedCutCells.Batch263.certificate3158,MergedCutCells.Batch263.certificate3159], c.population=PopulationCertificates.Batch028.certificate574
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers862 {x : ℝ} (hx : certificate862.interval.Contains x) : ∃ c∈certificate862.cells, c.region.interval.Contains x := rat_cut_group_covers certificate862 numericValid862 hx

def certificate863 : RatCutGroup := ⟨GeometryCertificates.Batch028.certificate575,PopulationCertificates.Batch028.certificate575,[MergedCutCells.Batch263.certificate3160,MergedCutCells.Batch263.certificate3161,MergedCutCells.Batch263.certificate3162],(10036640325219596061/1000000000000000000),none,(1/2),(5760556726517338469/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid863 : certificate863.NumericValid := by decide +kernel
theorem cellsSound863 : ∀ c∈certificate863.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3160,MergedCutCells.Batch263.certificate3161,MergedCutCells.Batch263.certificate3162], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.sound3162,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric863 : ∀ c∈certificate863.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3160,MergedCutCells.Batch263.certificate3161,MergedCutCells.Batch263.certificate3162], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch263.numericValid3162,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid863 : ∀ c∈certificate863.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3160,MergedCutCells.Batch263.certificate3161,MergedCutCells.Batch263.certificate3162], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches863 : ∀ c∈certificate863.cells, c.population=certificate863.population := by
  change ∀ c∈[MergedCutCells.Batch263.certificate3160,MergedCutCells.Batch263.certificate3161,MergedCutCells.Batch263.certificate3162], c.population=PopulationCertificates.Batch028.certificate575
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers863 {x : ℝ} (hx : certificate863.interval.Contains x) : ∃ c∈certificate863.cells, c.region.interval.Contains x := rat_cut_group_covers certificate863 numericValid863 hx

end Cycle12.MergedCutGroups.Batch071
