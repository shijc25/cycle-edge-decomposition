import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch003
import Cycle12.MergedCutCells.Batch026
import Cycle12.MergedCutCells.Batch027
import Cycle12.MergedCutCells.Batch028
import Cycle12.MergedCutCells.Batch029
import Cycle12.MergedCutCells.Batch030
import Cycle12.PopulationCertificates.Batch003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch008

def certificate96 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate64,PopulationCertificates.Batch003.certificate64,[MergedCutCells.Batch026.certificate312,MergedCutCells.Batch026.certificate313,MergedCutCells.Batch026.certificate314],(184827553382539697/250000000000000000),(some (993733697/1000000000)),(1/2),(48741683785858543/250000000000000000),(some (420127328113339511/1000000000000000000)),(some (148516600215273631/1000000000000000000))⟩
theorem numericValid96 : certificate96.NumericValid := by decide +kernel
theorem cellsSound96 : ∀ c∈certificate96.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch026.certificate312,MergedCutCells.Batch026.certificate313,MergedCutCells.Batch026.certificate314], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound312,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound313,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound314,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric96 : ∀ c∈certificate96.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch026.certificate312,MergedCutCells.Batch026.certificate313,MergedCutCells.Batch026.certificate314], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid312,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid313,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid314,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid96 : ∀ c∈certificate96.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch026.certificate312,MergedCutCells.Batch026.certificate313,MergedCutCells.Batch026.certificate314], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid33,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid33,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid33,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches96 : ∀ c∈certificate96.cells, c.population=certificate96.population := by
  change ∀ c∈[MergedCutCells.Batch026.certificate312,MergedCutCells.Batch026.certificate313,MergedCutCells.Batch026.certificate314], c.population=PopulationCertificates.Batch003.certificate64
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers96 {x : ℝ} (hx : certificate96.interval.Contains x) : ∃ c∈certificate96.cells, c.region.interval.Contains x := rat_cut_group_covers certificate96 numericValid96 hx

def certificate97 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate64,PopulationCertificates.Batch003.certificate64,[MergedCutCells.Batch026.certificate315,MergedCutCells.Batch026.certificate316,MergedCutCells.Batch026.certificate317,MergedCutCells.Batch026.certificate318,MergedCutCells.Batch026.certificate319,MergedCutCells.Batch026.certificate320],(993733697/1000000000),none,(1/2),(36196838924756283/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid97 : certificate97.NumericValid := by decide +kernel
theorem cellsSound97 : ∀ c∈certificate97.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch026.certificate315,MergedCutCells.Batch026.certificate316,MergedCutCells.Batch026.certificate317,MergedCutCells.Batch026.certificate318,MergedCutCells.Batch026.certificate319,MergedCutCells.Batch026.certificate320], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound315,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound316,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound317,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound318,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound319,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound320,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric97 : ∀ c∈certificate97.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch026.certificate315,MergedCutCells.Batch026.certificate316,MergedCutCells.Batch026.certificate317,MergedCutCells.Batch026.certificate318,MergedCutCells.Batch026.certificate319,MergedCutCells.Batch026.certificate320], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid315,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid316,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid317,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid318,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid319,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid320,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid97 : ∀ c∈certificate97.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch026.certificate315,MergedCutCells.Batch026.certificate316,MergedCutCells.Batch026.certificate317,MergedCutCells.Batch026.certificate318,MergedCutCells.Batch026.certificate319,MergedCutCells.Batch026.certificate320], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches97 : ∀ c∈certificate97.cells, c.population=certificate97.population := by
  change ∀ c∈[MergedCutCells.Batch026.certificate315,MergedCutCells.Batch026.certificate316,MergedCutCells.Batch026.certificate317,MergedCutCells.Batch026.certificate318,MergedCutCells.Batch026.certificate319,MergedCutCells.Batch026.certificate320], c.population=PopulationCertificates.Batch003.certificate64
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers97 {x : ℝ} (hx : certificate97.interval.Contains x) : ∃ c∈certificate97.cells, c.region.interval.Contains x := rat_cut_group_covers certificate97 numericValid97 hx

def certificate98 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate65,PopulationCertificates.Batch003.certificate65,[MergedCutCells.Batch026.certificate321,MergedCutCells.Batch026.certificate322,MergedCutCells.Batch026.certificate323,MergedCutCells.Batch027.certificate324],(924450126468980281/250000000000000000),none,(1/2),(216563335035495751/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid98 : certificate98.NumericValid := by decide +kernel
theorem cellsSound98 : ∀ c∈certificate98.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch026.certificate321,MergedCutCells.Batch026.certificate322,MergedCutCells.Batch026.certificate323,MergedCutCells.Batch027.certificate324], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound321,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.sound323,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound324,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric98 : ∀ c∈certificate98.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch026.certificate321,MergedCutCells.Batch026.certificate322,MergedCutCells.Batch026.certificate323,MergedCutCells.Batch027.certificate324], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid321,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch026.numericValid323,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid324,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid98 : ∀ c∈certificate98.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch026.certificate321,MergedCutCells.Batch026.certificate322,MergedCutCells.Batch026.certificate323,MergedCutCells.Batch027.certificate324], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches98 : ∀ c∈certificate98.cells, c.population=certificate98.population := by
  change ∀ c∈[MergedCutCells.Batch026.certificate321,MergedCutCells.Batch026.certificate322,MergedCutCells.Batch026.certificate323,MergedCutCells.Batch027.certificate324], c.population=PopulationCertificates.Batch003.certificate65
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers98 {x : ℝ} (hx : certificate98.interval.Contains x) : ∃ c∈certificate98.cells, c.region.interval.Contains x := rat_cut_group_covers certificate98 numericValid98 hx

def certificate99 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate66,PopulationCertificates.Batch003.certificate66,[MergedCutCells.Batch027.certificate325,MergedCutCells.Batch027.certificate326,MergedCutCells.Batch027.certificate327],(184942330557574413/250000000000000000),(some (248577469/250000000)),(1/2),(178968871753026253/1000000000000000000),(some (107085044309566577/250000000000000000)),(some (153270367886940079/1000000000000000000))⟩
theorem numericValid99 : certificate99.NumericValid := by decide +kernel
theorem cellsSound99 : ∀ c∈certificate99.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch027.certificate325,MergedCutCells.Batch027.certificate326,MergedCutCells.Batch027.certificate327], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound325,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound326,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound327,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric99 : ∀ c∈certificate99.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch027.certificate325,MergedCutCells.Batch027.certificate326,MergedCutCells.Batch027.certificate327], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid325,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid326,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid327,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid99 : ∀ c∈certificate99.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch027.certificate325,MergedCutCells.Batch027.certificate326,MergedCutCells.Batch027.certificate327], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid34,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid34,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid34,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches99 : ∀ c∈certificate99.cells, c.population=certificate99.population := by
  change ∀ c∈[MergedCutCells.Batch027.certificate325,MergedCutCells.Batch027.certificate326,MergedCutCells.Batch027.certificate327], c.population=PopulationCertificates.Batch003.certificate66
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers99 {x : ℝ} (hx : certificate99.interval.Contains x) : ∃ c∈certificate99.cells, c.region.interval.Contains x := rat_cut_group_covers certificate99 numericValid99 hx

def certificate100 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate66,PopulationCertificates.Batch003.certificate66,[MergedCutCells.Batch027.certificate328,MergedCutCells.Batch027.certificate329,MergedCutCells.Batch027.certificate330,MergedCutCells.Batch027.certificate331,MergedCutCells.Batch027.certificate332,MergedCutCells.Batch027.certificate333],(248577469/250000000),none,(1/2),(132880911708480423/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid100 : certificate100.NumericValid := by decide +kernel
theorem cellsSound100 : ∀ c∈certificate100.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch027.certificate328,MergedCutCells.Batch027.certificate329,MergedCutCells.Batch027.certificate330,MergedCutCells.Batch027.certificate331,MergedCutCells.Batch027.certificate332,MergedCutCells.Batch027.certificate333], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound328,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound329,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound331,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound332,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound333,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric100 : ∀ c∈certificate100.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch027.certificate328,MergedCutCells.Batch027.certificate329,MergedCutCells.Batch027.certificate330,MergedCutCells.Batch027.certificate331,MergedCutCells.Batch027.certificate332,MergedCutCells.Batch027.certificate333], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid328,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid329,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid331,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid332,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid333,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid100 : ∀ c∈certificate100.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch027.certificate328,MergedCutCells.Batch027.certificate329,MergedCutCells.Batch027.certificate330,MergedCutCells.Batch027.certificate331,MergedCutCells.Batch027.certificate332,MergedCutCells.Batch027.certificate333], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches100 : ∀ c∈certificate100.cells, c.population=certificate100.population := by
  change ∀ c∈[MergedCutCells.Batch027.certificate328,MergedCutCells.Batch027.certificate329,MergedCutCells.Batch027.certificate330,MergedCutCells.Batch027.certificate331,MergedCutCells.Batch027.certificate332,MergedCutCells.Batch027.certificate333], c.population=PopulationCertificates.Batch003.certificate66
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers100 {x : ℝ} (hx : certificate100.interval.Contains x) : ∃ c∈certificate100.cells, c.region.interval.Contains x := rat_cut_group_covers certificate100 numericValid100 hx

def certificate101 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate67,PopulationCertificates.Batch003.certificate67,[MergedCutCells.Batch027.certificate334,MergedCutCells.Batch027.certificate335,MergedCutCells.Batch028.certificate336],(3732600285901326481/1000000000000000000),none,(1/2),(56662424254637961/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid101 : certificate101.NumericValid := by decide +kernel
theorem cellsSound101 : ∀ c∈certificate101.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch027.certificate334,MergedCutCells.Batch027.certificate335,MergedCutCells.Batch028.certificate336], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.sound335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound336,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric101 : ∀ c∈certificate101.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch027.certificate334,MergedCutCells.Batch027.certificate335,MergedCutCells.Batch028.certificate336], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch027.numericValid335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid336,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid101 : ∀ c∈certificate101.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch027.certificate334,MergedCutCells.Batch027.certificate335,MergedCutCells.Batch028.certificate336], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches101 : ∀ c∈certificate101.cells, c.population=certificate101.population := by
  change ∀ c∈[MergedCutCells.Batch027.certificate334,MergedCutCells.Batch027.certificate335,MergedCutCells.Batch028.certificate336], c.population=PopulationCertificates.Batch003.certificate67
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers101 {x : ℝ} (hx : certificate101.interval.Contains x) : ∃ c∈certificate101.cells, c.region.interval.Contains x := rat_cut_group_covers certificate101 numericValid101 hx

def certificate102 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate68,PopulationCertificates.Batch003.certificate68,[MergedCutCells.Batch028.certificate337,MergedCutCells.Batch028.certificate338,MergedCutCells.Batch028.certificate339],(29877434772452329/40000000000000000),(some (489465603/500000000)),(1/2),(101073321076402259/500000000000000000),(some (217347786405286481/500000000000000000)),(some (31404049739306821/200000000000000000))⟩
theorem numericValid102 : certificate102.NumericValid := by decide +kernel
theorem cellsSound102 : ∀ c∈certificate102.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch028.certificate337,MergedCutCells.Batch028.certificate338,MergedCutCells.Batch028.certificate339], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound337,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound338,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound339,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric102 : ∀ c∈certificate102.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch028.certificate337,MergedCutCells.Batch028.certificate338,MergedCutCells.Batch028.certificate339], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid337,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid338,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid339,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid102 : ∀ c∈certificate102.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch028.certificate337,MergedCutCells.Batch028.certificate338,MergedCutCells.Batch028.certificate339], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid35,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid35,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid35,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches102 : ∀ c∈certificate102.cells, c.population=certificate102.population := by
  change ∀ c∈[MergedCutCells.Batch028.certificate337,MergedCutCells.Batch028.certificate338,MergedCutCells.Batch028.certificate339], c.population=PopulationCertificates.Batch003.certificate68
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers102 {x : ℝ} (hx : certificate102.interval.Contains x) : ∃ c∈certificate102.cells, c.region.interval.Contains x := rat_cut_group_covers certificate102 numericValid102 hx

def certificate103 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate68,PopulationCertificates.Batch003.certificate68,[MergedCutCells.Batch028.certificate340,MergedCutCells.Batch028.certificate341,MergedCutCells.Batch028.certificate342,MergedCutCells.Batch028.certificate343,MergedCutCells.Batch028.certificate344,MergedCutCells.Batch028.certificate345,MergedCutCells.Batch028.certificate346],(489465603/500000000),none,(1/2),(3575544922165729/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid103 : certificate103.NumericValid := by decide +kernel
theorem cellsSound103 : ∀ c∈certificate103.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch028.certificate340,MergedCutCells.Batch028.certificate341,MergedCutCells.Batch028.certificate342,MergedCutCells.Batch028.certificate343,MergedCutCells.Batch028.certificate344,MergedCutCells.Batch028.certificate345,MergedCutCells.Batch028.certificate346], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound341,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound342,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound343,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound344,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound345,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound346,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric103 : ∀ c∈certificate103.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch028.certificate340,MergedCutCells.Batch028.certificate341,MergedCutCells.Batch028.certificate342,MergedCutCells.Batch028.certificate343,MergedCutCells.Batch028.certificate344,MergedCutCells.Batch028.certificate345,MergedCutCells.Batch028.certificate346], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid341,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid342,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid343,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid344,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid345,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid346,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid103 : ∀ c∈certificate103.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch028.certificate340,MergedCutCells.Batch028.certificate341,MergedCutCells.Batch028.certificate342,MergedCutCells.Batch028.certificate343,MergedCutCells.Batch028.certificate344,MergedCutCells.Batch028.certificate345,MergedCutCells.Batch028.certificate346], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches103 : ∀ c∈certificate103.cells, c.population=certificate103.population := by
  change ∀ c∈[MergedCutCells.Batch028.certificate340,MergedCutCells.Batch028.certificate341,MergedCutCells.Batch028.certificate342,MergedCutCells.Batch028.certificate343,MergedCutCells.Batch028.certificate344,MergedCutCells.Batch028.certificate345,MergedCutCells.Batch028.certificate346], c.population=PopulationCertificates.Batch003.certificate68
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers103 {x : ℝ} (hx : certificate103.interval.Contains x) : ∃ c∈certificate103.cells, c.region.interval.Contains x := rat_cut_group_covers certificate103 numericValid103 hx

def certificate104 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate69,PopulationCertificates.Batch003.certificate69,[MergedCutCells.Batch028.certificate347,MergedCutCells.Batch029.certificate348,MergedCutCells.Batch029.certificate349,MergedCutCells.Batch029.certificate350],(467021589055879003/125000000000000000),none,(1/2),(59160572030250573/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid104 : certificate104.NumericValid := by decide +kernel
theorem cellsSound104 : ∀ c∈certificate104.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch028.certificate347,MergedCutCells.Batch029.certificate348,MergedCutCells.Batch029.certificate349,MergedCutCells.Batch029.certificate350], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.sound347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound348,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound349,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound350,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric104 : ∀ c∈certificate104.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch028.certificate347,MergedCutCells.Batch029.certificate348,MergedCutCells.Batch029.certificate349,MergedCutCells.Batch029.certificate350], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch028.numericValid347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid348,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid349,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid350,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid104 : ∀ c∈certificate104.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch028.certificate347,MergedCutCells.Batch029.certificate348,MergedCutCells.Batch029.certificate349,MergedCutCells.Batch029.certificate350], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches104 : ∀ c∈certificate104.cells, c.population=certificate104.population := by
  change ∀ c∈[MergedCutCells.Batch028.certificate347,MergedCutCells.Batch029.certificate348,MergedCutCells.Batch029.certificate349,MergedCutCells.Batch029.certificate350], c.population=PopulationCertificates.Batch003.certificate69
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers104 {x : ℝ} (hx : certificate104.interval.Contains x) : ∃ c∈certificate104.cells, c.region.interval.Contains x := rat_cut_group_covers certificate104 numericValid104 hx

def certificate105 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate70,PopulationCertificates.Batch003.certificate70,[MergedCutCells.Batch029.certificate351,MergedCutCells.Batch029.certificate352,MergedCutCells.Batch029.certificate353],(748443187216257967/1000000000000000000),(some (980786521/1000000000)),(1/2),(24467480920551521/125000000000000000),(some (221239456883181921/500000000000000000)),(some (32340093273335399/200000000000000000))⟩
theorem numericValid105 : certificate105.NumericValid := by decide +kernel
theorem cellsSound105 : ∀ c∈certificate105.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch029.certificate351,MergedCutCells.Batch029.certificate352,MergedCutCells.Batch029.certificate353], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound352,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound353,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric105 : ∀ c∈certificate105.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch029.certificate351,MergedCutCells.Batch029.certificate352,MergedCutCells.Batch029.certificate353], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid352,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid353,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid105 : ∀ c∈certificate105.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch029.certificate351,MergedCutCells.Batch029.certificate352,MergedCutCells.Batch029.certificate353], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid36,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid36,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid36,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches105 : ∀ c∈certificate105.cells, c.population=certificate105.population := by
  change ∀ c∈[MergedCutCells.Batch029.certificate351,MergedCutCells.Batch029.certificate352,MergedCutCells.Batch029.certificate353], c.population=PopulationCertificates.Batch003.certificate70
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers105 {x : ℝ} (hx : certificate105.interval.Contains x) : ∃ c∈certificate105.cells, c.region.interval.Contains x := rat_cut_group_covers certificate105 numericValid105 hx

def certificate106 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate70,PopulationCertificates.Batch003.certificate70,[MergedCutCells.Batch029.certificate354,MergedCutCells.Batch029.certificate355,MergedCutCells.Batch029.certificate356,MergedCutCells.Batch029.certificate357,MergedCutCells.Batch029.certificate358,MergedCutCells.Batch029.certificate359],(980786521/1000000000),none,(1/2),(5618983865058503/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid106 : certificate106.NumericValid := by decide +kernel
theorem cellsSound106 : ∀ c∈certificate106.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch029.certificate354,MergedCutCells.Batch029.certificate355,MergedCutCells.Batch029.certificate356,MergedCutCells.Batch029.certificate357,MergedCutCells.Batch029.certificate358,MergedCutCells.Batch029.certificate359], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound354,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound355,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound357,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.sound359,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric106 : ∀ c∈certificate106.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch029.certificate354,MergedCutCells.Batch029.certificate355,MergedCutCells.Batch029.certificate356,MergedCutCells.Batch029.certificate357,MergedCutCells.Batch029.certificate358,MergedCutCells.Batch029.certificate359], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid354,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid355,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid356,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid357,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid358,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch029.numericValid359,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid106 : ∀ c∈certificate106.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch029.certificate354,MergedCutCells.Batch029.certificate355,MergedCutCells.Batch029.certificate356,MergedCutCells.Batch029.certificate357,MergedCutCells.Batch029.certificate358,MergedCutCells.Batch029.certificate359], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches106 : ∀ c∈certificate106.cells, c.population=certificate106.population := by
  change ∀ c∈[MergedCutCells.Batch029.certificate354,MergedCutCells.Batch029.certificate355,MergedCutCells.Batch029.certificate356,MergedCutCells.Batch029.certificate357,MergedCutCells.Batch029.certificate358,MergedCutCells.Batch029.certificate359], c.population=PopulationCertificates.Batch003.certificate70
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers106 {x : ℝ} (hx : certificate106.interval.Contains x) : ∃ c∈certificate106.cells, c.region.interval.Contains x := rat_cut_group_covers certificate106 numericValid106 hx

def certificate107 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate71,PopulationCertificates.Batch003.certificate71,[MergedCutCells.Batch030.certificate360,MergedCutCells.Batch030.certificate361,MergedCutCells.Batch030.certificate362],(1877893750711201899/500000000000000000),none,(1/2),(123389601099680793/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid107 : certificate107.NumericValid := by decide +kernel
theorem cellsSound107 : ∀ c∈certificate107.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch030.certificate360,MergedCutCells.Batch030.certificate361,MergedCutCells.Batch030.certificate362], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound360,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound362,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric107 : ∀ c∈certificate107.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch030.certificate360,MergedCutCells.Batch030.certificate361,MergedCutCells.Batch030.certificate362], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid360,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid361,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid362,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid107 : ∀ c∈certificate107.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch030.certificate360,MergedCutCells.Batch030.certificate361,MergedCutCells.Batch030.certificate362], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches107 : ∀ c∈certificate107.cells, c.population=certificate107.population := by
  change ∀ c∈[MergedCutCells.Batch030.certificate360,MergedCutCells.Batch030.certificate361,MergedCutCells.Batch030.certificate362], c.population=PopulationCertificates.Batch003.certificate71
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers107 {x : ℝ} (hx : certificate107.interval.Contains x) : ∃ c∈certificate107.cells, c.region.interval.Contains x := rat_cut_group_covers certificate107 numericValid107 hx

end Cycle12.MergedCutGroups.Batch008
