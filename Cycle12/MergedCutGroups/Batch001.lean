import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch000
import Cycle12.MergedCutCells.Batch002
import Cycle12.MergedCutCells.Batch003
import Cycle12.MergedCutCells.Batch004
import Cycle12.PopulationCertificates.Batch000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch001

def certificate12 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate8,PopulationCertificates.Batch000.certificate8,[MergedCutCells.Batch002.certificate28,MergedCutCells.Batch002.certificate29],(35813207031428853/62500000000000000),(some (1294222741/1000000000)),(1/2),(273215974897909431/1000000000000000000),(some (16775603628410007/500000000000000000)),(some (2697171401962649/500000000000000000))⟩
theorem numericValid12 : certificate12.NumericValid := by decide +kernel
theorem cellsSound12 : ∀ c∈certificate12.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch002.certificate28,MergedCutCells.Batch002.certificate29], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound28,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound29,List.forall_mem_nil _⟩⟩
theorem cellsNumeric12 : ∀ c∈certificate12.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate28,MergedCutCells.Batch002.certificate29], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid28,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid29,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid12 : ∀ c∈certificate12.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate28,MergedCutCells.Batch002.certificate29], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid5,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid5,List.forall_mem_nil _⟩⟩
theorem populationMatches12 : ∀ c∈certificate12.cells, c.population=certificate12.population := by
  change ∀ c∈[MergedCutCells.Batch002.certificate28,MergedCutCells.Batch002.certificate29], c.population=PopulationCertificates.Batch000.certificate8
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers12 {x : ℝ} (hx : certificate12.interval.Contains x) : ∃ c∈certificate12.cells, c.region.interval.Contains x := rat_cut_group_covers certificate12 numericValid12 hx

def certificate13 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate8,PopulationCertificates.Batch000.certificate8,[MergedCutCells.Batch002.certificate30,MergedCutCells.Batch002.certificate31,MergedCutCells.Batch002.certificate32],(1294222741/1000000000),none,(1/2),(5431613834277241/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid13 : certificate13.NumericValid := by decide +kernel
theorem cellsSound13 : ∀ c∈certificate13.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch002.certificate30,MergedCutCells.Batch002.certificate31,MergedCutCells.Batch002.certificate32], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound30,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound31,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound32,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric13 : ∀ c∈certificate13.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate30,MergedCutCells.Batch002.certificate31,MergedCutCells.Batch002.certificate32], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid30,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid31,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid32,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid13 : ∀ c∈certificate13.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate30,MergedCutCells.Batch002.certificate31,MergedCutCells.Batch002.certificate32], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches13 : ∀ c∈certificate13.cells, c.population=certificate13.population := by
  change ∀ c∈[MergedCutCells.Batch002.certificate30,MergedCutCells.Batch002.certificate31,MergedCutCells.Batch002.certificate32], c.population=PopulationCertificates.Batch000.certificate8
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers13 {x : ℝ} (hx : certificate13.interval.Contains x) : ∃ c∈certificate13.cells, c.region.interval.Contains x := rat_cut_group_covers certificate13 numericValid13 hx

def certificate14 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate9,PopulationCertificates.Batch000.certificate9,[MergedCutCells.Batch002.certificate33,MergedCutCells.Batch002.certificate34],(1654446731702632883/500000000000000000),none,(1/2),(230273741889981111/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid14 : certificate14.NumericValid := by decide +kernel
theorem cellsSound14 : ∀ c∈certificate14.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch002.certificate33,MergedCutCells.Batch002.certificate34], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound33,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound34,List.forall_mem_nil _⟩⟩
theorem cellsNumeric14 : ∀ c∈certificate14.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate33,MergedCutCells.Batch002.certificate34], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid33,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid34,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid14 : ∀ c∈certificate14.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate33,MergedCutCells.Batch002.certificate34], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches14 : ∀ c∈certificate14.cells, c.population=certificate14.population := by
  change ∀ c∈[MergedCutCells.Batch002.certificate33,MergedCutCells.Batch002.certificate34], c.population=PopulationCertificates.Batch000.certificate9
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers14 {x : ℝ} (hx : certificate14.interval.Contains x) : ∃ c∈certificate14.cells, c.region.interval.Contains x := rat_cut_group_covers certificate14 numericValid14 hx

def certificate15 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate10,PopulationCertificates.Batch000.certificate10,[MergedCutCells.Batch002.certificate35,MergedCutCells.Batch003.certificate36],(576326753767153087/1000000000000000000),(some (1300414217/1000000000)),(1/2),(54113028508783483/200000000000000000),(some (10858420910896177/250000000000000000)),(some (229686272577979/31250000000000000))⟩
theorem numericValid15 : certificate15.NumericValid := by decide +kernel
theorem cellsSound15 : ∀ c∈certificate15.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch002.certificate35,MergedCutCells.Batch003.certificate36], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.sound35,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound36,List.forall_mem_nil _⟩⟩
theorem cellsNumeric15 : ∀ c∈certificate15.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate35,MergedCutCells.Batch003.certificate36], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch002.numericValid35,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid36,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid15 : ∀ c∈certificate15.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch002.certificate35,MergedCutCells.Batch003.certificate36], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid6,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid6,List.forall_mem_nil _⟩⟩
theorem populationMatches15 : ∀ c∈certificate15.cells, c.population=certificate15.population := by
  change ∀ c∈[MergedCutCells.Batch002.certificate35,MergedCutCells.Batch003.certificate36], c.population=PopulationCertificates.Batch000.certificate10
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers15 {x : ℝ} (hx : certificate15.interval.Contains x) : ∃ c∈certificate15.cells, c.region.interval.Contains x := rat_cut_group_covers certificate15 numericValid15 hx

def certificate16 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate10,PopulationCertificates.Batch000.certificate10,[MergedCutCells.Batch003.certificate37,MergedCutCells.Batch003.certificate38,MergedCutCells.Batch003.certificate39],(1300414217/1000000000),none,(1/2),(268257477607572071/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid16 : certificate16.NumericValid := by decide +kernel
theorem cellsSound16 : ∀ c∈certificate16.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch003.certificate37,MergedCutCells.Batch003.certificate38,MergedCutCells.Batch003.certificate39], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound37,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound38,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound39,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric16 : ∀ c∈certificate16.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch003.certificate37,MergedCutCells.Batch003.certificate38,MergedCutCells.Batch003.certificate39], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid37,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid38,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid39,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid16 : ∀ c∈certificate16.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch003.certificate37,MergedCutCells.Batch003.certificate38,MergedCutCells.Batch003.certificate39], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches16 : ∀ c∈certificate16.cells, c.population=certificate16.population := by
  change ∀ c∈[MergedCutCells.Batch003.certificate37,MergedCutCells.Batch003.certificate38,MergedCutCells.Batch003.certificate39], c.population=PopulationCertificates.Batch000.certificate10
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers16 {x : ℝ} (hx : certificate16.interval.Contains x) : ∃ c∈certificate16.cells, c.region.interval.Contains x := rat_cut_group_covers certificate16 numericValid16 hx

def certificate17 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate11,PopulationCertificates.Batch000.certificate11,[MergedCutCells.Batch003.certificate40,MergedCutCells.Batch003.certificate41],(3229170141460172409/1000000000000000000),none,(1/2),(71013983384244707/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid17 : certificate17.NumericValid := by decide +kernel
theorem cellsSound17 : ∀ c∈certificate17.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch003.certificate40,MergedCutCells.Batch003.certificate41], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound40,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound41,List.forall_mem_nil _⟩⟩
theorem cellsNumeric17 : ∀ c∈certificate17.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch003.certificate40,MergedCutCells.Batch003.certificate41], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid40,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid41,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid17 : ∀ c∈certificate17.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch003.certificate40,MergedCutCells.Batch003.certificate41], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches17 : ∀ c∈certificate17.cells, c.population=certificate17.population := by
  change ∀ c∈[MergedCutCells.Batch003.certificate40,MergedCutCells.Batch003.certificate41], c.population=PopulationCertificates.Batch000.certificate11
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers17 {x : ℝ} (hx : certificate17.interval.Contains x) : ∃ c∈certificate17.cells, c.region.interval.Contains x := rat_cut_group_covers certificate17 numericValid17 hx

def certificate18 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate12,PopulationCertificates.Batch000.certificate12,[MergedCutCells.Batch003.certificate42,MergedCutCells.Batch003.certificate43],(116010850728139807/200000000000000000),(some (318891533/250000000)),(1/2),(133941266143848201/500000000000000000),(some (53855555576563637/1000000000000000000)),(some (4767698567625307/500000000000000000))⟩
theorem numericValid18 : certificate18.NumericValid := by decide +kernel
theorem cellsSound18 : ∀ c∈certificate18.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch003.certificate42,MergedCutCells.Batch003.certificate43], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound42,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound43,List.forall_mem_nil _⟩⟩
theorem cellsNumeric18 : ∀ c∈certificate18.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch003.certificate42,MergedCutCells.Batch003.certificate43], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid42,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid43,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid18 : ∀ c∈certificate18.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch003.certificate42,MergedCutCells.Batch003.certificate43], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid7,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid7,List.forall_mem_nil _⟩⟩
theorem populationMatches18 : ∀ c∈certificate18.cells, c.population=certificate18.population := by
  change ∀ c∈[MergedCutCells.Batch003.certificate42,MergedCutCells.Batch003.certificate43], c.population=PopulationCertificates.Batch000.certificate12
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers18 {x : ℝ} (hx : certificate18.interval.Contains x) : ∃ c∈certificate18.cells, c.region.interval.Contains x := rat_cut_group_covers certificate18 numericValid18 hx

def certificate19 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate12,PopulationCertificates.Batch000.certificate12,[MergedCutCells.Batch003.certificate44,MergedCutCells.Batch003.certificate45,MergedCutCells.Batch003.certificate46,MergedCutCells.Batch003.certificate47],(318891533/250000000),none,(1/2),(264926253100409403/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid19 : certificate19.NumericValid := by decide +kernel
theorem cellsSound19 : ∀ c∈certificate19.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch003.certificate44,MergedCutCells.Batch003.certificate45,MergedCutCells.Batch003.certificate46,MergedCutCells.Batch003.certificate47], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound44,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound45,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound46,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.sound47,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric19 : ∀ c∈certificate19.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch003.certificate44,MergedCutCells.Batch003.certificate45,MergedCutCells.Batch003.certificate46,MergedCutCells.Batch003.certificate47], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid44,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid45,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid46,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch003.numericValid47,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid19 : ∀ c∈certificate19.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch003.certificate44,MergedCutCells.Batch003.certificate45,MergedCutCells.Batch003.certificate46,MergedCutCells.Batch003.certificate47], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches19 : ∀ c∈certificate19.cells, c.population=certificate19.population := by
  change ∀ c∈[MergedCutCells.Batch003.certificate44,MergedCutCells.Batch003.certificate45,MergedCutCells.Batch003.certificate46,MergedCutCells.Batch003.certificate47], c.population=PopulationCertificates.Batch000.certificate12
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers19 {x : ℝ} (hx : certificate19.interval.Contains x) : ∃ c∈certificate19.cells, c.region.interval.Contains x := rat_cut_group_covers certificate19 numericValid19 hx

def certificate20 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate13,PopulationCertificates.Batch000.certificate13,[MergedCutCells.Batch004.certificate48,MergedCutCells.Batch004.certificate49],(3260787563140408713/1000000000000000000),none,(1/2),(175278501970626239/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid20 : certificate20.NumericValid := by decide +kernel
theorem cellsSound20 : ∀ c∈certificate20.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch004.certificate48,MergedCutCells.Batch004.certificate49], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound48,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound49,List.forall_mem_nil _⟩⟩
theorem cellsNumeric20 : ∀ c∈certificate20.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate48,MergedCutCells.Batch004.certificate49], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid48,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid49,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid20 : ∀ c∈certificate20.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate48,MergedCutCells.Batch004.certificate49], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches20 : ∀ c∈certificate20.cells, c.population=certificate20.population := by
  change ∀ c∈[MergedCutCells.Batch004.certificate48,MergedCutCells.Batch004.certificate49], c.population=PopulationCertificates.Batch000.certificate13
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers20 {x : ℝ} (hx : certificate20.interval.Contains x) : ∃ c∈certificate20.cells, c.region.interval.Contains x := rat_cut_group_covers certificate20 numericValid20 hx

def certificate21 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate14,PopulationCertificates.Batch000.certificate14,[MergedCutCells.Batch004.certificate50,MergedCutCells.Batch004.certificate51],(584388887288127723/1000000000000000000),(some (320874061/250000000)),(1/2),(5304076280648419/20000000000000000),(some (1021638853354607/15625000000000000)),(some (12086903197871829/1000000000000000000))⟩
theorem numericValid21 : certificate21.NumericValid := by decide +kernel
theorem cellsSound21 : ∀ c∈certificate21.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch004.certificate50,MergedCutCells.Batch004.certificate51], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound50,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound51,List.forall_mem_nil _⟩⟩
theorem cellsNumeric21 : ∀ c∈certificate21.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate50,MergedCutCells.Batch004.certificate51], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid50,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid51,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid21 : ∀ c∈certificate21.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate50,MergedCutCells.Batch004.certificate51], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid8,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid8,List.forall_mem_nil _⟩⟩
theorem populationMatches21 : ∀ c∈certificate21.cells, c.population=certificate21.population := by
  change ∀ c∈[MergedCutCells.Batch004.certificate50,MergedCutCells.Batch004.certificate51], c.population=PopulationCertificates.Batch000.certificate14
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers21 {x : ℝ} (hx : certificate21.interval.Contains x) : ∃ c∈certificate21.cells, c.region.interval.Contains x := rat_cut_group_covers certificate21 numericValid21 hx

def certificate22 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate14,PopulationCertificates.Batch000.certificate14,[MergedCutCells.Batch004.certificate52,MergedCutCells.Batch004.certificate53,MergedCutCells.Batch004.certificate54],(320874061/250000000),none,(1/2),(52301735084585873/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid22 : certificate22.NumericValid := by decide +kernel
theorem cellsSound22 : ∀ c∈certificate22.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch004.certificate52,MergedCutCells.Batch004.certificate53,MergedCutCells.Batch004.certificate54], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound52,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound53,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound54,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric22 : ∀ c∈certificate22.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate52,MergedCutCells.Batch004.certificate53,MergedCutCells.Batch004.certificate54], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid52,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid53,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid54,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid22 : ∀ c∈certificate22.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate52,MergedCutCells.Batch004.certificate53,MergedCutCells.Batch004.certificate54], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches22 : ∀ c∈certificate22.cells, c.population=certificate22.population := by
  change ∀ c∈[MergedCutCells.Batch004.certificate52,MergedCutCells.Batch004.certificate53,MergedCutCells.Batch004.certificate54], c.population=PopulationCertificates.Batch000.certificate14
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers22 {x : ℝ} (hx : certificate22.interval.Contains x) : ∃ c∈certificate22.cells, c.region.interval.Contains x := rat_cut_group_covers certificate22 numericValid22 hx

def certificate23 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate15,PopulationCertificates.Batch000.certificate15,[MergedCutCells.Batch004.certificate55,MergedCutCells.Batch004.certificate56],(3216207583754941/976562500000000),none,(1/2),(26034422971658919/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid23 : certificate23.NumericValid := by decide +kernel
theorem cellsSound23 : ∀ c∈certificate23.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch004.certificate55,MergedCutCells.Batch004.certificate56], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound55,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound56,List.forall_mem_nil _⟩⟩
theorem cellsNumeric23 : ∀ c∈certificate23.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate55,MergedCutCells.Batch004.certificate56], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid55,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid56,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid23 : ∀ c∈certificate23.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate55,MergedCutCells.Batch004.certificate56], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches23 : ∀ c∈certificate23.cells, c.population=certificate23.population := by
  change ∀ c∈[MergedCutCells.Batch004.certificate55,MergedCutCells.Batch004.certificate56], c.population=PopulationCertificates.Batch000.certificate15
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers23 {x : ℝ} (hx : certificate23.interval.Contains x) : ∃ c∈certificate23.cells, c.region.interval.Contains x := rat_cut_group_covers certificate23 numericValid23 hx

end Cycle12.MergedCutGroups.Batch001
