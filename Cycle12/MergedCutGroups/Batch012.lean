import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch004
import Cycle12.GeometryCertificates.Batch005
import Cycle12.MergedCutCells.Batch043
import Cycle12.MergedCutCells.Batch044
import Cycle12.MergedCutCells.Batch045
import Cycle12.MergedCutCells.Batch046
import Cycle12.MergedCutCells.Batch047
import Cycle12.PopulationCertificates.Batch004
import Cycle12.PopulationCertificates.Batch005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch012

def certificate144 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate96,PopulationCertificates.Batch004.certificate96,[MergedCutCells.Batch043.certificate520,MergedCutCells.Batch043.certificate521,MergedCutCells.Batch043.certificate522],(789463278721296573/1000000000000000000),(some (914777907/1000000000)),(1/2),(133445988564893097/500000000000000000),(some (133009133108309521/250000000000000000)),(some (112045210325723831/500000000000000000))⟩
theorem numericValid144 : certificate144.NumericValid := by decide +kernel
theorem cellsSound144 : ∀ c∈certificate144.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch043.certificate520,MergedCutCells.Batch043.certificate521,MergedCutCells.Batch043.certificate522], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound520,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound521,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound522,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric144 : ∀ c∈certificate144.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch043.certificate520,MergedCutCells.Batch043.certificate521,MergedCutCells.Batch043.certificate522], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid520,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid521,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid522,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid144 : ∀ c∈certificate144.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch043.certificate520,MergedCutCells.Batch043.certificate521,MergedCutCells.Batch043.certificate522], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid49,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid49,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid49,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches144 : ∀ c∈certificate144.cells, c.population=certificate144.population := by
  change ∀ c∈[MergedCutCells.Batch043.certificate520,MergedCutCells.Batch043.certificate521,MergedCutCells.Batch043.certificate522], c.population=PopulationCertificates.Batch004.certificate96
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers144 {x : ℝ} (hx : certificate144.interval.Contains x) : ∃ c∈certificate144.cells, c.region.interval.Contains x := rat_cut_group_covers certificate144 numericValid144 hx

def certificate145 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate96,PopulationCertificates.Batch004.certificate96,[MergedCutCells.Batch043.certificate523,MergedCutCells.Batch043.certificate524,MergedCutCells.Batch043.certificate525,MergedCutCells.Batch043.certificate526,MergedCutCells.Batch043.certificate527,MergedCutCells.Batch044.certificate528,MergedCutCells.Batch044.certificate529],(914777907/1000000000),none,(1/2),(198561493148954131/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid145 : certificate145.NumericValid := by decide +kernel
theorem cellsSound145 : ∀ c∈certificate145.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch043.certificate523,MergedCutCells.Batch043.certificate524,MergedCutCells.Batch043.certificate525,MergedCutCells.Batch043.certificate526,MergedCutCells.Batch043.certificate527,MergedCutCells.Batch044.certificate528,MergedCutCells.Batch044.certificate529], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound523,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound525,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound526,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.sound527,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound529,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric145 : ∀ c∈certificate145.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch043.certificate523,MergedCutCells.Batch043.certificate524,MergedCutCells.Batch043.certificate525,MergedCutCells.Batch043.certificate526,MergedCutCells.Batch043.certificate527,MergedCutCells.Batch044.certificate528,MergedCutCells.Batch044.certificate529], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid523,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid525,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid526,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch043.numericValid527,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid529,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid145 : ∀ c∈certificate145.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch043.certificate523,MergedCutCells.Batch043.certificate524,MergedCutCells.Batch043.certificate525,MergedCutCells.Batch043.certificate526,MergedCutCells.Batch043.certificate527,MergedCutCells.Batch044.certificate528,MergedCutCells.Batch044.certificate529], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches145 : ∀ c∈certificate145.cells, c.population=certificate145.population := by
  change ∀ c∈[MergedCutCells.Batch043.certificate523,MergedCutCells.Batch043.certificate524,MergedCutCells.Batch043.certificate525,MergedCutCells.Batch043.certificate526,MergedCutCells.Batch043.certificate527,MergedCutCells.Batch044.certificate528,MergedCutCells.Batch044.certificate529], c.population=PopulationCertificates.Batch004.certificate96
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers145 {x : ℝ} (hx : certificate145.interval.Contains x) : ∃ c∈certificate145.cells, c.region.interval.Contains x := rat_cut_group_covers certificate145 numericValid145 hx

def certificate146 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate97,PopulationCertificates.Batch004.certificate97,[MergedCutCells.Batch044.certificate530,MergedCutCells.Batch044.certificate531,MergedCutCells.Batch044.certificate532,MergedCutCells.Batch044.certificate533],(1867892073501326683/500000000000000000),none,(1/2),(531429280071322167/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid146 : certificate146.NumericValid := by decide +kernel
theorem cellsSound146 : ∀ c∈certificate146.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch044.certificate530,MergedCutCells.Batch044.certificate531,MergedCutCells.Batch044.certificate532,MergedCutCells.Batch044.certificate533], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound530,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound531,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound532,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound533,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric146 : ∀ c∈certificate146.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch044.certificate530,MergedCutCells.Batch044.certificate531,MergedCutCells.Batch044.certificate532,MergedCutCells.Batch044.certificate533], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid530,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid531,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid532,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid533,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid146 : ∀ c∈certificate146.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch044.certificate530,MergedCutCells.Batch044.certificate531,MergedCutCells.Batch044.certificate532,MergedCutCells.Batch044.certificate533], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches146 : ∀ c∈certificate146.cells, c.population=certificate146.population := by
  change ∀ c∈[MergedCutCells.Batch044.certificate530,MergedCutCells.Batch044.certificate531,MergedCutCells.Batch044.certificate532,MergedCutCells.Batch044.certificate533], c.population=PopulationCertificates.Batch004.certificate97
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers146 {x : ℝ} (hx : certificate146.interval.Contains x) : ∃ c∈certificate146.cells, c.region.interval.Contains x := rat_cut_group_covers certificate146 numericValid146 hx

def certificate147 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate98,PopulationCertificates.Batch004.certificate98,[MergedCutCells.Batch044.certificate534,MergedCutCells.Batch044.certificate535,MergedCutCells.Batch044.certificate536],(789462393787773153/1000000000000000000),(some (228694229/250000000)),(1/2),(130413231294672259/500000000000000000),(some (269597343559360709/500000000000000000)),(some (114966216696431771/500000000000000000))⟩
theorem numericValid147 : certificate147.NumericValid := by decide +kernel
theorem cellsSound147 : ∀ c∈certificate147.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch044.certificate534,MergedCutCells.Batch044.certificate535,MergedCutCells.Batch044.certificate536], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound534,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound535,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound536,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric147 : ∀ c∈certificate147.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch044.certificate534,MergedCutCells.Batch044.certificate535,MergedCutCells.Batch044.certificate536], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid534,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid535,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid536,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid147 : ∀ c∈certificate147.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch044.certificate534,MergedCutCells.Batch044.certificate535,MergedCutCells.Batch044.certificate536], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid50,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid50,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid50,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches147 : ∀ c∈certificate147.cells, c.population=certificate147.population := by
  change ∀ c∈[MergedCutCells.Batch044.certificate534,MergedCutCells.Batch044.certificate535,MergedCutCells.Batch044.certificate536], c.population=PopulationCertificates.Batch004.certificate98
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers147 {x : ℝ} (hx : certificate147.interval.Contains x) : ∃ c∈certificate147.cells, c.region.interval.Contains x := rat_cut_group_covers certificate147 numericValid147 hx

def certificate148 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate98,PopulationCertificates.Batch004.certificate98,[MergedCutCells.Batch044.certificate537,MergedCutCells.Batch044.certificate538,MergedCutCells.Batch044.certificate539,MergedCutCells.Batch045.certificate540,MergedCutCells.Batch045.certificate541,MergedCutCells.Batch045.certificate542],(228694229/250000000),none,(1/2),(202915069417199861/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid148 : certificate148.NumericValid := by decide +kernel
theorem cellsSound148 : ∀ c∈certificate148.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch044.certificate537,MergedCutCells.Batch044.certificate538,MergedCutCells.Batch044.certificate539,MergedCutCells.Batch045.certificate540,MergedCutCells.Batch045.certificate541,MergedCutCells.Batch045.certificate542], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound537,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound538,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.sound539,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound540,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound541,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound542,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric148 : ∀ c∈certificate148.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch044.certificate537,MergedCutCells.Batch044.certificate538,MergedCutCells.Batch044.certificate539,MergedCutCells.Batch045.certificate540,MergedCutCells.Batch045.certificate541,MergedCutCells.Batch045.certificate542], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid537,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid538,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch044.numericValid539,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid540,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid541,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid542,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid148 : ∀ c∈certificate148.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch044.certificate537,MergedCutCells.Batch044.certificate538,MergedCutCells.Batch044.certificate539,MergedCutCells.Batch045.certificate540,MergedCutCells.Batch045.certificate541,MergedCutCells.Batch045.certificate542], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches148 : ∀ c∈certificate148.cells, c.population=certificate148.population := by
  change ∀ c∈[MergedCutCells.Batch044.certificate537,MergedCutCells.Batch044.certificate538,MergedCutCells.Batch044.certificate539,MergedCutCells.Batch045.certificate540,MergedCutCells.Batch045.certificate541,MergedCutCells.Batch045.certificate542], c.population=PopulationCertificates.Batch004.certificate98
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers148 {x : ℝ} (hx : certificate148.interval.Contains x) : ∃ c∈certificate148.cells, c.region.interval.Contains x := rat_cut_group_covers certificate148 numericValid148 hx

def certificate149 : RatCutGroup := ⟨GeometryCertificates.Batch004.certificate99,PopulationCertificates.Batch004.certificate99,[MergedCutCells.Batch045.certificate543,MergedCutCells.Batch045.certificate544,MergedCutCells.Batch045.certificate545],(3752084006030571863/1000000000000000000),none,(1/2),(138432537685039401/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid149 : certificate149.NumericValid := by decide +kernel
theorem cellsSound149 : ∀ c∈certificate149.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch045.certificate543,MergedCutCells.Batch045.certificate544,MergedCutCells.Batch045.certificate545], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound543,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound544,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound545,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric149 : ∀ c∈certificate149.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch045.certificate543,MergedCutCells.Batch045.certificate544,MergedCutCells.Batch045.certificate545], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid543,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid544,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid545,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid149 : ∀ c∈certificate149.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch045.certificate543,MergedCutCells.Batch045.certificate544,MergedCutCells.Batch045.certificate545], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches149 : ∀ c∈certificate149.cells, c.population=certificate149.population := by
  change ∀ c∈[MergedCutCells.Batch045.certificate543,MergedCutCells.Batch045.certificate544,MergedCutCells.Batch045.certificate545], c.population=PopulationCertificates.Batch004.certificate99
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers149 {x : ℝ} (hx : certificate149.interval.Contains x) : ∃ c∈certificate149.cells, c.region.interval.Contains x := rat_cut_group_covers certificate149 numericValid149 hx

def certificate150 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate100,PopulationCertificates.Batch005.certificate100,[MergedCutCells.Batch045.certificate546,MergedCutCells.Batch045.certificate547,MergedCutCells.Batch045.certificate548],(399218259653537777/500000000000000000),(some (451535443/500000000)),(1/2),(146646716731228427/500000000000000000),(some (13602152890639781/25000000000000000)),(some (117009073818992553/500000000000000000))⟩
theorem numericValid150 : certificate150.NumericValid := by decide +kernel
theorem cellsSound150 : ∀ c∈certificate150.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch045.certificate546,MergedCutCells.Batch045.certificate547,MergedCutCells.Batch045.certificate548], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound546,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound547,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound548,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric150 : ∀ c∈certificate150.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch045.certificate546,MergedCutCells.Batch045.certificate547,MergedCutCells.Batch045.certificate548], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid546,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid547,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid548,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid150 : ∀ c∈certificate150.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch045.certificate546,MergedCutCells.Batch045.certificate547,MergedCutCells.Batch045.certificate548], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid51,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid51,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid51,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches150 : ∀ c∈certificate150.cells, c.population=certificate150.population := by
  change ∀ c∈[MergedCutCells.Batch045.certificate546,MergedCutCells.Batch045.certificate547,MergedCutCells.Batch045.certificate548], c.population=PopulationCertificates.Batch005.certificate100
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers150 {x : ℝ} (hx : certificate150.interval.Contains x) : ∃ c∈certificate150.cells, c.region.interval.Contains x := rat_cut_group_covers certificate150 numericValid150 hx

def certificate151 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate100,PopulationCertificates.Batch005.certificate100,[MergedCutCells.Batch045.certificate549,MergedCutCells.Batch045.certificate550,MergedCutCells.Batch045.certificate551,MergedCutCells.Batch046.certificate552,MergedCutCells.Batch046.certificate553,MergedCutCells.Batch046.certificate554,MergedCutCells.Batch046.certificate555],(451535443/500000000),none,(1/2),(41290919347572711/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid151 : certificate151.NumericValid := by decide +kernel
theorem cellsSound151 : ∀ c∈certificate151.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch045.certificate549,MergedCutCells.Batch045.certificate550,MergedCutCells.Batch045.certificate551,MergedCutCells.Batch046.certificate552,MergedCutCells.Batch046.certificate553,MergedCutCells.Batch046.certificate554,MergedCutCells.Batch046.certificate555], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound549,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound550,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.sound551,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound552,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound553,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound554,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound555,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric151 : ∀ c∈certificate151.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch045.certificate549,MergedCutCells.Batch045.certificate550,MergedCutCells.Batch045.certificate551,MergedCutCells.Batch046.certificate552,MergedCutCells.Batch046.certificate553,MergedCutCells.Batch046.certificate554,MergedCutCells.Batch046.certificate555], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid549,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid550,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch045.numericValid551,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid552,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid553,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid554,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid555,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid151 : ∀ c∈certificate151.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch045.certificate549,MergedCutCells.Batch045.certificate550,MergedCutCells.Batch045.certificate551,MergedCutCells.Batch046.certificate552,MergedCutCells.Batch046.certificate553,MergedCutCells.Batch046.certificate554,MergedCutCells.Batch046.certificate555], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches151 : ∀ c∈certificate151.cells, c.population=certificate151.population := by
  change ∀ c∈[MergedCutCells.Batch045.certificate549,MergedCutCells.Batch045.certificate550,MergedCutCells.Batch045.certificate551,MergedCutCells.Batch046.certificate552,MergedCutCells.Batch046.certificate553,MergedCutCells.Batch046.certificate554,MergedCutCells.Batch046.certificate555], c.population=PopulationCertificates.Batch005.certificate100
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers151 {x : ℝ} (hx : certificate151.interval.Contains x) : ∃ c∈certificate151.cells, c.region.interval.Contains x := rat_cut_group_covers certificate151 numericValid151 hx

def certificate152 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate101,PopulationCertificates.Batch005.certificate101,[MergedCutCells.Batch046.certificate556,MergedCutCells.Batch046.certificate557,MergedCutCells.Batch046.certificate558],(1884328779523723637/500000000000000000),none,(1/2),(578173830669959259/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid152 : certificate152.NumericValid := by decide +kernel
theorem cellsSound152 : ∀ c∈certificate152.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch046.certificate556,MergedCutCells.Batch046.certificate557,MergedCutCells.Batch046.certificate558], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound556,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound558,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric152 : ∀ c∈certificate152.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch046.certificate556,MergedCutCells.Batch046.certificate557,MergedCutCells.Batch046.certificate558], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid556,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid557,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid558,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid152 : ∀ c∈certificate152.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch046.certificate556,MergedCutCells.Batch046.certificate557,MergedCutCells.Batch046.certificate558], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches152 : ∀ c∈certificate152.cells, c.population=certificate152.population := by
  change ∀ c∈[MergedCutCells.Batch046.certificate556,MergedCutCells.Batch046.certificate557,MergedCutCells.Batch046.certificate558], c.population=PopulationCertificates.Batch005.certificate101
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers152 {x : ℝ} (hx : certificate152.interval.Contains x) : ∃ c∈certificate152.cells, c.region.interval.Contains x := rat_cut_group_covers certificate152 numericValid152 hx

def certificate153 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate102,PopulationCertificates.Batch005.certificate102,[MergedCutCells.Batch046.certificate559,MergedCutCells.Batch046.certificate560,MergedCutCells.Batch046.certificate561],(801330703857886301/1000000000000000000),(some (453126119/500000000)),(1/2),(153929857462021359/500000000000000000),(some (547476659939056179/1000000000000000000)),(some (236896973495266683/1000000000000000000))⟩
theorem numericValid153 : certificate153.NumericValid := by decide +kernel
theorem cellsSound153 : ∀ c∈certificate153.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch046.certificate559,MergedCutCells.Batch046.certificate560,MergedCutCells.Batch046.certificate561], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound560,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound561,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric153 : ∀ c∈certificate153.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch046.certificate559,MergedCutCells.Batch046.certificate560,MergedCutCells.Batch046.certificate561], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid559,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid560,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid561,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid153 : ∀ c∈certificate153.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch046.certificate559,MergedCutCells.Batch046.certificate560,MergedCutCells.Batch046.certificate561], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid52,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid52,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid52,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches153 : ∀ c∈certificate153.cells, c.population=certificate153.population := by
  change ∀ c∈[MergedCutCells.Batch046.certificate559,MergedCutCells.Batch046.certificate560,MergedCutCells.Batch046.certificate561], c.population=PopulationCertificates.Batch005.certificate102
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers153 {x : ℝ} (hx : certificate153.interval.Contains x) : ∃ c∈certificate153.cells, c.region.interval.Contains x := rat_cut_group_covers certificate153 numericValid153 hx

def certificate154 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate102,PopulationCertificates.Batch005.certificate102,[MergedCutCells.Batch046.certificate562,MergedCutCells.Batch046.certificate563,MergedCutCells.Batch047.certificate564,MergedCutCells.Batch047.certificate565,MergedCutCells.Batch047.certificate566,MergedCutCells.Batch047.certificate567,MergedCutCells.Batch047.certificate568],(453126119/500000000),none,(1/2),(219028343684737297/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid154 : certificate154.NumericValid := by decide +kernel
theorem cellsSound154 : ∀ c∈certificate154.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch046.certificate562,MergedCutCells.Batch046.certificate563,MergedCutCells.Batch047.certificate564,MergedCutCells.Batch047.certificate565,MergedCutCells.Batch047.certificate566,MergedCutCells.Batch047.certificate567,MergedCutCells.Batch047.certificate568], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound562,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.sound563,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound564,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound566,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound568,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric154 : ∀ c∈certificate154.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch046.certificate562,MergedCutCells.Batch046.certificate563,MergedCutCells.Batch047.certificate564,MergedCutCells.Batch047.certificate565,MergedCutCells.Batch047.certificate566,MergedCutCells.Batch047.certificate567,MergedCutCells.Batch047.certificate568], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid562,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch046.numericValid563,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid564,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid565,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid566,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid567,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid568,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid154 : ∀ c∈certificate154.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch046.certificate562,MergedCutCells.Batch046.certificate563,MergedCutCells.Batch047.certificate564,MergedCutCells.Batch047.certificate565,MergedCutCells.Batch047.certificate566,MergedCutCells.Batch047.certificate567,MergedCutCells.Batch047.certificate568], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches154 : ∀ c∈certificate154.cells, c.population=certificate154.population := by
  change ∀ c∈[MergedCutCells.Batch046.certificate562,MergedCutCells.Batch046.certificate563,MergedCutCells.Batch047.certificate564,MergedCutCells.Batch047.certificate565,MergedCutCells.Batch047.certificate566,MergedCutCells.Batch047.certificate567,MergedCutCells.Batch047.certificate568], c.population=PopulationCertificates.Batch005.certificate102
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers154 {x : ℝ} (hx : certificate154.interval.Contains x) : ∃ c∈certificate154.cells, c.region.interval.Contains x := rat_cut_group_covers certificate154 numericValid154 hx

def certificate155 : RatCutGroup := ⟨GeometryCertificates.Batch005.certificate103,PopulationCertificates.Batch005.certificate103,[MergedCutCells.Batch047.certificate569,MergedCutCells.Batch047.certificate570,MergedCutCells.Batch047.certificate571],(3791216503948534307/1000000000000000000),none,(1/2),(61891312395972143/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid155 : certificate155.NumericValid := by decide +kernel
theorem cellsSound155 : ∀ c∈certificate155.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch047.certificate569,MergedCutCells.Batch047.certificate570,MergedCutCells.Batch047.certificate571], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound569,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.sound571,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric155 : ∀ c∈certificate155.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch047.certificate569,MergedCutCells.Batch047.certificate570,MergedCutCells.Batch047.certificate571], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid569,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid570,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch047.numericValid571,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid155 : ∀ c∈certificate155.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch047.certificate569,MergedCutCells.Batch047.certificate570,MergedCutCells.Batch047.certificate571], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches155 : ∀ c∈certificate155.cells, c.population=certificate155.population := by
  change ∀ c∈[MergedCutCells.Batch047.certificate569,MergedCutCells.Batch047.certificate570,MergedCutCells.Batch047.certificate571], c.population=PopulationCertificates.Batch005.certificate103
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers155 {x : ℝ} (hx : certificate155.interval.Contains x) : ∃ c∈certificate155.cells, c.region.interval.Contains x := rat_cut_group_covers certificate155 numericValid155 hx

end Cycle12.MergedCutGroups.Batch012
