import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch000
import Cycle12.GeometryCertificates.Batch001
import Cycle12.MergedCutCells.Batch004
import Cycle12.MergedCutCells.Batch005
import Cycle12.MergedCutCells.Batch006
import Cycle12.MergedCutCells.Batch007
import Cycle12.PopulationCertificates.Batch000
import Cycle12.PopulationCertificates.Batch001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch002

def certificate24 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate16,PopulationCertificates.Batch000.certificate16,[MergedCutCells.Batch004.certificate57,MergedCutCells.Batch004.certificate58],(588975309448360287/1000000000000000000),(some (1265610549/1000000000)),(1/2),(65613090383984047/250000000000000000),(some (77235686583736397/1000000000000000000)),(some (23752993401881/1600000000000000))⟩
theorem numericValid24 : certificate24.NumericValid := by decide +kernel
theorem cellsSound24 : ∀ c∈certificate24.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch004.certificate57,MergedCutCells.Batch004.certificate58], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound57,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound58,List.forall_mem_nil _⟩⟩
theorem cellsNumeric24 : ∀ c∈certificate24.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate57,MergedCutCells.Batch004.certificate58], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid57,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid58,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid24 : ∀ c∈certificate24.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate57,MergedCutCells.Batch004.certificate58], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid9,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid9,List.forall_mem_nil _⟩⟩
theorem populationMatches24 : ∀ c∈certificate24.cells, c.population=certificate24.population := by
  change ∀ c∈[MergedCutCells.Batch004.certificate57,MergedCutCells.Batch004.certificate58], c.population=PopulationCertificates.Batch000.certificate16
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers24 {x : ℝ} (hx : certificate24.interval.Contains x) : ∃ c∈certificate24.cells, c.region.interval.Contains x := rat_cut_group_covers certificate24 numericValid24 hx

def certificate25 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate16,PopulationCertificates.Batch000.certificate16,[MergedCutCells.Batch004.certificate59,MergedCutCells.Batch005.certificate60,MergedCutCells.Batch005.certificate61,MergedCutCells.Batch005.certificate62],(1265610549/1000000000),none,(1/2),(51608061025401423/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid25 : certificate25.NumericValid := by decide +kernel
theorem cellsSound25 : ∀ c∈certificate25.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch004.certificate59,MergedCutCells.Batch005.certificate60,MergedCutCells.Batch005.certificate61,MergedCutCells.Batch005.certificate62], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.sound59,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound60,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound61,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound62,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric25 : ∀ c∈certificate25.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate59,MergedCutCells.Batch005.certificate60,MergedCutCells.Batch005.certificate61,MergedCutCells.Batch005.certificate62], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch004.numericValid59,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid60,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid61,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid62,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid25 : ∀ c∈certificate25.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch004.certificate59,MergedCutCells.Batch005.certificate60,MergedCutCells.Batch005.certificate61,MergedCutCells.Batch005.certificate62], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches25 : ∀ c∈certificate25.cells, c.population=certificate25.population := by
  change ∀ c∈[MergedCutCells.Batch004.certificate59,MergedCutCells.Batch005.certificate60,MergedCutCells.Batch005.certificate61,MergedCutCells.Batch005.certificate62], c.population=PopulationCertificates.Batch000.certificate16
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers25 {x : ℝ} (hx : certificate25.interval.Contains x) : ∃ c∈certificate25.cells, c.region.interval.Contains x := rat_cut_group_covers certificate25 numericValid25 hx

def certificate26 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate17,PopulationCertificates.Batch000.certificate17,[MergedCutCells.Batch005.certificate63,MergedCutCells.Batch005.certificate64],(3326990168860181551/1000000000000000000),none,(1/2),(240938250293425917/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid26 : certificate26.NumericValid := by decide +kernel
theorem cellsSound26 : ∀ c∈certificate26.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch005.certificate63,MergedCutCells.Batch005.certificate64], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound63,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound64,List.forall_mem_nil _⟩⟩
theorem cellsNumeric26 : ∀ c∈certificate26.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch005.certificate63,MergedCutCells.Batch005.certificate64], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid63,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid64,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid26 : ∀ c∈certificate26.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch005.certificate63,MergedCutCells.Batch005.certificate64], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches26 : ∀ c∈certificate26.cells, c.population=certificate26.population := by
  change ∀ c∈[MergedCutCells.Batch005.certificate63,MergedCutCells.Batch005.certificate64], c.population=PopulationCertificates.Batch000.certificate17
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers26 {x : ℝ} (hx : certificate26.interval.Contains x) : ∃ c∈certificate26.cells, c.region.interval.Contains x := rat_cut_group_covers certificate26 numericValid26 hx

def certificate27 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate18,PopulationCertificates.Batch000.certificate18,[MergedCutCells.Batch005.certificate65,MergedCutCells.Batch005.certificate66],(594285173451838707/1000000000000000000),(some (19924249/15625000)),(1/2),(64967246195267663/250000000000000000),(some (90145748603152859/1000000000000000000)),(some (17998956320876493/1000000000000000000))⟩
theorem numericValid27 : certificate27.NumericValid := by decide +kernel
theorem cellsSound27 : ∀ c∈certificate27.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch005.certificate65,MergedCutCells.Batch005.certificate66], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound65,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound66,List.forall_mem_nil _⟩⟩
theorem cellsNumeric27 : ∀ c∈certificate27.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch005.certificate65,MergedCutCells.Batch005.certificate66], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid65,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid66,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid27 : ∀ c∈certificate27.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch005.certificate65,MergedCutCells.Batch005.certificate66], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid10,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid10,List.forall_mem_nil _⟩⟩
theorem populationMatches27 : ∀ c∈certificate27.cells, c.population=certificate27.population := by
  change ∀ c∈[MergedCutCells.Batch005.certificate65,MergedCutCells.Batch005.certificate66], c.population=PopulationCertificates.Batch000.certificate18
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers27 {x : ℝ} (hx : certificate27.interval.Contains x) : ∃ c∈certificate27.cells, c.region.interval.Contains x := rat_cut_group_covers certificate27 numericValid27 hx

def certificate28 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate18,PopulationCertificates.Batch000.certificate18,[MergedCutCells.Batch005.certificate67,MergedCutCells.Batch005.certificate68,MergedCutCells.Batch005.certificate69],(19924249/15625000),none,(1/2),(25444215314647939/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid28 : certificate28.NumericValid := by decide +kernel
theorem cellsSound28 : ∀ c∈certificate28.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch005.certificate67,MergedCutCells.Batch005.certificate68,MergedCutCells.Batch005.certificate69], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound67,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound68,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound69,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric28 : ∀ c∈certificate28.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch005.certificate67,MergedCutCells.Batch005.certificate68,MergedCutCells.Batch005.certificate69], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid67,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid68,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid69,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid28 : ∀ c∈certificate28.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch005.certificate67,MergedCutCells.Batch005.certificate68,MergedCutCells.Batch005.certificate69], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches28 : ∀ c∈certificate28.cells, c.population=certificate28.population := by
  change ∀ c∈[MergedCutCells.Batch005.certificate67,MergedCutCells.Batch005.certificate68,MergedCutCells.Batch005.certificate69], c.population=PopulationCertificates.Batch000.certificate18
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers28 {x : ℝ} (hx : certificate28.interval.Contains x) : ∃ c∈certificate28.cells, c.region.interval.Contains x := rat_cut_group_covers certificate28 numericValid28 hx

def certificate29 : RatCutGroup := ⟨GeometryCertificates.Batch000.certificate19,PopulationCertificates.Batch000.certificate19,[MergedCutCells.Batch005.certificate70,MergedCutCells.Batch005.certificate71],(3361589830246311363/1000000000000000000),none,(1/2),(273212231204944207/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid29 : certificate29.NumericValid := by decide +kernel
theorem cellsSound29 : ∀ c∈certificate29.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch005.certificate70,MergedCutCells.Batch005.certificate71], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound70,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.sound71,List.forall_mem_nil _⟩⟩
theorem cellsNumeric29 : ∀ c∈certificate29.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch005.certificate70,MergedCutCells.Batch005.certificate71], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid70,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch005.numericValid71,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid29 : ∀ c∈certificate29.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch005.certificate70,MergedCutCells.Batch005.certificate71], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches29 : ∀ c∈certificate29.cells, c.population=certificate29.population := by
  change ∀ c∈[MergedCutCells.Batch005.certificate70,MergedCutCells.Batch005.certificate71], c.population=PopulationCertificates.Batch000.certificate19
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers29 {x : ℝ} (hx : certificate29.interval.Contains x) : ∃ c∈certificate29.cells, c.region.interval.Contains x := rat_cut_group_covers certificate29 numericValid29 hx

def certificate30 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate20,PopulationCertificates.Batch001.certificate20,[MergedCutCells.Batch006.certificate72,MergedCutCells.Batch006.certificate73],(37352286987861673/62500000000000000),(some (1250037047/1000000000)),(1/2),(123380662487189109/500000000000000000),(some (103009623578620239/1000000000000000000)),(some (10643909018980193/500000000000000000))⟩
theorem numericValid30 : certificate30.NumericValid := by decide +kernel
theorem cellsSound30 : ∀ c∈certificate30.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch006.certificate72,MergedCutCells.Batch006.certificate73], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound72,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound73,List.forall_mem_nil _⟩⟩
theorem cellsNumeric30 : ∀ c∈certificate30.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate72,MergedCutCells.Batch006.certificate73], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid72,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid73,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid30 : ∀ c∈certificate30.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate72,MergedCutCells.Batch006.certificate73], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid11,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid11,List.forall_mem_nil _⟩⟩
theorem populationMatches30 : ∀ c∈certificate30.cells, c.population=certificate30.population := by
  change ∀ c∈[MergedCutCells.Batch006.certificate72,MergedCutCells.Batch006.certificate73], c.population=PopulationCertificates.Batch001.certificate20
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers30 {x : ℝ} (hx : certificate30.interval.Contains x) : ∃ c∈certificate30.cells, c.region.interval.Contains x := rat_cut_group_covers certificate30 numericValid30 hx

def certificate31 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate20,PopulationCertificates.Batch001.certificate20,[MergedCutCells.Batch006.certificate74,MergedCutCells.Batch006.certificate75,MergedCutCells.Batch006.certificate76,MergedCutCells.Batch006.certificate77],(1250037047/1000000000),none,(1/2),(120113232844447089/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid31 : certificate31.NumericValid := by decide +kernel
theorem cellsSound31 : ∀ c∈certificate31.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch006.certificate74,MergedCutCells.Batch006.certificate75,MergedCutCells.Batch006.certificate76,MergedCutCells.Batch006.certificate77], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound74,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound75,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound76,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound77,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric31 : ∀ c∈certificate31.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate74,MergedCutCells.Batch006.certificate75,MergedCutCells.Batch006.certificate76,MergedCutCells.Batch006.certificate77], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid74,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid75,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid76,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid77,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid31 : ∀ c∈certificate31.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate74,MergedCutCells.Batch006.certificate75,MergedCutCells.Batch006.certificate76,MergedCutCells.Batch006.certificate77], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches31 : ∀ c∈certificate31.cells, c.population=certificate31.population := by
  change ∀ c∈[MergedCutCells.Batch006.certificate74,MergedCutCells.Batch006.certificate75,MergedCutCells.Batch006.certificate76,MergedCutCells.Batch006.certificate77], c.population=PopulationCertificates.Batch001.certificate20
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers31 {x : ℝ} (hx : certificate31.interval.Contains x) : ∃ c∈certificate31.cells, c.region.interval.Contains x := rat_cut_group_covers certificate31 numericValid31 hx

def certificate32 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate21,PopulationCertificates.Batch001.certificate21,[MergedCutCells.Batch006.certificate78,MergedCutCells.Batch006.certificate79],(3412480648357843759/1000000000000000000),none,(1/2),(305765893244277953/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid32 : certificate32.NumericValid := by decide +kernel
theorem cellsSound32 : ∀ c∈certificate32.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch006.certificate78,MergedCutCells.Batch006.certificate79], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound78,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound79,List.forall_mem_nil _⟩⟩
theorem cellsNumeric32 : ∀ c∈certificate32.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate78,MergedCutCells.Batch006.certificate79], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid78,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid79,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid32 : ∀ c∈certificate32.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate78,MergedCutCells.Batch006.certificate79], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches32 : ∀ c∈certificate32.cells, c.population=certificate32.population := by
  change ∀ c∈[MergedCutCells.Batch006.certificate78,MergedCutCells.Batch006.certificate79], c.population=PopulationCertificates.Batch001.certificate21
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers32 {x : ℝ} (hx : certificate32.interval.Contains x) : ∃ c∈certificate32.cells, c.region.interval.Contains x := rat_cut_group_covers certificate32 numericValid32 hx

def certificate33 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate22,PopulationCertificates.Batch001.certificate22,[MergedCutCells.Batch006.certificate80,MergedCutCells.Batch006.certificate81],(150817343412717011/250000000000000000),(some (1234036961/1000000000)),(1/2),(9756764415004299/40000000000000000),(some (2910212793361803/25000000000000000)),(some (24864078235498561/1000000000000000000))⟩
theorem numericValid33 : certificate33.NumericValid := by decide +kernel
theorem cellsSound33 : ∀ c∈certificate33.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch006.certificate80,MergedCutCells.Batch006.certificate81], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound80,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound81,List.forall_mem_nil _⟩⟩
theorem cellsNumeric33 : ∀ c∈certificate33.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate80,MergedCutCells.Batch006.certificate81], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid80,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid81,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid33 : ∀ c∈certificate33.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate80,MergedCutCells.Batch006.certificate81], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid12,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid12,List.forall_mem_nil _⟩⟩
theorem populationMatches33 : ∀ c∈certificate33.cells, c.population=certificate33.population := by
  change ∀ c∈[MergedCutCells.Batch006.certificate80,MergedCutCells.Batch006.certificate81], c.population=PopulationCertificates.Batch001.certificate22
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers33 {x : ℝ} (hx : certificate33.interval.Contains x) : ∃ c∈certificate33.cells, c.region.interval.Contains x := rat_cut_group_covers certificate33 numericValid33 hx

def certificate34 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate22,PopulationCertificates.Batch001.certificate22,[MergedCutCells.Batch006.certificate82,MergedCutCells.Batch006.certificate83,MergedCutCells.Batch007.certificate84,MergedCutCells.Batch007.certificate85],(1234036961/1000000000),none,(1/2),(11821744466726197/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid34 : certificate34.NumericValid := by decide +kernel
theorem cellsSound34 : ∀ c∈certificate34.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch006.certificate82,MergedCutCells.Batch006.certificate83,MergedCutCells.Batch007.certificate84,MergedCutCells.Batch007.certificate85], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound82,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.sound83,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound84,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound85,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric34 : ∀ c∈certificate34.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate82,MergedCutCells.Batch006.certificate83,MergedCutCells.Batch007.certificate84,MergedCutCells.Batch007.certificate85], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid82,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch006.numericValid83,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid84,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid85,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid34 : ∀ c∈certificate34.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch006.certificate82,MergedCutCells.Batch006.certificate83,MergedCutCells.Batch007.certificate84,MergedCutCells.Batch007.certificate85], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches34 : ∀ c∈certificate34.cells, c.population=certificate34.population := by
  change ∀ c∈[MergedCutCells.Batch006.certificate82,MergedCutCells.Batch006.certificate83,MergedCutCells.Batch007.certificate84,MergedCutCells.Batch007.certificate85], c.population=PopulationCertificates.Batch001.certificate22
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers34 {x : ℝ} (hx : certificate34.interval.Contains x) : ∃ c∈certificate34.cells, c.region.interval.Contains x := rat_cut_group_covers certificate34 numericValid34 hx

def certificate35 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate23,PopulationCertificates.Batch001.certificate23,[MergedCutCells.Batch007.certificate86,MergedCutCells.Batch007.certificate87],(3337885108138372131/1000000000000000000),none,(1/2),(20876708912224671/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid35 : certificate35.NumericValid := by decide +kernel
theorem cellsSound35 : ∀ c∈certificate35.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch007.certificate86,MergedCutCells.Batch007.certificate87], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound86,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.sound87,List.forall_mem_nil _⟩⟩
theorem cellsNumeric35 : ∀ c∈certificate35.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch007.certificate86,MergedCutCells.Batch007.certificate87], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid86,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch007.numericValid87,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid35 : ∀ c∈certificate35.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch007.certificate86,MergedCutCells.Batch007.certificate87], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches35 : ∀ c∈certificate35.cells, c.population=certificate35.population := by
  change ∀ c∈[MergedCutCells.Batch007.certificate86,MergedCutCells.Batch007.certificate87], c.population=PopulationCertificates.Batch001.certificate23
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers35 {x : ℝ} (hx : certificate35.interval.Contains x) : ∃ c∈certificate35.cells, c.region.interval.Contains x := rat_cut_group_covers certificate35 numericValid35 hx

end Cycle12.MergedCutGroups.Batch002
