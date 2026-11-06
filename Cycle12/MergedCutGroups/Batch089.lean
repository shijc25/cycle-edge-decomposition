import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch035
import Cycle12.MergedCutCells.Batch320
import Cycle12.MergedCutCells.Batch321
import Cycle12.MergedCutCells.Batch322
import Cycle12.PopulationCertificates.Batch035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch089

def certificate1068 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate712,PopulationCertificates.Batch035.certificate712,[MergedCutCells.Batch320.certificate3848,MergedCutCells.Batch320.certificate3849],(558511688771171349/1000000000000000000),(some (76617041/62500000)),(1/2),(12901833713826277/100000000000000000),(some (1710254213202961/62500000000000000)),(some (4234346635925299/1000000000000000000))⟩
theorem numericValid1068 : certificate1068.NumericValid := by decide +kernel
theorem cellsSound1068 : ∀ c∈certificate1068.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3848,MergedCutCells.Batch320.certificate3849], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3848,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3849,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1068 : ∀ c∈certificate1068.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3848,MergedCutCells.Batch320.certificate3849], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3848,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3849,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1068 : ∀ c∈certificate1068.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3848,MergedCutCells.Batch320.certificate3849], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid357,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid357,List.forall_mem_nil _⟩⟩
theorem populationMatches1068 : ∀ c∈certificate1068.cells, c.population=certificate1068.population := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3848,MergedCutCells.Batch320.certificate3849], c.population=PopulationCertificates.Batch035.certificate712
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1068 {x : ℝ} (hx : certificate1068.interval.Contains x) : ∃ c∈certificate1068.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1068 numericValid1068 hx

def certificate1069 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate712,PopulationCertificates.Batch035.certificate712,[MergedCutCells.Batch320.certificate3850,MergedCutCells.Batch320.certificate3851,MergedCutCells.Batch321.certificate3852],(76617041/62500000),none,(1/2),(63762140051453667/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1069 : certificate1069.NumericValid := by decide +kernel
theorem cellsSound1069 : ∀ c∈certificate1069.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3850,MergedCutCells.Batch320.certificate3851,MergedCutCells.Batch321.certificate3852], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3850,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.sound3851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3852,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1069 : ∀ c∈certificate1069.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3850,MergedCutCells.Batch320.certificate3851,MergedCutCells.Batch321.certificate3852], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3850,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch320.numericValid3851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3852,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1069 : ∀ c∈certificate1069.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3850,MergedCutCells.Batch320.certificate3851,MergedCutCells.Batch321.certificate3852], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1069 : ∀ c∈certificate1069.cells, c.population=certificate1069.population := by
  change ∀ c∈[MergedCutCells.Batch320.certificate3850,MergedCutCells.Batch320.certificate3851,MergedCutCells.Batch321.certificate3852], c.population=PopulationCertificates.Batch035.certificate712
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1069 {x : ℝ} (hx : certificate1069.interval.Contains x) : ∃ c∈certificate1069.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1069 numericValid1069 hx

def certificate1070 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate713,PopulationCertificates.Batch035.certificate713,[MergedCutCells.Batch321.certificate3853,MergedCutCells.Batch321.certificate3854],(4881906208393732827/250000000000000000),none,(1/2),(258968186704745449/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1070 : certificate1070.NumericValid := by decide +kernel
theorem cellsSound1070 : ∀ c∈certificate1070.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3853,MergedCutCells.Batch321.certificate3854], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3853,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3854,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1070 : ∀ c∈certificate1070.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3853,MergedCutCells.Batch321.certificate3854], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3853,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3854,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1070 : ∀ c∈certificate1070.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3853,MergedCutCells.Batch321.certificate3854], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1070 : ∀ c∈certificate1070.cells, c.population=certificate1070.population := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3853,MergedCutCells.Batch321.certificate3854], c.population=PopulationCertificates.Batch035.certificate713
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1070 {x : ℝ} (hx : certificate1070.interval.Contains x) : ∃ c∈certificate1070.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1070 numericValid1070 hx

def certificate1071 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate714,PopulationCertificates.Batch035.certificate714,[MergedCutCells.Batch321.certificate3855,MergedCutCells.Batch321.certificate3856],(558701075044607803/1000000000000000000),(some (1226219407/1000000000)),(1/2),(5042948011761253/40000000000000000),(some (5684420602424461/200000000000000000)),(some (177157040043639/40000000000000000))⟩
theorem numericValid1071 : certificate1071.NumericValid := by decide +kernel
theorem cellsSound1071 : ∀ c∈certificate1071.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3855,MergedCutCells.Batch321.certificate3856], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3855,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3856,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1071 : ∀ c∈certificate1071.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3855,MergedCutCells.Batch321.certificate3856], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3855,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3856,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1071 : ∀ c∈certificate1071.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3855,MergedCutCells.Batch321.certificate3856], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid358,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid358,List.forall_mem_nil _⟩⟩
theorem populationMatches1071 : ∀ c∈certificate1071.cells, c.population=certificate1071.population := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3855,MergedCutCells.Batch321.certificate3856], c.population=PopulationCertificates.Batch035.certificate714
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1071 {x : ℝ} (hx : certificate1071.interval.Contains x) : ∃ c∈certificate1071.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1071 numericValid1071 hx

def certificate1072 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate714,PopulationCertificates.Batch035.certificate714,[MergedCutCells.Batch321.certificate3857,MergedCutCells.Batch321.certificate3858,MergedCutCells.Batch321.certificate3859],(1226219407/1000000000),none,(1/2),(124574024578115081/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1072 : certificate1072.NumericValid := by decide +kernel
theorem cellsSound1072 : ∀ c∈certificate1072.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3857,MergedCutCells.Batch321.certificate3858,MergedCutCells.Batch321.certificate3859], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3857,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3859,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1072 : ∀ c∈certificate1072.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3857,MergedCutCells.Batch321.certificate3858,MergedCutCells.Batch321.certificate3859], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3857,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3859,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1072 : ∀ c∈certificate1072.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3857,MergedCutCells.Batch321.certificate3858,MergedCutCells.Batch321.certificate3859], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1072 : ∀ c∈certificate1072.cells, c.population=certificate1072.population := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3857,MergedCutCells.Batch321.certificate3858,MergedCutCells.Batch321.certificate3859], c.population=PopulationCertificates.Batch035.certificate714
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1072 {x : ℝ} (hx : certificate1072.interval.Contains x) : ∃ c∈certificate1072.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1072 numericValid1072 hx

def certificate1073 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate715,PopulationCertificates.Batch035.certificate715,[MergedCutCells.Batch321.certificate3860,MergedCutCells.Batch321.certificate3861],(19714588126546406257/1000000000000000000),none,(1/2),(2615250550086023057/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1073 : certificate1073.NumericValid := by decide +kernel
theorem cellsSound1073 : ∀ c∈certificate1073.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3860,MergedCutCells.Batch321.certificate3861], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3860,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3861,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1073 : ∀ c∈certificate1073.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3860,MergedCutCells.Batch321.certificate3861], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3860,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3861,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1073 : ∀ c∈certificate1073.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3860,MergedCutCells.Batch321.certificate3861], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1073 : ∀ c∈certificate1073.cells, c.population=certificate1073.population := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3860,MergedCutCells.Batch321.certificate3861], c.population=PopulationCertificates.Batch035.certificate715
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1073 {x : ℝ} (hx : certificate1073.interval.Contains x) : ∃ c∈certificate1073.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1073 numericValid1073 hx

def certificate1074 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate716,PopulationCertificates.Batch035.certificate716,[MergedCutCells.Batch321.certificate3862,MergedCutCells.Batch321.certificate3863],(2183288751052101/3906250000000000),(some (615827793/500000000)),(1/2),(61626794454512651/500000000000000000),(some (29529314832816383/1000000000000000000)),(some (1158565214802241/250000000000000000))⟩
theorem numericValid1074 : certificate1074.NumericValid := by decide +kernel
theorem cellsSound1074 : ∀ c∈certificate1074.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3862,MergedCutCells.Batch321.certificate3863], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3862,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.sound3863,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1074 : ∀ c∈certificate1074.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3862,MergedCutCells.Batch321.certificate3863], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3862,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch321.numericValid3863,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1074 : ∀ c∈certificate1074.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3862,MergedCutCells.Batch321.certificate3863], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid359,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy017.valid359,List.forall_mem_nil _⟩⟩
theorem populationMatches1074 : ∀ c∈certificate1074.cells, c.population=certificate1074.population := by
  change ∀ c∈[MergedCutCells.Batch321.certificate3862,MergedCutCells.Batch321.certificate3863], c.population=PopulationCertificates.Batch035.certificate716
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1074 {x : ℝ} (hx : certificate1074.interval.Contains x) : ∃ c∈certificate1074.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1074 numericValid1074 hx

def certificate1075 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate716,PopulationCertificates.Batch035.certificate716,[MergedCutCells.Batch322.certificate3864,MergedCutCells.Batch322.certificate3865,MergedCutCells.Batch322.certificate3866],(615827793/500000000),none,(1/2),(60807901733543781/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1075 : certificate1075.NumericValid := by decide +kernel
theorem cellsSound1075 : ∀ c∈certificate1075.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3864,MergedCutCells.Batch322.certificate3865,MergedCutCells.Batch322.certificate3866], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3864,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3866,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1075 : ∀ c∈certificate1075.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3864,MergedCutCells.Batch322.certificate3865,MergedCutCells.Batch322.certificate3866], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3864,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3866,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1075 : ∀ c∈certificate1075.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3864,MergedCutCells.Batch322.certificate3865,MergedCutCells.Batch322.certificate3866], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1075 : ∀ c∈certificate1075.cells, c.population=certificate1075.population := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3864,MergedCutCells.Batch322.certificate3865,MergedCutCells.Batch322.certificate3866], c.population=PopulationCertificates.Batch035.certificate716
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1075 {x : ℝ} (hx : certificate1075.interval.Contains x) : ∃ c∈certificate1075.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1075 numericValid1075 hx

def certificate1076 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate717,PopulationCertificates.Batch035.certificate717,[MergedCutCells.Batch322.certificate3867,MergedCutCells.Batch322.certificate3868],(1235578016881867639/62500000000000000),none,(1/2),(65894575514333607/12500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1076 : certificate1076.NumericValid := by decide +kernel
theorem cellsSound1076 : ∀ c∈certificate1076.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3867,MergedCutCells.Batch322.certificate3868], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3867,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3868,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1076 : ∀ c∈certificate1076.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3867,MergedCutCells.Batch322.certificate3868], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3867,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3868,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1076 : ∀ c∈certificate1076.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3867,MergedCutCells.Batch322.certificate3868], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1076 : ∀ c∈certificate1076.cells, c.population=certificate1076.population := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3867,MergedCutCells.Batch322.certificate3868], c.population=PopulationCertificates.Batch035.certificate717
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1076 {x : ℝ} (hx : certificate1076.interval.Contains x) : ∃ c∈certificate1076.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1076 numericValid1076 hx

def certificate1077 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate718,PopulationCertificates.Batch035.certificate718,[MergedCutCells.Batch322.certificate3869,MergedCutCells.Batch322.certificate3870],(556580555573380941/1000000000000000000),(some (76395987/62500000)),(1/2),(53835268284095121/500000000000000000),(some (6340089324701361/200000000000000000)),(some (5041855942407029/1000000000000000000))⟩
theorem numericValid1077 : certificate1077.NumericValid := by decide +kernel
theorem cellsSound1077 : ∀ c∈certificate1077.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3869,MergedCutCells.Batch322.certificate3870], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3869,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3870,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1077 : ∀ c∈certificate1077.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3869,MergedCutCells.Batch322.certificate3870], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3869,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3870,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1077 : ∀ c∈certificate1077.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3869,MergedCutCells.Batch322.certificate3870], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid360,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy018.valid360,List.forall_mem_nil _⟩⟩
theorem populationMatches1077 : ∀ c∈certificate1077.cells, c.population=certificate1077.population := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3869,MergedCutCells.Batch322.certificate3870], c.population=PopulationCertificates.Batch035.certificate718
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1077 {x : ℝ} (hx : certificate1077.interval.Contains x) : ∃ c∈certificate1077.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1077 numericValid1077 hx

def certificate1078 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate718,PopulationCertificates.Batch035.certificate718,[MergedCutCells.Batch322.certificate3871,MergedCutCells.Batch322.certificate3872,MergedCutCells.Batch322.certificate3873],(76395987/62500000),none,(1/2),(13235952426763847/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1078 : certificate1078.NumericValid := by decide +kernel
theorem cellsSound1078 : ∀ c∈certificate1078.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3871,MergedCutCells.Batch322.certificate3872,MergedCutCells.Batch322.certificate3873], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3871,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3872,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3873,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1078 : ∀ c∈certificate1078.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3871,MergedCutCells.Batch322.certificate3872,MergedCutCells.Batch322.certificate3873], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3871,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3872,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3873,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1078 : ∀ c∈certificate1078.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3871,MergedCutCells.Batch322.certificate3872,MergedCutCells.Batch322.certificate3873], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1078 : ∀ c∈certificate1078.cells, c.population=certificate1078.population := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3871,MergedCutCells.Batch322.certificate3872,MergedCutCells.Batch322.certificate3873], c.population=PopulationCertificates.Batch035.certificate718
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1078 {x : ℝ} (hx : certificate1078.interval.Contains x) : ∃ c∈certificate1078.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1078 numericValid1078 hx

def certificate1079 : RatCutGroup := ⟨GeometryCertificates.Batch035.certificate719,PopulationCertificates.Batch035.certificate719,[MergedCutCells.Batch322.certificate3874,MergedCutCells.Batch322.certificate3875],(20022682314540942933/1000000000000000000),none,(1/2),(5321221803819908423/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1079 : certificate1079.NumericValid := by decide +kernel
theorem cellsSound1079 : ∀ c∈certificate1079.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3874,MergedCutCells.Batch322.certificate3875], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3874,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.sound3875,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1079 : ∀ c∈certificate1079.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3874,MergedCutCells.Batch322.certificate3875], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3874,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch322.numericValid3875,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1079 : ∀ c∈certificate1079.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3874,MergedCutCells.Batch322.certificate3875], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1079 : ∀ c∈certificate1079.cells, c.population=certificate1079.population := by
  change ∀ c∈[MergedCutCells.Batch322.certificate3874,MergedCutCells.Batch322.certificate3875], c.population=PopulationCertificates.Batch035.certificate719
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1079 {x : ℝ} (hx : certificate1079.interval.Contains x) : ∃ c∈certificate1079.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1079 numericValid1079 hx

end Cycle12.MergedCutGroups.Batch089
