import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch009
import Cycle12.MergedCutCells.Batch093
import Cycle12.MergedCutCells.Batch094
import Cycle12.MergedCutCells.Batch095
import Cycle12.MergedCutCells.Batch096
import Cycle12.MergedCutCells.Batch097
import Cycle12.PopulationCertificates.Batch009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch024

def certificate288 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate192,PopulationCertificates.Batch009.certificate192,[MergedCutCells.Batch093.certificate1120,MergedCutCells.Batch093.certificate1121,MergedCutCells.Batch093.certificate1122,MergedCutCells.Batch093.certificate1123,MergedCutCells.Batch093.certificate1124,MergedCutCells.Batch093.certificate1125,MergedCutCells.Batch093.certificate1126],(846475032567901681/1000000000000000000),(some 64),(1/2),(247534830806370953/500000000000000000),(some (69314718055994531/100000000000000000)),(some (1437818100908301841/1000000000000000000))⟩
theorem numericValid288 : certificate288.NumericValid := by decide +kernel
theorem cellsSound288 : ∀ c∈certificate288.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1120,MergedCutCells.Batch093.certificate1121,MergedCutCells.Batch093.certificate1122,MergedCutCells.Batch093.certificate1123,MergedCutCells.Batch093.certificate1124,MergedCutCells.Batch093.certificate1125,MergedCutCells.Batch093.certificate1126], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1120,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1124,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1126,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric288 : ∀ c∈certificate288.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1120,MergedCutCells.Batch093.certificate1121,MergedCutCells.Batch093.certificate1122,MergedCutCells.Batch093.certificate1123,MergedCutCells.Batch093.certificate1124,MergedCutCells.Batch093.certificate1125,MergedCutCells.Batch093.certificate1126], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1120,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1124,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1126,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid288 : ∀ c∈certificate288.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1120,MergedCutCells.Batch093.certificate1121,MergedCutCells.Batch093.certificate1122,MergedCutCells.Batch093.certificate1123,MergedCutCells.Batch093.certificate1124,MergedCutCells.Batch093.certificate1125,MergedCutCells.Batch093.certificate1126], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid97,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid97,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid97,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid97,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid97,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid97,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid97,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches288 : ∀ c∈certificate288.cells, c.population=certificate288.population := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1120,MergedCutCells.Batch093.certificate1121,MergedCutCells.Batch093.certificate1122,MergedCutCells.Batch093.certificate1123,MergedCutCells.Batch093.certificate1124,MergedCutCells.Batch093.certificate1125,MergedCutCells.Batch093.certificate1126], c.population=PopulationCertificates.Batch009.certificate192
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers288 {x : ℝ} (hx : certificate288.interval.Contains x) : ∃ c∈certificate288.cells, c.region.interval.Contains x := rat_cut_group_covers certificate288 numericValid288 hx

def certificate289 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate192,PopulationCertificates.Batch009.certificate192,[MergedCutCells.Batch093.certificate1127],64,none,(1/2),(236472748481864299/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid289 : certificate289.NumericValid := by decide +kernel
theorem cellsSound289 : ∀ c∈certificate289.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1127], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1127,List.forall_mem_nil _⟩
theorem cellsNumeric289 : ∀ c∈certificate289.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1127], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1127,List.forall_mem_nil _⟩
theorem cellsEntropyValid289 : ∀ c∈certificate289.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1127], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches289 : ∀ c∈certificate289.cells, c.population=certificate289.population := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1127], c.population=PopulationCertificates.Batch009.certificate192
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers289 {x : ℝ} (hx : certificate289.interval.Contains x) : ∃ c∈certificate289.cells, c.region.interval.Contains x := rat_cut_group_covers certificate289 numericValid289 hx

def certificate290 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate193,PopulationCertificates.Batch009.certificate193,[MergedCutCells.Batch094.certificate1128,MergedCutCells.Batch094.certificate1129,MergedCutCells.Batch094.certificate1130,MergedCutCells.Batch094.certificate1131],(3657321140320232363/1000000000000000000),none,(1/2),(1868372534009443/2500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid290 : certificate290.NumericValid := by decide +kernel
theorem cellsSound290 : ∀ c∈certificate290.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1128,MergedCutCells.Batch094.certificate1129,MergedCutCells.Batch094.certificate1130,MergedCutCells.Batch094.certificate1131], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1128,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1130,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1131,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric290 : ∀ c∈certificate290.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1128,MergedCutCells.Batch094.certificate1129,MergedCutCells.Batch094.certificate1130,MergedCutCells.Batch094.certificate1131], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1128,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1130,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1131,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid290 : ∀ c∈certificate290.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1128,MergedCutCells.Batch094.certificate1129,MergedCutCells.Batch094.certificate1130,MergedCutCells.Batch094.certificate1131], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches290 : ∀ c∈certificate290.cells, c.population=certificate290.population := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1128,MergedCutCells.Batch094.certificate1129,MergedCutCells.Batch094.certificate1130,MergedCutCells.Batch094.certificate1131], c.population=PopulationCertificates.Batch009.certificate193
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers290 {x : ℝ} (hx : certificate290.interval.Contains x) : ∃ c∈certificate290.cells, c.region.interval.Contains x := rat_cut_group_covers certificate290 numericValid290 hx

def certificate291 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate194,PopulationCertificates.Batch009.certificate194,[MergedCutCells.Batch094.certificate1132,MergedCutCells.Batch094.certificate1133,MergedCutCells.Batch094.certificate1134,MergedCutCells.Batch094.certificate1135,MergedCutCells.Batch094.certificate1136,MergedCutCells.Batch094.certificate1137,MergedCutCells.Batch094.certificate1138],(843261777840520253/1000000000000000000),(some 64),(1/2),(499870509683106573/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (720926879900507971/500000000000000000))⟩
theorem numericValid291 : certificate291.NumericValid := by decide +kernel
theorem cellsSound291 : ∀ c∈certificate291.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1132,MergedCutCells.Batch094.certificate1133,MergedCutCells.Batch094.certificate1134,MergedCutCells.Batch094.certificate1135,MergedCutCells.Batch094.certificate1136,MergedCutCells.Batch094.certificate1137,MergedCutCells.Batch094.certificate1138], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1132,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1134,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1137,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1138,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric291 : ∀ c∈certificate291.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1132,MergedCutCells.Batch094.certificate1133,MergedCutCells.Batch094.certificate1134,MergedCutCells.Batch094.certificate1135,MergedCutCells.Batch094.certificate1136,MergedCutCells.Batch094.certificate1137,MergedCutCells.Batch094.certificate1138], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1132,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1134,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1137,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1138,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid291 : ∀ c∈certificate291.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1132,MergedCutCells.Batch094.certificate1133,MergedCutCells.Batch094.certificate1134,MergedCutCells.Batch094.certificate1135,MergedCutCells.Batch094.certificate1136,MergedCutCells.Batch094.certificate1137,MergedCutCells.Batch094.certificate1138], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid98,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid98,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid98,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid98,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid98,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid98,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid98,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches291 : ∀ c∈certificate291.cells, c.population=certificate291.population := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1132,MergedCutCells.Batch094.certificate1133,MergedCutCells.Batch094.certificate1134,MergedCutCells.Batch094.certificate1135,MergedCutCells.Batch094.certificate1136,MergedCutCells.Batch094.certificate1137,MergedCutCells.Batch094.certificate1138], c.population=PopulationCertificates.Batch009.certificate194
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers291 {x : ℝ} (hx : certificate291.interval.Contains x) : ∃ c∈certificate291.cells, c.region.interval.Contains x := rat_cut_group_covers certificate291 numericValid291 hx

def certificate292 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate194,PopulationCertificates.Batch009.certificate194,[MergedCutCells.Batch094.certificate1139],64,none,(1/2),(1200748447870009609/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid292 : certificate292.NumericValid := by decide +kernel
theorem cellsSound292 : ∀ c∈certificate292.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1139], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.sound1139,List.forall_mem_nil _⟩
theorem cellsNumeric292 : ∀ c∈certificate292.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1139], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch094.numericValid1139,List.forall_mem_nil _⟩
theorem cellsEntropyValid292 : ∀ c∈certificate292.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1139], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches292 : ∀ c∈certificate292.cells, c.population=certificate292.population := by
  change ∀ c∈[MergedCutCells.Batch094.certificate1139], c.population=PopulationCertificates.Batch009.certificate194
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers292 {x : ℝ} (hx : certificate292.interval.Contains x) : ∃ c∈certificate292.cells, c.region.interval.Contains x := rat_cut_group_covers certificate292 numericValid292 hx

def certificate293 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate195,PopulationCertificates.Batch009.certificate195,[MergedCutCells.Batch095.certificate1140,MergedCutCells.Batch095.certificate1141,MergedCutCells.Batch095.certificate1142,MergedCutCells.Batch095.certificate1143],(3662671160803666109/1000000000000000000),none,(1/2),(764584465221632679/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid293 : certificate293.NumericValid := by decide +kernel
theorem cellsSound293 : ∀ c∈certificate293.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1140,MergedCutCells.Batch095.certificate1141,MergedCutCells.Batch095.certificate1142,MergedCutCells.Batch095.certificate1143], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1141,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1143,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric293 : ∀ c∈certificate293.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1140,MergedCutCells.Batch095.certificate1141,MergedCutCells.Batch095.certificate1142,MergedCutCells.Batch095.certificate1143], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1141,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1143,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid293 : ∀ c∈certificate293.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1140,MergedCutCells.Batch095.certificate1141,MergedCutCells.Batch095.certificate1142,MergedCutCells.Batch095.certificate1143], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches293 : ∀ c∈certificate293.cells, c.population=certificate293.population := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1140,MergedCutCells.Batch095.certificate1141,MergedCutCells.Batch095.certificate1142,MergedCutCells.Batch095.certificate1143], c.population=PopulationCertificates.Batch009.certificate195
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers293 {x : ℝ} (hx : certificate293.interval.Contains x) : ∃ c∈certificate293.cells, c.region.interval.Contains x := rat_cut_group_covers certificate293 numericValid293 hx

def certificate294 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate196,PopulationCertificates.Batch009.certificate196,[MergedCutCells.Batch095.certificate1144,MergedCutCells.Batch095.certificate1145,MergedCutCells.Batch095.certificate1146,MergedCutCells.Batch095.certificate1147,MergedCutCells.Batch095.certificate1148,MergedCutCells.Batch095.certificate1149,MergedCutCells.Batch095.certificate1150],(425082801362805553/500000000000000000),(some 64),(1/2),(510141190771897473/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (180248969330899917/125000000000000000))⟩
theorem numericValid294 : certificate294.NumericValid := by decide +kernel
theorem cellsSound294 : ∀ c∈certificate294.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1144,MergedCutCells.Batch095.certificate1145,MergedCutCells.Batch095.certificate1146,MergedCutCells.Batch095.certificate1147,MergedCutCells.Batch095.certificate1148,MergedCutCells.Batch095.certificate1149,MergedCutCells.Batch095.certificate1150], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1145,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1147,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1150,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric294 : ∀ c∈certificate294.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1144,MergedCutCells.Batch095.certificate1145,MergedCutCells.Batch095.certificate1146,MergedCutCells.Batch095.certificate1147,MergedCutCells.Batch095.certificate1148,MergedCutCells.Batch095.certificate1149,MergedCutCells.Batch095.certificate1150], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1145,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1147,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1150,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid294 : ∀ c∈certificate294.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1144,MergedCutCells.Batch095.certificate1145,MergedCutCells.Batch095.certificate1146,MergedCutCells.Batch095.certificate1147,MergedCutCells.Batch095.certificate1148,MergedCutCells.Batch095.certificate1149,MergedCutCells.Batch095.certificate1150], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid99,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid99,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid99,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid99,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid99,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid99,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid99,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches294 : ∀ c∈certificate294.cells, c.population=certificate294.population := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1144,MergedCutCells.Batch095.certificate1145,MergedCutCells.Batch095.certificate1146,MergedCutCells.Batch095.certificate1147,MergedCutCells.Batch095.certificate1148,MergedCutCells.Batch095.certificate1149,MergedCutCells.Batch095.certificate1150], c.population=PopulationCertificates.Batch009.certificate196
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers294 {x : ℝ} (hx : certificate294.interval.Contains x) : ∃ c∈certificate294.cells, c.region.interval.Contains x := rat_cut_group_covers certificate294 numericValid294 hx

def certificate295 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate196,PopulationCertificates.Batch009.certificate196,[MergedCutCells.Batch095.certificate1151],64,none,(1/2),(1222201165659566617/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid295 : certificate295.NumericValid := by decide +kernel
theorem cellsSound295 : ∀ c∈certificate295.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1151], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.sound1151,List.forall_mem_nil _⟩
theorem cellsNumeric295 : ∀ c∈certificate295.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1151], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch095.numericValid1151,List.forall_mem_nil _⟩
theorem cellsEntropyValid295 : ∀ c∈certificate295.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1151], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches295 : ∀ c∈certificate295.cells, c.population=certificate295.population := by
  change ∀ c∈[MergedCutCells.Batch095.certificate1151], c.population=PopulationCertificates.Batch009.certificate196
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers295 {x : ℝ} (hx : certificate295.interval.Contains x) : ∃ c∈certificate295.cells, c.region.interval.Contains x := rat_cut_group_covers certificate295 numericValid295 hx

def certificate296 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate197,PopulationCertificates.Batch009.certificate197,[MergedCutCells.Batch096.certificate1152,MergedCutCells.Batch096.certificate1153,MergedCutCells.Batch096.certificate1154],(1834026943300852141/500000000000000000),none,(1/2),(389855376182275107/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid296 : certificate296.NumericValid := by decide +kernel
theorem cellsSound296 : ∀ c∈certificate296.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1152,MergedCutCells.Batch096.certificate1153,MergedCutCells.Batch096.certificate1154], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1153,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1154,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric296 : ∀ c∈certificate296.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1152,MergedCutCells.Batch096.certificate1153,MergedCutCells.Batch096.certificate1154], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1153,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1154,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid296 : ∀ c∈certificate296.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1152,MergedCutCells.Batch096.certificate1153,MergedCutCells.Batch096.certificate1154], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches296 : ∀ c∈certificate296.cells, c.population=certificate296.population := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1152,MergedCutCells.Batch096.certificate1153,MergedCutCells.Batch096.certificate1154], c.population=PopulationCertificates.Batch009.certificate197
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers296 {x : ℝ} (hx : certificate296.interval.Contains x) : ∃ c∈certificate296.cells, c.region.interval.Contains x := rat_cut_group_covers certificate296 numericValid296 hx

def certificate297 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate198,PopulationCertificates.Batch009.certificate198,[MergedCutCells.Batch096.certificate1155,MergedCutCells.Batch096.certificate1156,MergedCutCells.Batch096.certificate1157,MergedCutCells.Batch096.certificate1158,MergedCutCells.Batch096.certificate1159,MergedCutCells.Batch096.certificate1160,MergedCutCells.Batch096.certificate1161,MergedCutCells.Batch096.certificate1162],(103892560620886961/125000000000000000),(some 64),(1/2),(209544510640782873/500000000000000000),(some (69314718055994531/100000000000000000)),(some (90681524223415999/62500000000000000))⟩
theorem numericValid297 : certificate297.NumericValid := by decide +kernel
theorem cellsSound297 : ∀ c∈certificate297.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1155,MergedCutCells.Batch096.certificate1156,MergedCutCells.Batch096.certificate1157,MergedCutCells.Batch096.certificate1158,MergedCutCells.Batch096.certificate1159,MergedCutCells.Batch096.certificate1160,MergedCutCells.Batch096.certificate1161,MergedCutCells.Batch096.certificate1162], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1157,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1159,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1162,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric297 : ∀ c∈certificate297.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1155,MergedCutCells.Batch096.certificate1156,MergedCutCells.Batch096.certificate1157,MergedCutCells.Batch096.certificate1158,MergedCutCells.Batch096.certificate1159,MergedCutCells.Batch096.certificate1160,MergedCutCells.Batch096.certificate1161,MergedCutCells.Batch096.certificate1162], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1157,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1159,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1162,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid297 : ∀ c∈certificate297.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1155,MergedCutCells.Batch096.certificate1156,MergedCutCells.Batch096.certificate1157,MergedCutCells.Batch096.certificate1158,MergedCutCells.Batch096.certificate1159,MergedCutCells.Batch096.certificate1160,MergedCutCells.Batch096.certificate1161,MergedCutCells.Batch096.certificate1162], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid100,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid100,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid100,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid100,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid100,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid100,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid100,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid100,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches297 : ∀ c∈certificate297.cells, c.population=certificate297.population := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1155,MergedCutCells.Batch096.certificate1156,MergedCutCells.Batch096.certificate1157,MergedCutCells.Batch096.certificate1158,MergedCutCells.Batch096.certificate1159,MergedCutCells.Batch096.certificate1160,MergedCutCells.Batch096.certificate1161,MergedCutCells.Batch096.certificate1162], c.population=PopulationCertificates.Batch009.certificate198
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers297 {x : ℝ} (hx : certificate297.interval.Contains x) : ∃ c∈certificate297.cells, c.region.interval.Contains x := rat_cut_group_covers certificate297 numericValid297 hx

def certificate298 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate198,PopulationCertificates.Batch009.certificate198,[MergedCutCells.Batch096.certificate1163],64,none,(1/2),(1133122572593498507/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid298 : certificate298.NumericValid := by decide +kernel
theorem cellsSound298 : ∀ c∈certificate298.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1163], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.sound1163,List.forall_mem_nil _⟩
theorem cellsNumeric298 : ∀ c∈certificate298.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1163], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch096.numericValid1163,List.forall_mem_nil _⟩
theorem cellsEntropyValid298 : ∀ c∈certificate298.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1163], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches298 : ∀ c∈certificate298.cells, c.population=certificate298.population := by
  change ∀ c∈[MergedCutCells.Batch096.certificate1163], c.population=PopulationCertificates.Batch009.certificate198
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers298 {x : ℝ} (hx : certificate298.interval.Contains x) : ∃ c∈certificate298.cells, c.region.interval.Contains x := rat_cut_group_covers certificate298 numericValid298 hx

def certificate299 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate199,PopulationCertificates.Batch009.certificate199,[MergedCutCells.Batch097.certificate1164,MergedCutCells.Batch097.certificate1165,MergedCutCells.Batch097.certificate1166,MergedCutCells.Batch097.certificate1167],(933673993516170141/250000000000000000),none,(1/2),(384828216805596933/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid299 : certificate299.NumericValid := by decide +kernel
theorem cellsSound299 : ∀ c∈certificate299.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch097.certificate1164,MergedCutCells.Batch097.certificate1165,MergedCutCells.Batch097.certificate1166,MergedCutCells.Batch097.certificate1167], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1164,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1166,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1167,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric299 : ∀ c∈certificate299.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch097.certificate1164,MergedCutCells.Batch097.certificate1165,MergedCutCells.Batch097.certificate1166,MergedCutCells.Batch097.certificate1167], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1164,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1166,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1167,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid299 : ∀ c∈certificate299.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch097.certificate1164,MergedCutCells.Batch097.certificate1165,MergedCutCells.Batch097.certificate1166,MergedCutCells.Batch097.certificate1167], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches299 : ∀ c∈certificate299.cells, c.population=certificate299.population := by
  change ∀ c∈[MergedCutCells.Batch097.certificate1164,MergedCutCells.Batch097.certificate1165,MergedCutCells.Batch097.certificate1166,MergedCutCells.Batch097.certificate1167], c.population=PopulationCertificates.Batch009.certificate199
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers299 {x : ℝ} (hx : certificate299.interval.Contains x) : ∃ c∈certificate299.cells, c.region.interval.Contains x := rat_cut_group_covers certificate299 numericValid299 hx

end Cycle12.MergedCutGroups.Batch024
