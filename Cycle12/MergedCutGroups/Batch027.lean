import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch010
import Cycle12.GeometryCertificates.Batch011
import Cycle12.MergedCutCells.Batch105
import Cycle12.MergedCutCells.Batch106
import Cycle12.MergedCutCells.Batch107
import Cycle12.MergedCutCells.Batch108
import Cycle12.PopulationCertificates.Batch010
import Cycle12.PopulationCertificates.Batch011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch027

def certificate324 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate216,PopulationCertificates.Batch010.certificate216,[MergedCutCells.Batch105.certificate1261,MergedCutCells.Batch105.certificate1262,MergedCutCells.Batch105.certificate1263,MergedCutCells.Batch105.certificate1264,MergedCutCells.Batch105.certificate1265,MergedCutCells.Batch105.certificate1266],(109986137019307837/125000000000000000),(some 64),(1/2),(615566239670433583/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1466671825125291763/1000000000000000000))⟩
theorem numericValid324 : certificate324.NumericValid := by decide +kernel
theorem cellsSound324 : ∀ c∈certificate324.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1261,MergedCutCells.Batch105.certificate1262,MergedCutCells.Batch105.certificate1263,MergedCutCells.Batch105.certificate1264,MergedCutCells.Batch105.certificate1265,MergedCutCells.Batch105.certificate1266], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1262,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1263,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1264,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1265,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1266,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric324 : ∀ c∈certificate324.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1261,MergedCutCells.Batch105.certificate1262,MergedCutCells.Batch105.certificate1263,MergedCutCells.Batch105.certificate1264,MergedCutCells.Batch105.certificate1265,MergedCutCells.Batch105.certificate1266], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1262,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1263,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1264,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1265,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1266,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid324 : ∀ c∈certificate324.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1261,MergedCutCells.Batch105.certificate1262,MergedCutCells.Batch105.certificate1263,MergedCutCells.Batch105.certificate1264,MergedCutCells.Batch105.certificate1265,MergedCutCells.Batch105.certificate1266], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid109,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid109,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid109,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid109,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid109,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid109,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches324 : ∀ c∈certificate324.cells, c.population=certificate324.population := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1261,MergedCutCells.Batch105.certificate1262,MergedCutCells.Batch105.certificate1263,MergedCutCells.Batch105.certificate1264,MergedCutCells.Batch105.certificate1265,MergedCutCells.Batch105.certificate1266], c.population=PopulationCertificates.Batch010.certificate216
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers324 {x : ℝ} (hx : certificate324.interval.Contains x) : ∃ c∈certificate324.cells, c.region.interval.Contains x := rat_cut_group_covers certificate324 numericValid324 hx

def certificate325 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate216,PopulationCertificates.Batch010.certificate216,[MergedCutCells.Batch105.certificate1267],64,none,(1/2),(1133986837175291/781250000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid325 : certificate325.NumericValid := by decide +kernel
theorem cellsSound325 : ∀ c∈certificate325.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1267], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1267,List.forall_mem_nil _⟩
theorem cellsNumeric325 : ∀ c∈certificate325.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1267], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1267,List.forall_mem_nil _⟩
theorem cellsEntropyValid325 : ∀ c∈certificate325.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1267], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches325 : ∀ c∈certificate325.cells, c.population=certificate325.population := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1267], c.population=PopulationCertificates.Batch010.certificate216
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers325 {x : ℝ} (hx : certificate325.interval.Contains x) : ∃ c∈certificate325.cells, c.region.interval.Contains x := rat_cut_group_covers certificate325 numericValid325 hx

def certificate326 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate217,PopulationCertificates.Batch010.certificate217,[MergedCutCells.Batch105.certificate1268,MergedCutCells.Batch105.certificate1269,MergedCutCells.Batch105.certificate1270],(3553675435647221703/1000000000000000000),none,(1/2),(186664675161190137/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid326 : certificate326.NumericValid := by decide +kernel
theorem cellsSound326 : ∀ c∈certificate326.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1268,MergedCutCells.Batch105.certificate1269,MergedCutCells.Batch105.certificate1270], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1268,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1270,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric326 : ∀ c∈certificate326.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1268,MergedCutCells.Batch105.certificate1269,MergedCutCells.Batch105.certificate1270], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1268,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1269,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1270,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid326 : ∀ c∈certificate326.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1268,MergedCutCells.Batch105.certificate1269,MergedCutCells.Batch105.certificate1270], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches326 : ∀ c∈certificate326.cells, c.population=certificate326.population := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1268,MergedCutCells.Batch105.certificate1269,MergedCutCells.Batch105.certificate1270], c.population=PopulationCertificates.Batch010.certificate217
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers326 {x : ℝ} (hx : certificate326.interval.Contains x) : ∃ c∈certificate326.cells, c.region.interval.Contains x := rat_cut_group_covers certificate326 numericValid326 hx

def certificate327 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate218,PopulationCertificates.Batch010.certificate218,[MergedCutCells.Batch105.certificate1271,MergedCutCells.Batch106.certificate1272,MergedCutCells.Batch106.certificate1273,MergedCutCells.Batch106.certificate1274,MergedCutCells.Batch106.certificate1275,MergedCutCells.Batch106.certificate1276,MergedCutCells.Batch106.certificate1277],(850165604181169593/1000000000000000000),(some 64),(1/2),(160444116561549947/250000000000000000),(some (69314718055994531/100000000000000000)),(some (1465525777410708881/1000000000000000000))⟩
theorem numericValid327 : certificate327.NumericValid := by decide +kernel
theorem cellsSound327 : ∀ c∈certificate327.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1271,MergedCutCells.Batch106.certificate1272,MergedCutCells.Batch106.certificate1273,MergedCutCells.Batch106.certificate1274,MergedCutCells.Batch106.certificate1275,MergedCutCells.Batch106.certificate1276,MergedCutCells.Batch106.certificate1277], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1271,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1272,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1273,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1274,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1276,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1277,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric327 : ∀ c∈certificate327.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1271,MergedCutCells.Batch106.certificate1272,MergedCutCells.Batch106.certificate1273,MergedCutCells.Batch106.certificate1274,MergedCutCells.Batch106.certificate1275,MergedCutCells.Batch106.certificate1276,MergedCutCells.Batch106.certificate1277], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1271,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1272,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1273,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1274,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1275,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1276,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1277,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid327 : ∀ c∈certificate327.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1271,MergedCutCells.Batch106.certificate1272,MergedCutCells.Batch106.certificate1273,MergedCutCells.Batch106.certificate1274,MergedCutCells.Batch106.certificate1275,MergedCutCells.Batch106.certificate1276,MergedCutCells.Batch106.certificate1277], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid110,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid110,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid110,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid110,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid110,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid110,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid110,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches327 : ∀ c∈certificate327.cells, c.population=certificate327.population := by
  change ∀ c∈[MergedCutCells.Batch105.certificate1271,MergedCutCells.Batch106.certificate1272,MergedCutCells.Batch106.certificate1273,MergedCutCells.Batch106.certificate1274,MergedCutCells.Batch106.certificate1275,MergedCutCells.Batch106.certificate1276,MergedCutCells.Batch106.certificate1277], c.population=PopulationCertificates.Batch010.certificate218
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers327 {x : ℝ} (hx : certificate327.interval.Contains x) : ∃ c∈certificate327.cells, c.region.interval.Contains x := rat_cut_group_covers certificate327 numericValid327 hx

def certificate328 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate218,PopulationCertificates.Batch010.certificate218,[MergedCutCells.Batch106.certificate1278],64,none,(1/2),(303340390840535463/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid328 : certificate328.NumericValid := by decide +kernel
theorem cellsSound328 : ∀ c∈certificate328.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1278], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1278,List.forall_mem_nil _⟩
theorem cellsNumeric328 : ∀ c∈certificate328.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1278], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1278,List.forall_mem_nil _⟩
theorem cellsEntropyValid328 : ∀ c∈certificate328.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1278], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches328 : ∀ c∈certificate328.cells, c.population=certificate328.population := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1278], c.population=PopulationCertificates.Batch010.certificate218
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers328 {x : ℝ} (hx : certificate328.interval.Contains x) : ∃ c∈certificate328.cells, c.region.interval.Contains x := rat_cut_group_covers certificate328 numericValid328 hx

def certificate329 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate219,PopulationCertificates.Batch010.certificate219,[MergedCutCells.Batch106.certificate1279,MergedCutCells.Batch106.certificate1280,MergedCutCells.Batch106.certificate1281,MergedCutCells.Batch106.certificate1282],(177859619202131793/50000000000000000),none,(1/2),(764820960307825453/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid329 : certificate329.NumericValid := by decide +kernel
theorem cellsSound329 : ∀ c∈certificate329.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1279,MergedCutCells.Batch106.certificate1280,MergedCutCells.Batch106.certificate1281,MergedCutCells.Batch106.certificate1282], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1279,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1280,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1281,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1282,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric329 : ∀ c∈certificate329.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1279,MergedCutCells.Batch106.certificate1280,MergedCutCells.Batch106.certificate1281,MergedCutCells.Batch106.certificate1282], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1279,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1280,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1281,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1282,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid329 : ∀ c∈certificate329.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1279,MergedCutCells.Batch106.certificate1280,MergedCutCells.Batch106.certificate1281,MergedCutCells.Batch106.certificate1282], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches329 : ∀ c∈certificate329.cells, c.population=certificate329.population := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1279,MergedCutCells.Batch106.certificate1280,MergedCutCells.Batch106.certificate1281,MergedCutCells.Batch106.certificate1282], c.population=PopulationCertificates.Batch010.certificate219
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers329 {x : ℝ} (hx : certificate329.interval.Contains x) : ∃ c∈certificate329.cells, c.region.interval.Contains x := rat_cut_group_covers certificate329 numericValid329 hx

def certificate330 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate220,PopulationCertificates.Batch011.certificate220,[MergedCutCells.Batch106.certificate1283,MergedCutCells.Batch107.certificate1284,MergedCutCells.Batch107.certificate1285,MergedCutCells.Batch107.certificate1286,MergedCutCells.Batch107.certificate1287,MergedCutCells.Batch107.certificate1288,MergedCutCells.Batch107.certificate1289],(846909091106130267/1000000000000000000),(some 64),(1/2),(324337378142178253/500000000000000000),(some (69314718055994531/100000000000000000)),(some (1467522896407304481/1000000000000000000))⟩
theorem numericValid330 : certificate330.NumericValid := by decide +kernel
theorem cellsSound330 : ∀ c∈certificate330.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1283,MergedCutCells.Batch107.certificate1284,MergedCutCells.Batch107.certificate1285,MergedCutCells.Batch107.certificate1286,MergedCutCells.Batch107.certificate1287,MergedCutCells.Batch107.certificate1288,MergedCutCells.Batch107.certificate1289], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.sound1283,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1284,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1286,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1288,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1289,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric330 : ∀ c∈certificate330.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1283,MergedCutCells.Batch107.certificate1284,MergedCutCells.Batch107.certificate1285,MergedCutCells.Batch107.certificate1286,MergedCutCells.Batch107.certificate1287,MergedCutCells.Batch107.certificate1288,MergedCutCells.Batch107.certificate1289], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch106.numericValid1283,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1284,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1285,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1286,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1287,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1288,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1289,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid330 : ∀ c∈certificate330.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1283,MergedCutCells.Batch107.certificate1284,MergedCutCells.Batch107.certificate1285,MergedCutCells.Batch107.certificate1286,MergedCutCells.Batch107.certificate1287,MergedCutCells.Batch107.certificate1288,MergedCutCells.Batch107.certificate1289], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid111,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid111,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid111,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid111,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid111,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid111,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid111,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches330 : ∀ c∈certificate330.cells, c.population=certificate330.population := by
  change ∀ c∈[MergedCutCells.Batch106.certificate1283,MergedCutCells.Batch107.certificate1284,MergedCutCells.Batch107.certificate1285,MergedCutCells.Batch107.certificate1286,MergedCutCells.Batch107.certificate1287,MergedCutCells.Batch107.certificate1288,MergedCutCells.Batch107.certificate1289], c.population=PopulationCertificates.Batch011.certificate220
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers330 {x : ℝ} (hx : certificate330.interval.Contains x) : ∃ c∈certificate330.cells, c.region.interval.Contains x := rat_cut_group_covers certificate330 numericValid330 hx

def certificate331 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate220,PopulationCertificates.Batch011.certificate220,[MergedCutCells.Batch107.certificate1290],64,none,(1/2),(772183812733767231/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid331 : certificate331.NumericValid := by decide +kernel
theorem cellsSound331 : ∀ c∈certificate331.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1290], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1290,List.forall_mem_nil _⟩
theorem cellsNumeric331 : ∀ c∈certificate331.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1290], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1290,List.forall_mem_nil _⟩
theorem cellsEntropyValid331 : ∀ c∈certificate331.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1290], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches331 : ∀ c∈certificate331.cells, c.population=certificate331.population := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1290], c.population=PopulationCertificates.Batch011.certificate220
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers331 {x : ℝ} (hx : certificate331.interval.Contains x) : ∃ c∈certificate331.cells, c.region.interval.Contains x := rat_cut_group_covers certificate331 numericValid331 hx

def certificate332 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate221,PopulationCertificates.Batch011.certificate221,[MergedCutCells.Batch107.certificate1291,MergedCutCells.Batch107.certificate1292,MergedCutCells.Batch107.certificate1293,MergedCutCells.Batch107.certificate1294],(3562919594914194107/1000000000000000000),none,(1/2),(785730155426477027/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid332 : certificate332.NumericValid := by decide +kernel
theorem cellsSound332 : ∀ c∈certificate332.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1291,MergedCutCells.Batch107.certificate1292,MergedCutCells.Batch107.certificate1293,MergedCutCells.Batch107.certificate1294], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1292,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1294,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric332 : ∀ c∈certificate332.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1291,MergedCutCells.Batch107.certificate1292,MergedCutCells.Batch107.certificate1293,MergedCutCells.Batch107.certificate1294], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1291,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1292,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1293,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1294,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid332 : ∀ c∈certificate332.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1291,MergedCutCells.Batch107.certificate1292,MergedCutCells.Batch107.certificate1293,MergedCutCells.Batch107.certificate1294], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches332 : ∀ c∈certificate332.cells, c.population=certificate332.population := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1291,MergedCutCells.Batch107.certificate1292,MergedCutCells.Batch107.certificate1293,MergedCutCells.Batch107.certificate1294], c.population=PopulationCertificates.Batch011.certificate221
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers332 {x : ℝ} (hx : certificate332.interval.Contains x) : ∃ c∈certificate332.cells, c.region.interval.Contains x := rat_cut_group_covers certificate332 numericValid332 hx

def certificate333 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate222,PopulationCertificates.Batch011.certificate222,[MergedCutCells.Batch107.certificate1295,MergedCutCells.Batch108.certificate1296,MergedCutCells.Batch108.certificate1297,MergedCutCells.Batch108.certificate1298,MergedCutCells.Batch108.certificate1299,MergedCutCells.Batch108.certificate1300,MergedCutCells.Batch108.certificate1301,MergedCutCells.Batch108.certificate1302],(425716960383630721/500000000000000000),(some 64),(1/2),(166306488014307259/250000000000000000),(some (69314718055994531/100000000000000000)),(some (1469887073642918433/1000000000000000000))⟩
theorem numericValid333 : certificate333.NumericValid := by decide +kernel
theorem cellsSound333 : ∀ c∈certificate333.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1295,MergedCutCells.Batch108.certificate1296,MergedCutCells.Batch108.certificate1297,MergedCutCells.Batch108.certificate1298,MergedCutCells.Batch108.certificate1299,MergedCutCells.Batch108.certificate1300,MergedCutCells.Batch108.certificate1301,MergedCutCells.Batch108.certificate1302], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.sound1295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1296,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1297,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1298,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1299,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1300,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1301,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1302,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric333 : ∀ c∈certificate333.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1295,MergedCutCells.Batch108.certificate1296,MergedCutCells.Batch108.certificate1297,MergedCutCells.Batch108.certificate1298,MergedCutCells.Batch108.certificate1299,MergedCutCells.Batch108.certificate1300,MergedCutCells.Batch108.certificate1301,MergedCutCells.Batch108.certificate1302], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch107.numericValid1295,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1296,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1297,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1298,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1299,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1300,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1301,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1302,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid333 : ∀ c∈certificate333.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1295,MergedCutCells.Batch108.certificate1296,MergedCutCells.Batch108.certificate1297,MergedCutCells.Batch108.certificate1298,MergedCutCells.Batch108.certificate1299,MergedCutCells.Batch108.certificate1300,MergedCutCells.Batch108.certificate1301,MergedCutCells.Batch108.certificate1302], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid112,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid112,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid112,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid112,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid112,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid112,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid112,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid112,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches333 : ∀ c∈certificate333.cells, c.population=certificate333.population := by
  change ∀ c∈[MergedCutCells.Batch107.certificate1295,MergedCutCells.Batch108.certificate1296,MergedCutCells.Batch108.certificate1297,MergedCutCells.Batch108.certificate1298,MergedCutCells.Batch108.certificate1299,MergedCutCells.Batch108.certificate1300,MergedCutCells.Batch108.certificate1301,MergedCutCells.Batch108.certificate1302], c.population=PopulationCertificates.Batch011.certificate222
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers333 {x : ℝ} (hx : certificate333.interval.Contains x) : ∃ c∈certificate333.cells, c.region.interval.Contains x := rat_cut_group_covers certificate333 numericValid333 hx

def certificate334 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate222,PopulationCertificates.Batch011.certificate222,[MergedCutCells.Batch108.certificate1303],64,none,(1/2),(1567980247428923887/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid334 : certificate334.NumericValid := by decide +kernel
theorem cellsSound334 : ∀ c∈certificate334.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch108.certificate1303], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1303,List.forall_mem_nil _⟩
theorem cellsNumeric334 : ∀ c∈certificate334.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch108.certificate1303], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1303,List.forall_mem_nil _⟩
theorem cellsEntropyValid334 : ∀ c∈certificate334.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch108.certificate1303], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches334 : ∀ c∈certificate334.cells, c.population=certificate334.population := by
  change ∀ c∈[MergedCutCells.Batch108.certificate1303], c.population=PopulationCertificates.Batch011.certificate222
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers334 {x : ℝ} (hx : certificate334.interval.Contains x) : ∃ c∈certificate334.cells, c.region.interval.Contains x := rat_cut_group_covers certificate334 numericValid334 hx

def certificate335 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate223,PopulationCertificates.Batch011.certificate223,[MergedCutCells.Batch108.certificate1304,MergedCutCells.Batch108.certificate1305,MergedCutCells.Batch108.certificate1306,MergedCutCells.Batch108.certificate1307],(3566516652835385047/1000000000000000000),none,(1/2),(402104957337716433/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid335 : certificate335.NumericValid := by decide +kernel
theorem cellsSound335 : ∀ c∈certificate335.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch108.certificate1304,MergedCutCells.Batch108.certificate1305,MergedCutCells.Batch108.certificate1306,MergedCutCells.Batch108.certificate1307], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1304,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1305,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1306,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.sound1307,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric335 : ∀ c∈certificate335.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch108.certificate1304,MergedCutCells.Batch108.certificate1305,MergedCutCells.Batch108.certificate1306,MergedCutCells.Batch108.certificate1307], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1304,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1305,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1306,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch108.numericValid1307,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid335 : ∀ c∈certificate335.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch108.certificate1304,MergedCutCells.Batch108.certificate1305,MergedCutCells.Batch108.certificate1306,MergedCutCells.Batch108.certificate1307], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches335 : ∀ c∈certificate335.cells, c.population=certificate335.population := by
  change ∀ c∈[MergedCutCells.Batch108.certificate1304,MergedCutCells.Batch108.certificate1305,MergedCutCells.Batch108.certificate1306,MergedCutCells.Batch108.certificate1307], c.population=PopulationCertificates.Batch011.certificate223
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers335 {x : ℝ} (hx : certificate335.interval.Contains x) : ∃ c∈certificate335.cells, c.region.interval.Contains x := rat_cut_group_covers certificate335 numericValid335 hx

end Cycle12.MergedCutGroups.Batch027
