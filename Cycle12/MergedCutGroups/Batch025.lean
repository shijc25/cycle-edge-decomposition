import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch010
import Cycle12.MergedCutCells.Batch097
import Cycle12.MergedCutCells.Batch098
import Cycle12.MergedCutCells.Batch099
import Cycle12.MergedCutCells.Batch100
import Cycle12.MergedCutCells.Batch101
import Cycle12.PopulationCertificates.Batch010

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch025

def certificate300 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate200,PopulationCertificates.Batch010.certificate200,[MergedCutCells.Batch097.certificate1168,MergedCutCells.Batch097.certificate1169,MergedCutCells.Batch097.certificate1170,MergedCutCells.Batch097.certificate1171,MergedCutCells.Batch097.certificate1172,MergedCutCells.Batch097.certificate1173,MergedCutCells.Batch097.certificate1174,MergedCutCells.Batch097.certificate1175],(418675193473321133/500000000000000000),(some 64),(1/2),(440911576865073057/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (726749994225033979/500000000000000000))⟩
theorem numericValid300 : certificate300.NumericValid := by decide +kernel
theorem cellsSound300 : ∀ c∈certificate300.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch097.certificate1168,MergedCutCells.Batch097.certificate1169,MergedCutCells.Batch097.certificate1170,MergedCutCells.Batch097.certificate1171,MergedCutCells.Batch097.certificate1172,MergedCutCells.Batch097.certificate1173,MergedCutCells.Batch097.certificate1174,MergedCutCells.Batch097.certificate1175], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1170,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1173,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1174,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.sound1175,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric300 : ∀ c∈certificate300.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch097.certificate1168,MergedCutCells.Batch097.certificate1169,MergedCutCells.Batch097.certificate1170,MergedCutCells.Batch097.certificate1171,MergedCutCells.Batch097.certificate1172,MergedCutCells.Batch097.certificate1173,MergedCutCells.Batch097.certificate1174,MergedCutCells.Batch097.certificate1175], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1170,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1173,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1174,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch097.numericValid1175,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid300 : ∀ c∈certificate300.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch097.certificate1168,MergedCutCells.Batch097.certificate1169,MergedCutCells.Batch097.certificate1170,MergedCutCells.Batch097.certificate1171,MergedCutCells.Batch097.certificate1172,MergedCutCells.Batch097.certificate1173,MergedCutCells.Batch097.certificate1174,MergedCutCells.Batch097.certificate1175], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid101,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid101,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid101,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid101,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid101,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid101,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid101,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid101,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches300 : ∀ c∈certificate300.cells, c.population=certificate300.population := by
  change ∀ c∈[MergedCutCells.Batch097.certificate1168,MergedCutCells.Batch097.certificate1169,MergedCutCells.Batch097.certificate1170,MergedCutCells.Batch097.certificate1171,MergedCutCells.Batch097.certificate1172,MergedCutCells.Batch097.certificate1173,MergedCutCells.Batch097.certificate1174,MergedCutCells.Batch097.certificate1175], c.population=PopulationCertificates.Batch010.certificate200
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers300 {x : ℝ} (hx : certificate300.interval.Contains x) : ∃ c∈certificate300.cells, c.region.interval.Contains x := rat_cut_group_covers certificate300 numericValid300 hx

def certificate301 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate200,PopulationCertificates.Batch010.certificate200,[MergedCutCells.Batch098.certificate1176],64,none,(1/2),(1175104845433882927/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid301 : certificate301.NumericValid := by decide +kernel
theorem cellsSound301 : ∀ c∈certificate301.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1176], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1176,List.forall_mem_nil _⟩
theorem cellsNumeric301 : ∀ c∈certificate301.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1176], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1176,List.forall_mem_nil _⟩
theorem cellsEntropyValid301 : ∀ c∈certificate301.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1176], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches301 : ∀ c∈certificate301.cells, c.population=certificate301.population := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1176], c.population=PopulationCertificates.Batch010.certificate200
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers301 {x : ℝ} (hx : certificate301.interval.Contains x) : ∃ c∈certificate301.cells, c.region.interval.Contains x := rat_cut_group_covers certificate301 numericValid301 hx

def certificate302 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate201,PopulationCertificates.Batch010.certificate201,[MergedCutCells.Batch098.certificate1177,MergedCutCells.Batch098.certificate1178,MergedCutCells.Batch098.certificate1179,MergedCutCells.Batch098.certificate1180],(182928902807249877/50000000000000000),none,(1/2),(685253088432138923/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid302 : certificate302.NumericValid := by decide +kernel
theorem cellsSound302 : ∀ c∈certificate302.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1177,MergedCutCells.Batch098.certificate1178,MergedCutCells.Batch098.certificate1179,MergedCutCells.Batch098.certificate1180], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1178,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1180,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric302 : ∀ c∈certificate302.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1177,MergedCutCells.Batch098.certificate1178,MergedCutCells.Batch098.certificate1179,MergedCutCells.Batch098.certificate1180], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1178,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1180,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid302 : ∀ c∈certificate302.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1177,MergedCutCells.Batch098.certificate1178,MergedCutCells.Batch098.certificate1179,MergedCutCells.Batch098.certificate1180], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches302 : ∀ c∈certificate302.cells, c.population=certificate302.population := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1177,MergedCutCells.Batch098.certificate1178,MergedCutCells.Batch098.certificate1179,MergedCutCells.Batch098.certificate1180], c.population=PopulationCertificates.Batch010.certificate201
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers302 {x : ℝ} (hx : certificate302.interval.Contains x) : ∃ c∈certificate302.cells, c.region.interval.Contains x := rat_cut_group_covers certificate302 numericValid302 hx

def certificate303 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate202,PopulationCertificates.Batch010.certificate202,[MergedCutCells.Batch098.certificate1181,MergedCutCells.Batch098.certificate1182,MergedCutCells.Batch098.certificate1183,MergedCutCells.Batch098.certificate1184,MergedCutCells.Batch098.certificate1185,MergedCutCells.Batch098.certificate1186,MergedCutCells.Batch098.certificate1187],(850165604207499791/1000000000000000000),(some 64),(1/2),(281151295251482323/500000000000000000),(some (69314718055994531/100000000000000000)),(some (2268279131877791/1562500000000000))⟩
theorem numericValid303 : certificate303.NumericValid := by decide +kernel
theorem cellsSound303 : ∀ c∈certificate303.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1181,MergedCutCells.Batch098.certificate1182,MergedCutCells.Batch098.certificate1183,MergedCutCells.Batch098.certificate1184,MergedCutCells.Batch098.certificate1185,MergedCutCells.Batch098.certificate1186,MergedCutCells.Batch098.certificate1187], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1182,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1184,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1185,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1186,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.sound1187,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric303 : ∀ c∈certificate303.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1181,MergedCutCells.Batch098.certificate1182,MergedCutCells.Batch098.certificate1183,MergedCutCells.Batch098.certificate1184,MergedCutCells.Batch098.certificate1185,MergedCutCells.Batch098.certificate1186,MergedCutCells.Batch098.certificate1187], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1182,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1183,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1184,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1185,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1186,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch098.numericValid1187,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid303 : ∀ c∈certificate303.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1181,MergedCutCells.Batch098.certificate1182,MergedCutCells.Batch098.certificate1183,MergedCutCells.Batch098.certificate1184,MergedCutCells.Batch098.certificate1185,MergedCutCells.Batch098.certificate1186,MergedCutCells.Batch098.certificate1187], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid102,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid102,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid102,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid102,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid102,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid102,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid102,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches303 : ∀ c∈certificate303.cells, c.population=certificate303.population := by
  change ∀ c∈[MergedCutCells.Batch098.certificate1181,MergedCutCells.Batch098.certificate1182,MergedCutCells.Batch098.certificate1183,MergedCutCells.Batch098.certificate1184,MergedCutCells.Batch098.certificate1185,MergedCutCells.Batch098.certificate1186,MergedCutCells.Batch098.certificate1187], c.population=PopulationCertificates.Batch010.certificate202
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers303 {x : ℝ} (hx : certificate303.interval.Contains x) : ∃ c∈certificate303.cells, c.region.interval.Contains x := rat_cut_group_covers certificate303 numericValid303 hx

def certificate304 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate202,PopulationCertificates.Batch010.certificate202,[MergedCutCells.Batch099.certificate1188],64,none,(1/2),(1337844608233293713/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid304 : certificate304.NumericValid := by decide +kernel
theorem cellsSound304 : ∀ c∈certificate304.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1188], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1188,List.forall_mem_nil _⟩
theorem cellsNumeric304 : ∀ c∈certificate304.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1188], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1188,List.forall_mem_nil _⟩
theorem cellsEntropyValid304 : ∀ c∈certificate304.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1188], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches304 : ∀ c∈certificate304.cells, c.population=certificate304.population := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1188], c.population=PopulationCertificates.Batch010.certificate202
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers304 {x : ℝ} (hx : certificate304.interval.Contains x) : ∃ c∈certificate304.cells, c.region.interval.Contains x := rat_cut_group_covers certificate304 numericValid304 hx

def certificate305 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate203,PopulationCertificates.Batch010.certificate203,[MergedCutCells.Batch099.certificate1189,MergedCutCells.Batch099.certificate1190,MergedCutCells.Batch099.certificate1191,MergedCutCells.Batch099.certificate1192],(901799532402232753/250000000000000000),none,(1/2),(376577137590774923/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid305 : certificate305.NumericValid := by decide +kernel
theorem cellsSound305 : ∀ c∈certificate305.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1189,MergedCutCells.Batch099.certificate1190,MergedCutCells.Batch099.certificate1191,MergedCutCells.Batch099.certificate1192], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1189,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1192,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric305 : ∀ c∈certificate305.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1189,MergedCutCells.Batch099.certificate1190,MergedCutCells.Batch099.certificate1191,MergedCutCells.Batch099.certificate1192], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1189,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1192,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid305 : ∀ c∈certificate305.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1189,MergedCutCells.Batch099.certificate1190,MergedCutCells.Batch099.certificate1191,MergedCutCells.Batch099.certificate1192], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches305 : ∀ c∈certificate305.cells, c.population=certificate305.population := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1189,MergedCutCells.Batch099.certificate1190,MergedCutCells.Batch099.certificate1191,MergedCutCells.Batch099.certificate1192], c.population=PopulationCertificates.Batch010.certificate203
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers305 {x : ℝ} (hx : certificate305.interval.Contains x) : ∃ c∈certificate305.cells, c.region.interval.Contains x := rat_cut_group_covers certificate305 numericValid305 hx

def certificate306 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate204,PopulationCertificates.Batch010.certificate204,[MergedCutCells.Batch099.certificate1193,MergedCutCells.Batch099.certificate1194,MergedCutCells.Batch099.certificate1195,MergedCutCells.Batch099.certificate1196,MergedCutCells.Batch099.certificate1197,MergedCutCells.Batch099.certificate1198],(864752541266041591/1000000000000000000),(some 64),(1/2),(282717379695897527/500000000000000000),(some (69314718055994531/100000000000000000)),(some (181919524406903377/125000000000000000))⟩
theorem numericValid306 : certificate306.NumericValid := by decide +kernel
theorem cellsSound306 : ∀ c∈certificate306.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1193,MergedCutCells.Batch099.certificate1194,MergedCutCells.Batch099.certificate1195,MergedCutCells.Batch099.certificate1196,MergedCutCells.Batch099.certificate1197,MergedCutCells.Batch099.certificate1198], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1194,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1196,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1198,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric306 : ∀ c∈certificate306.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1193,MergedCutCells.Batch099.certificate1194,MergedCutCells.Batch099.certificate1195,MergedCutCells.Batch099.certificate1196,MergedCutCells.Batch099.certificate1197,MergedCutCells.Batch099.certificate1198], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1194,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1196,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1198,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid306 : ∀ c∈certificate306.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1193,MergedCutCells.Batch099.certificate1194,MergedCutCells.Batch099.certificate1195,MergedCutCells.Batch099.certificate1196,MergedCutCells.Batch099.certificate1197,MergedCutCells.Batch099.certificate1198], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid103,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid103,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid103,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid103,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid103,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid103,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches306 : ∀ c∈certificate306.cells, c.population=certificate306.population := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1193,MergedCutCells.Batch099.certificate1194,MergedCutCells.Batch099.certificate1195,MergedCutCells.Batch099.certificate1196,MergedCutCells.Batch099.certificate1197,MergedCutCells.Batch099.certificate1198], c.population=PopulationCertificates.Batch010.certificate204
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers306 {x : ℝ} (hx : certificate306.interval.Contains x) : ∃ c∈certificate306.cells, c.region.interval.Contains x := rat_cut_group_covers certificate306 numericValid306 hx

def certificate307 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate204,PopulationCertificates.Batch010.certificate204,[MergedCutCells.Batch099.certificate1199],64,none,(1/2),(335875342657178161/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid307 : certificate307.NumericValid := by decide +kernel
theorem cellsSound307 : ∀ c∈certificate307.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1199], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.sound1199,List.forall_mem_nil _⟩
theorem cellsNumeric307 : ∀ c∈certificate307.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1199], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch099.numericValid1199,List.forall_mem_nil _⟩
theorem cellsEntropyValid307 : ∀ c∈certificate307.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1199], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches307 : ∀ c∈certificate307.cells, c.population=certificate307.population := by
  change ∀ c∈[MergedCutCells.Batch099.certificate1199], c.population=PopulationCertificates.Batch010.certificate204
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers307 {x : ℝ} (hx : certificate307.interval.Contains x) : ∃ c∈certificate307.cells, c.region.interval.Contains x := rat_cut_group_covers certificate307 numericValid307 hx

def certificate308 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate205,PopulationCertificates.Batch010.certificate205,[MergedCutCells.Batch100.certificate1200,MergedCutCells.Batch100.certificate1201,MergedCutCells.Batch100.certificate1202,MergedCutCells.Batch100.certificate1203],(1806366654373950237/500000000000000000),none,(1/2),(772858681419540277/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid308 : certificate308.NumericValid := by decide +kernel
theorem cellsSound308 : ∀ c∈certificate308.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1200,MergedCutCells.Batch100.certificate1201,MergedCutCells.Batch100.certificate1202,MergedCutCells.Batch100.certificate1203], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1200,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1202,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1203,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric308 : ∀ c∈certificate308.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1200,MergedCutCells.Batch100.certificate1201,MergedCutCells.Batch100.certificate1202,MergedCutCells.Batch100.certificate1203], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1200,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1202,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1203,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid308 : ∀ c∈certificate308.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1200,MergedCutCells.Batch100.certificate1201,MergedCutCells.Batch100.certificate1202,MergedCutCells.Batch100.certificate1203], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches308 : ∀ c∈certificate308.cells, c.population=certificate308.population := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1200,MergedCutCells.Batch100.certificate1201,MergedCutCells.Batch100.certificate1202,MergedCutCells.Batch100.certificate1203], c.population=PopulationCertificates.Batch010.certificate205
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers308 {x : ℝ} (hx : certificate308.interval.Contains x) : ∃ c∈certificate308.cells, c.region.interval.Contains x := rat_cut_group_covers certificate308 numericValid308 hx

def certificate309 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate206,PopulationCertificates.Batch010.certificate206,[MergedCutCells.Batch100.certificate1204,MergedCutCells.Batch100.certificate1205,MergedCutCells.Batch100.certificate1206,MergedCutCells.Batch100.certificate1207,MergedCutCells.Batch100.certificate1208,MergedCutCells.Batch100.certificate1209,MergedCutCells.Batch100.certificate1210],(850165604122726569/1000000000000000000),(some 64),(1/2),(291568168105613787/500000000000000000),(some (69314718055994531/100000000000000000)),(some (1455539756424112271/1000000000000000000))⟩
theorem numericValid309 : certificate309.NumericValid := by decide +kernel
theorem cellsSound309 : ∀ c∈certificate309.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1204,MergedCutCells.Batch100.certificate1205,MergedCutCells.Batch100.certificate1206,MergedCutCells.Batch100.certificate1207,MergedCutCells.Batch100.certificate1208,MergedCutCells.Batch100.certificate1209,MergedCutCells.Batch100.certificate1210], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1205,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1206,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1208,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1209,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1210,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric309 : ∀ c∈certificate309.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1204,MergedCutCells.Batch100.certificate1205,MergedCutCells.Batch100.certificate1206,MergedCutCells.Batch100.certificate1207,MergedCutCells.Batch100.certificate1208,MergedCutCells.Batch100.certificate1209,MergedCutCells.Batch100.certificate1210], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1205,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1206,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1208,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1209,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1210,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid309 : ∀ c∈certificate309.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1204,MergedCutCells.Batch100.certificate1205,MergedCutCells.Batch100.certificate1206,MergedCutCells.Batch100.certificate1207,MergedCutCells.Batch100.certificate1208,MergedCutCells.Batch100.certificate1209,MergedCutCells.Batch100.certificate1210], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid104,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid104,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid104,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid104,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid104,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid104,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid104,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches309 : ∀ c∈certificate309.cells, c.population=certificate309.population := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1204,MergedCutCells.Batch100.certificate1205,MergedCutCells.Batch100.certificate1206,MergedCutCells.Batch100.certificate1207,MergedCutCells.Batch100.certificate1208,MergedCutCells.Batch100.certificate1209,MergedCutCells.Batch100.certificate1210], c.population=PopulationCertificates.Batch010.certificate206
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers309 {x : ℝ} (hx : certificate309.interval.Contains x) : ∃ c∈certificate309.cells, c.region.interval.Contains x := rat_cut_group_covers certificate309 numericValid309 hx

def certificate310 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate206,PopulationCertificates.Batch010.certificate206,[MergedCutCells.Batch100.certificate1211],64,none,(1/2),(2164950388261713/1562500000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid310 : certificate310.NumericValid := by decide +kernel
theorem cellsSound310 : ∀ c∈certificate310.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1211], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.sound1211,List.forall_mem_nil _⟩
theorem cellsNumeric310 : ∀ c∈certificate310.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1211], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch100.numericValid1211,List.forall_mem_nil _⟩
theorem cellsEntropyValid310 : ∀ c∈certificate310.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1211], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches310 : ∀ c∈certificate310.cells, c.population=certificate310.population := by
  change ∀ c∈[MergedCutCells.Batch100.certificate1211], c.population=PopulationCertificates.Batch010.certificate206
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers310 {x : ℝ} (hx : certificate310.interval.Contains x) : ∃ c∈certificate310.cells, c.region.interval.Contains x := rat_cut_group_covers certificate310 numericValid310 hx

def certificate311 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate207,PopulationCertificates.Batch010.certificate207,[MergedCutCells.Batch101.certificate1212,MergedCutCells.Batch101.certificate1213,MergedCutCells.Batch101.certificate1214],(1809160439803610679/500000000000000000),none,(1/2),(393384222871326473/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid311 : certificate311.NumericValid := by decide +kernel
theorem cellsSound311 : ∀ c∈certificate311.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1212,MergedCutCells.Batch101.certificate1213,MergedCutCells.Batch101.certificate1214], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1212,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1214,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric311 : ∀ c∈certificate311.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1212,MergedCutCells.Batch101.certificate1213,MergedCutCells.Batch101.certificate1214], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1212,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1214,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid311 : ∀ c∈certificate311.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1212,MergedCutCells.Batch101.certificate1213,MergedCutCells.Batch101.certificate1214], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches311 : ∀ c∈certificate311.cells, c.population=certificate311.population := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1212,MergedCutCells.Batch101.certificate1213,MergedCutCells.Batch101.certificate1214], c.population=PopulationCertificates.Batch010.certificate207
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers311 {x : ℝ} (hx : certificate311.interval.Contains x) : ∃ c∈certificate311.cells, c.region.interval.Contains x := rat_cut_group_covers certificate311 numericValid311 hx

end Cycle12.MergedCutGroups.Batch025
