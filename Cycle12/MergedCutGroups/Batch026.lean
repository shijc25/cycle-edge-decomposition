import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch010
import Cycle12.MergedCutCells.Batch101
import Cycle12.MergedCutCells.Batch102
import Cycle12.MergedCutCells.Batch103
import Cycle12.MergedCutCells.Batch104
import Cycle12.MergedCutCells.Batch105
import Cycle12.PopulationCertificates.Batch010

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch026

def certificate312 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate208,PopulationCertificates.Batch010.certificate208,[MergedCutCells.Batch101.certificate1215,MergedCutCells.Batch101.certificate1216,MergedCutCells.Batch101.certificate1217,MergedCutCells.Batch101.certificate1218,MergedCutCells.Batch101.certificate1219,MergedCutCells.Batch101.certificate1220,MergedCutCells.Batch101.certificate1221],(106269912150056919/125000000000000000),(some 64),(1/2),(148633229518939261/250000000000000000),(some (69314718055994531/100000000000000000)),(some (1457755849111309407/1000000000000000000))⟩
theorem numericValid312 : certificate312.NumericValid := by decide +kernel
theorem cellsSound312 : ∀ c∈certificate312.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1215,MergedCutCells.Batch101.certificate1216,MergedCutCells.Batch101.certificate1217,MergedCutCells.Batch101.certificate1218,MergedCutCells.Batch101.certificate1219,MergedCutCells.Batch101.certificate1220,MergedCutCells.Batch101.certificate1221], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1216,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1217,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1218,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1220,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1221,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric312 : ∀ c∈certificate312.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1215,MergedCutCells.Batch101.certificate1216,MergedCutCells.Batch101.certificate1217,MergedCutCells.Batch101.certificate1218,MergedCutCells.Batch101.certificate1219,MergedCutCells.Batch101.certificate1220,MergedCutCells.Batch101.certificate1221], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1216,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1217,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1218,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1220,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1221,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid312 : ∀ c∈certificate312.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1215,MergedCutCells.Batch101.certificate1216,MergedCutCells.Batch101.certificate1217,MergedCutCells.Batch101.certificate1218,MergedCutCells.Batch101.certificate1219,MergedCutCells.Batch101.certificate1220,MergedCutCells.Batch101.certificate1221], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid105,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid105,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid105,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid105,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid105,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid105,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid105,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches312 : ∀ c∈certificate312.cells, c.population=certificate312.population := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1215,MergedCutCells.Batch101.certificate1216,MergedCutCells.Batch101.certificate1217,MergedCutCells.Batch101.certificate1218,MergedCutCells.Batch101.certificate1219,MergedCutCells.Batch101.certificate1220,MergedCutCells.Batch101.certificate1221], c.population=PopulationCertificates.Batch010.certificate208
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers312 {x : ℝ} (hx : certificate312.interval.Contains x) : ∃ c∈certificate312.cells, c.region.interval.Contains x := rat_cut_group_covers certificate312 numericValid312 hx

def certificate313 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate208,PopulationCertificates.Batch010.certificate208,[MergedCutCells.Batch101.certificate1222],64,none,(1/2),(1410804190081904751/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid313 : certificate313.NumericValid := by decide +kernel
theorem cellsSound313 : ∀ c∈certificate313.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1222], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1222,List.forall_mem_nil _⟩
theorem cellsNumeric313 : ∀ c∈certificate313.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1222], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1222,List.forall_mem_nil _⟩
theorem cellsEntropyValid313 : ∀ c∈certificate313.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1222], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches313 : ∀ c∈certificate313.cells, c.population=certificate313.population := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1222], c.population=PopulationCertificates.Batch010.certificate208
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers313 {x : ℝ} (hx : certificate313.interval.Contains x) : ∃ c∈certificate313.cells, c.region.interval.Contains x := rat_cut_group_covers certificate313 numericValid313 hx

def certificate314 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate209,PopulationCertificates.Batch010.certificate209,[MergedCutCells.Batch101.certificate1223,MergedCutCells.Batch102.certificate1224,MergedCutCells.Batch102.certificate1225],(1810889942870435071/500000000000000000),none,(1/2),(402281889105811321/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid314 : certificate314.NumericValid := by decide +kernel
theorem cellsSound314 : ∀ c∈certificate314.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1223,MergedCutCells.Batch102.certificate1224,MergedCutCells.Batch102.certificate1225], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.sound1223,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1225,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric314 : ∀ c∈certificate314.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1223,MergedCutCells.Batch102.certificate1224,MergedCutCells.Batch102.certificate1225], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch101.numericValid1223,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1225,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid314 : ∀ c∈certificate314.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1223,MergedCutCells.Batch102.certificate1224,MergedCutCells.Batch102.certificate1225], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches314 : ∀ c∈certificate314.cells, c.population=certificate314.population := by
  change ∀ c∈[MergedCutCells.Batch101.certificate1223,MergedCutCells.Batch102.certificate1224,MergedCutCells.Batch102.certificate1225], c.population=PopulationCertificates.Batch010.certificate209
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers314 {x : ℝ} (hx : certificate314.interval.Contains x) : ∃ c∈certificate314.cells, c.region.interval.Contains x := rat_cut_group_covers certificate314 numericValid314 hx

def certificate315 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate210,PopulationCertificates.Batch010.certificate210,[MergedCutCells.Batch102.certificate1226,MergedCutCells.Batch102.certificate1227,MergedCutCells.Batch102.certificate1228,MergedCutCells.Batch102.certificate1229,MergedCutCells.Batch102.certificate1230,MergedCutCells.Batch102.certificate1231,MergedCutCells.Batch102.certificate1232,MergedCutCells.Batch102.certificate1233],(854026925781557751/1000000000000000000),(some 64),(1/2),(18799990946725833/31250000000000000),(some (69314718055994531/100000000000000000)),(some (36502466971941923/25000000000000000))⟩
theorem numericValid315 : certificate315.NumericValid := by decide +kernel
theorem cellsSound315 : ∀ c∈certificate315.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1226,MergedCutCells.Batch102.certificate1227,MergedCutCells.Batch102.certificate1228,MergedCutCells.Batch102.certificate1229,MergedCutCells.Batch102.certificate1230,MergedCutCells.Batch102.certificate1231,MergedCutCells.Batch102.certificate1232,MergedCutCells.Batch102.certificate1233], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1226,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1227,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1228,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1229,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1231,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1232,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1233,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric315 : ∀ c∈certificate315.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1226,MergedCutCells.Batch102.certificate1227,MergedCutCells.Batch102.certificate1228,MergedCutCells.Batch102.certificate1229,MergedCutCells.Batch102.certificate1230,MergedCutCells.Batch102.certificate1231,MergedCutCells.Batch102.certificate1232,MergedCutCells.Batch102.certificate1233], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1226,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1227,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1228,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1229,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1231,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1232,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1233,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid315 : ∀ c∈certificate315.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1226,MergedCutCells.Batch102.certificate1227,MergedCutCells.Batch102.certificate1228,MergedCutCells.Batch102.certificate1229,MergedCutCells.Batch102.certificate1230,MergedCutCells.Batch102.certificate1231,MergedCutCells.Batch102.certificate1232,MergedCutCells.Batch102.certificate1233], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid106,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid106,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid106,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid106,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid106,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid106,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid106,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid106,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches315 : ∀ c∈certificate315.cells, c.population=certificate315.population := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1226,MergedCutCells.Batch102.certificate1227,MergedCutCells.Batch102.certificate1228,MergedCutCells.Batch102.certificate1229,MergedCutCells.Batch102.certificate1230,MergedCutCells.Batch102.certificate1231,MergedCutCells.Batch102.certificate1232,MergedCutCells.Batch102.certificate1233], c.population=PopulationCertificates.Batch010.certificate210
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers315 {x : ℝ} (hx : certificate315.interval.Contains x) : ∃ c∈certificate315.cells, c.region.interval.Contains x := rat_cut_group_covers certificate315 numericValid315 hx

def certificate316 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate210,PopulationCertificates.Batch010.certificate210,[MergedCutCells.Batch102.certificate1234],64,none,(1/2),(715347616013590301/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid316 : certificate316.NumericValid := by decide +kernel
theorem cellsSound316 : ∀ c∈certificate316.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1234], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1234,List.forall_mem_nil _⟩
theorem cellsNumeric316 : ∀ c∈certificate316.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1234], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1234,List.forall_mem_nil _⟩
theorem cellsEntropyValid316 : ∀ c∈certificate316.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1234], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches316 : ∀ c∈certificate316.cells, c.population=certificate316.population := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1234], c.population=PopulationCertificates.Batch010.certificate210
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers316 {x : ℝ} (hx : certificate316.interval.Contains x) : ∃ c∈certificate316.cells, c.region.interval.Contains x := rat_cut_group_covers certificate316 numericValid316 hx

def certificate317 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate211,PopulationCertificates.Batch010.certificate211,[MergedCutCells.Batch102.certificate1235,MergedCutCells.Batch103.certificate1236,MergedCutCells.Batch103.certificate1237],(725492933332147771/200000000000000000),none,(1/2),(412777600662341873/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid317 : certificate317.NumericValid := by decide +kernel
theorem cellsSound317 : ∀ c∈certificate317.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1235,MergedCutCells.Batch103.certificate1236,MergedCutCells.Batch103.certificate1237], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.sound1235,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1237,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric317 : ∀ c∈certificate317.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1235,MergedCutCells.Batch103.certificate1236,MergedCutCells.Batch103.certificate1237], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch102.numericValid1235,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1237,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid317 : ∀ c∈certificate317.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1235,MergedCutCells.Batch103.certificate1236,MergedCutCells.Batch103.certificate1237], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches317 : ∀ c∈certificate317.cells, c.population=certificate317.population := by
  change ∀ c∈[MergedCutCells.Batch102.certificate1235,MergedCutCells.Batch103.certificate1236,MergedCutCells.Batch103.certificate1237], c.population=PopulationCertificates.Batch010.certificate211
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers317 {x : ℝ} (hx : certificate317.interval.Contains x) : ∃ c∈certificate317.cells, c.region.interval.Contains x := rat_cut_group_covers certificate317 numericValid317 hx

def certificate318 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate212,PopulationCertificates.Batch010.certificate212,[MergedCutCells.Batch103.certificate1238,MergedCutCells.Batch103.certificate1239,MergedCutCells.Batch103.certificate1240,MergedCutCells.Batch103.certificate1241,MergedCutCells.Batch103.certificate1242,MergedCutCells.Batch103.certificate1243,MergedCutCells.Batch103.certificate1244],(425074493975244737/500000000000000000),(some 64),(1/2),(618377337063325149/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1459743206984645613/1000000000000000000))⟩
theorem numericValid318 : certificate318.NumericValid := by decide +kernel
theorem cellsSound318 : ∀ c∈certificate318.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1238,MergedCutCells.Batch103.certificate1239,MergedCutCells.Batch103.certificate1240,MergedCutCells.Batch103.certificate1241,MergedCutCells.Batch103.certificate1242,MergedCutCells.Batch103.certificate1243,MergedCutCells.Batch103.certificate1244], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1238,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1239,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1241,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1243,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1244,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric318 : ∀ c∈certificate318.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1238,MergedCutCells.Batch103.certificate1239,MergedCutCells.Batch103.certificate1240,MergedCutCells.Batch103.certificate1241,MergedCutCells.Batch103.certificate1242,MergedCutCells.Batch103.certificate1243,MergedCutCells.Batch103.certificate1244], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1238,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1239,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1241,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1243,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1244,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid318 : ∀ c∈certificate318.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1238,MergedCutCells.Batch103.certificate1239,MergedCutCells.Batch103.certificate1240,MergedCutCells.Batch103.certificate1241,MergedCutCells.Batch103.certificate1242,MergedCutCells.Batch103.certificate1243,MergedCutCells.Batch103.certificate1244], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid107,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid107,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid107,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid107,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid107,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid107,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid107,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches318 : ∀ c∈certificate318.cells, c.population=certificate318.population := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1238,MergedCutCells.Batch103.certificate1239,MergedCutCells.Batch103.certificate1240,MergedCutCells.Batch103.certificate1241,MergedCutCells.Batch103.certificate1242,MergedCutCells.Batch103.certificate1243,MergedCutCells.Batch103.certificate1244], c.population=PopulationCertificates.Batch010.certificate212
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers318 {x : ℝ} (hx : certificate318.interval.Contains x) : ∃ c∈certificate318.cells, c.region.interval.Contains x := rat_cut_group_covers certificate318 numericValid318 hx

def certificate319 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate212,PopulationCertificates.Batch010.certificate212,[MergedCutCells.Batch103.certificate1245],64,none,(1/2),(732178855114611877/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid319 : certificate319.NumericValid := by decide +kernel
theorem cellsSound319 : ∀ c∈certificate319.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1245], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1245,List.forall_mem_nil _⟩
theorem cellsNumeric319 : ∀ c∈certificate319.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1245], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1245,List.forall_mem_nil _⟩
theorem cellsEntropyValid319 : ∀ c∈certificate319.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1245], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches319 : ∀ c∈certificate319.cells, c.population=certificate319.population := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1245], c.population=PopulationCertificates.Batch010.certificate212
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers319 {x : ℝ} (hx : certificate319.interval.Contains x) : ∃ c∈certificate319.cells, c.region.interval.Contains x := rat_cut_group_covers certificate319 numericValid319 hx

def certificate320 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate213,PopulationCertificates.Batch010.certificate213,[MergedCutCells.Batch103.certificate1246,MergedCutCells.Batch103.certificate1247,MergedCutCells.Batch104.certificate1248],(3634686560602250633/1000000000000000000),none,(1/2),(212961619250321203/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid320 : certificate320.NumericValid := by decide +kernel
theorem cellsSound320 : ∀ c∈certificate320.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1246,MergedCutCells.Batch103.certificate1247,MergedCutCells.Batch104.certificate1248], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.sound1247,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1248,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric320 : ∀ c∈certificate320.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1246,MergedCutCells.Batch103.certificate1247,MergedCutCells.Batch104.certificate1248], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch103.numericValid1247,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1248,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid320 : ∀ c∈certificate320.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1246,MergedCutCells.Batch103.certificate1247,MergedCutCells.Batch104.certificate1248], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches320 : ∀ c∈certificate320.cells, c.population=certificate320.population := by
  change ∀ c∈[MergedCutCells.Batch103.certificate1246,MergedCutCells.Batch103.certificate1247,MergedCutCells.Batch104.certificate1248], c.population=PopulationCertificates.Batch010.certificate213
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers320 {x : ℝ} (hx : certificate320.interval.Contains x) : ∃ c∈certificate320.cells, c.region.interval.Contains x := rat_cut_group_covers certificate320 numericValid320 hx

def certificate321 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate214,PopulationCertificates.Batch010.certificate214,[MergedCutCells.Batch104.certificate1249,MergedCutCells.Batch104.certificate1250,MergedCutCells.Batch104.certificate1251,MergedCutCells.Batch104.certificate1252,MergedCutCells.Batch104.certificate1253,MergedCutCells.Batch104.certificate1254,MergedCutCells.Batch104.certificate1255],(850165604304907253/1000000000000000000),(some 64),(1/2),(313554870334804157/500000000000000000),(some (69314718055994531/100000000000000000)),(some (730567686038212161/500000000000000000))⟩
theorem numericValid321 : certificate321.NumericValid := by decide +kernel
theorem cellsSound321 : ∀ c∈certificate321.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1249,MergedCutCells.Batch104.certificate1250,MergedCutCells.Batch104.certificate1251,MergedCutCells.Batch104.certificate1252,MergedCutCells.Batch104.certificate1253,MergedCutCells.Batch104.certificate1254,MergedCutCells.Batch104.certificate1255], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1250,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1251,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1252,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1253,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1254,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1255,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric321 : ∀ c∈certificate321.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1249,MergedCutCells.Batch104.certificate1250,MergedCutCells.Batch104.certificate1251,MergedCutCells.Batch104.certificate1252,MergedCutCells.Batch104.certificate1253,MergedCutCells.Batch104.certificate1254,MergedCutCells.Batch104.certificate1255], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1250,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1251,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1252,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1253,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1254,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1255,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid321 : ∀ c∈certificate321.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1249,MergedCutCells.Batch104.certificate1250,MergedCutCells.Batch104.certificate1251,MergedCutCells.Batch104.certificate1252,MergedCutCells.Batch104.certificate1253,MergedCutCells.Batch104.certificate1254,MergedCutCells.Batch104.certificate1255], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid108,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid108,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid108,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid108,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid108,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid108,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid108,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches321 : ∀ c∈certificate321.cells, c.population=certificate321.population := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1249,MergedCutCells.Batch104.certificate1250,MergedCutCells.Batch104.certificate1251,MergedCutCells.Batch104.certificate1252,MergedCutCells.Batch104.certificate1253,MergedCutCells.Batch104.certificate1254,MergedCutCells.Batch104.certificate1255], c.population=PopulationCertificates.Batch010.certificate214
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers321 {x : ℝ} (hx : certificate321.interval.Contains x) : ∃ c∈certificate321.cells, c.region.interval.Contains x := rat_cut_group_covers certificate321 numericValid321 hx

def certificate322 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate214,PopulationCertificates.Batch010.certificate214,[MergedCutCells.Batch104.certificate1256],64,none,(1/2),(1475729007179607901/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid322 : certificate322.NumericValid := by decide +kernel
theorem cellsSound322 : ∀ c∈certificate322.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1256], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1256,List.forall_mem_nil _⟩
theorem cellsNumeric322 : ∀ c∈certificate322.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1256], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1256,List.forall_mem_nil _⟩
theorem cellsEntropyValid322 : ∀ c∈certificate322.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1256], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches322 : ∀ c∈certificate322.cells, c.population=certificate322.population := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1256], c.population=PopulationCertificates.Batch010.certificate214
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers322 {x : ℝ} (hx : certificate322.interval.Contains x) : ∃ c∈certificate322.cells, c.region.interval.Contains x := rat_cut_group_covers certificate322 numericValid322 hx

def certificate323 : RatCutGroup := ⟨GeometryCertificates.Batch010.certificate215,PopulationCertificates.Batch010.certificate215,[MergedCutCells.Batch104.certificate1257,MergedCutCells.Batch104.certificate1258,MergedCutCells.Batch104.certificate1259,MergedCutCells.Batch105.certificate1260],(3637570472078883113/1000000000000000000),none,(1/2),(53988376549835141/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid323 : certificate323.NumericValid := by decide +kernel
theorem cellsSound323 : ∀ c∈certificate323.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1257,MergedCutCells.Batch104.certificate1258,MergedCutCells.Batch104.certificate1259,MergedCutCells.Batch105.certificate1260], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1258,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.sound1259,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.sound1260,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric323 : ∀ c∈certificate323.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1257,MergedCutCells.Batch104.certificate1258,MergedCutCells.Batch104.certificate1259,MergedCutCells.Batch105.certificate1260], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1258,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch104.numericValid1259,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch105.numericValid1260,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid323 : ∀ c∈certificate323.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1257,MergedCutCells.Batch104.certificate1258,MergedCutCells.Batch104.certificate1259,MergedCutCells.Batch105.certificate1260], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches323 : ∀ c∈certificate323.cells, c.population=certificate323.population := by
  change ∀ c∈[MergedCutCells.Batch104.certificate1257,MergedCutCells.Batch104.certificate1258,MergedCutCells.Batch104.certificate1259,MergedCutCells.Batch105.certificate1260], c.population=PopulationCertificates.Batch010.certificate215
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers323 {x : ℝ} (hx : certificate323.interval.Contains x) : ∃ c∈certificate323.cells, c.region.interval.Contains x := rat_cut_group_covers certificate323 numericValid323 hx

end Cycle12.MergedCutGroups.Batch026
