import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch011
import Cycle12.MergedCutCells.Batch109
import Cycle12.MergedCutCells.Batch110
import Cycle12.MergedCutCells.Batch111
import Cycle12.MergedCutCells.Batch112
import Cycle12.PopulationCertificates.Batch011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch028

def certificate336 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate224,PopulationCertificates.Batch011.certificate224,[MergedCutCells.Batch109.certificate1308,MergedCutCells.Batch109.certificate1309,MergedCutCells.Batch109.certificate1310,MergedCutCells.Batch109.certificate1311,MergedCutCells.Batch109.certificate1312,MergedCutCells.Batch109.certificate1313,MergedCutCells.Batch109.certificate1314,MergedCutCells.Batch109.certificate1315],(850165604702613157/1000000000000000000),(some 64),(1/2),(5419366566424653/8000000000000000),(some (69314718055994531/100000000000000000)),(some (147164091751246659/100000000000000000))⟩
theorem numericValid336 : certificate336.NumericValid := by decide +kernel
theorem cellsSound336 : ∀ c∈certificate336.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1308,MergedCutCells.Batch109.certificate1309,MergedCutCells.Batch109.certificate1310,MergedCutCells.Batch109.certificate1311,MergedCutCells.Batch109.certificate1312,MergedCutCells.Batch109.certificate1313,MergedCutCells.Batch109.certificate1314,MergedCutCells.Batch109.certificate1315], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1308,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1311,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1312,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1313,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1314,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1315,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric336 : ∀ c∈certificate336.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1308,MergedCutCells.Batch109.certificate1309,MergedCutCells.Batch109.certificate1310,MergedCutCells.Batch109.certificate1311,MergedCutCells.Batch109.certificate1312,MergedCutCells.Batch109.certificate1313,MergedCutCells.Batch109.certificate1314,MergedCutCells.Batch109.certificate1315], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1308,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1309,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1310,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1311,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1312,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1313,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1314,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1315,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid336 : ∀ c∈certificate336.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1308,MergedCutCells.Batch109.certificate1309,MergedCutCells.Batch109.certificate1310,MergedCutCells.Batch109.certificate1311,MergedCutCells.Batch109.certificate1312,MergedCutCells.Batch109.certificate1313,MergedCutCells.Batch109.certificate1314,MergedCutCells.Batch109.certificate1315], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid113,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid113,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid113,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid113,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid113,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid113,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid113,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid113,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches336 : ∀ c∈certificate336.cells, c.population=certificate336.population := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1308,MergedCutCells.Batch109.certificate1309,MergedCutCells.Batch109.certificate1310,MergedCutCells.Batch109.certificate1311,MergedCutCells.Batch109.certificate1312,MergedCutCells.Batch109.certificate1313,MergedCutCells.Batch109.certificate1314,MergedCutCells.Batch109.certificate1315], c.population=PopulationCertificates.Batch011.certificate224
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers336 {x : ℝ} (hx : certificate336.interval.Contains x) : ∃ c∈certificate336.cells, c.region.interval.Contains x := rat_cut_group_covers certificate336 numericValid336 hx

def certificate337 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate224,PopulationCertificates.Batch011.certificate224,[MergedCutCells.Batch109.certificate1316],64,none,(1/2),(79943916415643109/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid337 : certificate337.NumericValid := by decide +kernel
theorem cellsSound337 : ∀ c∈certificate337.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1316], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1316,List.forall_mem_nil _⟩
theorem cellsNumeric337 : ∀ c∈certificate337.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1316], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1316,List.forall_mem_nil _⟩
theorem cellsEntropyValid337 : ∀ c∈certificate337.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1316], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches337 : ∀ c∈certificate337.cells, c.population=certificate337.population := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1316], c.population=PopulationCertificates.Batch011.certificate224
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers337 {x : ℝ} (hx : certificate337.interval.Contains x) : ∃ c∈certificate337.cells, c.region.interval.Contains x := rat_cut_group_covers certificate337 numericValid337 hx

def certificate338 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate225,PopulationCertificates.Batch011.certificate225,[MergedCutCells.Batch109.certificate1317,MergedCutCells.Batch109.certificate1318,MergedCutCells.Batch109.certificate1319,MergedCutCells.Batch110.certificate1320],(3570149614151003697/1000000000000000000),none,(1/2),(825746934871827667/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid338 : certificate338.NumericValid := by decide +kernel
theorem cellsSound338 : ∀ c∈certificate338.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1317,MergedCutCells.Batch109.certificate1318,MergedCutCells.Batch109.certificate1319,MergedCutCells.Batch110.certificate1320], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1317,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1318,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.sound1319,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1320,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric338 : ∀ c∈certificate338.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1317,MergedCutCells.Batch109.certificate1318,MergedCutCells.Batch109.certificate1319,MergedCutCells.Batch110.certificate1320], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1317,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1318,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch109.numericValid1319,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1320,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid338 : ∀ c∈certificate338.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1317,MergedCutCells.Batch109.certificate1318,MergedCutCells.Batch109.certificate1319,MergedCutCells.Batch110.certificate1320], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches338 : ∀ c∈certificate338.cells, c.population=certificate338.population := by
  change ∀ c∈[MergedCutCells.Batch109.certificate1317,MergedCutCells.Batch109.certificate1318,MergedCutCells.Batch109.certificate1319,MergedCutCells.Batch110.certificate1320], c.population=PopulationCertificates.Batch011.certificate225
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers338 {x : ℝ} (hx : certificate338.interval.Contains x) : ∃ c∈certificate338.cells, c.region.interval.Contains x := rat_cut_group_covers certificate338 numericValid338 hx

def certificate339 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate226,PopulationCertificates.Batch011.certificate226,[MergedCutCells.Batch110.certificate1321,MergedCutCells.Batch110.certificate1322,MergedCutCells.Batch110.certificate1323,MergedCutCells.Batch110.certificate1324,MergedCutCells.Batch110.certificate1325,MergedCutCells.Batch110.certificate1326],(108376035377524809/125000000000000000),(some 64),(1/2),(85494788489290877/125000000000000000),(some (69314718055994531/100000000000000000)),(some (368413679019128993/250000000000000000))⟩
theorem numericValid339 : certificate339.NumericValid := by decide +kernel
theorem cellsSound339 : ∀ c∈certificate339.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1321,MergedCutCells.Batch110.certificate1322,MergedCutCells.Batch110.certificate1323,MergedCutCells.Batch110.certificate1324,MergedCutCells.Batch110.certificate1325,MergedCutCells.Batch110.certificate1326], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1321,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1323,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1324,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1325,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1326,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric339 : ∀ c∈certificate339.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1321,MergedCutCells.Batch110.certificate1322,MergedCutCells.Batch110.certificate1323,MergedCutCells.Batch110.certificate1324,MergedCutCells.Batch110.certificate1325,MergedCutCells.Batch110.certificate1326], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1321,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1322,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1323,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1324,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1325,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1326,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid339 : ∀ c∈certificate339.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1321,MergedCutCells.Batch110.certificate1322,MergedCutCells.Batch110.certificate1323,MergedCutCells.Batch110.certificate1324,MergedCutCells.Batch110.certificate1325,MergedCutCells.Batch110.certificate1326], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid114,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid114,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid114,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid114,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid114,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid114,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches339 : ∀ c∈certificate339.cells, c.population=certificate339.population := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1321,MergedCutCells.Batch110.certificate1322,MergedCutCells.Batch110.certificate1323,MergedCutCells.Batch110.certificate1324,MergedCutCells.Batch110.certificate1325,MergedCutCells.Batch110.certificate1326], c.population=PopulationCertificates.Batch011.certificate226
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers339 {x : ℝ} (hx : certificate339.interval.Contains x) : ∃ c∈certificate339.cells, c.region.interval.Contains x := rat_cut_group_covers certificate339 numericValid339 hx

def certificate340 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate226,PopulationCertificates.Batch011.certificate226,[MergedCutCells.Batch110.certificate1327],64,none,(1/2),(802526245589518381/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid340 : certificate340.NumericValid := by decide +kernel
theorem cellsSound340 : ∀ c∈certificate340.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1327], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1327,List.forall_mem_nil _⟩
theorem cellsNumeric340 : ∀ c∈certificate340.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1327], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1327,List.forall_mem_nil _⟩
theorem cellsEntropyValid340 : ∀ c∈certificate340.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1327], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches340 : ∀ c∈certificate340.cells, c.population=certificate340.population := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1327], c.population=PopulationCertificates.Batch011.certificate226
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers340 {x : ℝ} (hx : certificate340.interval.Contains x) : ∃ c∈certificate340.cells, c.region.interval.Contains x := rat_cut_group_covers certificate340 numericValid340 hx

def certificate341 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate227,PopulationCertificates.Batch011.certificate227,[MergedCutCells.Batch110.certificate1328,MergedCutCells.Batch110.certificate1329,MergedCutCells.Batch110.certificate1330,MergedCutCells.Batch110.certificate1331],(3579672135622291863/1000000000000000000),none,(1/2),(853310512291898803/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid341 : certificate341.NumericValid := by decide +kernel
theorem cellsSound341 : ∀ c∈certificate341.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1328,MergedCutCells.Batch110.certificate1329,MergedCutCells.Batch110.certificate1330,MergedCutCells.Batch110.certificate1331], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1328,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1329,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.sound1331,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric341 : ∀ c∈certificate341.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1328,MergedCutCells.Batch110.certificate1329,MergedCutCells.Batch110.certificate1330,MergedCutCells.Batch110.certificate1331], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1328,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1329,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1330,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch110.numericValid1331,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid341 : ∀ c∈certificate341.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1328,MergedCutCells.Batch110.certificate1329,MergedCutCells.Batch110.certificate1330,MergedCutCells.Batch110.certificate1331], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches341 : ∀ c∈certificate341.cells, c.population=certificate341.population := by
  change ∀ c∈[MergedCutCells.Batch110.certificate1328,MergedCutCells.Batch110.certificate1329,MergedCutCells.Batch110.certificate1330,MergedCutCells.Batch110.certificate1331], c.population=PopulationCertificates.Batch011.certificate227
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers341 {x : ℝ} (hx : certificate341.interval.Contains x) : ∃ c∈certificate341.cells, c.region.interval.Contains x := rat_cut_group_covers certificate341 numericValid341 hx

def certificate342 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate228,PopulationCertificates.Batch011.certificate228,[MergedCutCells.Batch111.certificate1332,MergedCutCells.Batch111.certificate1333,MergedCutCells.Batch111.certificate1334,MergedCutCells.Batch111.certificate1335,MergedCutCells.Batch111.certificate1336,MergedCutCells.Batch111.certificate1337],(440166756006258867/500000000000000000),(some 64),(1/2),(172111690081302747/250000000000000000),(some (69314718055994531/100000000000000000)),(some (368979443809480281/250000000000000000))⟩
theorem numericValid342 : certificate342.NumericValid := by decide +kernel
theorem cellsSound342 : ∀ c∈certificate342.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1332,MergedCutCells.Batch111.certificate1333,MergedCutCells.Batch111.certificate1334,MergedCutCells.Batch111.certificate1335,MergedCutCells.Batch111.certificate1336,MergedCutCells.Batch111.certificate1337], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1332,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1333,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1336,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1337,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric342 : ∀ c∈certificate342.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1332,MergedCutCells.Batch111.certificate1333,MergedCutCells.Batch111.certificate1334,MergedCutCells.Batch111.certificate1335,MergedCutCells.Batch111.certificate1336,MergedCutCells.Batch111.certificate1337], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1332,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1333,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1334,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1335,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1336,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1337,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid342 : ∀ c∈certificate342.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1332,MergedCutCells.Batch111.certificate1333,MergedCutCells.Batch111.certificate1334,MergedCutCells.Batch111.certificate1335,MergedCutCells.Batch111.certificate1336,MergedCutCells.Batch111.certificate1337], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid115,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid115,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid115,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid115,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid115,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid115,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches342 : ∀ c∈certificate342.cells, c.population=certificate342.population := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1332,MergedCutCells.Batch111.certificate1333,MergedCutCells.Batch111.certificate1334,MergedCutCells.Batch111.certificate1335,MergedCutCells.Batch111.certificate1336,MergedCutCells.Batch111.certificate1337], c.population=PopulationCertificates.Batch011.certificate228
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers342 {x : ℝ} (hx : certificate342.interval.Contains x) : ∃ c∈certificate342.cells, c.region.interval.Contains x := rat_cut_group_covers certificate342 numericValid342 hx

def certificate343 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate228,PopulationCertificates.Batch011.certificate228,[MergedCutCells.Batch111.certificate1338],64,none,(1/2),(401037365893948113/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid343 : certificate343.NumericValid := by decide +kernel
theorem cellsSound343 : ∀ c∈certificate343.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1338], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1338,List.forall_mem_nil _⟩
theorem cellsNumeric343 : ∀ c∈certificate343.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1338], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1338,List.forall_mem_nil _⟩
theorem cellsEntropyValid343 : ∀ c∈certificate343.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1338], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches343 : ∀ c∈certificate343.cells, c.population=certificate343.population := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1338], c.population=PopulationCertificates.Batch011.certificate228
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers343 {x : ℝ} (hx : certificate343.interval.Contains x) : ∃ c∈certificate343.cells, c.region.interval.Contains x := rat_cut_group_covers certificate343 numericValid343 hx

def certificate344 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate229,PopulationCertificates.Batch011.certificate229,[MergedCutCells.Batch111.certificate1339,MergedCutCells.Batch111.certificate1340,MergedCutCells.Batch111.certificate1341],(3580410893889384427/1000000000000000000),none,(1/2),(429865284548378539/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid344 : certificate344.NumericValid := by decide +kernel
theorem cellsSound344 : ∀ c∈certificate344.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1339,MergedCutCells.Batch111.certificate1340,MergedCutCells.Batch111.certificate1341], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1339,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1341,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric344 : ∀ c∈certificate344.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1339,MergedCutCells.Batch111.certificate1340,MergedCutCells.Batch111.certificate1341], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1339,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1340,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1341,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid344 : ∀ c∈certificate344.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1339,MergedCutCells.Batch111.certificate1340,MergedCutCells.Batch111.certificate1341], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches344 : ∀ c∈certificate344.cells, c.population=certificate344.population := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1339,MergedCutCells.Batch111.certificate1340,MergedCutCells.Batch111.certificate1341], c.population=PopulationCertificates.Batch011.certificate229
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers344 {x : ℝ} (hx : certificate344.interval.Contains x) : ∃ c∈certificate344.cells, c.region.interval.Contains x := rat_cut_group_covers certificate344 numericValid344 hx

def certificate345 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate230,PopulationCertificates.Batch011.certificate230,[MergedCutCells.Batch111.certificate1342,MergedCutCells.Batch111.certificate1343,MergedCutCells.Batch112.certificate1344,MergedCutCells.Batch112.certificate1345,MergedCutCells.Batch112.certificate1346,MergedCutCells.Batch112.certificate1347,MergedCutCells.Batch112.certificate1348,MergedCutCells.Batch112.certificate1349],(850165584204900373/1000000000000000000),(some 64),(1/2),(701770067978069059/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (737849288326602389/500000000000000000))⟩
theorem numericValid345 : certificate345.NumericValid := by decide +kernel
theorem cellsSound345 : ∀ c∈certificate345.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1342,MergedCutCells.Batch111.certificate1343,MergedCutCells.Batch112.certificate1344,MergedCutCells.Batch112.certificate1345,MergedCutCells.Batch112.certificate1346,MergedCutCells.Batch112.certificate1347,MergedCutCells.Batch112.certificate1348,MergedCutCells.Batch112.certificate1349], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1342,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.sound1343,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1344,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1345,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1346,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1348,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1349,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric345 : ∀ c∈certificate345.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1342,MergedCutCells.Batch111.certificate1343,MergedCutCells.Batch112.certificate1344,MergedCutCells.Batch112.certificate1345,MergedCutCells.Batch112.certificate1346,MergedCutCells.Batch112.certificate1347,MergedCutCells.Batch112.certificate1348,MergedCutCells.Batch112.certificate1349], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1342,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch111.numericValid1343,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1344,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1345,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1346,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1347,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1348,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1349,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid345 : ∀ c∈certificate345.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1342,MergedCutCells.Batch111.certificate1343,MergedCutCells.Batch112.certificate1344,MergedCutCells.Batch112.certificate1345,MergedCutCells.Batch112.certificate1346,MergedCutCells.Batch112.certificate1347,MergedCutCells.Batch112.certificate1348,MergedCutCells.Batch112.certificate1349], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid116,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid116,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid116,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid116,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid116,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid116,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid116,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy005.valid116,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches345 : ∀ c∈certificate345.cells, c.population=certificate345.population := by
  change ∀ c∈[MergedCutCells.Batch111.certificate1342,MergedCutCells.Batch111.certificate1343,MergedCutCells.Batch112.certificate1344,MergedCutCells.Batch112.certificate1345,MergedCutCells.Batch112.certificate1346,MergedCutCells.Batch112.certificate1347,MergedCutCells.Batch112.certificate1348,MergedCutCells.Batch112.certificate1349], c.population=PopulationCertificates.Batch011.certificate230
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers345 {x : ℝ} (hx : certificate345.interval.Contains x) : ∃ c∈certificate345.cells, c.region.interval.Contains x := rat_cut_group_covers certificate345 numericValid345 hx

def certificate346 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate230,PopulationCertificates.Batch011.certificate230,[MergedCutCells.Batch112.certificate1350],64,none,(1/2),(827811834395426551/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid346 : certificate346.NumericValid := by decide +kernel
theorem cellsSound346 : ∀ c∈certificate346.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1350], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1350,List.forall_mem_nil _⟩
theorem cellsNumeric346 : ∀ c∈certificate346.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1350], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1350,List.forall_mem_nil _⟩
theorem cellsEntropyValid346 : ∀ c∈certificate346.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1350], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches346 : ∀ c∈certificate346.cells, c.population=certificate346.population := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1350], c.population=PopulationCertificates.Batch011.certificate230
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers346 {x : ℝ} (hx : certificate346.interval.Contains x) : ∃ c∈certificate346.cells, c.region.interval.Contains x := rat_cut_group_covers certificate346 numericValid346 hx

def certificate347 : RatCutGroup := ⟨GeometryCertificates.Batch011.certificate231,PopulationCertificates.Batch011.certificate231,[MergedCutCells.Batch112.certificate1351,MergedCutCells.Batch112.certificate1352,MergedCutCells.Batch112.certificate1353],(1789857992530305113/500000000000000000),none,(1/2),(21530329676179617/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid347 : certificate347.NumericValid := by decide +kernel
theorem cellsSound347 : ∀ c∈certificate347.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1351,MergedCutCells.Batch112.certificate1352,MergedCutCells.Batch112.certificate1353], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1352,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.sound1353,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric347 : ∀ c∈certificate347.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1351,MergedCutCells.Batch112.certificate1352,MergedCutCells.Batch112.certificate1353], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1351,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1352,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch112.numericValid1353,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid347 : ∀ c∈certificate347.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1351,MergedCutCells.Batch112.certificate1352,MergedCutCells.Batch112.certificate1353], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches347 : ∀ c∈certificate347.cells, c.population=certificate347.population := by
  change ∀ c∈[MergedCutCells.Batch112.certificate1351,MergedCutCells.Batch112.certificate1352,MergedCutCells.Batch112.certificate1353], c.population=PopulationCertificates.Batch011.certificate231
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers347 {x : ℝ} (hx : certificate347.interval.Contains x) : ∃ c∈certificate347.cells, c.region.interval.Contains x := rat_cut_group_covers certificate347 numericValid347 hx

end Cycle12.MergedCutGroups.Batch028
