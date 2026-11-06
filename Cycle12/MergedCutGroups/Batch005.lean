import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch002
import Cycle12.MergedCutCells.Batch013
import Cycle12.MergedCutCells.Batch014
import Cycle12.MergedCutCells.Batch015
import Cycle12.MergedCutCells.Batch016
import Cycle12.MergedCutCells.Batch017
import Cycle12.PopulationCertificates.Batch002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch005

def certificate60 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate40,PopulationCertificates.Batch002.certificate40,[MergedCutCells.Batch013.certificate163,MergedCutCells.Batch013.certificate164],(166482678987833373/250000000000000000),(some (1146081873/1000000000)),(1/2),(1739803596460271/8000000000000000),(some (251453389906555187/1000000000000000000)),(some (34578596283928039/500000000000000000))⟩
theorem numericValid60 : certificate60.NumericValid := by decide +kernel
theorem cellsSound60 : ∀ c∈certificate60.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch013.certificate163,MergedCutCells.Batch013.certificate164], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound164,List.forall_mem_nil _⟩⟩
theorem cellsNumeric60 : ∀ c∈certificate60.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch013.certificate163,MergedCutCells.Batch013.certificate164], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid163,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid164,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid60 : ∀ c∈certificate60.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch013.certificate163,MergedCutCells.Batch013.certificate164], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid21,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid21,List.forall_mem_nil _⟩⟩
theorem populationMatches60 : ∀ c∈certificate60.cells, c.population=certificate60.population := by
  change ∀ c∈[MergedCutCells.Batch013.certificate163,MergedCutCells.Batch013.certificate164], c.population=PopulationCertificates.Batch002.certificate40
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers60 {x : ℝ} (hx : certificate60.interval.Contains x) : ∃ c∈certificate60.cells, c.region.interval.Contains x := rat_cut_group_covers certificate60 numericValid60 hx

def certificate61 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate40,PopulationCertificates.Batch002.certificate40,[MergedCutCells.Batch013.certificate165,MergedCutCells.Batch013.certificate166,MergedCutCells.Batch013.certificate167,MergedCutCells.Batch014.certificate168,MergedCutCells.Batch014.certificate169,MergedCutCells.Batch014.certificate170],(1146081873/1000000000),none,(1/2),(12479887371907777/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid61 : certificate61.NumericValid := by decide +kernel
theorem cellsSound61 : ∀ c∈certificate61.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch013.certificate165,MergedCutCells.Batch013.certificate166,MergedCutCells.Batch013.certificate167,MergedCutCells.Batch014.certificate168,MergedCutCells.Batch014.certificate169,MergedCutCells.Batch014.certificate170], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound166,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound167,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound170,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric61 : ∀ c∈certificate61.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch013.certificate165,MergedCutCells.Batch013.certificate166,MergedCutCells.Batch013.certificate167,MergedCutCells.Batch014.certificate168,MergedCutCells.Batch014.certificate169,MergedCutCells.Batch014.certificate170], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid165,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid166,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid167,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid168,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid169,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid170,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid61 : ∀ c∈certificate61.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch013.certificate165,MergedCutCells.Batch013.certificate166,MergedCutCells.Batch013.certificate167,MergedCutCells.Batch014.certificate168,MergedCutCells.Batch014.certificate169,MergedCutCells.Batch014.certificate170], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches61 : ∀ c∈certificate61.cells, c.population=certificate61.population := by
  change ∀ c∈[MergedCutCells.Batch013.certificate165,MergedCutCells.Batch013.certificate166,MergedCutCells.Batch013.certificate167,MergedCutCells.Batch014.certificate168,MergedCutCells.Batch014.certificate169,MergedCutCells.Batch014.certificate170], c.population=PopulationCertificates.Batch002.certificate40
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers61 {x : ℝ} (hx : certificate61.interval.Contains x) : ∃ c∈certificate61.cells, c.region.interval.Contains x := rat_cut_group_covers certificate61 numericValid61 hx

def certificate62 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate41,PopulationCertificates.Batch002.certificate41,[MergedCutCells.Batch014.certificate171,MergedCutCells.Batch014.certificate172,MergedCutCells.Batch014.certificate173],(1786319061275095751/500000000000000000),none,(1/2),(37613055799023913/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid62 : certificate62.NumericValid := by decide +kernel
theorem cellsSound62 : ∀ c∈certificate62.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch014.certificate171,MergedCutCells.Batch014.certificate172,MergedCutCells.Batch014.certificate173], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound173,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric62 : ∀ c∈certificate62.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch014.certificate171,MergedCutCells.Batch014.certificate172,MergedCutCells.Batch014.certificate173], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid171,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid172,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid173,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid62 : ∀ c∈certificate62.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch014.certificate171,MergedCutCells.Batch014.certificate172,MergedCutCells.Batch014.certificate173], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches62 : ∀ c∈certificate62.cells, c.population=certificate62.population := by
  change ∀ c∈[MergedCutCells.Batch014.certificate171,MergedCutCells.Batch014.certificate172,MergedCutCells.Batch014.certificate173], c.population=PopulationCertificates.Batch002.certificate41
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers62 {x : ℝ} (hx : certificate62.interval.Contains x) : ∃ c∈certificate62.cells, c.region.interval.Contains x := rat_cut_group_covers certificate62 numericValid62 hx

def certificate63 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate42,PopulationCertificates.Batch002.certificate42,[MergedCutCells.Batch014.certificate174,MergedCutCells.Batch014.certificate175,MergedCutCells.Batch014.certificate176],(671563538905409761/1000000000000000000),(some (563262577/500000000)),(1/2),(41495133262577491/200000000000000000),(some (8338823837627741/31250000000000000)),(some (75182358000219201/1000000000000000000))⟩
theorem numericValid63 : certificate63.NumericValid := by decide +kernel
theorem cellsSound63 : ∀ c∈certificate63.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch014.certificate174,MergedCutCells.Batch014.certificate175,MergedCutCells.Batch014.certificate176], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound174,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound176,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric63 : ∀ c∈certificate63.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch014.certificate174,MergedCutCells.Batch014.certificate175,MergedCutCells.Batch014.certificate176], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid174,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid175,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid176,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid63 : ∀ c∈certificate63.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch014.certificate174,MergedCutCells.Batch014.certificate175,MergedCutCells.Batch014.certificate176], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid22,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid22,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid22,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches63 : ∀ c∈certificate63.cells, c.population=certificate63.population := by
  change ∀ c∈[MergedCutCells.Batch014.certificate174,MergedCutCells.Batch014.certificate175,MergedCutCells.Batch014.certificate176], c.population=PopulationCertificates.Batch002.certificate42
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers63 {x : ℝ} (hx : certificate63.interval.Contains x) : ∃ c∈certificate63.cells, c.region.interval.Contains x := rat_cut_group_covers certificate63 numericValid63 hx

def certificate64 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate42,PopulationCertificates.Batch002.certificate42,[MergedCutCells.Batch014.certificate177,MergedCutCells.Batch014.certificate178,MergedCutCells.Batch014.certificate179,MergedCutCells.Batch015.certificate180,MergedCutCells.Batch015.certificate181,MergedCutCells.Batch015.certificate182,MergedCutCells.Batch015.certificate183],(563262577/500000000),none,(1/2),(188083723925795713/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid64 : certificate64.NumericValid := by decide +kernel
theorem cellsSound64 : ∀ c∈certificate64.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch014.certificate177,MergedCutCells.Batch014.certificate178,MergedCutCells.Batch014.certificate179,MergedCutCells.Batch015.certificate180,MergedCutCells.Batch015.certificate181,MergedCutCells.Batch015.certificate182,MergedCutCells.Batch015.certificate183], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound178,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.sound179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound182,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound183,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric64 : ∀ c∈certificate64.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch014.certificate177,MergedCutCells.Batch014.certificate178,MergedCutCells.Batch014.certificate179,MergedCutCells.Batch015.certificate180,MergedCutCells.Batch015.certificate181,MergedCutCells.Batch015.certificate182,MergedCutCells.Batch015.certificate183], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid177,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid178,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch014.numericValid179,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid180,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid181,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid182,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid183,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid64 : ∀ c∈certificate64.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch014.certificate177,MergedCutCells.Batch014.certificate178,MergedCutCells.Batch014.certificate179,MergedCutCells.Batch015.certificate180,MergedCutCells.Batch015.certificate181,MergedCutCells.Batch015.certificate182,MergedCutCells.Batch015.certificate183], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches64 : ∀ c∈certificate64.cells, c.population=certificate64.population := by
  change ∀ c∈[MergedCutCells.Batch014.certificate177,MergedCutCells.Batch014.certificate178,MergedCutCells.Batch014.certificate179,MergedCutCells.Batch015.certificate180,MergedCutCells.Batch015.certificate181,MergedCutCells.Batch015.certificate182,MergedCutCells.Batch015.certificate183], c.population=PopulationCertificates.Batch002.certificate42
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers64 {x : ℝ} (hx : certificate64.interval.Contains x) : ∃ c∈certificate64.cells, c.region.interval.Contains x := rat_cut_group_covers certificate64 numericValid64 hx

def certificate65 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate43,PopulationCertificates.Batch002.certificate43,[MergedCutCells.Batch015.certificate184,MergedCutCells.Batch015.certificate185,MergedCutCells.Batch015.certificate186],(1808662218518331113/500000000000000000),none,(1/2),(204458615897048899/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid65 : certificate65.NumericValid := by decide +kernel
theorem cellsSound65 : ∀ c∈certificate65.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch015.certificate184,MergedCutCells.Batch015.certificate185,MergedCutCells.Batch015.certificate186], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound184,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound185,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound186,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric65 : ∀ c∈certificate65.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch015.certificate184,MergedCutCells.Batch015.certificate185,MergedCutCells.Batch015.certificate186], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid184,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid185,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid186,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid65 : ∀ c∈certificate65.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch015.certificate184,MergedCutCells.Batch015.certificate185,MergedCutCells.Batch015.certificate186], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches65 : ∀ c∈certificate65.cells, c.population=certificate65.population := by
  change ∀ c∈[MergedCutCells.Batch015.certificate184,MergedCutCells.Batch015.certificate185,MergedCutCells.Batch015.certificate186], c.population=PopulationCertificates.Batch002.certificate43
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers65 {x : ℝ} (hx : certificate65.interval.Contains x) : ∃ c∈certificate65.cells, c.region.interval.Contains x := rat_cut_group_covers certificate65 numericValid65 hx

def certificate66 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate44,PopulationCertificates.Batch002.certificate44,[MergedCutCells.Batch015.certificate187,MergedCutCells.Batch015.certificate188,MergedCutCells.Batch015.certificate189],(84968351296773707/125000000000000000),(some (138881539/125000000)),(1/2),(26174201189945717/125000000000000000),(some (141203640310960281/500000000000000000)),(some (20373925261785973/250000000000000000))⟩
theorem numericValid66 : certificate66.NumericValid := by decide +kernel
theorem cellsSound66 : ∀ c∈certificate66.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch015.certificate187,MergedCutCells.Batch015.certificate188,MergedCutCells.Batch015.certificate189], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound187,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound189,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric66 : ∀ c∈certificate66.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch015.certificate187,MergedCutCells.Batch015.certificate188,MergedCutCells.Batch015.certificate189], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid187,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid189,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid66 : ∀ c∈certificate66.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch015.certificate187,MergedCutCells.Batch015.certificate188,MergedCutCells.Batch015.certificate189], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid23,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid23,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid23,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches66 : ∀ c∈certificate66.cells, c.population=certificate66.population := by
  change ∀ c∈[MergedCutCells.Batch015.certificate187,MergedCutCells.Batch015.certificate188,MergedCutCells.Batch015.certificate189], c.population=PopulationCertificates.Batch002.certificate44
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers66 {x : ℝ} (hx : certificate66.interval.Contains x) : ∃ c∈certificate66.cells, c.region.interval.Contains x := rat_cut_group_covers certificate66 numericValid66 hx

def certificate67 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate44,PopulationCertificates.Batch002.certificate44,[MergedCutCells.Batch015.certificate190,MergedCutCells.Batch015.certificate191,MergedCutCells.Batch016.certificate192,MergedCutCells.Batch016.certificate193,MergedCutCells.Batch016.certificate194,MergedCutCells.Batch016.certificate195,MergedCutCells.Batch016.certificate196],(138881539/125000000),none,(1/2),(186231504310517993/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid67 : certificate67.NumericValid := by decide +kernel
theorem cellsSound67 : ∀ c∈certificate67.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch015.certificate190,MergedCutCells.Batch015.certificate191,MergedCutCells.Batch016.certificate192,MergedCutCells.Batch016.certificate193,MergedCutCells.Batch016.certificate194,MergedCutCells.Batch016.certificate195,MergedCutCells.Batch016.certificate196], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.sound191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound192,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound194,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound196,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric67 : ∀ c∈certificate67.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch015.certificate190,MergedCutCells.Batch015.certificate191,MergedCutCells.Batch016.certificate192,MergedCutCells.Batch016.certificate193,MergedCutCells.Batch016.certificate194,MergedCutCells.Batch016.certificate195,MergedCutCells.Batch016.certificate196], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid190,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch015.numericValid191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid192,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid194,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid196,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid67 : ∀ c∈certificate67.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch015.certificate190,MergedCutCells.Batch015.certificate191,MergedCutCells.Batch016.certificate192,MergedCutCells.Batch016.certificate193,MergedCutCells.Batch016.certificate194,MergedCutCells.Batch016.certificate195,MergedCutCells.Batch016.certificate196], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches67 : ∀ c∈certificate67.cells, c.population=certificate67.population := by
  change ∀ c∈[MergedCutCells.Batch015.certificate190,MergedCutCells.Batch015.certificate191,MergedCutCells.Batch016.certificate192,MergedCutCells.Batch016.certificate193,MergedCutCells.Batch016.certificate194,MergedCutCells.Batch016.certificate195,MergedCutCells.Batch016.certificate196], c.population=PopulationCertificates.Batch002.certificate44
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers67 {x : ℝ} (hx : certificate67.interval.Contains x) : ∃ c∈certificate67.cells, c.region.interval.Contains x := rat_cut_group_covers certificate67 numericValid67 hx

def certificate68 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate45,PopulationCertificates.Batch002.certificate45,[MergedCutCells.Batch016.certificate197,MergedCutCells.Batch016.certificate198,MergedCutCells.Batch016.certificate199,MergedCutCells.Batch016.certificate200],(353688061770049553/100000000000000000),none,(1/2),(78392402689872731/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid68 : certificate68.NumericValid := by decide +kernel
theorem cellsSound68 : ∀ c∈certificate68.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch016.certificate197,MergedCutCells.Batch016.certificate198,MergedCutCells.Batch016.certificate199,MergedCutCells.Batch016.certificate200], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound198,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound200,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric68 : ∀ c∈certificate68.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch016.certificate197,MergedCutCells.Batch016.certificate198,MergedCutCells.Batch016.certificate199,MergedCutCells.Batch016.certificate200], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid198,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid200,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid68 : ∀ c∈certificate68.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch016.certificate197,MergedCutCells.Batch016.certificate198,MergedCutCells.Batch016.certificate199,MergedCutCells.Batch016.certificate200], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches68 : ∀ c∈certificate68.cells, c.population=certificate68.population := by
  change ∀ c∈[MergedCutCells.Batch016.certificate197,MergedCutCells.Batch016.certificate198,MergedCutCells.Batch016.certificate199,MergedCutCells.Batch016.certificate200], c.population=PopulationCertificates.Batch002.certificate45
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers68 {x : ℝ} (hx : certificate68.interval.Contains x) : ∃ c∈certificate68.cells, c.region.interval.Contains x := rat_cut_group_covers certificate68 numericValid68 hx

def certificate69 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate46,PopulationCertificates.Batch002.certificate46,[MergedCutCells.Batch016.certificate201,MergedCutCells.Batch016.certificate202,MergedCutCells.Batch016.certificate203],(686475354414618681/1000000000000000000),(some (548242777/500000000)),(1/2),(201949848807311119/1000000000000000000),(some (74536112005407301/250000000000000000)),(some (22027643528860111/250000000000000000))⟩
theorem numericValid69 : certificate69.NumericValid := by decide +kernel
theorem cellsSound69 : ∀ c∈certificate69.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch016.certificate201,MergedCutCells.Batch016.certificate202,MergedCutCells.Batch016.certificate203], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound202,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.sound203,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric69 : ∀ c∈certificate69.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch016.certificate201,MergedCutCells.Batch016.certificate202,MergedCutCells.Batch016.certificate203], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid202,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch016.numericValid203,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid69 : ∀ c∈certificate69.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch016.certificate201,MergedCutCells.Batch016.certificate202,MergedCutCells.Batch016.certificate203], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid24,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid24,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid24,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches69 : ∀ c∈certificate69.cells, c.population=certificate69.population := by
  change ∀ c∈[MergedCutCells.Batch016.certificate201,MergedCutCells.Batch016.certificate202,MergedCutCells.Batch016.certificate203], c.population=PopulationCertificates.Batch002.certificate46
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers69 {x : ℝ} (hx : certificate69.interval.Contains x) : ∃ c∈certificate69.cells, c.region.interval.Contains x := rat_cut_group_covers certificate69 numericValid69 hx

def certificate70 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate46,PopulationCertificates.Batch002.certificate46,[MergedCutCells.Batch017.certificate204,MergedCutCells.Batch017.certificate205,MergedCutCells.Batch017.certificate206,MergedCutCells.Batch017.certificate207,MergedCutCells.Batch017.certificate208,MergedCutCells.Batch017.certificate209,MergedCutCells.Batch017.certificate210],(548242777/500000000),none,(1/2),(173875917617089447/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid70 : certificate70.NumericValid := by decide +kernel
theorem cellsSound70 : ∀ c∈certificate70.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch017.certificate204,MergedCutCells.Batch017.certificate205,MergedCutCells.Batch017.certificate206,MergedCutCells.Batch017.certificate207,MergedCutCells.Batch017.certificate208,MergedCutCells.Batch017.certificate209,MergedCutCells.Batch017.certificate210], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound205,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound206,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound208,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound209,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound210,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric70 : ∀ c∈certificate70.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch017.certificate204,MergedCutCells.Batch017.certificate205,MergedCutCells.Batch017.certificate206,MergedCutCells.Batch017.certificate207,MergedCutCells.Batch017.certificate208,MergedCutCells.Batch017.certificate209,MergedCutCells.Batch017.certificate210], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid205,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid206,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid208,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid209,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid210,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid70 : ∀ c∈certificate70.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch017.certificate204,MergedCutCells.Batch017.certificate205,MergedCutCells.Batch017.certificate206,MergedCutCells.Batch017.certificate207,MergedCutCells.Batch017.certificate208,MergedCutCells.Batch017.certificate209,MergedCutCells.Batch017.certificate210], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches70 : ∀ c∈certificate70.cells, c.population=certificate70.population := by
  change ∀ c∈[MergedCutCells.Batch017.certificate204,MergedCutCells.Batch017.certificate205,MergedCutCells.Batch017.certificate206,MergedCutCells.Batch017.certificate207,MergedCutCells.Batch017.certificate208,MergedCutCells.Batch017.certificate209,MergedCutCells.Batch017.certificate210], c.population=PopulationCertificates.Batch002.certificate46
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers70 {x : ℝ} (hx : certificate70.interval.Contains x) : ∃ c∈certificate70.cells, c.region.interval.Contains x := rat_cut_group_covers certificate70 numericValid70 hx

def certificate71 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate47,PopulationCertificates.Batch002.certificate47,[MergedCutCells.Batch017.certificate211,MergedCutCells.Batch017.certificate212,MergedCutCells.Batch017.certificate213,MergedCutCells.Batch017.certificate214],(3582377073644304293/1000000000000000000),none,(1/2),(347344854528507319/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid71 : certificate71.NumericValid := by decide +kernel
theorem cellsSound71 : ∀ c∈certificate71.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch017.certificate211,MergedCutCells.Batch017.certificate212,MergedCutCells.Batch017.certificate213,MergedCutCells.Batch017.certificate214], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound211,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound212,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound214,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric71 : ∀ c∈certificate71.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch017.certificate211,MergedCutCells.Batch017.certificate212,MergedCutCells.Batch017.certificate213,MergedCutCells.Batch017.certificate214], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid211,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid212,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid214,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid71 : ∀ c∈certificate71.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch017.certificate211,MergedCutCells.Batch017.certificate212,MergedCutCells.Batch017.certificate213,MergedCutCells.Batch017.certificate214], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches71 : ∀ c∈certificate71.cells, c.population=certificate71.population := by
  change ∀ c∈[MergedCutCells.Batch017.certificate211,MergedCutCells.Batch017.certificate212,MergedCutCells.Batch017.certificate213,MergedCutCells.Batch017.certificate214], c.population=PopulationCertificates.Batch002.certificate47
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers71 {x : ℝ} (hx : certificate71.interval.Contains x) : ∃ c∈certificate71.cells, c.region.interval.Contains x := rat_cut_group_covers certificate71 numericValid71 hx

end Cycle12.MergedCutGroups.Batch005
