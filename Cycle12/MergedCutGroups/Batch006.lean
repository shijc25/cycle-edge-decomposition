import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch002
import Cycle12.MergedCutCells.Batch017
import Cycle12.MergedCutCells.Batch018
import Cycle12.MergedCutCells.Batch019
import Cycle12.MergedCutCells.Batch020
import Cycle12.MergedCutCells.Batch021
import Cycle12.PopulationCertificates.Batch002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch006

def certificate72 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate48,PopulationCertificates.Batch002.certificate48,[MergedCutCells.Batch017.certificate215,MergedCutCells.Batch018.certificate216,MergedCutCells.Batch018.certificate217],(348885252251275369/500000000000000000),(some (21765677/20000000)),(1/2),(208288835515625519/1000000000000000000),(some (313833070917997273/1000000000000000000)),(some (94945537311997371/1000000000000000000))⟩
theorem numericValid72 : certificate72.NumericValid := by decide +kernel
theorem cellsSound72 : ∀ c∈certificate72.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch017.certificate215,MergedCutCells.Batch018.certificate216,MergedCutCells.Batch018.certificate217], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.sound215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound216,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound217,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric72 : ∀ c∈certificate72.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch017.certificate215,MergedCutCells.Batch018.certificate216,MergedCutCells.Batch018.certificate217], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch017.numericValid215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid216,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid217,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid72 : ∀ c∈certificate72.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch017.certificate215,MergedCutCells.Batch018.certificate216,MergedCutCells.Batch018.certificate217], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid25,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid25,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid25,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches72 : ∀ c∈certificate72.cells, c.population=certificate72.population := by
  change ∀ c∈[MergedCutCells.Batch017.certificate215,MergedCutCells.Batch018.certificate216,MergedCutCells.Batch018.certificate217], c.population=PopulationCertificates.Batch002.certificate48
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers72 {x : ℝ} (hx : certificate72.interval.Contains x) : ∃ c∈certificate72.cells, c.region.interval.Contains x := rat_cut_group_covers certificate72 numericValid72 hx

def certificate73 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate48,PopulationCertificates.Batch002.certificate48,[MergedCutCells.Batch018.certificate218,MergedCutCells.Batch018.certificate219,MergedCutCells.Batch018.certificate220,MergedCutCells.Batch018.certificate221,MergedCutCells.Batch018.certificate222,MergedCutCells.Batch018.certificate223],(21765677/20000000),none,(1/2),(6380302063819423/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid73 : certificate73.NumericValid := by decide +kernel
theorem cellsSound73 : ∀ c∈certificate73.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch018.certificate218,MergedCutCells.Batch018.certificate219,MergedCutCells.Batch018.certificate220,MergedCutCells.Batch018.certificate221,MergedCutCells.Batch018.certificate222,MergedCutCells.Batch018.certificate223], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound218,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound220,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound221,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound222,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound223,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric73 : ∀ c∈certificate73.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch018.certificate218,MergedCutCells.Batch018.certificate219,MergedCutCells.Batch018.certificate220,MergedCutCells.Batch018.certificate221,MergedCutCells.Batch018.certificate222,MergedCutCells.Batch018.certificate223], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid218,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid219,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid220,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid221,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid222,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid223,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid73 : ∀ c∈certificate73.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch018.certificate218,MergedCutCells.Batch018.certificate219,MergedCutCells.Batch018.certificate220,MergedCutCells.Batch018.certificate221,MergedCutCells.Batch018.certificate222,MergedCutCells.Batch018.certificate223], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches73 : ∀ c∈certificate73.cells, c.population=certificate73.population := by
  change ∀ c∈[MergedCutCells.Batch018.certificate218,MergedCutCells.Batch018.certificate219,MergedCutCells.Batch018.certificate220,MergedCutCells.Batch018.certificate221,MergedCutCells.Batch018.certificate222,MergedCutCells.Batch018.certificate223], c.population=PopulationCertificates.Batch002.certificate48
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers73 {x : ℝ} (hx : certificate73.interval.Contains x) : ∃ c∈certificate73.cells, c.region.interval.Contains x := rat_cut_group_covers certificate73 numericValid73 hx

def certificate74 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate49,PopulationCertificates.Batch002.certificate49,[MergedCutCells.Batch018.certificate224,MergedCutCells.Batch018.certificate225,MergedCutCells.Batch018.certificate226],(181454593129484529/50000000000000000),none,(1/2),(381842512240743703/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid74 : certificate74.NumericValid := by decide +kernel
theorem cellsSound74 : ∀ c∈certificate74.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch018.certificate224,MergedCutCells.Batch018.certificate225,MergedCutCells.Batch018.certificate226], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound225,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound226,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric74 : ∀ c∈certificate74.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch018.certificate224,MergedCutCells.Batch018.certificate225,MergedCutCells.Batch018.certificate226], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid224,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid225,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid226,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid74 : ∀ c∈certificate74.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch018.certificate224,MergedCutCells.Batch018.certificate225,MergedCutCells.Batch018.certificate226], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches74 : ∀ c∈certificate74.cells, c.population=certificate74.population := by
  change ∀ c∈[MergedCutCells.Batch018.certificate224,MergedCutCells.Batch018.certificate225,MergedCutCells.Batch018.certificate226], c.population=PopulationCertificates.Batch002.certificate49
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers74 {x : ℝ} (hx : certificate74.interval.Contains x) : ∃ c∈certificate74.cells, c.region.interval.Contains x := rat_cut_group_covers certificate74 numericValid74 hx

def certificate75 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate50,PopulationCertificates.Batch002.certificate50,[MergedCutCells.Batch018.certificate227,MergedCutCells.Batch019.certificate228,MergedCutCells.Batch019.certificate229],(2725666031449963/3906250000000000),(some (135707273/125000000)),(1/2),(4614971663858963/25000000000000000),(some (3302252846903657/10000000000000000)),(some (102354284405087273/1000000000000000000))⟩
theorem numericValid75 : certificate75.NumericValid := by decide +kernel
theorem cellsSound75 : ∀ c∈certificate75.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch018.certificate227,MergedCutCells.Batch019.certificate228,MergedCutCells.Batch019.certificate229], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.sound227,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound228,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound229,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric75 : ∀ c∈certificate75.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch018.certificate227,MergedCutCells.Batch019.certificate228,MergedCutCells.Batch019.certificate229], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch018.numericValid227,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid228,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid229,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid75 : ∀ c∈certificate75.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch018.certificate227,MergedCutCells.Batch019.certificate228,MergedCutCells.Batch019.certificate229], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid26,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid26,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid26,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches75 : ∀ c∈certificate75.cells, c.population=certificate75.population := by
  change ∀ c∈[MergedCutCells.Batch018.certificate227,MergedCutCells.Batch019.certificate228,MergedCutCells.Batch019.certificate229], c.population=PopulationCertificates.Batch002.certificate50
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers75 {x : ℝ} (hx : certificate75.interval.Contains x) : ∃ c∈certificate75.cells, c.region.interval.Contains x := rat_cut_group_covers certificate75 numericValid75 hx

def certificate76 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate50,PopulationCertificates.Batch002.certificate50,[MergedCutCells.Batch019.certificate230,MergedCutCells.Batch019.certificate231,MergedCutCells.Batch019.certificate232,MergedCutCells.Batch019.certificate233,MergedCutCells.Batch019.certificate234,MergedCutCells.Batch019.certificate235],(135707273/125000000),none,(1/2),(79438795534172033/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid76 : certificate76.NumericValid := by decide +kernel
theorem cellsSound76 : ∀ c∈certificate76.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch019.certificate230,MergedCutCells.Batch019.certificate231,MergedCutCells.Batch019.certificate232,MergedCutCells.Batch019.certificate233,MergedCutCells.Batch019.certificate234,MergedCutCells.Batch019.certificate235], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound231,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound232,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound233,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound234,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound235,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric76 : ∀ c∈certificate76.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch019.certificate230,MergedCutCells.Batch019.certificate231,MergedCutCells.Batch019.certificate232,MergedCutCells.Batch019.certificate233,MergedCutCells.Batch019.certificate234,MergedCutCells.Batch019.certificate235], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid230,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid231,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid232,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid233,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid234,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid235,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid76 : ∀ c∈certificate76.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch019.certificate230,MergedCutCells.Batch019.certificate231,MergedCutCells.Batch019.certificate232,MergedCutCells.Batch019.certificate233,MergedCutCells.Batch019.certificate234,MergedCutCells.Batch019.certificate235], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches76 : ∀ c∈certificate76.cells, c.population=certificate76.population := by
  change ∀ c∈[MergedCutCells.Batch019.certificate230,MergedCutCells.Batch019.certificate231,MergedCutCells.Batch019.certificate232,MergedCutCells.Batch019.certificate233,MergedCutCells.Batch019.certificate234,MergedCutCells.Batch019.certificate235], c.population=PopulationCertificates.Batch002.certificate50
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers76 {x : ℝ} (hx : certificate76.interval.Contains x) : ∃ c∈certificate76.cells, c.region.interval.Contains x := rat_cut_group_covers certificate76 numericValid76 hx

def certificate77 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate51,PopulationCertificates.Batch002.certificate51,[MergedCutCells.Batch019.certificate236,MergedCutCells.Batch019.certificate237,MergedCutCells.Batch019.certificate238],(1830732875332963701/500000000000000000),none,(1/2),(26024527764297869/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid77 : certificate77.NumericValid := by decide +kernel
theorem cellsSound77 : ∀ c∈certificate77.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch019.certificate236,MergedCutCells.Batch019.certificate237,MergedCutCells.Batch019.certificate238], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound237,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound238,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric77 : ∀ c∈certificate77.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch019.certificate236,MergedCutCells.Batch019.certificate237,MergedCutCells.Batch019.certificate238], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid236,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid237,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid238,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid77 : ∀ c∈certificate77.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch019.certificate236,MergedCutCells.Batch019.certificate237,MergedCutCells.Batch019.certificate238], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches77 : ∀ c∈certificate77.cells, c.population=certificate77.population := by
  change ∀ c∈[MergedCutCells.Batch019.certificate236,MergedCutCells.Batch019.certificate237,MergedCutCells.Batch019.certificate238], c.population=PopulationCertificates.Batch002.certificate51
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers77 {x : ℝ} (hx : certificate77.interval.Contains x) : ∃ c∈certificate77.cells, c.region.interval.Contains x := rat_cut_group_covers certificate77 numericValid77 hx

def certificate78 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate52,PopulationCertificates.Batch002.certificate52,[MergedCutCells.Batch019.certificate239,MergedCutCells.Batch020.certificate240,MergedCutCells.Batch020.certificate241],(141221297206928463/200000000000000000),(some (536619927/500000000)),(1/2),(7533458439528283/40000000000000000),(some (43219196224814703/125000000000000000)),(some (54817985672925693/500000000000000000))⟩
theorem numericValid78 : certificate78.NumericValid := by decide +kernel
theorem cellsSound78 : ∀ c∈certificate78.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch019.certificate239,MergedCutCells.Batch020.certificate240,MergedCutCells.Batch020.certificate241], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.sound239,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound241,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric78 : ∀ c∈certificate78.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch019.certificate239,MergedCutCells.Batch020.certificate240,MergedCutCells.Batch020.certificate241], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch019.numericValid239,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid240,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid241,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid78 : ∀ c∈certificate78.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch019.certificate239,MergedCutCells.Batch020.certificate240,MergedCutCells.Batch020.certificate241], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid27,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid27,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid27,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches78 : ∀ c∈certificate78.cells, c.population=certificate78.population := by
  change ∀ c∈[MergedCutCells.Batch019.certificate239,MergedCutCells.Batch020.certificate240,MergedCutCells.Batch020.certificate241], c.population=PopulationCertificates.Batch002.certificate52
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers78 {x : ℝ} (hx : certificate78.interval.Contains x) : ∃ c∈certificate78.cells, c.region.interval.Contains x := rat_cut_group_covers certificate78 numericValid78 hx

def certificate79 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate52,PopulationCertificates.Batch002.certificate52,[MergedCutCells.Batch020.certificate242,MergedCutCells.Batch020.certificate243,MergedCutCells.Batch020.certificate244,MergedCutCells.Batch020.certificate245,MergedCutCells.Batch020.certificate246,MergedCutCells.Batch020.certificate247],(536619927/500000000),none,(1/2),(31281535819581349/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid79 : certificate79.NumericValid := by decide +kernel
theorem cellsSound79 : ∀ c∈certificate79.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch020.certificate242,MergedCutCells.Batch020.certificate243,MergedCutCells.Batch020.certificate244,MergedCutCells.Batch020.certificate245,MergedCutCells.Batch020.certificate246,MergedCutCells.Batch020.certificate247], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound243,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound244,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound245,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound247,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric79 : ∀ c∈certificate79.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch020.certificate242,MergedCutCells.Batch020.certificate243,MergedCutCells.Batch020.certificate244,MergedCutCells.Batch020.certificate245,MergedCutCells.Batch020.certificate246,MergedCutCells.Batch020.certificate247], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid242,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid243,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid244,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid245,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid246,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid247,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid79 : ∀ c∈certificate79.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch020.certificate242,MergedCutCells.Batch020.certificate243,MergedCutCells.Batch020.certificate244,MergedCutCells.Batch020.certificate245,MergedCutCells.Batch020.certificate246,MergedCutCells.Batch020.certificate247], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches79 : ∀ c∈certificate79.cells, c.population=certificate79.population := by
  change ∀ c∈[MergedCutCells.Batch020.certificate242,MergedCutCells.Batch020.certificate243,MergedCutCells.Batch020.certificate244,MergedCutCells.Batch020.certificate245,MergedCutCells.Batch020.certificate246,MergedCutCells.Batch020.certificate247], c.population=PopulationCertificates.Batch002.certificate52
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers79 {x : ℝ} (hx : certificate79.interval.Contains x) : ∃ c∈certificate79.cells, c.region.interval.Contains x := rat_cut_group_covers certificate79 numericValid79 hx

def certificate80 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate53,PopulationCertificates.Batch002.certificate53,[MergedCutCells.Batch020.certificate248,MergedCutCells.Batch020.certificate249,MergedCutCells.Batch020.certificate250],(3694811182409305561/1000000000000000000),none,(1/2),(451416333140384861/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid80 : certificate80.NumericValid := by decide +kernel
theorem cellsSound80 : ∀ c∈certificate80.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch020.certificate248,MergedCutCells.Batch020.certificate249,MergedCutCells.Batch020.certificate250], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound248,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound250,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric80 : ∀ c∈certificate80.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch020.certificate248,MergedCutCells.Batch020.certificate249,MergedCutCells.Batch020.certificate250], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid248,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid249,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid250,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid80 : ∀ c∈certificate80.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch020.certificate248,MergedCutCells.Batch020.certificate249,MergedCutCells.Batch020.certificate250], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches80 : ∀ c∈certificate80.cells, c.population=certificate80.population := by
  change ∀ c∈[MergedCutCells.Batch020.certificate248,MergedCutCells.Batch020.certificate249,MergedCutCells.Batch020.certificate250], c.population=PopulationCertificates.Batch002.certificate53
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers80 {x : ℝ} (hx : certificate80.interval.Contains x) : ∃ c∈certificate80.cells, c.region.interval.Contains x := rat_cut_group_covers certificate80 numericValid80 hx

def certificate81 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate54,PopulationCertificates.Batch002.certificate54,[MergedCutCells.Batch020.certificate251,MergedCutCells.Batch021.certificate252,MergedCutCells.Batch021.certificate253],(710899008604598927/1000000000000000000),(some (1053615059/1000000000)),(1/2),(88480856787155943/500000000000000000),(some (360880775385888979/1000000000000000000)),(some (116988125377074891/1000000000000000000))⟩
theorem numericValid81 : certificate81.NumericValid := by decide +kernel
theorem cellsSound81 : ∀ c∈certificate81.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch020.certificate251,MergedCutCells.Batch021.certificate252,MergedCutCells.Batch021.certificate253], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.sound251,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound252,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound253,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric81 : ∀ c∈certificate81.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch020.certificate251,MergedCutCells.Batch021.certificate252,MergedCutCells.Batch021.certificate253], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch020.numericValid251,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid252,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid253,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid81 : ∀ c∈certificate81.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch020.certificate251,MergedCutCells.Batch021.certificate252,MergedCutCells.Batch021.certificate253], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid28,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid28,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid28,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches81 : ∀ c∈certificate81.cells, c.population=certificate81.population := by
  change ∀ c∈[MergedCutCells.Batch020.certificate251,MergedCutCells.Batch021.certificate252,MergedCutCells.Batch021.certificate253], c.population=PopulationCertificates.Batch002.certificate54
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers81 {x : ℝ} (hx : certificate81.interval.Contains x) : ∃ c∈certificate81.cells, c.region.interval.Contains x := rat_cut_group_covers certificate81 numericValid81 hx

def certificate82 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate54,PopulationCertificates.Batch002.certificate54,[MergedCutCells.Batch021.certificate254,MergedCutCells.Batch021.certificate255,MergedCutCells.Batch021.certificate256,MergedCutCells.Batch021.certificate257,MergedCutCells.Batch021.certificate258,MergedCutCells.Batch021.certificate259],(1053615059/1000000000),none,(1/2),(71275039024803071/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid82 : certificate82.NumericValid := by decide +kernel
theorem cellsSound82 : ∀ c∈certificate82.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch021.certificate254,MergedCutCells.Batch021.certificate255,MergedCutCells.Batch021.certificate256,MergedCutCells.Batch021.certificate257,MergedCutCells.Batch021.certificate258,MergedCutCells.Batch021.certificate259], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound254,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound255,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound256,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound258,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound259,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric82 : ∀ c∈certificate82.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch021.certificate254,MergedCutCells.Batch021.certificate255,MergedCutCells.Batch021.certificate256,MergedCutCells.Batch021.certificate257,MergedCutCells.Batch021.certificate258,MergedCutCells.Batch021.certificate259], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid254,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid255,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid256,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid257,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid258,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid259,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid82 : ∀ c∈certificate82.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch021.certificate254,MergedCutCells.Batch021.certificate255,MergedCutCells.Batch021.certificate256,MergedCutCells.Batch021.certificate257,MergedCutCells.Batch021.certificate258,MergedCutCells.Batch021.certificate259], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches82 : ∀ c∈certificate82.cells, c.population=certificate82.population := by
  change ∀ c∈[MergedCutCells.Batch021.certificate254,MergedCutCells.Batch021.certificate255,MergedCutCells.Batch021.certificate256,MergedCutCells.Batch021.certificate257,MergedCutCells.Batch021.certificate258,MergedCutCells.Batch021.certificate259], c.population=PopulationCertificates.Batch002.certificate54
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers82 {x : ℝ} (hx : certificate82.interval.Contains x) : ∃ c∈certificate82.cells, c.region.interval.Contains x := rat_cut_group_covers certificate82 numericValid82 hx

def certificate83 : RatCutGroup := ⟨GeometryCertificates.Batch002.certificate55,PopulationCertificates.Batch002.certificate55,[MergedCutCells.Batch021.certificate260,MergedCutCells.Batch021.certificate261,MergedCutCells.Batch021.certificate262],(227173706247332241/62500000000000000),none,(1/2),(360210832549288121/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid83 : certificate83.NumericValid := by decide +kernel
theorem cellsSound83 : ∀ c∈certificate83.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch021.certificate260,MergedCutCells.Batch021.certificate261,MergedCutCells.Batch021.certificate262], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound260,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.sound262,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric83 : ∀ c∈certificate83.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch021.certificate260,MergedCutCells.Batch021.certificate261,MergedCutCells.Batch021.certificate262], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid260,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid261,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch021.numericValid262,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid83 : ∀ c∈certificate83.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch021.certificate260,MergedCutCells.Batch021.certificate261,MergedCutCells.Batch021.certificate262], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches83 : ∀ c∈certificate83.cells, c.population=certificate83.population := by
  change ∀ c∈[MergedCutCells.Batch021.certificate260,MergedCutCells.Batch021.certificate261,MergedCutCells.Batch021.certificate262], c.population=PopulationCertificates.Batch002.certificate55
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers83 {x : ℝ} (hx : certificate83.interval.Contains x) : ∃ c∈certificate83.cells, c.region.interval.Contains x := rat_cut_group_covers certificate83 numericValid83 hx

end Cycle12.MergedCutGroups.Batch006
