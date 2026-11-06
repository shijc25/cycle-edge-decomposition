import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch021
import Cycle12.MergedCutCells.Batch199
import Cycle12.MergedCutCells.Batch200
import Cycle12.MergedCutCells.Batch201
import Cycle12.MergedCutCells.Batch202
import Cycle12.MergedCutCells.Batch203
import Cycle12.PopulationCertificates.Batch021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch053

def certificate636 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate424,PopulationCertificates.Batch021.certificate424,[MergedCutCells.Batch199.certificate2395,MergedCutCells.Batch199.certificate2396,MergedCutCells.Batch199.certificate2397],(824359641485261517/1000000000000000000),(some (1003559923/1000000000)),(1/2),(400773375033713857/500000000000000000),(some (228908352726461357/500000000000000000)),(some (171220818922186309/1000000000000000000))⟩
theorem numericValid636 : certificate636.NumericValid := by decide +kernel
theorem cellsSound636 : ∀ c∈certificate636.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2395,MergedCutCells.Batch199.certificate2396,MergedCutCells.Batch199.certificate2397], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2395,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2397,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric636 : ∀ c∈certificate636.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2395,MergedCutCells.Batch199.certificate2396,MergedCutCells.Batch199.certificate2397], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2395,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2397,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid636 : ∀ c∈certificate636.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2395,MergedCutCells.Batch199.certificate2396,MergedCutCells.Batch199.certificate2397], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid213,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid213,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid213,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches636 : ∀ c∈certificate636.cells, c.population=certificate636.population := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2395,MergedCutCells.Batch199.certificate2396,MergedCutCells.Batch199.certificate2397], c.population=PopulationCertificates.Batch021.certificate424
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers636 {x : ℝ} (hx : certificate636.interval.Contains x) : ∃ c∈certificate636.cells, c.region.interval.Contains x := rat_cut_group_covers certificate636 numericValid636 hx

def certificate637 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate424,PopulationCertificates.Batch021.certificate424,[MergedCutCells.Batch199.certificate2398,MergedCutCells.Batch199.certificate2399,MergedCutCells.Batch200.certificate2400,MergedCutCells.Batch200.certificate2401,MergedCutCells.Batch200.certificate2402,MergedCutCells.Batch200.certificate2403],(1003559923/1000000000),none,(1/2),(746565562147772967/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid637 : certificate637.NumericValid := by decide +kernel
theorem cellsSound637 : ∀ c∈certificate637.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2398,MergedCutCells.Batch199.certificate2399,MergedCutCells.Batch200.certificate2400,MergedCutCells.Batch200.certificate2401,MergedCutCells.Batch200.certificate2402,MergedCutCells.Batch200.certificate2403], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2398,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.sound2399,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2400,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2401,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2402,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2403,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric637 : ∀ c∈certificate637.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2398,MergedCutCells.Batch199.certificate2399,MergedCutCells.Batch200.certificate2400,MergedCutCells.Batch200.certificate2401,MergedCutCells.Batch200.certificate2402,MergedCutCells.Batch200.certificate2403], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2398,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch199.numericValid2399,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2400,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2401,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2402,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2403,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid637 : ∀ c∈certificate637.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2398,MergedCutCells.Batch199.certificate2399,MergedCutCells.Batch200.certificate2400,MergedCutCells.Batch200.certificate2401,MergedCutCells.Batch200.certificate2402,MergedCutCells.Batch200.certificate2403], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches637 : ∀ c∈certificate637.cells, c.population=certificate637.population := by
  change ∀ c∈[MergedCutCells.Batch199.certificate2398,MergedCutCells.Batch199.certificate2399,MergedCutCells.Batch200.certificate2400,MergedCutCells.Batch200.certificate2401,MergedCutCells.Batch200.certificate2402,MergedCutCells.Batch200.certificate2403], c.population=PopulationCertificates.Batch021.certificate424
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers637 {x : ℝ} (hx : certificate637.interval.Contains x) : ∃ c∈certificate637.cells, c.region.interval.Contains x := rat_cut_group_covers certificate637 numericValid637 hx

def certificate638 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate425,PopulationCertificates.Batch021.certificate425,[MergedCutCells.Batch200.certificate2404,MergedCutCells.Batch200.certificate2405,MergedCutCells.Batch200.certificate2406],(2773103617053132697/500000000000000000),none,(1/2),(3165084182856448981/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid638 : certificate638.NumericValid := by decide +kernel
theorem cellsSound638 : ∀ c∈certificate638.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2404,MergedCutCells.Batch200.certificate2405,MergedCutCells.Batch200.certificate2406], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2404,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2405,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2406,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric638 : ∀ c∈certificate638.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2404,MergedCutCells.Batch200.certificate2405,MergedCutCells.Batch200.certificate2406], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2404,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2405,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2406,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid638 : ∀ c∈certificate638.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2404,MergedCutCells.Batch200.certificate2405,MergedCutCells.Batch200.certificate2406], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches638 : ∀ c∈certificate638.cells, c.population=certificate638.population := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2404,MergedCutCells.Batch200.certificate2405,MergedCutCells.Batch200.certificate2406], c.population=PopulationCertificates.Batch021.certificate425
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers638 {x : ℝ} (hx : certificate638.interval.Contains x) : ∃ c∈certificate638.cells, c.region.interval.Contains x := rat_cut_group_covers certificate638 numericValid638 hx

def certificate639 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate426,PopulationCertificates.Batch021.certificate426,[MergedCutCells.Batch200.certificate2407,MergedCutCells.Batch200.certificate2408,MergedCutCells.Batch200.certificate2409],(829429857562084927/1000000000000000000),(some (1009452513/1000000000)),(1/2),(839229812529006111/1000000000000000000),(some (469648839833091509/1000000000000000000)),(some (89426194147770609/500000000000000000))⟩
theorem numericValid639 : certificate639.NumericValid := by decide +kernel
theorem cellsSound639 : ∀ c∈certificate639.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2407,MergedCutCells.Batch200.certificate2408,MergedCutCells.Batch200.certificate2409], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2408,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2409,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric639 : ∀ c∈certificate639.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2407,MergedCutCells.Batch200.certificate2408,MergedCutCells.Batch200.certificate2409], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2408,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2409,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid639 : ∀ c∈certificate639.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2407,MergedCutCells.Batch200.certificate2408,MergedCutCells.Batch200.certificate2409], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid214,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid214,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid214,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches639 : ∀ c∈certificate639.cells, c.population=certificate639.population := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2407,MergedCutCells.Batch200.certificate2408,MergedCutCells.Batch200.certificate2409], c.population=PopulationCertificates.Batch021.certificate426
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers639 {x : ℝ} (hx : certificate639.interval.Contains x) : ∃ c∈certificate639.cells, c.region.interval.Contains x := rat_cut_group_covers certificate639 numericValid639 hx

def certificate640 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate426,PopulationCertificates.Batch021.certificate426,[MergedCutCells.Batch200.certificate2410,MergedCutCells.Batch200.certificate2411,MergedCutCells.Batch201.certificate2412,MergedCutCells.Batch201.certificate2413,MergedCutCells.Batch201.certificate2414,MergedCutCells.Batch201.certificate2415,MergedCutCells.Batch201.certificate2416],(1009452513/1000000000),none,(1/2),(99680698003813507/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid640 : certificate640.NumericValid := by decide +kernel
theorem cellsSound640 : ∀ c∈certificate640.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2410,MergedCutCells.Batch200.certificate2411,MergedCutCells.Batch201.certificate2412,MergedCutCells.Batch201.certificate2413,MergedCutCells.Batch201.certificate2414,MergedCutCells.Batch201.certificate2415,MergedCutCells.Batch201.certificate2416], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2410,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.sound2411,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2413,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2414,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2415,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2416,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric640 : ∀ c∈certificate640.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2410,MergedCutCells.Batch200.certificate2411,MergedCutCells.Batch201.certificate2412,MergedCutCells.Batch201.certificate2413,MergedCutCells.Batch201.certificate2414,MergedCutCells.Batch201.certificate2415,MergedCutCells.Batch201.certificate2416], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2410,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch200.numericValid2411,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2413,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2414,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2415,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2416,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid640 : ∀ c∈certificate640.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2410,MergedCutCells.Batch200.certificate2411,MergedCutCells.Batch201.certificate2412,MergedCutCells.Batch201.certificate2413,MergedCutCells.Batch201.certificate2414,MergedCutCells.Batch201.certificate2415,MergedCutCells.Batch201.certificate2416], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches640 : ∀ c∈certificate640.cells, c.population=certificate640.population := by
  change ∀ c∈[MergedCutCells.Batch200.certificate2410,MergedCutCells.Batch200.certificate2411,MergedCutCells.Batch201.certificate2412,MergedCutCells.Batch201.certificate2413,MergedCutCells.Batch201.certificate2414,MergedCutCells.Batch201.certificate2415,MergedCutCells.Batch201.certificate2416], c.population=PopulationCertificates.Batch021.certificate426
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers640 {x : ℝ} (hx : certificate640.interval.Contains x) : ∃ c∈certificate640.cells, c.region.interval.Contains x := rat_cut_group_covers certificate640 numericValid640 hx

def certificate641 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate427,PopulationCertificates.Batch021.certificate427,[MergedCutCells.Batch201.certificate2417,MergedCutCells.Batch201.certificate2418,MergedCutCells.Batch201.certificate2419,MergedCutCells.Batch201.certificate2420],(5477901008702628699/1000000000000000000),none,(1/2),(3182954682663531141/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid641 : certificate641.NumericValid := by decide +kernel
theorem cellsSound641 : ∀ c∈certificate641.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch201.certificate2417,MergedCutCells.Batch201.certificate2418,MergedCutCells.Batch201.certificate2419,MergedCutCells.Batch201.certificate2420], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2417,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2418,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2419,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2420,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric641 : ∀ c∈certificate641.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch201.certificate2417,MergedCutCells.Batch201.certificate2418,MergedCutCells.Batch201.certificate2419,MergedCutCells.Batch201.certificate2420], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2417,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2418,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2419,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2420,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid641 : ∀ c∈certificate641.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch201.certificate2417,MergedCutCells.Batch201.certificate2418,MergedCutCells.Batch201.certificate2419,MergedCutCells.Batch201.certificate2420], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches641 : ∀ c∈certificate641.cells, c.population=certificate641.population := by
  change ∀ c∈[MergedCutCells.Batch201.certificate2417,MergedCutCells.Batch201.certificate2418,MergedCutCells.Batch201.certificate2419,MergedCutCells.Batch201.certificate2420], c.population=PopulationCertificates.Batch021.certificate427
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers641 {x : ℝ} (hx : certificate641.interval.Contains x) : ∃ c∈certificate641.cells, c.region.interval.Contains x := rat_cut_group_covers certificate641 numericValid641 hx

def certificate642 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate428,PopulationCertificates.Batch021.certificate428,[MergedCutCells.Batch201.certificate2421,MergedCutCells.Batch201.certificate2422,MergedCutCells.Batch201.certificate2423],(417855955065042661/500000000000000000),(some (496550383/500000000)),(1/2),(888990919731448649/1000000000000000000),(some (2396369690438209/5000000000000000)),(some (92629151562967549/500000000000000000))⟩
theorem numericValid642 : certificate642.NumericValid := by decide +kernel
theorem cellsSound642 : ∀ c∈certificate642.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch201.certificate2421,MergedCutCells.Batch201.certificate2422,MergedCutCells.Batch201.certificate2423], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2421,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2422,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.sound2423,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric642 : ∀ c∈certificate642.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch201.certificate2421,MergedCutCells.Batch201.certificate2422,MergedCutCells.Batch201.certificate2423], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2421,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2422,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch201.numericValid2423,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid642 : ∀ c∈certificate642.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch201.certificate2421,MergedCutCells.Batch201.certificate2422,MergedCutCells.Batch201.certificate2423], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid215,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid215,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid215,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches642 : ∀ c∈certificate642.cells, c.population=certificate642.population := by
  change ∀ c∈[MergedCutCells.Batch201.certificate2421,MergedCutCells.Batch201.certificate2422,MergedCutCells.Batch201.certificate2423], c.population=PopulationCertificates.Batch021.certificate428
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers642 {x : ℝ} (hx : certificate642.interval.Contains x) : ∃ c∈certificate642.cells, c.region.interval.Contains x := rat_cut_group_covers certificate642 numericValid642 hx

def certificate643 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate428,PopulationCertificates.Batch021.certificate428,[MergedCutCells.Batch202.certificate2424,MergedCutCells.Batch202.certificate2425,MergedCutCells.Batch202.certificate2426,MergedCutCells.Batch202.certificate2427,MergedCutCells.Batch202.certificate2428,MergedCutCells.Batch202.certificate2429,MergedCutCells.Batch202.certificate2430],(496550383/500000000),none,(1/2),(84492223734019833/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid643 : certificate643.NumericValid := by decide +kernel
theorem cellsSound643 : ∀ c∈certificate643.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2424,MergedCutCells.Batch202.certificate2425,MergedCutCells.Batch202.certificate2426,MergedCutCells.Batch202.certificate2427,MergedCutCells.Batch202.certificate2428,MergedCutCells.Batch202.certificate2429,MergedCutCells.Batch202.certificate2430], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2424,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2426,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2428,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2429,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2430,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric643 : ∀ c∈certificate643.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2424,MergedCutCells.Batch202.certificate2425,MergedCutCells.Batch202.certificate2426,MergedCutCells.Batch202.certificate2427,MergedCutCells.Batch202.certificate2428,MergedCutCells.Batch202.certificate2429,MergedCutCells.Batch202.certificate2430], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2424,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2425,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2426,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2427,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2428,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2429,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2430,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid643 : ∀ c∈certificate643.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2424,MergedCutCells.Batch202.certificate2425,MergedCutCells.Batch202.certificate2426,MergedCutCells.Batch202.certificate2427,MergedCutCells.Batch202.certificate2428,MergedCutCells.Batch202.certificate2429,MergedCutCells.Batch202.certificate2430], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches643 : ∀ c∈certificate643.cells, c.population=certificate643.population := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2424,MergedCutCells.Batch202.certificate2425,MergedCutCells.Batch202.certificate2426,MergedCutCells.Batch202.certificate2427,MergedCutCells.Batch202.certificate2428,MergedCutCells.Batch202.certificate2429,MergedCutCells.Batch202.certificate2430], c.population=PopulationCertificates.Batch021.certificate428
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers643 {x : ℝ} (hx : certificate643.interval.Contains x) : ∃ c∈certificate643.cells, c.region.interval.Contains x := rat_cut_group_covers certificate643 numericValid643 hx

def certificate644 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate429,PopulationCertificates.Batch021.certificate429,[MergedCutCells.Batch202.certificate2431,MergedCutCells.Batch202.certificate2432,MergedCutCells.Batch202.certificate2433,MergedCutCells.Batch202.certificate2434],(68851270641261433/12500000000000000),none,(1/2),(3286238845190486479/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid644 : certificate644.NumericValid := by decide +kernel
theorem cellsSound644 : ∀ c∈certificate644.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2431,MergedCutCells.Batch202.certificate2432,MergedCutCells.Batch202.certificate2433,MergedCutCells.Batch202.certificate2434], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2431,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2433,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2434,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric644 : ∀ c∈certificate644.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2431,MergedCutCells.Batch202.certificate2432,MergedCutCells.Batch202.certificate2433,MergedCutCells.Batch202.certificate2434], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2431,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2432,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2433,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2434,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid644 : ∀ c∈certificate644.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2431,MergedCutCells.Batch202.certificate2432,MergedCutCells.Batch202.certificate2433,MergedCutCells.Batch202.certificate2434], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches644 : ∀ c∈certificate644.cells, c.population=certificate644.population := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2431,MergedCutCells.Batch202.certificate2432,MergedCutCells.Batch202.certificate2433,MergedCutCells.Batch202.certificate2434], c.population=PopulationCertificates.Batch021.certificate429
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers644 {x : ℝ} (hx : certificate644.interval.Contains x) : ∃ c∈certificate644.cells, c.region.interval.Contains x := rat_cut_group_covers certificate644 numericValid644 hx

def certificate645 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate430,PopulationCertificates.Batch021.certificate430,[MergedCutCells.Batch202.certificate2435,MergedCutCells.Batch203.certificate2436,MergedCutCells.Batch203.certificate2437],(848671719139253627/1000000000000000000),(some (1007884227/1000000000)),(1/2),(977580933207136913/1000000000000000000),(some (490960998186918609/1000000000000000000)),(some (193291758248716917/1000000000000000000))⟩
theorem numericValid645 : certificate645.NumericValid := by decide +kernel
theorem cellsSound645 : ∀ c∈certificate645.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2435,MergedCutCells.Batch203.certificate2436,MergedCutCells.Batch203.certificate2437], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.sound2435,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2436,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2437,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric645 : ∀ c∈certificate645.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2435,MergedCutCells.Batch203.certificate2436,MergedCutCells.Batch203.certificate2437], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch202.numericValid2435,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2436,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2437,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid645 : ∀ c∈certificate645.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2435,MergedCutCells.Batch203.certificate2436,MergedCutCells.Batch203.certificate2437], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid216,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid216,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy010.valid216,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches645 : ∀ c∈certificate645.cells, c.population=certificate645.population := by
  change ∀ c∈[MergedCutCells.Batch202.certificate2435,MergedCutCells.Batch203.certificate2436,MergedCutCells.Batch203.certificate2437], c.population=PopulationCertificates.Batch021.certificate430
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers645 {x : ℝ} (hx : certificate645.interval.Contains x) : ∃ c∈certificate645.cells, c.region.interval.Contains x := rat_cut_group_covers certificate645 numericValid645 hx

def certificate646 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate430,PopulationCertificates.Batch021.certificate430,[MergedCutCells.Batch203.certificate2438,MergedCutCells.Batch203.certificate2439,MergedCutCells.Batch203.certificate2440,MergedCutCells.Batch203.certificate2441,MergedCutCells.Batch203.certificate2442,MergedCutCells.Batch203.certificate2443],(1007884227/1000000000),none,(1/2),(228670545806064287/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid646 : certificate646.NumericValid := by decide +kernel
theorem cellsSound646 : ∀ c∈certificate646.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch203.certificate2438,MergedCutCells.Batch203.certificate2439,MergedCutCells.Batch203.certificate2440,MergedCutCells.Batch203.certificate2441,MergedCutCells.Batch203.certificate2442,MergedCutCells.Batch203.certificate2443], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2439,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2440,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2441,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2442,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2443,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric646 : ∀ c∈certificate646.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch203.certificate2438,MergedCutCells.Batch203.certificate2439,MergedCutCells.Batch203.certificate2440,MergedCutCells.Batch203.certificate2441,MergedCutCells.Batch203.certificate2442,MergedCutCells.Batch203.certificate2443], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2438,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2439,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2440,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2441,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2442,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2443,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid646 : ∀ c∈certificate646.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch203.certificate2438,MergedCutCells.Batch203.certificate2439,MergedCutCells.Batch203.certificate2440,MergedCutCells.Batch203.certificate2441,MergedCutCells.Batch203.certificate2442,MergedCutCells.Batch203.certificate2443], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches646 : ∀ c∈certificate646.cells, c.population=certificate646.population := by
  change ∀ c∈[MergedCutCells.Batch203.certificate2438,MergedCutCells.Batch203.certificate2439,MergedCutCells.Batch203.certificate2440,MergedCutCells.Batch203.certificate2441,MergedCutCells.Batch203.certificate2442,MergedCutCells.Batch203.certificate2443], c.population=PopulationCertificates.Batch021.certificate430
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers646 {x : ℝ} (hx : certificate646.interval.Contains x) : ∃ c∈certificate646.cells, c.region.interval.Contains x := rat_cut_group_covers certificate646 numericValid646 hx

def certificate647 : RatCutGroup := ⟨GeometryCertificates.Batch021.certificate431,PopulationCertificates.Batch021.certificate431,[MergedCutCells.Batch203.certificate2444,MergedCutCells.Batch203.certificate2445,MergedCutCells.Batch203.certificate2446,MergedCutCells.Batch203.certificate2447],(1354602112845585893/250000000000000000),none,(1/2),(3305583903488995821/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid647 : certificate647.NumericValid := by decide +kernel
theorem cellsSound647 : ∀ c∈certificate647.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch203.certificate2444,MergedCutCells.Batch203.certificate2445,MergedCutCells.Batch203.certificate2446,MergedCutCells.Batch203.certificate2447], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2444,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2445,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2446,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.sound2447,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric647 : ∀ c∈certificate647.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch203.certificate2444,MergedCutCells.Batch203.certificate2445,MergedCutCells.Batch203.certificate2446,MergedCutCells.Batch203.certificate2447], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2444,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2445,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2446,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch203.numericValid2447,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid647 : ∀ c∈certificate647.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch203.certificate2444,MergedCutCells.Batch203.certificate2445,MergedCutCells.Batch203.certificate2446,MergedCutCells.Batch203.certificate2447], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches647 : ∀ c∈certificate647.cells, c.population=certificate647.population := by
  change ∀ c∈[MergedCutCells.Batch203.certificate2444,MergedCutCells.Batch203.certificate2445,MergedCutCells.Batch203.certificate2446,MergedCutCells.Batch203.certificate2447], c.population=PopulationCertificates.Batch021.certificate431
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers647 {x : ℝ} (hx : certificate647.interval.Contains x) : ∃ c∈certificate647.cells, c.region.interval.Contains x := rat_cut_group_covers certificate647 numericValid647 hx

end Cycle12.MergedCutGroups.Batch053
