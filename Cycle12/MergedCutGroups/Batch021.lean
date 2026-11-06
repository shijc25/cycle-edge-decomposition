import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch008
import Cycle12.MergedCutCells.Batch081
import Cycle12.MergedCutCells.Batch082
import Cycle12.MergedCutCells.Batch083
import Cycle12.MergedCutCells.Batch084
import Cycle12.MergedCutCells.Batch085
import Cycle12.PopulationCertificates.Batch008

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch021

def certificate252 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate168,PopulationCertificates.Batch008.certificate168,[MergedCutCells.Batch081.certificate973,MergedCutCells.Batch081.certificate974,MergedCutCells.Batch081.certificate975,MergedCutCells.Batch081.certificate976,MergedCutCells.Batch081.certificate977,MergedCutCells.Batch081.certificate978,MergedCutCells.Batch081.certificate979],(170033120808722371/200000000000000000),(some 64),(1/2),(393750800487041881/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1416218480365272519/1000000000000000000))⟩
theorem numericValid252 : certificate252.NumericValid := by decide +kernel
theorem cellsSound252 : ∀ c∈certificate252.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch081.certificate973,MergedCutCells.Batch081.certificate974,MergedCutCells.Batch081.certificate975,MergedCutCells.Batch081.certificate976,MergedCutCells.Batch081.certificate977,MergedCutCells.Batch081.certificate978,MergedCutCells.Batch081.certificate979], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound973,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound974,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound975,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound976,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound977,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound978,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound979,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric252 : ∀ c∈certificate252.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch081.certificate973,MergedCutCells.Batch081.certificate974,MergedCutCells.Batch081.certificate975,MergedCutCells.Batch081.certificate976,MergedCutCells.Batch081.certificate977,MergedCutCells.Batch081.certificate978,MergedCutCells.Batch081.certificate979], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid973,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid974,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid975,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid976,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid977,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid978,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid979,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid252 : ∀ c∈certificate252.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch081.certificate973,MergedCutCells.Batch081.certificate974,MergedCutCells.Batch081.certificate975,MergedCutCells.Batch081.certificate976,MergedCutCells.Batch081.certificate977,MergedCutCells.Batch081.certificate978,MergedCutCells.Batch081.certificate979], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid85,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid85,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid85,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid85,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid85,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid85,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid85,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches252 : ∀ c∈certificate252.cells, c.population=certificate252.population := by
  change ∀ c∈[MergedCutCells.Batch081.certificate973,MergedCutCells.Batch081.certificate974,MergedCutCells.Batch081.certificate975,MergedCutCells.Batch081.certificate976,MergedCutCells.Batch081.certificate977,MergedCutCells.Batch081.certificate978,MergedCutCells.Batch081.certificate979], c.population=PopulationCertificates.Batch008.certificate168
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers252 {x : ℝ} (hx : certificate252.interval.Contains x) : ∃ c∈certificate252.cells, c.region.interval.Contains x := rat_cut_group_covers certificate252 numericValid252 hx

def certificate253 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate168,PopulationCertificates.Batch008.certificate168,[MergedCutCells.Batch081.certificate980],64,none,(1/2),(236284424402986613/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid253 : certificate253.NumericValid := by decide +kernel
theorem cellsSound253 : ∀ c∈certificate253.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch081.certificate980], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound980,List.forall_mem_nil _⟩
theorem cellsNumeric253 : ∀ c∈certificate253.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch081.certificate980], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid980,List.forall_mem_nil _⟩
theorem cellsEntropyValid253 : ∀ c∈certificate253.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch081.certificate980], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches253 : ∀ c∈certificate253.cells, c.population=certificate253.population := by
  change ∀ c∈[MergedCutCells.Batch081.certificate980], c.population=PopulationCertificates.Batch008.certificate168
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers253 {x : ℝ} (hx : certificate253.interval.Contains x) : ∃ c∈certificate253.cells, c.region.interval.Contains x := rat_cut_group_covers certificate253 numericValid253 hx

def certificate254 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate169,PopulationCertificates.Batch008.certificate169,[MergedCutCells.Batch081.certificate981,MergedCutCells.Batch081.certificate982,MergedCutCells.Batch081.certificate983,MergedCutCells.Batch082.certificate984],(1838313598144314721/500000000000000000),none,(1/2),(664330110099004353/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid254 : certificate254.NumericValid := by decide +kernel
theorem cellsSound254 : ∀ c∈certificate254.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch081.certificate981,MergedCutCells.Batch081.certificate982,MergedCutCells.Batch081.certificate983,MergedCutCells.Batch082.certificate984], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound981,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound982,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.sound983,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound984,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric254 : ∀ c∈certificate254.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch081.certificate981,MergedCutCells.Batch081.certificate982,MergedCutCells.Batch081.certificate983,MergedCutCells.Batch082.certificate984], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid981,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid982,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch081.numericValid983,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid984,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid254 : ∀ c∈certificate254.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch081.certificate981,MergedCutCells.Batch081.certificate982,MergedCutCells.Batch081.certificate983,MergedCutCells.Batch082.certificate984], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches254 : ∀ c∈certificate254.cells, c.population=certificate254.population := by
  change ∀ c∈[MergedCutCells.Batch081.certificate981,MergedCutCells.Batch081.certificate982,MergedCutCells.Batch081.certificate983,MergedCutCells.Batch082.certificate984], c.population=PopulationCertificates.Batch008.certificate169
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers254 {x : ℝ} (hx : certificate254.interval.Contains x) : ∃ c∈certificate254.cells, c.region.interval.Contains x := rat_cut_group_covers certificate254 numericValid254 hx

def certificate255 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate170,PopulationCertificates.Batch008.certificate170,[MergedCutCells.Batch082.certificate985,MergedCutCells.Batch082.certificate986,MergedCutCells.Batch082.certificate987,MergedCutCells.Batch082.certificate988,MergedCutCells.Batch082.certificate989,MergedCutCells.Batch082.certificate990,MergedCutCells.Batch082.certificate991,MergedCutCells.Batch082.certificate992],(168713417955691459/200000000000000000),(some 64),(1/2),(6263307748026201/15625000000000000),(some (69314718055994531/100000000000000000)),(some (708916292752564491/500000000000000000))⟩
theorem numericValid255 : certificate255.NumericValid := by decide +kernel
theorem cellsSound255 : ∀ c∈certificate255.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch082.certificate985,MergedCutCells.Batch082.certificate986,MergedCutCells.Batch082.certificate987,MergedCutCells.Batch082.certificate988,MergedCutCells.Batch082.certificate989,MergedCutCells.Batch082.certificate990,MergedCutCells.Batch082.certificate991,MergedCutCells.Batch082.certificate992], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound985,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound986,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound987,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound988,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound990,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound991,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound992,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric255 : ∀ c∈certificate255.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch082.certificate985,MergedCutCells.Batch082.certificate986,MergedCutCells.Batch082.certificate987,MergedCutCells.Batch082.certificate988,MergedCutCells.Batch082.certificate989,MergedCutCells.Batch082.certificate990,MergedCutCells.Batch082.certificate991,MergedCutCells.Batch082.certificate992], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid985,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid986,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid987,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid988,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid990,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid991,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid992,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid255 : ∀ c∈certificate255.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch082.certificate985,MergedCutCells.Batch082.certificate986,MergedCutCells.Batch082.certificate987,MergedCutCells.Batch082.certificate988,MergedCutCells.Batch082.certificate989,MergedCutCells.Batch082.certificate990,MergedCutCells.Batch082.certificate991,MergedCutCells.Batch082.certificate992], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid86,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid86,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid86,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid86,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid86,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid86,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid86,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid86,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches255 : ∀ c∈certificate255.cells, c.population=certificate255.population := by
  change ∀ c∈[MergedCutCells.Batch082.certificate985,MergedCutCells.Batch082.certificate986,MergedCutCells.Batch082.certificate987,MergedCutCells.Batch082.certificate988,MergedCutCells.Batch082.certificate989,MergedCutCells.Batch082.certificate990,MergedCutCells.Batch082.certificate991,MergedCutCells.Batch082.certificate992], c.population=PopulationCertificates.Batch008.certificate170
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers255 {x : ℝ} (hx : certificate255.interval.Contains x) : ∃ c∈certificate255.cells, c.region.interval.Contains x := rat_cut_group_covers certificate255 numericValid255 hx

def certificate256 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate170,PopulationCertificates.Batch008.certificate170,[MergedCutCells.Batch082.certificate993],64,none,(1/2),(484778262713490747/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid256 : certificate256.NumericValid := by decide +kernel
theorem cellsSound256 : ∀ c∈certificate256.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch082.certificate993], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound993,List.forall_mem_nil _⟩
theorem cellsNumeric256 : ∀ c∈certificate256.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch082.certificate993], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid993,List.forall_mem_nil _⟩
theorem cellsEntropyValid256 : ∀ c∈certificate256.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch082.certificate993], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches256 : ∀ c∈certificate256.cells, c.population=certificate256.population := by
  change ∀ c∈[MergedCutCells.Batch082.certificate993], c.population=PopulationCertificates.Batch008.certificate170
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers256 {x : ℝ} (hx : certificate256.interval.Contains x) : ∃ c∈certificate256.cells, c.region.interval.Contains x := rat_cut_group_covers certificate256 numericValid256 hx

def certificate257 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate171,PopulationCertificates.Batch008.certificate171,[MergedCutCells.Batch082.certificate994,MergedCutCells.Batch082.certificate995,MergedCutCells.Batch083.certificate996],(23009338821876071/6250000000000000),none,(1/2),(135999017087475609/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid257 : certificate257.NumericValid := by decide +kernel
theorem cellsSound257 : ∀ c∈certificate257.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch082.certificate994,MergedCutCells.Batch082.certificate995,MergedCutCells.Batch083.certificate996], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound994,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.sound995,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound996,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric257 : ∀ c∈certificate257.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch082.certificate994,MergedCutCells.Batch082.certificate995,MergedCutCells.Batch083.certificate996], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid994,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch082.numericValid995,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid996,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid257 : ∀ c∈certificate257.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch082.certificate994,MergedCutCells.Batch082.certificate995,MergedCutCells.Batch083.certificate996], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches257 : ∀ c∈certificate257.cells, c.population=certificate257.population := by
  change ∀ c∈[MergedCutCells.Batch082.certificate994,MergedCutCells.Batch082.certificate995,MergedCutCells.Batch083.certificate996], c.population=PopulationCertificates.Batch008.certificate171
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers257 {x : ℝ} (hx : certificate257.interval.Contains x) : ∃ c∈certificate257.cells, c.region.interval.Contains x := rat_cut_group_covers certificate257 numericValid257 hx

def certificate258 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate172,PopulationCertificates.Batch008.certificate172,[MergedCutCells.Batch083.certificate997,MergedCutCells.Batch083.certificate998,MergedCutCells.Batch083.certificate999,MergedCutCells.Batch083.certificate1000,MergedCutCells.Batch083.certificate1001,MergedCutCells.Batch083.certificate1002,MergedCutCells.Batch083.certificate1003],(850165604735466541/1000000000000000000),(some 64),(1/2),(16214322770742949/40000000000000000),(some (69314718055994531/100000000000000000)),(some (1419783158979229661/1000000000000000000))⟩
theorem numericValid258 : certificate258.NumericValid := by decide +kernel
theorem cellsSound258 : ∀ c∈certificate258.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch083.certificate997,MergedCutCells.Batch083.certificate998,MergedCutCells.Batch083.certificate999,MergedCutCells.Batch083.certificate1000,MergedCutCells.Batch083.certificate1001,MergedCutCells.Batch083.certificate1002,MergedCutCells.Batch083.certificate1003], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound998,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound999,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound1000,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound1001,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound1002,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound1003,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric258 : ∀ c∈certificate258.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch083.certificate997,MergedCutCells.Batch083.certificate998,MergedCutCells.Batch083.certificate999,MergedCutCells.Batch083.certificate1000,MergedCutCells.Batch083.certificate1001,MergedCutCells.Batch083.certificate1002,MergedCutCells.Batch083.certificate1003], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid998,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid999,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid1000,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid1001,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid1002,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid1003,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid258 : ∀ c∈certificate258.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch083.certificate997,MergedCutCells.Batch083.certificate998,MergedCutCells.Batch083.certificate999,MergedCutCells.Batch083.certificate1000,MergedCutCells.Batch083.certificate1001,MergedCutCells.Batch083.certificate1002,MergedCutCells.Batch083.certificate1003], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid87,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid87,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid87,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid87,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid87,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid87,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid87,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches258 : ∀ c∈certificate258.cells, c.population=certificate258.population := by
  change ∀ c∈[MergedCutCells.Batch083.certificate997,MergedCutCells.Batch083.certificate998,MergedCutCells.Batch083.certificate999,MergedCutCells.Batch083.certificate1000,MergedCutCells.Batch083.certificate1001,MergedCutCells.Batch083.certificate1002,MergedCutCells.Batch083.certificate1003], c.population=PopulationCertificates.Batch008.certificate172
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers258 {x : ℝ} (hx : certificate258.interval.Contains x) : ∃ c∈certificate258.cells, c.region.interval.Contains x := rat_cut_group_covers certificate258 numericValid258 hx

def certificate259 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate172,PopulationCertificates.Batch008.certificate172,[MergedCutCells.Batch083.certificate1004],64,none,(1/2),(490614249351910999/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid259 : certificate259.NumericValid := by decide +kernel
theorem cellsSound259 : ∀ c∈certificate259.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch083.certificate1004], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound1004,List.forall_mem_nil _⟩
theorem cellsNumeric259 : ∀ c∈certificate259.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch083.certificate1004], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid1004,List.forall_mem_nil _⟩
theorem cellsEntropyValid259 : ∀ c∈certificate259.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch083.certificate1004], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches259 : ∀ c∈certificate259.cells, c.population=certificate259.population := by
  change ∀ c∈[MergedCutCells.Batch083.certificate1004], c.population=PopulationCertificates.Batch008.certificate172
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers259 {x : ℝ} (hx : certificate259.interval.Contains x) : ∃ c∈certificate259.cells, c.region.interval.Contains x := rat_cut_group_covers certificate259 numericValid259 hx

def certificate260 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate173,PopulationCertificates.Batch008.certificate173,[MergedCutCells.Batch083.certificate1005,MergedCutCells.Batch083.certificate1006,MergedCutCells.Batch083.certificate1007,MergedCutCells.Batch084.certificate1008],(3688530289704540959/1000000000000000000),none,(1/2),(349126477436717557/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid260 : certificate260.NumericValid := by decide +kernel
theorem cellsSound260 : ∀ c∈certificate260.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch083.certificate1005,MergedCutCells.Batch083.certificate1006,MergedCutCells.Batch083.certificate1007,MergedCutCells.Batch084.certificate1008], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound1005,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound1006,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.sound1007,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1008,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric260 : ∀ c∈certificate260.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch083.certificate1005,MergedCutCells.Batch083.certificate1006,MergedCutCells.Batch083.certificate1007,MergedCutCells.Batch084.certificate1008], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid1005,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid1006,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch083.numericValid1007,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1008,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid260 : ∀ c∈certificate260.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch083.certificate1005,MergedCutCells.Batch083.certificate1006,MergedCutCells.Batch083.certificate1007,MergedCutCells.Batch084.certificate1008], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches260 : ∀ c∈certificate260.cells, c.population=certificate260.population := by
  change ∀ c∈[MergedCutCells.Batch083.certificate1005,MergedCutCells.Batch083.certificate1006,MergedCutCells.Batch083.certificate1007,MergedCutCells.Batch084.certificate1008], c.population=PopulationCertificates.Batch008.certificate173
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers260 {x : ℝ} (hx : certificate260.interval.Contains x) : ∃ c∈certificate260.cells, c.region.interval.Contains x := rat_cut_group_covers certificate260 numericValid260 hx

def certificate261 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate174,PopulationCertificates.Batch008.certificate174,[MergedCutCells.Batch084.certificate1009,MergedCutCells.Batch084.certificate1010,MergedCutCells.Batch084.certificate1011,MergedCutCells.Batch084.certificate1012,MergedCutCells.Batch084.certificate1013,MergedCutCells.Batch084.certificate1014,MergedCutCells.Batch084.certificate1015,MergedCutCells.Batch084.certificate1016],(421700000661846177/500000000000000000),(some 64),(1/2),(418266509273696627/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1421178695365118793/1000000000000000000))⟩
theorem numericValid261 : certificate261.NumericValid := by decide +kernel
theorem cellsSound261 : ∀ c∈certificate261.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1009,MergedCutCells.Batch084.certificate1010,MergedCutCells.Batch084.certificate1011,MergedCutCells.Batch084.certificate1012,MergedCutCells.Batch084.certificate1013,MergedCutCells.Batch084.certificate1014,MergedCutCells.Batch084.certificate1015,MergedCutCells.Batch084.certificate1016], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1009,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1010,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1011,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1012,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1013,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1014,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1015,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1016,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric261 : ∀ c∈certificate261.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1009,MergedCutCells.Batch084.certificate1010,MergedCutCells.Batch084.certificate1011,MergedCutCells.Batch084.certificate1012,MergedCutCells.Batch084.certificate1013,MergedCutCells.Batch084.certificate1014,MergedCutCells.Batch084.certificate1015,MergedCutCells.Batch084.certificate1016], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1009,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1010,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1011,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1012,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1013,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1014,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1015,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1016,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid261 : ∀ c∈certificate261.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1009,MergedCutCells.Batch084.certificate1010,MergedCutCells.Batch084.certificate1011,MergedCutCells.Batch084.certificate1012,MergedCutCells.Batch084.certificate1013,MergedCutCells.Batch084.certificate1014,MergedCutCells.Batch084.certificate1015,MergedCutCells.Batch084.certificate1016], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid88,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid88,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid88,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid88,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid88,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid88,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid88,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid88,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches261 : ∀ c∈certificate261.cells, c.population=certificate261.population := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1009,MergedCutCells.Batch084.certificate1010,MergedCutCells.Batch084.certificate1011,MergedCutCells.Batch084.certificate1012,MergedCutCells.Batch084.certificate1013,MergedCutCells.Batch084.certificate1014,MergedCutCells.Batch084.certificate1015,MergedCutCells.Batch084.certificate1016], c.population=PopulationCertificates.Batch008.certificate174
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers261 {x : ℝ} (hx : certificate261.interval.Contains x) : ∃ c∈certificate261.cells, c.region.interval.Contains x := rat_cut_group_covers certificate261 numericValid261 hx

def certificate262 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate174,PopulationCertificates.Batch008.certificate174,[MergedCutCells.Batch084.certificate1017],64,none,(1/2),(503438245678428799/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid262 : certificate262.NumericValid := by decide +kernel
theorem cellsSound262 : ∀ c∈certificate262.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1017], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1017,List.forall_mem_nil _⟩
theorem cellsNumeric262 : ∀ c∈certificate262.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1017], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1017,List.forall_mem_nil _⟩
theorem cellsEntropyValid262 : ∀ c∈certificate262.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1017], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches262 : ∀ c∈certificate262.cells, c.population=certificate262.population := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1017], c.population=PopulationCertificates.Batch008.certificate174
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers262 {x : ℝ} (hx : certificate262.interval.Contains x) : ∃ c∈certificate262.cells, c.region.interval.Contains x := rat_cut_group_covers certificate262 numericValid262 hx

def certificate263 : RatCutGroup := ⟨GeometryCertificates.Batch008.certificate175,PopulationCertificates.Batch008.certificate175,[MergedCutCells.Batch084.certificate1018,MergedCutCells.Batch084.certificate1019,MergedCutCells.Batch085.certificate1020,MergedCutCells.Batch085.certificate1021],(923375543519927311/250000000000000000),none,(1/2),(17861128273924879/25000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid263 : certificate263.NumericValid := by decide +kernel
theorem cellsSound263 : ∀ c∈certificate263.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1018,MergedCutCells.Batch084.certificate1019,MergedCutCells.Batch085.certificate1020,MergedCutCells.Batch085.certificate1021], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1018,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.sound1019,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1020,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.sound1021,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric263 : ∀ c∈certificate263.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1018,MergedCutCells.Batch084.certificate1019,MergedCutCells.Batch085.certificate1020,MergedCutCells.Batch085.certificate1021], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1018,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch084.numericValid1019,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1020,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch085.numericValid1021,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid263 : ∀ c∈certificate263.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1018,MergedCutCells.Batch084.certificate1019,MergedCutCells.Batch085.certificate1020,MergedCutCells.Batch085.certificate1021], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches263 : ∀ c∈certificate263.cells, c.population=certificate263.population := by
  change ∀ c∈[MergedCutCells.Batch084.certificate1018,MergedCutCells.Batch084.certificate1019,MergedCutCells.Batch085.certificate1020,MergedCutCells.Batch085.certificate1021], c.population=PopulationCertificates.Batch008.certificate175
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers263 {x : ℝ} (hx : certificate263.interval.Contains x) : ∃ c∈certificate263.cells, c.region.interval.Contains x := rat_cut_group_covers certificate263 numericValid263 hx

end Cycle12.MergedCutGroups.Batch021
