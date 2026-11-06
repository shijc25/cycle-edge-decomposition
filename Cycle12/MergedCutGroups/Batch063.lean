import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch025
import Cycle12.MergedCutCells.Batch237
import Cycle12.MergedCutCells.Batch238
import Cycle12.MergedCutCells.Batch239
import Cycle12.PopulationCertificates.Batch025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch063

def certificate756 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate504,PopulationCertificates.Batch025.certificate504,[MergedCutCells.Batch237.certificate2849,MergedCutCells.Batch237.certificate2850],(3616467723388961/6250000000000000),(some (254593437/200000000)),(1/2),(276268893020903673/1000000000000000000),(some (14144501096598863/500000000000000000)),(some (176174374560843/40000000000000000))⟩
theorem numericValid756 : certificate756.NumericValid := by decide +kernel
theorem cellsSound756 : ∀ c∈certificate756.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2849,MergedCutCells.Batch237.certificate2850], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2849,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2850,List.forall_mem_nil _⟩⟩
theorem cellsNumeric756 : ∀ c∈certificate756.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2849,MergedCutCells.Batch237.certificate2850], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2849,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2850,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid756 : ∀ c∈certificate756.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2849,MergedCutCells.Batch237.certificate2850], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid253,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid253,List.forall_mem_nil _⟩⟩
theorem populationMatches756 : ∀ c∈certificate756.cells, c.population=certificate756.population := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2849,MergedCutCells.Batch237.certificate2850], c.population=PopulationCertificates.Batch025.certificate504
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers756 {x : ℝ} (hx : certificate756.interval.Contains x) : ∃ c∈certificate756.cells, c.region.interval.Contains x := rat_cut_group_covers certificate756 numericValid756 hx

def certificate757 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate504,PopulationCertificates.Batch025.certificate504,[MergedCutCells.Batch237.certificate2851,MergedCutCells.Batch237.certificate2852,MergedCutCells.Batch237.certificate2853],(254593437/200000000),none,(1/2),(137433590231004497/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid757 : certificate757.NumericValid := by decide +kernel
theorem cellsSound757 : ∀ c∈certificate757.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2851,MergedCutCells.Batch237.certificate2852,MergedCutCells.Batch237.certificate2853], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2852,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2853,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric757 : ∀ c∈certificate757.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2851,MergedCutCells.Batch237.certificate2852,MergedCutCells.Batch237.certificate2853], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2851,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2852,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2853,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid757 : ∀ c∈certificate757.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2851,MergedCutCells.Batch237.certificate2852,MergedCutCells.Batch237.certificate2853], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches757 : ∀ c∈certificate757.cells, c.population=certificate757.population := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2851,MergedCutCells.Batch237.certificate2852,MergedCutCells.Batch237.certificate2853], c.population=PopulationCertificates.Batch025.certificate504
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers757 {x : ℝ} (hx : certificate757.interval.Contains x) : ∃ c∈certificate757.cells, c.region.interval.Contains x := rat_cut_group_covers certificate757 numericValid757 hx

def certificate758 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate505,PopulationCertificates.Batch025.certificate505,[MergedCutCells.Batch237.certificate2854,MergedCutCells.Batch237.certificate2855],(992348042387879227/125000000000000000),none,(1/2),(1466015244275051553/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid758 : certificate758.NumericValid := by decide +kernel
theorem cellsSound758 : ∀ c∈certificate758.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2854,MergedCutCells.Batch237.certificate2855], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2854,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.sound2855,List.forall_mem_nil _⟩⟩
theorem cellsNumeric758 : ∀ c∈certificate758.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2854,MergedCutCells.Batch237.certificate2855], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2854,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch237.numericValid2855,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid758 : ∀ c∈certificate758.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2854,MergedCutCells.Batch237.certificate2855], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches758 : ∀ c∈certificate758.cells, c.population=certificate758.population := by
  change ∀ c∈[MergedCutCells.Batch237.certificate2854,MergedCutCells.Batch237.certificate2855], c.population=PopulationCertificates.Batch025.certificate505
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers758 {x : ℝ} (hx : certificate758.interval.Contains x) : ∃ c∈certificate758.cells, c.region.interval.Contains x := rat_cut_group_covers certificate758 numericValid758 hx

def certificate759 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate506,PopulationCertificates.Batch025.certificate506,[MergedCutCells.Batch238.certificate2856,MergedCutCells.Batch238.certificate2857],(57913896892782441/100000000000000000),(some (1273890373/1000000000)),(1/2),(4219346493364499/15625000000000000),(some (1298157555061167/40000000000000000)),(some (5184811632642599/1000000000000000000))⟩
theorem numericValid759 : certificate759.NumericValid := by decide +kernel
theorem cellsSound759 : ∀ c∈certificate759.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2856,MergedCutCells.Batch238.certificate2857], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2856,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2857,List.forall_mem_nil _⟩⟩
theorem cellsNumeric759 : ∀ c∈certificate759.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2856,MergedCutCells.Batch238.certificate2857], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2856,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2857,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid759 : ∀ c∈certificate759.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2856,MergedCutCells.Batch238.certificate2857], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid254,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid254,List.forall_mem_nil _⟩⟩
theorem populationMatches759 : ∀ c∈certificate759.cells, c.population=certificate759.population := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2856,MergedCutCells.Batch238.certificate2857], c.population=PopulationCertificates.Batch025.certificate506
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers759 {x : ℝ} (hx : certificate759.interval.Contains x) : ∃ c∈certificate759.cells, c.region.interval.Contains x := rat_cut_group_covers certificate759 numericValid759 hx

def certificate760 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate506,PopulationCertificates.Batch025.certificate506,[MergedCutCells.Batch238.certificate2858,MergedCutCells.Batch238.certificate2859,MergedCutCells.Batch238.certificate2860],(1273890373/1000000000),none,(1/2),(134166707129606721/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid760 : certificate760.NumericValid := by decide +kernel
theorem cellsSound760 : ∀ c∈certificate760.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2858,MergedCutCells.Batch238.certificate2859,MergedCutCells.Batch238.certificate2860], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2859,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2860,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric760 : ∀ c∈certificate760.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2858,MergedCutCells.Batch238.certificate2859,MergedCutCells.Batch238.certificate2860], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2858,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2859,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2860,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid760 : ∀ c∈certificate760.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2858,MergedCutCells.Batch238.certificate2859,MergedCutCells.Batch238.certificate2860], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches760 : ∀ c∈certificate760.cells, c.population=certificate760.population := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2858,MergedCutCells.Batch238.certificate2859,MergedCutCells.Batch238.certificate2860], c.population=PopulationCertificates.Batch025.certificate506
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers760 {x : ℝ} (hx : certificate760.interval.Contains x) : ∃ c∈certificate760.cells, c.region.interval.Contains x := rat_cut_group_covers certificate760 numericValid760 hx

def certificate761 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate507,PopulationCertificates.Batch025.certificate507,[MergedCutCells.Batch238.certificate2861,MergedCutCells.Batch238.certificate2862],(999847510871568229/125000000000000000),none,(1/2),(592864995939181019/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid761 : certificate761.NumericValid := by decide +kernel
theorem cellsSound761 : ∀ c∈certificate761.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2861,MergedCutCells.Batch238.certificate2862], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2861,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2862,List.forall_mem_nil _⟩⟩
theorem cellsNumeric761 : ∀ c∈certificate761.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2861,MergedCutCells.Batch238.certificate2862], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2861,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2862,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid761 : ∀ c∈certificate761.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2861,MergedCutCells.Batch238.certificate2862], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches761 : ∀ c∈certificate761.cells, c.population=certificate761.population := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2861,MergedCutCells.Batch238.certificate2862], c.population=PopulationCertificates.Batch025.certificate507
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers761 {x : ℝ} (hx : certificate761.interval.Contains x) : ∃ c∈certificate761.cells, c.region.interval.Contains x := rat_cut_group_covers certificate761 numericValid761 hx

def certificate762 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate508,PopulationCertificates.Batch025.certificate508,[MergedCutCells.Batch238.certificate2863,MergedCutCells.Batch238.certificate2864],(9062618241877769/15625000000000000),(some (1275480667/1000000000)),(1/2),(32864669439848907/125000000000000000),(some (18418086592157959/500000000000000000)),(some (1507745374617841/250000000000000000))⟩
theorem numericValid762 : certificate762.NumericValid := by decide +kernel
theorem cellsSound762 : ∀ c∈certificate762.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2863,MergedCutCells.Batch238.certificate2864], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2863,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2864,List.forall_mem_nil _⟩⟩
theorem cellsNumeric762 : ∀ c∈certificate762.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2863,MergedCutCells.Batch238.certificate2864], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2863,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2864,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid762 : ∀ c∈certificate762.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2863,MergedCutCells.Batch238.certificate2864], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid255,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid255,List.forall_mem_nil _⟩⟩
theorem populationMatches762 : ∀ c∈certificate762.cells, c.population=certificate762.population := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2863,MergedCutCells.Batch238.certificate2864], c.population=PopulationCertificates.Batch025.certificate508
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers762 {x : ℝ} (hx : certificate762.interval.Contains x) : ∃ c∈certificate762.cells, c.region.interval.Contains x := rat_cut_group_covers certificate762 numericValid762 hx

def certificate763 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate508,PopulationCertificates.Batch025.certificate508,[MergedCutCells.Batch238.certificate2865,MergedCutCells.Batch238.certificate2866,MergedCutCells.Batch238.certificate2867],(1275480667/1000000000),none,(1/2),(130447830077894707/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid763 : certificate763.NumericValid := by decide +kernel
theorem cellsSound763 : ∀ c∈certificate763.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2865,MergedCutCells.Batch238.certificate2866,MergedCutCells.Batch238.certificate2867], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2866,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.sound2867,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric763 : ∀ c∈certificate763.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2865,MergedCutCells.Batch238.certificate2866,MergedCutCells.Batch238.certificate2867], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2865,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2866,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch238.numericValid2867,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid763 : ∀ c∈certificate763.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2865,MergedCutCells.Batch238.certificate2866,MergedCutCells.Batch238.certificate2867], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches763 : ∀ c∈certificate763.cells, c.population=certificate763.population := by
  change ∀ c∈[MergedCutCells.Batch238.certificate2865,MergedCutCells.Batch238.certificate2866,MergedCutCells.Batch238.certificate2867], c.population=PopulationCertificates.Batch025.certificate508
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers763 {x : ℝ} (hx : certificate763.interval.Contains x) : ∃ c∈certificate763.cells, c.region.interval.Contains x := rat_cut_group_covers certificate763 numericValid763 hx

def certificate764 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate509,PopulationCertificates.Batch025.certificate509,[MergedCutCells.Batch239.certificate2868,MergedCutCells.Batch239.certificate2869],(8142021655799800351/1000000000000000000),none,(1/2),(3038976182836191151/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid764 : certificate764.NumericValid := by decide +kernel
theorem cellsSound764 : ∀ c∈certificate764.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2868,MergedCutCells.Batch239.certificate2869], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2868,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2869,List.forall_mem_nil _⟩⟩
theorem cellsNumeric764 : ∀ c∈certificate764.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2868,MergedCutCells.Batch239.certificate2869], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2868,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2869,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid764 : ∀ c∈certificate764.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2868,MergedCutCells.Batch239.certificate2869], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches764 : ∀ c∈certificate764.cells, c.population=certificate764.population := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2868,MergedCutCells.Batch239.certificate2869], c.population=PopulationCertificates.Batch025.certificate509
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers764 {x : ℝ} (hx : certificate764.interval.Contains x) : ∃ c∈certificate764.cells, c.region.interval.Contains x := rat_cut_group_covers certificate764 numericValid764 hx

def certificate765 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate510,PopulationCertificates.Batch025.certificate510,[MergedCutCells.Batch239.certificate2870,MergedCutCells.Batch239.certificate2871],(9111200908907863/15625000000000000),(some (1250040121/1000000000)),(1/2),(133255291710454299/500000000000000000),(some (10296146892123511/250000000000000000)),(some (861806645945301/125000000000000000))⟩
theorem numericValid765 : certificate765.NumericValid := by decide +kernel
theorem cellsSound765 : ∀ c∈certificate765.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2870,MergedCutCells.Batch239.certificate2871], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2870,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2871,List.forall_mem_nil _⟩⟩
theorem cellsNumeric765 : ∀ c∈certificate765.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2870,MergedCutCells.Batch239.certificate2871], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2870,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2871,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid765 : ∀ c∈certificate765.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2870,MergedCutCells.Batch239.certificate2871], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid256,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy012.valid256,List.forall_mem_nil _⟩⟩
theorem populationMatches765 : ∀ c∈certificate765.cells, c.population=certificate765.population := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2870,MergedCutCells.Batch239.certificate2871], c.population=PopulationCertificates.Batch025.certificate510
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers765 {x : ℝ} (hx : certificate765.interval.Contains x) : ∃ c∈certificate765.cells, c.region.interval.Contains x := rat_cut_group_covers certificate765 numericValid765 hx

def certificate766 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate510,PopulationCertificates.Batch025.certificate510,[MergedCutCells.Batch239.certificate2872,MergedCutCells.Batch239.certificate2873,MergedCutCells.Batch239.certificate2874,MergedCutCells.Batch239.certificate2875],(1250040121/1000000000),none,(1/2),(264018800105264729/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid766 : certificate766.NumericValid := by decide +kernel
theorem cellsSound766 : ∀ c∈certificate766.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2872,MergedCutCells.Batch239.certificate2873,MergedCutCells.Batch239.certificate2874,MergedCutCells.Batch239.certificate2875], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2872,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2873,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2874,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2875,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric766 : ∀ c∈certificate766.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2872,MergedCutCells.Batch239.certificate2873,MergedCutCells.Batch239.certificate2874,MergedCutCells.Batch239.certificate2875], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2872,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2873,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2874,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2875,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid766 : ∀ c∈certificate766.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2872,MergedCutCells.Batch239.certificate2873,MergedCutCells.Batch239.certificate2874,MergedCutCells.Batch239.certificate2875], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches766 : ∀ c∈certificate766.cells, c.population=certificate766.population := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2872,MergedCutCells.Batch239.certificate2873,MergedCutCells.Batch239.certificate2874,MergedCutCells.Batch239.certificate2875], c.population=PopulationCertificates.Batch025.certificate510
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers766 {x : ℝ} (hx : certificate766.interval.Contains x) : ∃ c∈certificate766.cells, c.region.interval.Contains x := rat_cut_group_covers certificate766 numericValid766 hx

def certificate767 : RatCutGroup := ⟨GeometryCertificates.Batch025.certificate511,PopulationCertificates.Batch025.certificate511,[MergedCutCells.Batch239.certificate2876,MergedCutCells.Batch239.certificate2877],(8134844503729419927/1000000000000000000),none,(1/2),(3079510842125454049/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid767 : certificate767.NumericValid := by decide +kernel
theorem cellsSound767 : ∀ c∈certificate767.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2876,MergedCutCells.Batch239.certificate2877], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2876,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.sound2877,List.forall_mem_nil _⟩⟩
theorem cellsNumeric767 : ∀ c∈certificate767.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2876,MergedCutCells.Batch239.certificate2877], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2876,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch239.numericValid2877,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid767 : ∀ c∈certificate767.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2876,MergedCutCells.Batch239.certificate2877], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches767 : ∀ c∈certificate767.cells, c.population=certificate767.population := by
  change ∀ c∈[MergedCutCells.Batch239.certificate2876,MergedCutCells.Batch239.certificate2877], c.population=PopulationCertificates.Batch025.certificate511
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers767 {x : ℝ} (hx : certificate767.interval.Contains x) : ∃ c∈certificate767.cells, c.region.interval.Contains x := rat_cut_group_covers certificate767 numericValid767 hx

end Cycle12.MergedCutGroups.Batch063
