import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch015
import Cycle12.MergedCutCells.Batch147
import Cycle12.MergedCutCells.Batch148
import Cycle12.MergedCutCells.Batch149
import Cycle12.MergedCutCells.Batch150
import Cycle12.MergedCutCells.Batch151
import Cycle12.PopulationCertificates.Batch015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch038

def certificate456 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate304,PopulationCertificates.Batch015.certificate304,[MergedCutCells.Batch147.certificate1770,MergedCutCells.Batch147.certificate1771,MergedCutCells.Batch147.certificate1772,MergedCutCells.Batch147.certificate1773,MergedCutCells.Batch147.certificate1774,MergedCutCells.Batch147.certificate1775],(448350620586136831/500000000000000000),(some 64),(1/2),(1112847712488286997/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (766290938809515907/500000000000000000))⟩
theorem numericValid456 : certificate456.NumericValid := by decide +kernel
theorem cellsSound456 : ∀ c∈certificate456.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1770,MergedCutCells.Batch147.certificate1771,MergedCutCells.Batch147.certificate1772,MergedCutCells.Batch147.certificate1773,MergedCutCells.Batch147.certificate1774,MergedCutCells.Batch147.certificate1775], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1770,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1771,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1772,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1773,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1774,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.sound1775,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric456 : ∀ c∈certificate456.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1770,MergedCutCells.Batch147.certificate1771,MergedCutCells.Batch147.certificate1772,MergedCutCells.Batch147.certificate1773,MergedCutCells.Batch147.certificate1774,MergedCutCells.Batch147.certificate1775], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1770,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1771,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1772,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1773,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1774,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch147.numericValid1775,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid456 : ∀ c∈certificate456.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1770,MergedCutCells.Batch147.certificate1771,MergedCutCells.Batch147.certificate1772,MergedCutCells.Batch147.certificate1773,MergedCutCells.Batch147.certificate1774,MergedCutCells.Batch147.certificate1775], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid153,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid153,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid153,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid153,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid153,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid153,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches456 : ∀ c∈certificate456.cells, c.population=certificate456.population := by
  change ∀ c∈[MergedCutCells.Batch147.certificate1770,MergedCutCells.Batch147.certificate1771,MergedCutCells.Batch147.certificate1772,MergedCutCells.Batch147.certificate1773,MergedCutCells.Batch147.certificate1774,MergedCutCells.Batch147.certificate1775], c.population=PopulationCertificates.Batch015.certificate304
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers456 {x : ℝ} (hx : certificate456.interval.Contains x) : ∃ c∈certificate456.cells, c.region.interval.Contains x := rat_cut_group_covers certificate456 numericValid456 hx

def certificate457 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate304,PopulationCertificates.Batch015.certificate304,[MergedCutCells.Batch148.certificate1776],64,none,(1/2),(2516890822811591867/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid457 : certificate457.NumericValid := by decide +kernel
theorem cellsSound457 : ∀ c∈certificate457.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1776], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1776,List.forall_mem_nil _⟩
theorem cellsNumeric457 : ∀ c∈certificate457.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1776], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1776,List.forall_mem_nil _⟩
theorem cellsEntropyValid457 : ∀ c∈certificate457.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1776], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches457 : ∀ c∈certificate457.cells, c.population=certificate457.population := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1776], c.population=PopulationCertificates.Batch015.certificate304
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers457 {x : ℝ} (hx : certificate457.interval.Contains x) : ∃ c∈certificate457.cells, c.region.interval.Contains x := rat_cut_group_covers certificate457 numericValid457 hx

def certificate458 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate305,PopulationCertificates.Batch015.certificate305,[MergedCutCells.Batch148.certificate1777,MergedCutCells.Batch148.certificate1778,MergedCutCells.Batch148.certificate1779,MergedCutCells.Batch148.certificate1780],(600213099641392917/200000000000000000),none,(1/2),(43752071223957119/40000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid458 : certificate458.NumericValid := by decide +kernel
theorem cellsSound458 : ∀ c∈certificate458.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1777,MergedCutCells.Batch148.certificate1778,MergedCutCells.Batch148.certificate1779,MergedCutCells.Batch148.certificate1780], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1777,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1778,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1779,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1780,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric458 : ∀ c∈certificate458.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1777,MergedCutCells.Batch148.certificate1778,MergedCutCells.Batch148.certificate1779,MergedCutCells.Batch148.certificate1780], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1777,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1778,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1779,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1780,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid458 : ∀ c∈certificate458.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1777,MergedCutCells.Batch148.certificate1778,MergedCutCells.Batch148.certificate1779,MergedCutCells.Batch148.certificate1780], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches458 : ∀ c∈certificate458.cells, c.population=certificate458.population := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1777,MergedCutCells.Batch148.certificate1778,MergedCutCells.Batch148.certificate1779,MergedCutCells.Batch148.certificate1780], c.population=PopulationCertificates.Batch015.certificate305
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers458 {x : ℝ} (hx : certificate458.interval.Contains x) : ∃ c∈certificate458.cells, c.region.interval.Contains x := rat_cut_group_covers certificate458 numericValid458 hx

def certificate459 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate306,PopulationCertificates.Batch015.certificate306,[MergedCutCells.Batch148.certificate1781,MergedCutCells.Batch148.certificate1782,MergedCutCells.Batch148.certificate1783,MergedCutCells.Batch148.certificate1784,MergedCutCells.Batch148.certificate1785,MergedCutCells.Batch148.certificate1786],(223301309464688343/250000000000000000),(some 64),(1/2),(224997740709744209/200000000000000000),(some (69314718055994531/100000000000000000)),(some (383329929329372409/250000000000000000))⟩
theorem numericValid459 : certificate459.NumericValid := by decide +kernel
theorem cellsSound459 : ∀ c∈certificate459.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1781,MergedCutCells.Batch148.certificate1782,MergedCutCells.Batch148.certificate1783,MergedCutCells.Batch148.certificate1784,MergedCutCells.Batch148.certificate1785,MergedCutCells.Batch148.certificate1786], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1781,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1782,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1783,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1784,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1785,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1786,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric459 : ∀ c∈certificate459.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1781,MergedCutCells.Batch148.certificate1782,MergedCutCells.Batch148.certificate1783,MergedCutCells.Batch148.certificate1784,MergedCutCells.Batch148.certificate1785,MergedCutCells.Batch148.certificate1786], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1781,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1782,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1783,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1784,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1785,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1786,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid459 : ∀ c∈certificate459.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1781,MergedCutCells.Batch148.certificate1782,MergedCutCells.Batch148.certificate1783,MergedCutCells.Batch148.certificate1784,MergedCutCells.Batch148.certificate1785,MergedCutCells.Batch148.certificate1786], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid154,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid154,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid154,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid154,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid154,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid154,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches459 : ∀ c∈certificate459.cells, c.population=certificate459.population := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1781,MergedCutCells.Batch148.certificate1782,MergedCutCells.Batch148.certificate1783,MergedCutCells.Batch148.certificate1784,MergedCutCells.Batch148.certificate1785,MergedCutCells.Batch148.certificate1786], c.population=PopulationCertificates.Batch015.certificate306
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers459 {x : ℝ} (hx : certificate459.interval.Contains x) : ∃ c∈certificate459.cells, c.region.interval.Contains x := rat_cut_group_covers certificate459 numericValid459 hx

def certificate460 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate306,PopulationCertificates.Batch015.certificate306,[MergedCutCells.Batch148.certificate1787],64,none,(1/2),(2546013192167973433/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid460 : certificate460.NumericValid := by decide +kernel
theorem cellsSound460 : ∀ c∈certificate460.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1787], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.sound1787,List.forall_mem_nil _⟩
theorem cellsNumeric460 : ∀ c∈certificate460.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1787], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch148.numericValid1787,List.forall_mem_nil _⟩
theorem cellsEntropyValid460 : ∀ c∈certificate460.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1787], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches460 : ∀ c∈certificate460.cells, c.population=certificate460.population := by
  change ∀ c∈[MergedCutCells.Batch148.certificate1787], c.population=PopulationCertificates.Batch015.certificate306
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers460 {x : ℝ} (hx : certificate460.interval.Contains x) : ∃ c∈certificate460.cells, c.region.interval.Contains x := rat_cut_group_covers certificate460 numericValid460 hx

def certificate461 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate307,PopulationCertificates.Batch015.certificate307,[MergedCutCells.Batch149.certificate1788,MergedCutCells.Batch149.certificate1789,MergedCutCells.Batch149.certificate1790,MergedCutCells.Batch149.certificate1791],(1493316537816292213/500000000000000000),none,(1/2),(222359549719050257/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid461 : certificate461.NumericValid := by decide +kernel
theorem cellsSound461 : ∀ c∈certificate461.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1788,MergedCutCells.Batch149.certificate1789,MergedCutCells.Batch149.certificate1790,MergedCutCells.Batch149.certificate1791], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1788,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1789,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1790,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1791,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric461 : ∀ c∈certificate461.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1788,MergedCutCells.Batch149.certificate1789,MergedCutCells.Batch149.certificate1790,MergedCutCells.Batch149.certificate1791], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1788,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1789,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1790,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1791,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid461 : ∀ c∈certificate461.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1788,MergedCutCells.Batch149.certificate1789,MergedCutCells.Batch149.certificate1790,MergedCutCells.Batch149.certificate1791], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches461 : ∀ c∈certificate461.cells, c.population=certificate461.population := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1788,MergedCutCells.Batch149.certificate1789,MergedCutCells.Batch149.certificate1790,MergedCutCells.Batch149.certificate1791], c.population=PopulationCertificates.Batch015.certificate307
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers461 {x : ℝ} (hx : certificate461.interval.Contains x) : ∃ c∈certificate461.cells, c.region.interval.Contains x := rat_cut_group_covers certificate461 numericValid461 hx

def certificate462 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate308,PopulationCertificates.Batch015.certificate308,[MergedCutCells.Batch149.certificate1792,MergedCutCells.Batch149.certificate1793,MergedCutCells.Batch149.certificate1794,MergedCutCells.Batch149.certificate1795,MergedCutCells.Batch149.certificate1796,MergedCutCells.Batch149.certificate1797],(114441921153487039/125000000000000000),(some 64),(1/2),(1131194269070668757/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1535645548093982297/1000000000000000000))⟩
theorem numericValid462 : certificate462.NumericValid := by decide +kernel
theorem cellsSound462 : ∀ c∈certificate462.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1792,MergedCutCells.Batch149.certificate1793,MergedCutCells.Batch149.certificate1794,MergedCutCells.Batch149.certificate1795,MergedCutCells.Batch149.certificate1796,MergedCutCells.Batch149.certificate1797], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1792,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1793,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1794,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1795,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1796,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1797,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric462 : ∀ c∈certificate462.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1792,MergedCutCells.Batch149.certificate1793,MergedCutCells.Batch149.certificate1794,MergedCutCells.Batch149.certificate1795,MergedCutCells.Batch149.certificate1796,MergedCutCells.Batch149.certificate1797], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1792,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1793,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1794,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1795,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1796,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1797,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid462 : ∀ c∈certificate462.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1792,MergedCutCells.Batch149.certificate1793,MergedCutCells.Batch149.certificate1794,MergedCutCells.Batch149.certificate1795,MergedCutCells.Batch149.certificate1796,MergedCutCells.Batch149.certificate1797], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid155,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid155,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid155,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid155,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid155,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid155,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches462 : ∀ c∈certificate462.cells, c.population=certificate462.population := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1792,MergedCutCells.Batch149.certificate1793,MergedCutCells.Batch149.certificate1794,MergedCutCells.Batch149.certificate1795,MergedCutCells.Batch149.certificate1796,MergedCutCells.Batch149.certificate1797], c.population=PopulationCertificates.Batch015.certificate308
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers462 {x : ℝ} (hx : certificate462.interval.Contains x) : ∃ c∈certificate462.cells, c.region.interval.Contains x := rat_cut_group_covers certificate462 numericValid462 hx

def certificate463 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate308,PopulationCertificates.Batch015.certificate308,[MergedCutCells.Batch149.certificate1798],64,none,(1/2),(2531704525159685829/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid463 : certificate463.NumericValid := by decide +kernel
theorem cellsSound463 : ∀ c∈certificate463.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1798], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1798,List.forall_mem_nil _⟩
theorem cellsNumeric463 : ∀ c∈certificate463.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1798], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1798,List.forall_mem_nil _⟩
theorem cellsEntropyValid463 : ∀ c∈certificate463.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1798], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches463 : ∀ c∈certificate463.cells, c.population=certificate463.population := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1798], c.population=PopulationCertificates.Batch015.certificate308
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers463 {x : ℝ} (hx : certificate463.interval.Contains x) : ∃ c∈certificate463.cells, c.region.interval.Contains x := rat_cut_group_covers certificate463 numericValid463 hx

def certificate464 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate309,PopulationCertificates.Batch015.certificate309,[MergedCutCells.Batch149.certificate1799,MergedCutCells.Batch150.certificate1800,MergedCutCells.Batch150.certificate1801,MergedCutCells.Batch150.certificate1802],(742993280068030593/250000000000000000),none,(1/2),(4411525592169409/3906250000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid464 : certificate464.NumericValid := by decide +kernel
theorem cellsSound464 : ∀ c∈certificate464.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1799,MergedCutCells.Batch150.certificate1800,MergedCutCells.Batch150.certificate1801,MergedCutCells.Batch150.certificate1802], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.sound1799,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1800,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1802,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric464 : ∀ c∈certificate464.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1799,MergedCutCells.Batch150.certificate1800,MergedCutCells.Batch150.certificate1801,MergedCutCells.Batch150.certificate1802], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch149.numericValid1799,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1800,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1801,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1802,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid464 : ∀ c∈certificate464.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1799,MergedCutCells.Batch150.certificate1800,MergedCutCells.Batch150.certificate1801,MergedCutCells.Batch150.certificate1802], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches464 : ∀ c∈certificate464.cells, c.population=certificate464.population := by
  change ∀ c∈[MergedCutCells.Batch149.certificate1799,MergedCutCells.Batch150.certificate1800,MergedCutCells.Batch150.certificate1801,MergedCutCells.Batch150.certificate1802], c.population=PopulationCertificates.Batch015.certificate309
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers464 {x : ℝ} (hx : certificate464.interval.Contains x) : ∃ c∈certificate464.cells, c.region.interval.Contains x := rat_cut_group_covers certificate464 numericValid464 hx

def certificate465 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate310,PopulationCertificates.Batch015.certificate310,[MergedCutCells.Batch150.certificate1803,MergedCutCells.Batch150.certificate1804,MergedCutCells.Batch150.certificate1805,MergedCutCells.Batch150.certificate1806,MergedCutCells.Batch150.certificate1807,MergedCutCells.Batch150.certificate1808],(913072024108182507/1000000000000000000),(some 64),(1/2),(1143476073527501697/1000000000000000000),(some (69314718055994531/100000000000000000)),(some (1536666834305168453/1000000000000000000))⟩
theorem numericValid465 : certificate465.NumericValid := by decide +kernel
theorem cellsSound465 : ∀ c∈certificate465.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1803,MergedCutCells.Batch150.certificate1804,MergedCutCells.Batch150.certificate1805,MergedCutCells.Batch150.certificate1806,MergedCutCells.Batch150.certificate1807,MergedCutCells.Batch150.certificate1808], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1804,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1806,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1808,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric465 : ∀ c∈certificate465.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1803,MergedCutCells.Batch150.certificate1804,MergedCutCells.Batch150.certificate1805,MergedCutCells.Batch150.certificate1806,MergedCutCells.Batch150.certificate1807,MergedCutCells.Batch150.certificate1808], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1803,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1804,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1805,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1806,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1807,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1808,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid465 : ∀ c∈certificate465.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1803,MergedCutCells.Batch150.certificate1804,MergedCutCells.Batch150.certificate1805,MergedCutCells.Batch150.certificate1806,MergedCutCells.Batch150.certificate1807,MergedCutCells.Batch150.certificate1808], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid156,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid156,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid156,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid156,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid156,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy007.valid156,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches465 : ∀ c∈certificate465.cells, c.population=certificate465.population := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1803,MergedCutCells.Batch150.certificate1804,MergedCutCells.Batch150.certificate1805,MergedCutCells.Batch150.certificate1806,MergedCutCells.Batch150.certificate1807,MergedCutCells.Batch150.certificate1808], c.population=PopulationCertificates.Batch015.certificate310
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers465 {x : ℝ} (hx : certificate465.interval.Contains x) : ∃ c∈certificate465.cells, c.region.interval.Contains x := rat_cut_group_covers certificate465 numericValid465 hx

def certificate466 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate310,PopulationCertificates.Batch015.certificate310,[MergedCutCells.Batch150.certificate1809],64,none,(1/2),(127871468672809249/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid466 : certificate466.NumericValid := by decide +kernel
theorem cellsSound466 : ∀ c∈certificate466.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1809], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1809,List.forall_mem_nil _⟩
theorem cellsNumeric466 : ∀ c∈certificate466.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1809], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1809,List.forall_mem_nil _⟩
theorem cellsEntropyValid466 : ∀ c∈certificate466.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1809], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches466 : ∀ c∈certificate466.cells, c.population=certificate466.population := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1809], c.population=PopulationCertificates.Batch015.certificate310
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers466 {x : ℝ} (hx : certificate466.interval.Contains x) : ∃ c∈certificate466.cells, c.region.interval.Contains x := rat_cut_group_covers certificate466 numericValid466 hx

def certificate467 : RatCutGroup := ⟨GeometryCertificates.Batch015.certificate311,PopulationCertificates.Batch015.certificate311,[MergedCutCells.Batch150.certificate1810,MergedCutCells.Batch150.certificate1811,MergedCutCells.Batch151.certificate1812,MergedCutCells.Batch151.certificate1813],(1478702017317138463/500000000000000000),none,(1/2),(1146996304754426967/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid467 : certificate467.NumericValid := by decide +kernel
theorem cellsSound467 : ∀ c∈certificate467.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1810,MergedCutCells.Batch150.certificate1811,MergedCutCells.Batch151.certificate1812,MergedCutCells.Batch151.certificate1813], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1810,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.sound1811,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1812,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.sound1813,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric467 : ∀ c∈certificate467.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1810,MergedCutCells.Batch150.certificate1811,MergedCutCells.Batch151.certificate1812,MergedCutCells.Batch151.certificate1813], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1810,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch150.numericValid1811,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1812,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch151.numericValid1813,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid467 : ∀ c∈certificate467.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1810,MergedCutCells.Batch150.certificate1811,MergedCutCells.Batch151.certificate1812,MergedCutCells.Batch151.certificate1813], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches467 : ∀ c∈certificate467.cells, c.population=certificate467.population := by
  change ∀ c∈[MergedCutCells.Batch150.certificate1810,MergedCutCells.Batch150.certificate1811,MergedCutCells.Batch151.certificate1812,MergedCutCells.Batch151.certificate1813], c.population=PopulationCertificates.Batch015.certificate311
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers467 {x : ℝ} (hx : certificate467.interval.Contains x) : ∃ c∈certificate467.cells, c.region.interval.Contains x := rat_cut_group_covers certificate467 numericValid467 hx

end Cycle12.MergedCutGroups.Batch038
