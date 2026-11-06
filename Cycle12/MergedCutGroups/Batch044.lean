import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch017
import Cycle12.MergedCutCells.Batch166
import Cycle12.MergedCutCells.Batch167
import Cycle12.MergedCutCells.Batch168
import Cycle12.MergedCutCells.Batch169
import Cycle12.PopulationCertificates.Batch017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch044

def certificate528 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate352,PopulationCertificates.Batch017.certificate352,[MergedCutCells.Batch166.certificate2002,MergedCutCells.Batch166.certificate2003],(591428257662270171/1000000000000000000),(some (19844063/15625000)),(1/2),(276294110656209997/1000000000000000000),(some (13653920424066977/200000000000000000)),(some (2549212559213693/200000000000000000))⟩
theorem numericValid528 : certificate528.NumericValid := by decide +kernel
theorem cellsSound528 : ∀ c∈certificate528.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch166.certificate2002,MergedCutCells.Batch166.certificate2003], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound2002,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound2003,List.forall_mem_nil _⟩⟩
theorem cellsNumeric528 : ∀ c∈certificate528.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate2002,MergedCutCells.Batch166.certificate2003], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid2002,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid2003,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid528 : ∀ c∈certificate528.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate2002,MergedCutCells.Batch166.certificate2003], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid177,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid177,List.forall_mem_nil _⟩⟩
theorem populationMatches528 : ∀ c∈certificate528.cells, c.population=certificate528.population := by
  change ∀ c∈[MergedCutCells.Batch166.certificate2002,MergedCutCells.Batch166.certificate2003], c.population=PopulationCertificates.Batch017.certificate352
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers528 {x : ℝ} (hx : certificate528.interval.Contains x) : ∃ c∈certificate528.cells, c.region.interval.Contains x := rat_cut_group_covers certificate528 numericValid528 hx

def certificate529 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate352,PopulationCertificates.Batch017.certificate352,[MergedCutCells.Batch167.certificate2004,MergedCutCells.Batch167.certificate2005,MergedCutCells.Batch167.certificate2006],(19844063/15625000),none,(1/2),(272338669118891177/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid529 : certificate529.NumericValid := by decide +kernel
theorem cellsSound529 : ∀ c∈certificate529.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2004,MergedCutCells.Batch167.certificate2005,MergedCutCells.Batch167.certificate2006], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2004,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2005,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2006,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric529 : ∀ c∈certificate529.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2004,MergedCutCells.Batch167.certificate2005,MergedCutCells.Batch167.certificate2006], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2004,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2005,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2006,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid529 : ∀ c∈certificate529.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2004,MergedCutCells.Batch167.certificate2005,MergedCutCells.Batch167.certificate2006], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches529 : ∀ c∈certificate529.cells, c.population=certificate529.population := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2004,MergedCutCells.Batch167.certificate2005,MergedCutCells.Batch167.certificate2006], c.population=PopulationCertificates.Batch017.certificate352
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers529 {x : ℝ} (hx : certificate529.interval.Contains x) : ∃ c∈certificate529.cells, c.region.interval.Contains x := rat_cut_group_covers certificate529 numericValid529 hx

def certificate530 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate353,PopulationCertificates.Batch017.certificate353,[MergedCutCells.Batch167.certificate2007,MergedCutCells.Batch167.certificate2008],(2471453906485928251/500000000000000000),none,(1/2),(412715853992210957/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid530 : certificate530.NumericValid := by decide +kernel
theorem cellsSound530 : ∀ c∈certificate530.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2007,MergedCutCells.Batch167.certificate2008], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2007,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2008,List.forall_mem_nil _⟩⟩
theorem cellsNumeric530 : ∀ c∈certificate530.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2007,MergedCutCells.Batch167.certificate2008], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2007,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2008,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid530 : ∀ c∈certificate530.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2007,MergedCutCells.Batch167.certificate2008], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches530 : ∀ c∈certificate530.cells, c.population=certificate530.population := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2007,MergedCutCells.Batch167.certificate2008], c.population=PopulationCertificates.Batch017.certificate353
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers530 {x : ℝ} (hx : certificate530.interval.Contains x) : ∃ c∈certificate530.cells, c.region.interval.Contains x := rat_cut_group_covers certificate530 numericValid530 hx

def certificate531 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate354,PopulationCertificates.Batch017.certificate354,[MergedCutCells.Batch167.certificate2009,MergedCutCells.Batch167.certificate2010],(119092271769551423/200000000000000000),(some (1246204541/1000000000)),(1/2),(277210560118517733/1000000000000000000),(some (3065331658127013/40000000000000000)),(some (7351096944928787/500000000000000000))⟩
theorem numericValid531 : certificate531.NumericValid := by decide +kernel
theorem cellsSound531 : ∀ c∈certificate531.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2009,MergedCutCells.Batch167.certificate2010], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2009,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2010,List.forall_mem_nil _⟩⟩
theorem cellsNumeric531 : ∀ c∈certificate531.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2009,MergedCutCells.Batch167.certificate2010], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2009,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2010,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid531 : ∀ c∈certificate531.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2009,MergedCutCells.Batch167.certificate2010], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid178,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid178,List.forall_mem_nil _⟩⟩
theorem populationMatches531 : ∀ c∈certificate531.cells, c.population=certificate531.population := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2009,MergedCutCells.Batch167.certificate2010], c.population=PopulationCertificates.Batch017.certificate354
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers531 {x : ℝ} (hx : certificate531.interval.Contains x) : ∃ c∈certificate531.cells, c.region.interval.Contains x := rat_cut_group_covers certificate531 numericValid531 hx

def certificate532 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate354,PopulationCertificates.Batch017.certificate354,[MergedCutCells.Batch167.certificate2011,MergedCutCells.Batch167.certificate2012,MergedCutCells.Batch167.certificate2013,MergedCutCells.Batch167.certificate2014],(1246204541/1000000000),none,(1/2),(272664809679388861/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid532 : certificate532.NumericValid := by decide +kernel
theorem cellsSound532 : ∀ c∈certificate532.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2011,MergedCutCells.Batch167.certificate2012,MergedCutCells.Batch167.certificate2013,MergedCutCells.Batch167.certificate2014], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2011,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2012,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2013,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2014,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric532 : ∀ c∈certificate532.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2011,MergedCutCells.Batch167.certificate2012,MergedCutCells.Batch167.certificate2013,MergedCutCells.Batch167.certificate2014], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2011,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2012,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2013,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2014,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid532 : ∀ c∈certificate532.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2011,MergedCutCells.Batch167.certificate2012,MergedCutCells.Batch167.certificate2013,MergedCutCells.Batch167.certificate2014], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches532 : ∀ c∈certificate532.cells, c.population=certificate532.population := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2011,MergedCutCells.Batch167.certificate2012,MergedCutCells.Batch167.certificate2013,MergedCutCells.Batch167.certificate2014], c.population=PopulationCertificates.Batch017.certificate354
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers532 {x : ℝ} (hx : certificate532.interval.Contains x) : ∃ c∈certificate532.cells, c.region.interval.Contains x := rat_cut_group_covers certificate532 numericValid532 hx

def certificate533 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate355,PopulationCertificates.Batch017.certificate355,[MergedCutCells.Batch167.certificate2015,MergedCutCells.Batch168.certificate2016],(4889979367912039857/1000000000000000000),none,(1/2),(408213685466685661/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid533 : certificate533.NumericValid := by decide +kernel
theorem cellsSound533 : ∀ c∈certificate533.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2015,MergedCutCells.Batch168.certificate2016], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.sound2015,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2016,List.forall_mem_nil _⟩⟩
theorem cellsNumeric533 : ∀ c∈certificate533.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2015,MergedCutCells.Batch168.certificate2016], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch167.numericValid2015,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2016,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid533 : ∀ c∈certificate533.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2015,MergedCutCells.Batch168.certificate2016], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches533 : ∀ c∈certificate533.cells, c.population=certificate533.population := by
  change ∀ c∈[MergedCutCells.Batch167.certificate2015,MergedCutCells.Batch168.certificate2016], c.population=PopulationCertificates.Batch017.certificate355
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers533 {x : ℝ} (hx : certificate533.interval.Contains x) : ∃ c∈certificate533.cells, c.region.interval.Contains x := rat_cut_group_covers certificate533 numericValid533 hx

def certificate534 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate356,PopulationCertificates.Batch017.certificate356,[MergedCutCells.Batch168.certificate2017,MergedCutCells.Batch168.certificate2018],(149973459800606483/250000000000000000),(some (627005863/500000000)),(1/2),(139079709123755739/500000000000000000),(some (21453504578334553/250000000000000000)),(some (676966562739121/40000000000000000))⟩
theorem numericValid534 : certificate534.NumericValid := by decide +kernel
theorem cellsSound534 : ∀ c∈certificate534.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2017,MergedCutCells.Batch168.certificate2018], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2017,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2018,List.forall_mem_nil _⟩⟩
theorem cellsNumeric534 : ∀ c∈certificate534.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2017,MergedCutCells.Batch168.certificate2018], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2017,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2018,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid534 : ∀ c∈certificate534.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2017,MergedCutCells.Batch168.certificate2018], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid179,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid179,List.forall_mem_nil _⟩⟩
theorem populationMatches534 : ∀ c∈certificate534.cells, c.population=certificate534.population := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2017,MergedCutCells.Batch168.certificate2018], c.population=PopulationCertificates.Batch017.certificate356
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers534 {x : ℝ} (hx : certificate534.interval.Contains x) : ∃ c∈certificate534.cells, c.region.interval.Contains x := rat_cut_group_covers certificate534 numericValid534 hx

def certificate535 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate356,PopulationCertificates.Batch017.certificate356,[MergedCutCells.Batch168.certificate2019,MergedCutCells.Batch168.certificate2020,MergedCutCells.Batch168.certificate2021],(627005863/500000000),none,(1/2),(272969764911629407/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid535 : certificate535.NumericValid := by decide +kernel
theorem cellsSound535 : ∀ c∈certificate535.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2019,MergedCutCells.Batch168.certificate2020,MergedCutCells.Batch168.certificate2021], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2019,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2020,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2021,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric535 : ∀ c∈certificate535.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2019,MergedCutCells.Batch168.certificate2020,MergedCutCells.Batch168.certificate2021], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2019,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2020,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2021,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid535 : ∀ c∈certificate535.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2019,MergedCutCells.Batch168.certificate2020,MergedCutCells.Batch168.certificate2021], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches535 : ∀ c∈certificate535.cells, c.population=certificate535.population := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2019,MergedCutCells.Batch168.certificate2020,MergedCutCells.Batch168.certificate2021], c.population=PopulationCertificates.Batch017.certificate356
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers535 {x : ℝ} (hx : certificate535.interval.Contains x) : ∃ c∈certificate535.cells, c.region.interval.Contains x := rat_cut_group_covers certificate535 numericValid535 hx

def certificate536 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate357,PopulationCertificates.Batch017.certificate357,[MergedCutCells.Batch168.certificate2022,MergedCutCells.Batch168.certificate2023],(1237710374622032713/250000000000000000),none,(1/2),(845196008754462311/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid536 : certificate536.NumericValid := by decide +kernel
theorem cellsSound536 : ∀ c∈certificate536.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2022,MergedCutCells.Batch168.certificate2023], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2022,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2023,List.forall_mem_nil _⟩⟩
theorem cellsNumeric536 : ∀ c∈certificate536.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2022,MergedCutCells.Batch168.certificate2023], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2022,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2023,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid536 : ∀ c∈certificate536.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2022,MergedCutCells.Batch168.certificate2023], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches536 : ∀ c∈certificate536.cells, c.population=certificate536.population := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2022,MergedCutCells.Batch168.certificate2023], c.population=PopulationCertificates.Batch017.certificate357
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers536 {x : ℝ} (hx : certificate536.interval.Contains x) : ∃ c∈certificate536.cells, c.region.interval.Contains x := rat_cut_group_covers certificate536 numericValid536 hx

def certificate537 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate358,PopulationCertificates.Batch017.certificate358,[MergedCutCells.Batch168.certificate2024,MergedCutCells.Batch168.certificate2025],(302118660045357649/500000000000000000),(some (1235712959/1000000000)),(1/2),(139570561384191427/500000000000000000),(some (94817260421427977/1000000000000000000)),(some (19176652099368087/1000000000000000000))⟩
theorem numericValid537 : certificate537.NumericValid := by decide +kernel
theorem cellsSound537 : ∀ c∈certificate537.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2024,MergedCutCells.Batch168.certificate2025], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2024,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2025,List.forall_mem_nil _⟩⟩
theorem cellsNumeric537 : ∀ c∈certificate537.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2024,MergedCutCells.Batch168.certificate2025], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2024,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2025,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid537 : ∀ c∈certificate537.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2024,MergedCutCells.Batch168.certificate2025], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid180,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid180,List.forall_mem_nil _⟩⟩
theorem populationMatches537 : ∀ c∈certificate537.cells, c.population=certificate537.population := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2024,MergedCutCells.Batch168.certificate2025], c.population=PopulationCertificates.Batch017.certificate358
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers537 {x : ℝ} (hx : certificate537.interval.Contains x) : ∃ c∈certificate537.cells, c.region.interval.Contains x := rat_cut_group_covers certificate537 numericValid537 hx

def certificate538 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate358,PopulationCertificates.Batch017.certificate358,[MergedCutCells.Batch168.certificate2026,MergedCutCells.Batch168.certificate2027,MergedCutCells.Batch169.certificate2028,MergedCutCells.Batch169.certificate2029],(1235712959/1000000000),none,(1/2),(273346118964402429/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid538 : certificate538.NumericValid := by decide +kernel
theorem cellsSound538 : ∀ c∈certificate538.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2026,MergedCutCells.Batch168.certificate2027,MergedCutCells.Batch169.certificate2028,MergedCutCells.Batch169.certificate2029], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2026,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.sound2027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2028,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2029,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric538 : ∀ c∈certificate538.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2026,MergedCutCells.Batch168.certificate2027,MergedCutCells.Batch169.certificate2028,MergedCutCells.Batch169.certificate2029], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2026,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch168.numericValid2027,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2028,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2029,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid538 : ∀ c∈certificate538.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2026,MergedCutCells.Batch168.certificate2027,MergedCutCells.Batch169.certificate2028,MergedCutCells.Batch169.certificate2029], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches538 : ∀ c∈certificate538.cells, c.population=certificate538.population := by
  change ∀ c∈[MergedCutCells.Batch168.certificate2026,MergedCutCells.Batch168.certificate2027,MergedCutCells.Batch169.certificate2028,MergedCutCells.Batch169.certificate2029], c.population=PopulationCertificates.Batch017.certificate358
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers538 {x : ℝ} (hx : certificate538.interval.Contains x) : ∃ c∈certificate538.cells, c.region.interval.Contains x := rat_cut_group_covers certificate538 numericValid538 hx

def certificate539 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate359,PopulationCertificates.Batch017.certificate359,[MergedCutCells.Batch169.certificate2030,MergedCutCells.Batch169.certificate2031],(2506602540922815353/500000000000000000),none,(1/2),(174863413765798907/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid539 : certificate539.NumericValid := by decide +kernel
theorem cellsSound539 : ∀ c∈certificate539.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2030,MergedCutCells.Batch169.certificate2031], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2030,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2031,List.forall_mem_nil _⟩⟩
theorem cellsNumeric539 : ∀ c∈certificate539.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2030,MergedCutCells.Batch169.certificate2031], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2030,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2031,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid539 : ∀ c∈certificate539.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2030,MergedCutCells.Batch169.certificate2031], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches539 : ∀ c∈certificate539.cells, c.population=certificate539.population := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2030,MergedCutCells.Batch169.certificate2031], c.population=PopulationCertificates.Batch017.certificate359
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers539 {x : ℝ} (hx : certificate539.interval.Contains x) : ∃ c∈certificate539.cells, c.region.interval.Contains x := rat_cut_group_covers certificate539 numericValid539 hx

end Cycle12.MergedCutGroups.Batch044
