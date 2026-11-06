import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch018
import Cycle12.MergedCutCells.Batch169
import Cycle12.MergedCutCells.Batch170
import Cycle12.MergedCutCells.Batch171
import Cycle12.PopulationCertificates.Batch018

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch045

def certificate540 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate360,PopulationCertificates.Batch018.certificate360,[MergedCutCells.Batch169.certificate2032,MergedCutCells.Batch169.certificate2033],(609196848838466723/1000000000000000000),(some (1244293919/1000000000)),(1/2),(280286569124796369/1000000000000000000),(some (10463448001574531/100000000000000000)),(some (339271889621247/15625000000000000))⟩
theorem numericValid540 : certificate540.NumericValid := by decide +kernel
theorem cellsSound540 : ∀ c∈certificate540.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2032,MergedCutCells.Batch169.certificate2033], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2032,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2033,List.forall_mem_nil _⟩⟩
theorem cellsNumeric540 : ∀ c∈certificate540.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2032,MergedCutCells.Batch169.certificate2033], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2032,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2033,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid540 : ∀ c∈certificate540.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2032,MergedCutCells.Batch169.certificate2033], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid181,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid181,List.forall_mem_nil _⟩⟩
theorem populationMatches540 : ∀ c∈certificate540.cells, c.population=certificate540.population := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2032,MergedCutCells.Batch169.certificate2033], c.population=PopulationCertificates.Batch018.certificate360
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers540 {x : ℝ} (hx : certificate540.interval.Contains x) : ∃ c∈certificate540.cells, c.region.interval.Contains x := rat_cut_group_covers certificate540 numericValid540 hx

def certificate541 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate360,PopulationCertificates.Batch018.certificate360,[MergedCutCells.Batch169.certificate2034,MergedCutCells.Batch169.certificate2035,MergedCutCells.Batch169.certificate2036],(1244293919/1000000000),none,(1/2),(273665265262678413/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid541 : certificate541.NumericValid := by decide +kernel
theorem cellsSound541 : ∀ c∈certificate541.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2034,MergedCutCells.Batch169.certificate2035,MergedCutCells.Batch169.certificate2036], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2034,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2035,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2036,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric541 : ∀ c∈certificate541.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2034,MergedCutCells.Batch169.certificate2035,MergedCutCells.Batch169.certificate2036], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2034,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2035,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2036,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid541 : ∀ c∈certificate541.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2034,MergedCutCells.Batch169.certificate2035,MergedCutCells.Batch169.certificate2036], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches541 : ∀ c∈certificate541.cells, c.population=certificate541.population := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2034,MergedCutCells.Batch169.certificate2035,MergedCutCells.Batch169.certificate2036], c.population=PopulationCertificates.Batch018.certificate360
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers541 {x : ℝ} (hx : certificate541.interval.Contains x) : ∃ c∈certificate541.cells, c.region.interval.Contains x := rat_cut_group_covers certificate541 numericValid541 hx

def certificate542 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate361,PopulationCertificates.Batch018.certificate361,[MergedCutCells.Batch169.certificate2037,MergedCutCells.Batch169.certificate2038],(5077075845851184483/1000000000000000000),none,(1/2),(1807577241417716583/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid542 : certificate542.NumericValid := by decide +kernel
theorem cellsSound542 : ∀ c∈certificate542.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2037,MergedCutCells.Batch169.certificate2038], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2038,List.forall_mem_nil _⟩⟩
theorem cellsNumeric542 : ∀ c∈certificate542.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2037,MergedCutCells.Batch169.certificate2038], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2037,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2038,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid542 : ∀ c∈certificate542.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2037,MergedCutCells.Batch169.certificate2038], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches542 : ∀ c∈certificate542.cells, c.population=certificate542.population := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2037,MergedCutCells.Batch169.certificate2038], c.population=PopulationCertificates.Batch018.certificate361
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers542 {x : ℝ} (hx : certificate542.interval.Contains x) : ∃ c∈certificate542.cells, c.region.interval.Contains x := rat_cut_group_covers certificate542 numericValid542 hx

def certificate543 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate362,PopulationCertificates.Batch018.certificate362,[MergedCutCells.Batch169.certificate2039,MergedCutCells.Batch170.certificate2040],(122774168037686221/200000000000000000),(some (48878201/40000000)),(1/2),(281606758009864869/1000000000000000000),(some (890848086634879/7812500000000000)),(some (24217806477693433/1000000000000000000))⟩
theorem numericValid543 : certificate543.NumericValid := by decide +kernel
theorem cellsSound543 : ∀ c∈certificate543.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2039,MergedCutCells.Batch170.certificate2040], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.sound2039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2040,List.forall_mem_nil _⟩⟩
theorem cellsNumeric543 : ∀ c∈certificate543.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2039,MergedCutCells.Batch170.certificate2040], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch169.numericValid2039,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2040,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid543 : ∀ c∈certificate543.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2039,MergedCutCells.Batch170.certificate2040], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid182,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid182,List.forall_mem_nil _⟩⟩
theorem populationMatches543 : ∀ c∈certificate543.cells, c.population=certificate543.population := by
  change ∀ c∈[MergedCutCells.Batch169.certificate2039,MergedCutCells.Batch170.certificate2040], c.population=PopulationCertificates.Batch018.certificate362
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers543 {x : ℝ} (hx : certificate543.interval.Contains x) : ∃ c∈certificate543.cells, c.region.interval.Contains x := rat_cut_group_covers certificate543 numericValid543 hx

def certificate544 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate362,PopulationCertificates.Batch018.certificate362,[MergedCutCells.Batch170.certificate2041,MergedCutCells.Batch170.certificate2042,MergedCutCells.Batch170.certificate2043,MergedCutCells.Batch170.certificate2044],(48878201/40000000),none,(1/2),(68523935932197013/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid544 : certificate544.NumericValid := by decide +kernel
theorem cellsSound544 : ∀ c∈certificate544.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2041,MergedCutCells.Batch170.certificate2042,MergedCutCells.Batch170.certificate2043,MergedCutCells.Batch170.certificate2044], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2041,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2042,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2043,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2044,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric544 : ∀ c∈certificate544.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2041,MergedCutCells.Batch170.certificate2042,MergedCutCells.Batch170.certificate2043,MergedCutCells.Batch170.certificate2044], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2041,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2042,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2043,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2044,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid544 : ∀ c∈certificate544.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2041,MergedCutCells.Batch170.certificate2042,MergedCutCells.Batch170.certificate2043,MergedCutCells.Batch170.certificate2044], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches544 : ∀ c∈certificate544.cells, c.population=certificate544.population := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2041,MergedCutCells.Batch170.certificate2042,MergedCutCells.Batch170.certificate2043,MergedCutCells.Batch170.certificate2044], c.population=PopulationCertificates.Batch018.certificate362
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers544 {x : ℝ} (hx : certificate544.interval.Contains x) : ∃ c∈certificate544.cells, c.region.interval.Contains x := rat_cut_group_covers certificate544 numericValid544 hx

def certificate545 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate363,PopulationCertificates.Batch018.certificate363,[MergedCutCells.Batch170.certificate2045,MergedCutCells.Batch170.certificate2046],(502818751961226307/100000000000000000),none,(1/2),(1789953530741538241/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid545 : certificate545.NumericValid := by decide +kernel
theorem cellsSound545 : ∀ c∈certificate545.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2045,MergedCutCells.Batch170.certificate2046], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2045,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2046,List.forall_mem_nil _⟩⟩
theorem cellsNumeric545 : ∀ c∈certificate545.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2045,MergedCutCells.Batch170.certificate2046], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2045,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2046,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid545 : ∀ c∈certificate545.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2045,MergedCutCells.Batch170.certificate2046], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches545 : ∀ c∈certificate545.cells, c.population=certificate545.population := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2045,MergedCutCells.Batch170.certificate2046], c.population=PopulationCertificates.Batch018.certificate363
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers545 {x : ℝ} (hx : certificate545.interval.Contains x) : ∃ c∈certificate545.cells, c.region.interval.Contains x := rat_cut_group_covers certificate545 numericValid545 hx

def certificate546 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate364,PopulationCertificates.Batch018.certificate364,[MergedCutCells.Batch170.certificate2047,MergedCutCells.Batch170.certificate2048],(619072625733355623/1000000000000000000),(some (308819237/250000000)),(1/2),(282597386706682607/1000000000000000000),(some (3890791973535683/31250000000000000)),(some (2709807497312019/100000000000000000))⟩
theorem numericValid546 : certificate546.NumericValid := by decide +kernel
theorem cellsSound546 : ∀ c∈certificate546.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2047,MergedCutCells.Batch170.certificate2048], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2047,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2048,List.forall_mem_nil _⟩⟩
theorem cellsNumeric546 : ∀ c∈certificate546.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2047,MergedCutCells.Batch170.certificate2048], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2047,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2048,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid546 : ∀ c∈certificate546.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2047,MergedCutCells.Batch170.certificate2048], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid183,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid183,List.forall_mem_nil _⟩⟩
theorem populationMatches546 : ∀ c∈certificate546.cells, c.population=certificate546.population := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2047,MergedCutCells.Batch170.certificate2048], c.population=PopulationCertificates.Batch018.certificate364
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers546 {x : ℝ} (hx : certificate546.interval.Contains x) : ∃ c∈certificate546.cells, c.region.interval.Contains x := rat_cut_group_covers certificate546 numericValid546 hx

def certificate547 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate364,PopulationCertificates.Batch018.certificate364,[MergedCutCells.Batch170.certificate2049,MergedCutCells.Batch170.certificate2050,MergedCutCells.Batch170.certificate2051,MergedCutCells.Batch171.certificate2052],(308819237/250000000),none,(1/2),(137230087029064929/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid547 : certificate547.NumericValid := by decide +kernel
theorem cellsSound547 : ∀ c∈certificate547.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2049,MergedCutCells.Batch170.certificate2050,MergedCutCells.Batch170.certificate2051,MergedCutCells.Batch171.certificate2052], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2050,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.sound2051,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2052,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric547 : ∀ c∈certificate547.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2049,MergedCutCells.Batch170.certificate2050,MergedCutCells.Batch170.certificate2051,MergedCutCells.Batch171.certificate2052], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2049,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2050,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch170.numericValid2051,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2052,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid547 : ∀ c∈certificate547.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2049,MergedCutCells.Batch170.certificate2050,MergedCutCells.Batch170.certificate2051,MergedCutCells.Batch171.certificate2052], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches547 : ∀ c∈certificate547.cells, c.population=certificate547.population := by
  change ∀ c∈[MergedCutCells.Batch170.certificate2049,MergedCutCells.Batch170.certificate2050,MergedCutCells.Batch170.certificate2051,MergedCutCells.Batch171.certificate2052], c.population=PopulationCertificates.Batch018.certificate364
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers547 {x : ℝ} (hx : certificate547.interval.Contains x) : ∃ c∈certificate547.cells, c.region.interval.Contains x := rat_cut_group_covers certificate547 numericValid547 hx

def certificate548 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate365,PopulationCertificates.Batch018.certificate365,[MergedCutCells.Batch171.certificate2053,MergedCutCells.Batch171.certificate2054],(1273427206644296749/250000000000000000),none,(1/2),(924823848465236257/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid548 : certificate548.NumericValid := by decide +kernel
theorem cellsSound548 : ∀ c∈certificate548.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2053,MergedCutCells.Batch171.certificate2054], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2053,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2054,List.forall_mem_nil _⟩⟩
theorem cellsNumeric548 : ∀ c∈certificate548.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2053,MergedCutCells.Batch171.certificate2054], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2053,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2054,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid548 : ∀ c∈certificate548.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2053,MergedCutCells.Batch171.certificate2054], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches548 : ∀ c∈certificate548.cells, c.population=certificate548.population := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2053,MergedCutCells.Batch171.certificate2054], c.population=PopulationCertificates.Batch018.certificate365
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers548 {x : ℝ} (hx : certificate548.interval.Contains x) : ∃ c∈certificate548.cells, c.region.interval.Contains x := rat_cut_group_covers certificate548 numericValid548 hx

def certificate549 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate366,PopulationCertificates.Batch018.certificate366,[MergedCutCells.Batch171.certificate2055,MergedCutCells.Batch171.certificate2056],(124832350306812373/200000000000000000),(some (242730387/200000000)),(1/2),(284144825560792189/1000000000000000000),(some (134305907900463919/1000000000000000000)),(some (14937287509219139/500000000000000000))⟩
theorem numericValid549 : certificate549.NumericValid := by decide +kernel
theorem cellsSound549 : ∀ c∈certificate549.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2055,MergedCutCells.Batch171.certificate2056], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2055,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2056,List.forall_mem_nil _⟩⟩
theorem cellsNumeric549 : ∀ c∈certificate549.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2055,MergedCutCells.Batch171.certificate2056], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2055,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2056,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid549 : ∀ c∈certificate549.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2055,MergedCutCells.Batch171.certificate2056], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid184,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy009.valid184,List.forall_mem_nil _⟩⟩
theorem populationMatches549 : ∀ c∈certificate549.cells, c.population=certificate549.population := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2055,MergedCutCells.Batch171.certificate2056], c.population=PopulationCertificates.Batch018.certificate366
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers549 {x : ℝ} (hx : certificate549.interval.Contains x) : ∃ c∈certificate549.cells, c.region.interval.Contains x := rat_cut_group_covers certificate549 numericValid549 hx

def certificate550 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate366,PopulationCertificates.Batch018.certificate366,[MergedCutCells.Batch171.certificate2057,MergedCutCells.Batch171.certificate2058,MergedCutCells.Batch171.certificate2059,MergedCutCells.Batch171.certificate2060],(242730387/200000000),none,(1/2),(274907098172745881/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid550 : certificate550.NumericValid := by decide +kernel
theorem cellsSound550 : ∀ c∈certificate550.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2057,MergedCutCells.Batch171.certificate2058,MergedCutCells.Batch171.certificate2059,MergedCutCells.Batch171.certificate2060], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2057,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2058,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2059,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2060,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric550 : ∀ c∈certificate550.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2057,MergedCutCells.Batch171.certificate2058,MergedCutCells.Batch171.certificate2059,MergedCutCells.Batch171.certificate2060], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2057,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2058,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2059,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2060,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid550 : ∀ c∈certificate550.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2057,MergedCutCells.Batch171.certificate2058,MergedCutCells.Batch171.certificate2059,MergedCutCells.Batch171.certificate2060], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches550 : ∀ c∈certificate550.cells, c.population=certificate550.population := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2057,MergedCutCells.Batch171.certificate2058,MergedCutCells.Batch171.certificate2059,MergedCutCells.Batch171.certificate2060], c.population=PopulationCertificates.Batch018.certificate366
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers550 {x : ℝ} (hx : certificate550.interval.Contains x) : ∃ c∈certificate550.cells, c.region.interval.Contains x := rat_cut_group_covers certificate550 numericValid550 hx

def certificate551 : RatCutGroup := ⟨GeometryCertificates.Batch018.certificate367,PopulationCertificates.Batch018.certificate367,[MergedCutCells.Batch171.certificate2061,MergedCutCells.Batch171.certificate2062],(5160810676542461459/1000000000000000000),none,(1/2),(477509535759114147/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid551 : certificate551.NumericValid := by decide +kernel
theorem cellsSound551 : ∀ c∈certificate551.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2061,MergedCutCells.Batch171.certificate2062], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2061,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.sound2062,List.forall_mem_nil _⟩⟩
theorem cellsNumeric551 : ∀ c∈certificate551.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2061,MergedCutCells.Batch171.certificate2062], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2061,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch171.numericValid2062,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid551 : ∀ c∈certificate551.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2061,MergedCutCells.Batch171.certificate2062], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches551 : ∀ c∈certificate551.cells, c.population=certificate551.population := by
  change ∀ c∈[MergedCutCells.Batch171.certificate2061,MergedCutCells.Batch171.certificate2062], c.population=PopulationCertificates.Batch018.certificate367
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers551 {x : ℝ} (hx : certificate551.interval.Contains x) : ∃ c∈certificate551.cells, c.region.interval.Contains x := rat_cut_group_covers certificate551 numericValid551 hx

end Cycle12.MergedCutGroups.Batch045
