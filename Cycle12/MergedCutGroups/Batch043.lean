import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch017
import Cycle12.MergedCutCells.Batch164
import Cycle12.MergedCutCells.Batch165
import Cycle12.MergedCutCells.Batch166
import Cycle12.PopulationCertificates.Batch017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch043

def certificate516 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate344,PopulationCertificates.Batch017.certificate344,[MergedCutCells.Batch164.certificate1973,MergedCutCells.Batch164.certificate1974],(289582977526709937/500000000000000000),(some (652855721/500000000)),(1/2),(56729307849235817/200000000000000000),(some (7480888520145087/200000000000000000)),(some (3071252082605993/500000000000000000))⟩
theorem numericValid516 : certificate516.NumericValid := by decide +kernel
theorem cellsSound516 : ∀ c∈certificate516.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1973,MergedCutCells.Batch164.certificate1974], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1973,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1974,List.forall_mem_nil _⟩⟩
theorem cellsNumeric516 : ∀ c∈certificate516.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1973,MergedCutCells.Batch164.certificate1974], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1973,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1974,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid516 : ∀ c∈certificate516.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1973,MergedCutCells.Batch164.certificate1974], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid173,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid173,List.forall_mem_nil _⟩⟩
theorem populationMatches516 : ∀ c∈certificate516.cells, c.population=certificate516.population := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1973,MergedCutCells.Batch164.certificate1974], c.population=PopulationCertificates.Batch017.certificate344
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers516 {x : ℝ} (hx : certificate516.interval.Contains x) : ∃ c∈certificate516.cells, c.region.interval.Contains x := rat_cut_group_covers certificate516 numericValid516 hx

def certificate517 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate344,PopulationCertificates.Batch017.certificate344,[MergedCutCells.Batch164.certificate1975,MergedCutCells.Batch164.certificate1976,MergedCutCells.Batch164.certificate1977],(652855721/500000000),none,(1/2),(281839980023914499/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid517 : certificate517.NumericValid := by decide +kernel
theorem cellsSound517 : ∀ c∈certificate517.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1975,MergedCutCells.Batch164.certificate1976,MergedCutCells.Batch164.certificate1977], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1975,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1976,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1977,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric517 : ∀ c∈certificate517.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1975,MergedCutCells.Batch164.certificate1976,MergedCutCells.Batch164.certificate1977], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1975,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1976,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1977,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid517 : ∀ c∈certificate517.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1975,MergedCutCells.Batch164.certificate1976,MergedCutCells.Batch164.certificate1977], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches517 : ∀ c∈certificate517.cells, c.population=certificate517.population := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1975,MergedCutCells.Batch164.certificate1976,MergedCutCells.Batch164.certificate1977], c.population=PopulationCertificates.Batch017.certificate344
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers517 {x : ℝ} (hx : certificate517.interval.Contains x) : ∃ c∈certificate517.cells, c.region.interval.Contains x := rat_cut_group_covers certificate517 numericValid517 hx

def certificate518 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate345,PopulationCertificates.Batch017.certificate345,[MergedCutCells.Batch164.certificate1978,MergedCutCells.Batch164.certificate1979],(2402239539803458241/500000000000000000),none,(1/2),(750371959181614883/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid518 : certificate518.NumericValid := by decide +kernel
theorem cellsSound518 : ∀ c∈certificate518.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1978,MergedCutCells.Batch164.certificate1979], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1978,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.sound1979,List.forall_mem_nil _⟩⟩
theorem cellsNumeric518 : ∀ c∈certificate518.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1978,MergedCutCells.Batch164.certificate1979], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1978,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch164.numericValid1979,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid518 : ∀ c∈certificate518.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1978,MergedCutCells.Batch164.certificate1979], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches518 : ∀ c∈certificate518.cells, c.population=certificate518.population := by
  change ∀ c∈[MergedCutCells.Batch164.certificate1978,MergedCutCells.Batch164.certificate1979], c.population=PopulationCertificates.Batch017.certificate345
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers518 {x : ℝ} (hx : certificate518.interval.Contains x) : ∃ c∈certificate518.cells, c.region.interval.Contains x := rat_cut_group_covers certificate518 numericValid518 hx

def certificate519 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate346,PopulationCertificates.Batch017.certificate346,[MergedCutCells.Batch165.certificate1980,MergedCutCells.Batch165.certificate1981],(145565588156558711/250000000000000000),(some (639803517/500000000)),(1/2),(71116292470777329/250000000000000000),(some (44358338609879409/1000000000000000000)),(some (3769470964153143/500000000000000000))⟩
theorem numericValid519 : certificate519.NumericValid := by decide +kernel
theorem cellsSound519 : ∀ c∈certificate519.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1980,MergedCutCells.Batch165.certificate1981], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1980,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1981,List.forall_mem_nil _⟩⟩
theorem cellsNumeric519 : ∀ c∈certificate519.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1980,MergedCutCells.Batch165.certificate1981], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1980,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1981,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid519 : ∀ c∈certificate519.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1980,MergedCutCells.Batch165.certificate1981], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid174,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid174,List.forall_mem_nil _⟩⟩
theorem populationMatches519 : ∀ c∈certificate519.cells, c.population=certificate519.population := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1980,MergedCutCells.Batch165.certificate1981], c.population=PopulationCertificates.Batch017.certificate346
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers519 {x : ℝ} (hx : certificate519.interval.Contains x) : ∃ c∈certificate519.cells, c.region.interval.Contains x := rat_cut_group_covers certificate519 numericValid519 hx

def certificate520 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate346,PopulationCertificates.Batch017.certificate346,[MergedCutCells.Batch165.certificate1982,MergedCutCells.Batch165.certificate1983,MergedCutCells.Batch165.certificate1984],(639803517/500000000),none,(1/2),(141057470999819311/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid520 : certificate520.NumericValid := by decide +kernel
theorem cellsSound520 : ∀ c∈certificate520.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1982,MergedCutCells.Batch165.certificate1983,MergedCutCells.Batch165.certificate1984], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1982,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1983,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1984,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric520 : ∀ c∈certificate520.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1982,MergedCutCells.Batch165.certificate1983,MergedCutCells.Batch165.certificate1984], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1982,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1983,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1984,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid520 : ∀ c∈certificate520.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1982,MergedCutCells.Batch165.certificate1983,MergedCutCells.Batch165.certificate1984], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches520 : ∀ c∈certificate520.cells, c.population=certificate520.population := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1982,MergedCutCells.Batch165.certificate1983,MergedCutCells.Batch165.certificate1984], c.population=PopulationCertificates.Batch017.certificate346
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers520 {x : ℝ} (hx : certificate520.interval.Contains x) : ∃ c∈certificate520.cells, c.region.interval.Contains x := rat_cut_group_covers certificate520 numericValid520 hx

def certificate521 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate347,PopulationCertificates.Batch017.certificate347,[MergedCutCells.Batch165.certificate1985,MergedCutCells.Batch165.certificate1986],(2373836221299913911/500000000000000000),none,(1/2),(1482044014366091357/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid521 : certificate521.NumericValid := by decide +kernel
theorem cellsSound521 : ∀ c∈certificate521.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1985,MergedCutCells.Batch165.certificate1986], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1985,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1986,List.forall_mem_nil _⟩⟩
theorem cellsNumeric521 : ∀ c∈certificate521.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1985,MergedCutCells.Batch165.certificate1986], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1985,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1986,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid521 : ∀ c∈certificate521.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1985,MergedCutCells.Batch165.certificate1986], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches521 : ∀ c∈certificate521.cells, c.population=certificate521.population := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1985,MergedCutCells.Batch165.certificate1986], c.population=PopulationCertificates.Batch017.certificate347
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers521 {x : ℝ} (hx : certificate521.interval.Contains x) : ∃ c∈certificate521.cells, c.region.interval.Contains x := rat_cut_group_covers certificate521 numericValid521 hx

def certificate522 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate348,PopulationCertificates.Batch017.certificate348,[MergedCutCells.Batch165.certificate1987,MergedCutCells.Batch165.certificate1988],(58574648335077559/100000000000000000),(some (257195581/200000000)),(1/2),(285355320765708619/1000000000000000000),(some (52026493649062901/1000000000000000000)),(some (2285812250937881/250000000000000000))⟩
theorem numericValid522 : certificate522.NumericValid := by decide +kernel
theorem cellsSound522 : ∀ c∈certificate522.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1987,MergedCutCells.Batch165.certificate1988], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1987,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1988,List.forall_mem_nil _⟩⟩
theorem cellsNumeric522 : ∀ c∈certificate522.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1987,MergedCutCells.Batch165.certificate1988], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1987,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1988,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid522 : ∀ c∈certificate522.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1987,MergedCutCells.Batch165.certificate1988], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid175,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid175,List.forall_mem_nil _⟩⟩
theorem populationMatches522 : ∀ c∈certificate522.cells, c.population=certificate522.population := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1987,MergedCutCells.Batch165.certificate1988], c.population=PopulationCertificates.Batch017.certificate348
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers522 {x : ℝ} (hx : certificate522.interval.Contains x) : ∃ c∈certificate522.cells, c.region.interval.Contains x := rat_cut_group_covers certificate522 numericValid522 hx

def certificate523 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate348,PopulationCertificates.Batch017.certificate348,[MergedCutCells.Batch165.certificate1989,MergedCutCells.Batch165.certificate1990,MergedCutCells.Batch165.certificate1991],(257195581/200000000),none,(1/2),(282405278447697889/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid523 : certificate523.NumericValid := by decide +kernel
theorem cellsSound523 : ∀ c∈certificate523.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1989,MergedCutCells.Batch165.certificate1990,MergedCutCells.Batch165.certificate1991], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1990,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.sound1991,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric523 : ∀ c∈certificate523.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1989,MergedCutCells.Batch165.certificate1990,MergedCutCells.Batch165.certificate1991], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1989,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1990,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch165.numericValid1991,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid523 : ∀ c∈certificate523.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1989,MergedCutCells.Batch165.certificate1990,MergedCutCells.Batch165.certificate1991], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches523 : ∀ c∈certificate523.cells, c.population=certificate523.population := by
  change ∀ c∈[MergedCutCells.Batch165.certificate1989,MergedCutCells.Batch165.certificate1990,MergedCutCells.Batch165.certificate1991], c.population=PopulationCertificates.Batch017.certificate348
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers523 {x : ℝ} (hx : certificate523.interval.Contains x) : ∃ c∈certificate523.cells, c.region.interval.Contains x := rat_cut_group_covers certificate523 numericValid523 hx

def certificate524 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate349,PopulationCertificates.Batch017.certificate349,[MergedCutCells.Batch166.certificate1992,MergedCutCells.Batch166.certificate1993],(2402003004088827699/500000000000000000),none,(1/2),(1537372064001882737/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid524 : certificate524.NumericValid := by decide +kernel
theorem cellsSound524 : ∀ c∈certificate524.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1992,MergedCutCells.Batch166.certificate1993], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound1992,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound1993,List.forall_mem_nil _⟩⟩
theorem cellsNumeric524 : ∀ c∈certificate524.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1992,MergedCutCells.Batch166.certificate1993], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid1992,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid1993,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid524 : ∀ c∈certificate524.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1992,MergedCutCells.Batch166.certificate1993], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches524 : ∀ c∈certificate524.cells, c.population=certificate524.population := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1992,MergedCutCells.Batch166.certificate1993], c.population=PopulationCertificates.Batch017.certificate349
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers524 {x : ℝ} (hx : certificate524.interval.Contains x) : ∃ c∈certificate524.cells, c.region.interval.Contains x := rat_cut_group_covers certificate524 numericValid524 hx

def certificate525 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate350,PopulationCertificates.Batch017.certificate350,[MergedCutCells.Batch166.certificate1994,MergedCutCells.Batch166.certificate1995],(587392084229440781/1000000000000000000),(some (1262762911/1000000000)),(1/2),(275463617738183141/1000000000000000000),(some (59796772303822341/1000000000000000000)),(some (1354169940615399/125000000000000000))⟩
theorem numericValid525 : certificate525.NumericValid := by decide +kernel
theorem cellsSound525 : ∀ c∈certificate525.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1994,MergedCutCells.Batch166.certificate1995], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound1994,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound1995,List.forall_mem_nil _⟩⟩
theorem cellsNumeric525 : ∀ c∈certificate525.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1994,MergedCutCells.Batch166.certificate1995], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid1994,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid1995,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid525 : ∀ c∈certificate525.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1994,MergedCutCells.Batch166.certificate1995], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid176,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy008.valid176,List.forall_mem_nil _⟩⟩
theorem populationMatches525 : ∀ c∈certificate525.cells, c.population=certificate525.population := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1994,MergedCutCells.Batch166.certificate1995], c.population=PopulationCertificates.Batch017.certificate350
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers525 {x : ℝ} (hx : certificate525.interval.Contains x) : ∃ c∈certificate525.cells, c.region.interval.Contains x := rat_cut_group_covers certificate525 numericValid525 hx

def certificate526 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate350,PopulationCertificates.Batch017.certificate350,[MergedCutCells.Batch166.certificate1996,MergedCutCells.Batch166.certificate1997,MergedCutCells.Batch166.certificate1998,MergedCutCells.Batch166.certificate1999],(1262762911/1000000000),none,(1/2),(272087688399117397/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid526 : certificate526.NumericValid := by decide +kernel
theorem cellsSound526 : ∀ c∈certificate526.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1996,MergedCutCells.Batch166.certificate1997,MergedCutCells.Batch166.certificate1998,MergedCutCells.Batch166.certificate1999], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound1996,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound1997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound1998,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound1999,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric526 : ∀ c∈certificate526.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1996,MergedCutCells.Batch166.certificate1997,MergedCutCells.Batch166.certificate1998,MergedCutCells.Batch166.certificate1999], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid1996,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid1997,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid1998,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid1999,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid526 : ∀ c∈certificate526.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1996,MergedCutCells.Batch166.certificate1997,MergedCutCells.Batch166.certificate1998,MergedCutCells.Batch166.certificate1999], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches526 : ∀ c∈certificate526.cells, c.population=certificate526.population := by
  change ∀ c∈[MergedCutCells.Batch166.certificate1996,MergedCutCells.Batch166.certificate1997,MergedCutCells.Batch166.certificate1998,MergedCutCells.Batch166.certificate1999], c.population=PopulationCertificates.Batch017.certificate350
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers526 {x : ℝ} (hx : certificate526.interval.Contains x) : ∃ c∈certificate526.cells, c.region.interval.Contains x := rat_cut_group_covers certificate526 numericValid526 hx

def certificate527 : RatCutGroup := ⟨GeometryCertificates.Batch017.certificate351,PopulationCertificates.Batch017.certificate351,[MergedCutCells.Batch166.certificate2000,MergedCutCells.Batch166.certificate2001],(4883574185300548147/1000000000000000000),none,(1/2),(199270375090537853/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid527 : certificate527.NumericValid := by decide +kernel
theorem cellsSound527 : ∀ c∈certificate527.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch166.certificate2000,MergedCutCells.Batch166.certificate2001], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound2000,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.sound2001,List.forall_mem_nil _⟩⟩
theorem cellsNumeric527 : ∀ c∈certificate527.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate2000,MergedCutCells.Batch166.certificate2001], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid2000,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch166.numericValid2001,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid527 : ∀ c∈certificate527.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch166.certificate2000,MergedCutCells.Batch166.certificate2001], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches527 : ∀ c∈certificate527.cells, c.population=certificate527.population := by
  change ∀ c∈[MergedCutCells.Batch166.certificate2000,MergedCutCells.Batch166.certificate2001], c.population=PopulationCertificates.Batch017.certificate351
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers527 {x : ℝ} (hx : certificate527.interval.Contains x) : ∃ c∈certificate527.cells, c.region.interval.Contains x := rat_cut_group_covers certificate527 numericValid527 hx

end Cycle12.MergedCutGroups.Batch043
