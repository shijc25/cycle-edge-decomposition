import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch001
import Cycle12.MergedCutCells.Batch010
import Cycle12.MergedCutCells.Batch011
import Cycle12.MergedCutCells.Batch012
import Cycle12.MergedCutCells.Batch013
import Cycle12.PopulationCertificates.Batch001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch004

def certificate48 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate32,PopulationCertificates.Batch001.certificate32,[MergedCutCells.Batch010.certificate122,MergedCutCells.Batch010.certificate123,MergedCutCells.Batch010.certificate124],(159149696416131567/250000000000000000),(some (1208543893/1000000000)),(1/2),(229067220900134253/1000000000000000000),(some (190236273049480777/1000000000000000000)),(some (11804117289452677/250000000000000000))⟩
theorem numericValid48 : certificate48.NumericValid := by decide +kernel
theorem cellsSound48 : ∀ c∈certificate48.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch010.certificate122,MergedCutCells.Batch010.certificate123,MergedCutCells.Batch010.certificate124], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound124,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric48 : ∀ c∈certificate48.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate122,MergedCutCells.Batch010.certificate123,MergedCutCells.Batch010.certificate124], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid123,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid124,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid48 : ∀ c∈certificate48.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate122,MergedCutCells.Batch010.certificate123,MergedCutCells.Batch010.certificate124], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid17,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid17,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid17,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches48 : ∀ c∈certificate48.cells, c.population=certificate48.population := by
  change ∀ c∈[MergedCutCells.Batch010.certificate122,MergedCutCells.Batch010.certificate123,MergedCutCells.Batch010.certificate124], c.population=PopulationCertificates.Batch001.certificate32
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers48 {x : ℝ} (hx : certificate48.interval.Contains x) : ∃ c∈certificate48.cells, c.region.interval.Contains x := rat_cut_group_covers certificate48 numericValid48 hx

def certificate49 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate32,PopulationCertificates.Batch001.certificate32,[MergedCutCells.Batch010.certificate125,MergedCutCells.Batch010.certificate126,MergedCutCells.Batch010.certificate127,MergedCutCells.Batch010.certificate128],(1208543893/1000000000),none,(1/2),(53872450301677121/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid49 : certificate49.NumericValid := by decide +kernel
theorem cellsSound49 : ∀ c∈certificate49.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch010.certificate125,MergedCutCells.Batch010.certificate126,MergedCutCells.Batch010.certificate127,MergedCutCells.Batch010.certificate128], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound126,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound127,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound128,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric49 : ∀ c∈certificate49.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate125,MergedCutCells.Batch010.certificate126,MergedCutCells.Batch010.certificate127,MergedCutCells.Batch010.certificate128], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid125,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid126,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid127,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid128,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid49 : ∀ c∈certificate49.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate125,MergedCutCells.Batch010.certificate126,MergedCutCells.Batch010.certificate127,MergedCutCells.Batch010.certificate128], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches49 : ∀ c∈certificate49.cells, c.population=certificate49.population := by
  change ∀ c∈[MergedCutCells.Batch010.certificate125,MergedCutCells.Batch010.certificate126,MergedCutCells.Batch010.certificate127,MergedCutCells.Batch010.certificate128], c.population=PopulationCertificates.Batch001.certificate32
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers49 {x : ℝ} (hx : certificate49.interval.Contains x) : ∃ c∈certificate49.cells, c.region.interval.Contains x := rat_cut_group_covers certificate49 numericValid49 hx

def certificate50 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate33,PopulationCertificates.Batch001.certificate33,[MergedCutCells.Batch010.certificate129,MergedCutCells.Batch010.certificate130],(706094556336518541/200000000000000000),none,(1/2),(369026669387329231/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid50 : certificate50.NumericValid := by decide +kernel
theorem cellsSound50 : ∀ c∈certificate50.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch010.certificate129,MergedCutCells.Batch010.certificate130], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound130,List.forall_mem_nil _⟩⟩
theorem cellsNumeric50 : ∀ c∈certificate50.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate129,MergedCutCells.Batch010.certificate130], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid130,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid50 : ∀ c∈certificate50.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate129,MergedCutCells.Batch010.certificate130], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches50 : ∀ c∈certificate50.cells, c.population=certificate50.population := by
  change ∀ c∈[MergedCutCells.Batch010.certificate129,MergedCutCells.Batch010.certificate130], c.population=PopulationCertificates.Batch001.certificate33
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers50 {x : ℝ} (hx : certificate50.interval.Contains x) : ∃ c∈certificate50.cells, c.region.interval.Contains x := rat_cut_group_covers certificate50 numericValid50 hx

def certificate51 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate34,PopulationCertificates.Batch001.certificate34,[MergedCutCells.Batch010.certificate131,MergedCutCells.Batch011.certificate132,MergedCutCells.Batch011.certificate133],(643743465419417109/1000000000000000000),(some (1190567149/1000000000)),(1/2),(45185238917861759/200000000000000000),(some (205298084835789153/1000000000000000000)),(some (52322619793003051/1000000000000000000))⟩
theorem numericValid51 : certificate51.NumericValid := by decide +kernel
theorem cellsSound51 : ∀ c∈certificate51.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch010.certificate131,MergedCutCells.Batch011.certificate132,MergedCutCells.Batch011.certificate133], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.sound131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound132,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound133,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric51 : ∀ c∈certificate51.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate131,MergedCutCells.Batch011.certificate132,MergedCutCells.Batch011.certificate133], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch010.numericValid131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid132,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid133,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid51 : ∀ c∈certificate51.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch010.certificate131,MergedCutCells.Batch011.certificate132,MergedCutCells.Batch011.certificate133], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid18,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid18,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid18,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches51 : ∀ c∈certificate51.cells, c.population=certificate51.population := by
  change ∀ c∈[MergedCutCells.Batch010.certificate131,MergedCutCells.Batch011.certificate132,MergedCutCells.Batch011.certificate133], c.population=PopulationCertificates.Batch001.certificate34
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers51 {x : ℝ} (hx : certificate51.interval.Contains x) : ∃ c∈certificate51.cells, c.region.interval.Contains x := rat_cut_group_covers certificate51 numericValid51 hx

def certificate52 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate34,PopulationCertificates.Batch001.certificate34,[MergedCutCells.Batch011.certificate134,MergedCutCells.Batch011.certificate135,MergedCutCells.Batch011.certificate136,MergedCutCells.Batch011.certificate137],(1190567149/1000000000),none,(1/2),(52741922599683703/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid52 : certificate52.NumericValid := by decide +kernel
theorem cellsSound52 : ∀ c∈certificate52.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch011.certificate134,MergedCutCells.Batch011.certificate135,MergedCutCells.Batch011.certificate136,MergedCutCells.Batch011.certificate137], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound134,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound137,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric52 : ∀ c∈certificate52.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch011.certificate134,MergedCutCells.Batch011.certificate135,MergedCutCells.Batch011.certificate136,MergedCutCells.Batch011.certificate137], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid134,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid137,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid52 : ∀ c∈certificate52.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch011.certificate134,MergedCutCells.Batch011.certificate135,MergedCutCells.Batch011.certificate136,MergedCutCells.Batch011.certificate137], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches52 : ∀ c∈certificate52.cells, c.population=certificate52.population := by
  change ∀ c∈[MergedCutCells.Batch011.certificate134,MergedCutCells.Batch011.certificate135,MergedCutCells.Batch011.certificate136,MergedCutCells.Batch011.certificate137], c.population=PopulationCertificates.Batch001.certificate34
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers52 {x : ℝ} (hx : certificate52.interval.Contains x) : ∃ c∈certificate52.cells, c.region.interval.Contains x := rat_cut_group_covers certificate52 numericValid52 hx

def certificate53 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate35,PopulationCertificates.Batch001.certificate35,[MergedCutCells.Batch011.certificate138,MergedCutCells.Batch011.certificate139,MergedCutCells.Batch011.certificate140],(692091280134315691/200000000000000000),none,(1/2),(34322550680320981/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid53 : certificate53.NumericValid := by decide +kernel
theorem cellsSound53 : ∀ c∈certificate53.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch011.certificate138,MergedCutCells.Batch011.certificate139,MergedCutCells.Batch011.certificate140], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound138,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound139,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound140,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric53 : ∀ c∈certificate53.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch011.certificate138,MergedCutCells.Batch011.certificate139,MergedCutCells.Batch011.certificate140], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid138,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid139,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid140,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid53 : ∀ c∈certificate53.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch011.certificate138,MergedCutCells.Batch011.certificate139,MergedCutCells.Batch011.certificate140], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches53 : ∀ c∈certificate53.cells, c.population=certificate53.population := by
  change ∀ c∈[MergedCutCells.Batch011.certificate138,MergedCutCells.Batch011.certificate139,MergedCutCells.Batch011.certificate140], c.population=PopulationCertificates.Batch001.certificate35
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers53 {x : ℝ} (hx : certificate53.interval.Contains x) : ∃ c∈certificate53.cells, c.region.interval.Contains x := rat_cut_group_covers certificate53 numericValid53 hx

def certificate54 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate36,PopulationCertificates.Batch001.certificate36,[MergedCutCells.Batch011.certificate141,MergedCutCells.Batch011.certificate142,MergedCutCells.Batch011.certificate143],(32558808725710849/50000000000000000),(some (1177044509/1000000000)),(1/2),(22224813264932001/100000000000000000),(some (110325595883775233/500000000000000000)),(some (57721365009697971/1000000000000000000))⟩
theorem numericValid54 : certificate54.NumericValid := by decide +kernel
theorem cellsSound54 : ∀ c∈certificate54.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch011.certificate141,MergedCutCells.Batch011.certificate142,MergedCutCells.Batch011.certificate143], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound141,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.sound143,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric54 : ∀ c∈certificate54.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch011.certificate141,MergedCutCells.Batch011.certificate142,MergedCutCells.Batch011.certificate143], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid141,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch011.numericValid143,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid54 : ∀ c∈certificate54.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch011.certificate141,MergedCutCells.Batch011.certificate142,MergedCutCells.Batch011.certificate143], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid19,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid19,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid19,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches54 : ∀ c∈certificate54.cells, c.population=certificate54.population := by
  change ∀ c∈[MergedCutCells.Batch011.certificate141,MergedCutCells.Batch011.certificate142,MergedCutCells.Batch011.certificate143], c.population=PopulationCertificates.Batch001.certificate36
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers54 {x : ℝ} (hx : certificate54.interval.Contains x) : ∃ c∈certificate54.cells, c.region.interval.Contains x := rat_cut_group_covers certificate54 numericValid54 hx

def certificate55 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate36,PopulationCertificates.Batch001.certificate36,[MergedCutCells.Batch012.certificate144,MergedCutCells.Batch012.certificate145,MergedCutCells.Batch012.certificate146,MergedCutCells.Batch012.certificate147,MergedCutCells.Batch012.certificate148],(1177044509/1000000000),none,(1/2),(51560271887689019/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid55 : certificate55.NumericValid := by decide +kernel
theorem cellsSound55 : ∀ c∈certificate55.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch012.certificate144,MergedCutCells.Batch012.certificate145,MergedCutCells.Batch012.certificate146,MergedCutCells.Batch012.certificate147,MergedCutCells.Batch012.certificate148], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound145,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound147,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound148,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsNumeric55 : ∀ c∈certificate55.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch012.certificate144,MergedCutCells.Batch012.certificate145,MergedCutCells.Batch012.certificate146,MergedCutCells.Batch012.certificate147,MergedCutCells.Batch012.certificate148], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid145,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid147,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid148,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem cellsEntropyValid55 : ∀ c∈certificate55.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch012.certificate144,MergedCutCells.Batch012.certificate145,MergedCutCells.Batch012.certificate146,MergedCutCells.Batch012.certificate147,MergedCutCells.Batch012.certificate148], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem populationMatches55 : ∀ c∈certificate55.cells, c.population=certificate55.population := by
  change ∀ c∈[MergedCutCells.Batch012.certificate144,MergedCutCells.Batch012.certificate145,MergedCutCells.Batch012.certificate146,MergedCutCells.Batch012.certificate147,MergedCutCells.Batch012.certificate148], c.population=PopulationCertificates.Batch001.certificate36
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem covers55 {x : ℝ} (hx : certificate55.interval.Contains x) : ∃ c∈certificate55.cells, c.region.interval.Contains x := rat_cut_group_covers certificate55 numericValid55 hx

def certificate56 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate37,PopulationCertificates.Batch001.certificate37,[MergedCutCells.Batch012.certificate149,MergedCutCells.Batch012.certificate150,MergedCutCells.Batch012.certificate151],(3501875410708896779/1000000000000000000),none,(1/2),(154783607966616821/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid56 : certificate56.NumericValid := by decide +kernel
theorem cellsSound56 : ∀ c∈certificate56.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch012.certificate149,MergedCutCells.Batch012.certificate150,MergedCutCells.Batch012.certificate151], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound150,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound151,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric56 : ∀ c∈certificate56.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch012.certificate149,MergedCutCells.Batch012.certificate150,MergedCutCells.Batch012.certificate151], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid149,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid150,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid151,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid56 : ∀ c∈certificate56.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch012.certificate149,MergedCutCells.Batch012.certificate150,MergedCutCells.Batch012.certificate151], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches56 : ∀ c∈certificate56.cells, c.population=certificate56.population := by
  change ∀ c∈[MergedCutCells.Batch012.certificate149,MergedCutCells.Batch012.certificate150,MergedCutCells.Batch012.certificate151], c.population=PopulationCertificates.Batch001.certificate37
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers56 {x : ℝ} (hx : certificate56.interval.Contains x) : ∃ c∈certificate56.cells, c.region.interval.Contains x := rat_cut_group_covers certificate56 numericValid56 hx

def certificate57 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate38,PopulationCertificates.Batch001.certificate38,[MergedCutCells.Batch012.certificate152,MergedCutCells.Batch012.certificate153],(164693015638822573/250000000000000000),(some (580048731/500000000)),(1/2),(14091197419815829/62500000000000000),(some (235760729075146927/1000000000000000000)),(some (12645756995938561/200000000000000000))⟩
theorem numericValid57 : certificate57.NumericValid := by decide +kernel
theorem cellsSound57 : ∀ c∈certificate57.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch012.certificate152,MergedCutCells.Batch012.certificate153], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound153,List.forall_mem_nil _⟩⟩
theorem cellsNumeric57 : ∀ c∈certificate57.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch012.certificate152,MergedCutCells.Batch012.certificate153], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid152,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid153,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid57 : ∀ c∈certificate57.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch012.certificate152,MergedCutCells.Batch012.certificate153], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid20,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid20,List.forall_mem_nil _⟩⟩
theorem populationMatches57 : ∀ c∈certificate57.cells, c.population=certificate57.population := by
  change ∀ c∈[MergedCutCells.Batch012.certificate152,MergedCutCells.Batch012.certificate153], c.population=PopulationCertificates.Batch001.certificate38
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers57 {x : ℝ} (hx : certificate57.interval.Contains x) : ∃ c∈certificate57.cells, c.region.interval.Contains x := rat_cut_group_covers certificate57 numericValid57 hx

def certificate58 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate38,PopulationCertificates.Batch001.certificate38,[MergedCutCells.Batch012.certificate154,MergedCutCells.Batch012.certificate155,MergedCutCells.Batch013.certificate156,MergedCutCells.Batch013.certificate157,MergedCutCells.Batch013.certificate158,MergedCutCells.Batch013.certificate159],(580048731/500000000),none,(1/2),(52201985865870529/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid58 : certificate58.NumericValid := by decide +kernel
theorem cellsSound58 : ∀ c∈certificate58.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch012.certificate154,MergedCutCells.Batch012.certificate155,MergedCutCells.Batch013.certificate156,MergedCutCells.Batch013.certificate157,MergedCutCells.Batch013.certificate158,MergedCutCells.Batch013.certificate159], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound154,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.sound155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound157,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound159,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric58 : ∀ c∈certificate58.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch012.certificate154,MergedCutCells.Batch012.certificate155,MergedCutCells.Batch013.certificate156,MergedCutCells.Batch013.certificate157,MergedCutCells.Batch013.certificate158,MergedCutCells.Batch013.certificate159], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid154,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch012.numericValid155,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid156,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid157,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid158,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid159,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid58 : ∀ c∈certificate58.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch012.certificate154,MergedCutCells.Batch012.certificate155,MergedCutCells.Batch013.certificate156,MergedCutCells.Batch013.certificate157,MergedCutCells.Batch013.certificate158,MergedCutCells.Batch013.certificate159], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches58 : ∀ c∈certificate58.cells, c.population=certificate58.population := by
  change ∀ c∈[MergedCutCells.Batch012.certificate154,MergedCutCells.Batch012.certificate155,MergedCutCells.Batch013.certificate156,MergedCutCells.Batch013.certificate157,MergedCutCells.Batch013.certificate158,MergedCutCells.Batch013.certificate159], c.population=PopulationCertificates.Batch001.certificate38
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers58 {x : ℝ} (hx : certificate58.interval.Contains x) : ∃ c∈certificate58.cells, c.region.interval.Contains x := rat_cut_group_covers certificate58 numericValid58 hx

def certificate59 : RatCutGroup := ⟨GeometryCertificates.Batch001.certificate39,PopulationCertificates.Batch001.certificate39,[MergedCutCells.Batch013.certificate160,MergedCutCells.Batch013.certificate161,MergedCutCells.Batch013.certificate162],(880995115915363757/250000000000000000),none,(1/2),(6791604187930767/20000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid59 : certificate59.NumericValid := by decide +kernel
theorem cellsSound59 : ∀ c∈certificate59.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch013.certificate160,MergedCutCells.Batch013.certificate161,MergedCutCells.Batch013.certificate162], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.sound162,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric59 : ∀ c∈certificate59.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch013.certificate160,MergedCutCells.Batch013.certificate161,MergedCutCells.Batch013.certificate162], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid160,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid161,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch013.numericValid162,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid59 : ∀ c∈certificate59.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch013.certificate160,MergedCutCells.Batch013.certificate161,MergedCutCells.Batch013.certificate162], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches59 : ∀ c∈certificate59.cells, c.population=certificate59.population := by
  change ∀ c∈[MergedCutCells.Batch013.certificate160,MergedCutCells.Batch013.certificate161,MergedCutCells.Batch013.certificate162], c.population=PopulationCertificates.Batch001.certificate39
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers59 {x : ℝ} (hx : certificate59.interval.Contains x) : ∃ c∈certificate59.cells, c.region.interval.Contains x := rat_cut_group_covers certificate59 numericValid59 hx

end Cycle12.MergedCutGroups.Batch004
