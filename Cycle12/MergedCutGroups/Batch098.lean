import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch039
import Cycle12.MergedCutCells.Batch343
import Cycle12.MergedCutCells.Batch344
import Cycle12.MergedCutCells.Batch345
import Cycle12.PopulationCertificates.Batch039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch098

def certificate1176 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate784,PopulationCertificates.Batch039.certificate784,[MergedCutCells.Batch343.certificate4118,MergedCutCells.Batch343.certificate4119],(173057148871508469/250000000000000000),(some (1104722559/1000000000)),(1/2),(616663770021962477/1000000000000000000),(some (122815667050624143/1000000000000000000)),(some (13313693316077/500000000000000))⟩
theorem numericValid1176 : certificate1176.NumericValid := by decide +kernel
theorem cellsSound1176 : ∀ c∈certificate1176.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4118,MergedCutCells.Batch343.certificate4119], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4119,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1176 : ∀ c∈certificate1176.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4118,MergedCutCells.Batch343.certificate4119], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4119,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1176 : ∀ c∈certificate1176.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4118,MergedCutCells.Batch343.certificate4119], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid393,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid393,List.forall_mem_nil _⟩⟩
theorem populationMatches1176 : ∀ c∈certificate1176.cells, c.population=certificate1176.population := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4118,MergedCutCells.Batch343.certificate4119], c.population=PopulationCertificates.Batch039.certificate784
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1176 {x : ℝ} (hx : certificate1176.interval.Contains x) : ∃ c∈certificate1176.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1176 numericValid1176 hx

def certificate1177 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate784,PopulationCertificates.Batch039.certificate784,[MergedCutCells.Batch343.certificate4120,MergedCutCells.Batch343.certificate4121,MergedCutCells.Batch343.certificate4122,MergedCutCells.Batch343.certificate4123],(1104722559/1000000000),none,(1/2),(606265931950545071/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1177 : certificate1177.NumericValid := by decide +kernel
theorem cellsSound1177 : ∀ c∈certificate1177.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4120,MergedCutCells.Batch343.certificate4121,MergedCutCells.Batch343.certificate4122,MergedCutCells.Batch343.certificate4123], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4120,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4123,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1177 : ∀ c∈certificate1177.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4120,MergedCutCells.Batch343.certificate4121,MergedCutCells.Batch343.certificate4122,MergedCutCells.Batch343.certificate4123], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4120,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4121,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4122,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4123,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1177 : ∀ c∈certificate1177.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4120,MergedCutCells.Batch343.certificate4121,MergedCutCells.Batch343.certificate4122,MergedCutCells.Batch343.certificate4123], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1177 : ∀ c∈certificate1177.cells, c.population=certificate1177.population := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4120,MergedCutCells.Batch343.certificate4121,MergedCutCells.Batch343.certificate4122,MergedCutCells.Batch343.certificate4123], c.population=PopulationCertificates.Batch039.certificate784
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1177 {x : ℝ} (hx : certificate1177.interval.Contains x) : ∃ c∈certificate1177.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1177 numericValid1177 hx

def certificate1178 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate785,PopulationCertificates.Batch039.certificate785,[MergedCutCells.Batch343.certificate4124,MergedCutCells.Batch343.certificate4125],(6291194853624526439/250000000000000000),none,(1/2),(9531231178368668933/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1178 : certificate1178.NumericValid := by decide +kernel
theorem cellsSound1178 : ∀ c∈certificate1178.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4124,MergedCutCells.Batch343.certificate4125], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4124,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4125,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1178 : ∀ c∈certificate1178.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4124,MergedCutCells.Batch343.certificate4125], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4124,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4125,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1178 : ∀ c∈certificate1178.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4124,MergedCutCells.Batch343.certificate4125], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1178 : ∀ c∈certificate1178.cells, c.population=certificate1178.population := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4124,MergedCutCells.Batch343.certificate4125], c.population=PopulationCertificates.Batch039.certificate785
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1178 {x : ℝ} (hx : certificate1178.interval.Contains x) : ∃ c∈certificate1178.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1178 numericValid1178 hx

def certificate1179 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate786,PopulationCertificates.Batch039.certificate786,[MergedCutCells.Batch343.certificate4126,MergedCutCells.Batch343.certificate4127,MergedCutCells.Batch344.certificate4128],(352182789204628163/500000000000000000),(some (8780431/8000000)),(1/2),(700279654223987083/1000000000000000000),(some (31513369549972187/250000000000000000)),(some (6882851312215891/250000000000000000))⟩
theorem numericValid1179 : certificate1179.NumericValid := by decide +kernel
theorem cellsSound1179 : ∀ c∈certificate1179.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4126,MergedCutCells.Batch343.certificate4127,MergedCutCells.Batch344.certificate4128], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4126,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.sound4127,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4128,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1179 : ∀ c∈certificate1179.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4126,MergedCutCells.Batch343.certificate4127,MergedCutCells.Batch344.certificate4128], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4126,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch343.numericValid4127,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4128,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1179 : ∀ c∈certificate1179.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4126,MergedCutCells.Batch343.certificate4127,MergedCutCells.Batch344.certificate4128], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid394,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid394,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid394,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1179 : ∀ c∈certificate1179.cells, c.population=certificate1179.population := by
  change ∀ c∈[MergedCutCells.Batch343.certificate4126,MergedCutCells.Batch343.certificate4127,MergedCutCells.Batch344.certificate4128], c.population=PopulationCertificates.Batch039.certificate786
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1179 {x : ℝ} (hx : certificate1179.interval.Contains x) : ∃ c∈certificate1179.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1179 numericValid1179 hx

def certificate1180 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate786,PopulationCertificates.Batch039.certificate786,[MergedCutCells.Batch344.certificate4129,MergedCutCells.Batch344.certificate4130,MergedCutCells.Batch344.certificate4131,MergedCutCells.Batch344.certificate4132],(8780431/8000000),none,(1/2),(344810394118505279/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1180 : certificate1180.NumericValid := by decide +kernel
theorem cellsSound1180 : ∀ c∈certificate1180.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4129,MergedCutCells.Batch344.certificate4130,MergedCutCells.Batch344.certificate4131,MergedCutCells.Batch344.certificate4132], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4130,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4132,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1180 : ∀ c∈certificate1180.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4129,MergedCutCells.Batch344.certificate4130,MergedCutCells.Batch344.certificate4131,MergedCutCells.Batch344.certificate4132], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4129,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4130,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4131,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4132,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1180 : ∀ c∈certificate1180.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4129,MergedCutCells.Batch344.certificate4130,MergedCutCells.Batch344.certificate4131,MergedCutCells.Batch344.certificate4132], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1180 : ∀ c∈certificate1180.cells, c.population=certificate1180.population := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4129,MergedCutCells.Batch344.certificate4130,MergedCutCells.Batch344.certificate4131,MergedCutCells.Batch344.certificate4132], c.population=PopulationCertificates.Batch039.certificate786
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1180 {x : ℝ} (hx : certificate1180.interval.Contains x) : ∃ c∈certificate1180.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1180 numericValid1180 hx

def certificate1181 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate787,PopulationCertificates.Batch039.certificate787,[MergedCutCells.Batch344.certificate4133,MergedCutCells.Batch344.certificate4134],(1565974799311868649/62500000000000000),none,(1/2),(9726452355610722551/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1181 : certificate1181.NumericValid := by decide +kernel
theorem cellsSound1181 : ∀ c∈certificate1181.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4133,MergedCutCells.Batch344.certificate4134], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4134,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1181 : ∀ c∈certificate1181.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4133,MergedCutCells.Batch344.certificate4134], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4133,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4134,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1181 : ∀ c∈certificate1181.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4133,MergedCutCells.Batch344.certificate4134], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1181 : ∀ c∈certificate1181.cells, c.population=certificate1181.population := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4133,MergedCutCells.Batch344.certificate4134], c.population=PopulationCertificates.Batch039.certificate787
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1181 {x : ℝ} (hx : certificate1181.interval.Contains x) : ∃ c∈certificate1181.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1181 numericValid1181 hx

def certificate1182 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate788,PopulationCertificates.Batch039.certificate788,[MergedCutCells.Batch344.certificate4135,MergedCutCells.Batch344.certificate4136,MergedCutCells.Batch344.certificate4137],(142801303315325107/200000000000000000),(some (1111089829/1000000000)),(1/2),(774593784717983671/1000000000000000000),(some (511963251319721/4000000000000000)),(some (7019114590047393/250000000000000000))⟩
theorem numericValid1182 : certificate1182.NumericValid := by decide +kernel
theorem cellsSound1182 : ∀ c∈certificate1182.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4135,MergedCutCells.Batch344.certificate4136,MergedCutCells.Batch344.certificate4137], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4137,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1182 : ∀ c∈certificate1182.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4135,MergedCutCells.Batch344.certificate4136,MergedCutCells.Batch344.certificate4137], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4135,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4136,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4137,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1182 : ∀ c∈certificate1182.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4135,MergedCutCells.Batch344.certificate4136,MergedCutCells.Batch344.certificate4137], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid395,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid395,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid395,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1182 : ∀ c∈certificate1182.cells, c.population=certificate1182.population := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4135,MergedCutCells.Batch344.certificate4136,MergedCutCells.Batch344.certificate4137], c.population=PopulationCertificates.Batch039.certificate788
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1182 {x : ℝ} (hx : certificate1182.interval.Contains x) : ∃ c∈certificate1182.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1182 numericValid1182 hx

def certificate1183 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate788,PopulationCertificates.Batch039.certificate788,[MergedCutCells.Batch344.certificate4138,MergedCutCells.Batch344.certificate4139,MergedCutCells.Batch345.certificate4140,MergedCutCells.Batch345.certificate4141],(1111089829/1000000000),none,(1/2),(763248546587409751/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1183 : certificate1183.NumericValid := by decide +kernel
theorem cellsSound1183 : ∀ c∈certificate1183.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4138,MergedCutCells.Batch344.certificate4139,MergedCutCells.Batch345.certificate4140,MergedCutCells.Batch345.certificate4141], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4138,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.sound4139,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4141,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1183 : ∀ c∈certificate1183.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4138,MergedCutCells.Batch344.certificate4139,MergedCutCells.Batch345.certificate4140,MergedCutCells.Batch345.certificate4141], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4138,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch344.numericValid4139,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4140,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4141,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1183 : ∀ c∈certificate1183.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4138,MergedCutCells.Batch344.certificate4139,MergedCutCells.Batch345.certificate4140,MergedCutCells.Batch345.certificate4141], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1183 : ∀ c∈certificate1183.cells, c.population=certificate1183.population := by
  change ∀ c∈[MergedCutCells.Batch344.certificate4138,MergedCutCells.Batch344.certificate4139,MergedCutCells.Batch345.certificate4140,MergedCutCells.Batch345.certificate4141], c.population=PopulationCertificates.Batch039.certificate788
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1183 {x : ℝ} (hx : certificate1183.interval.Contains x) : ∃ c∈certificate1183.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1183 numericValid1183 hx

def certificate1184 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate789,PopulationCertificates.Batch039.certificate789,[MergedCutCells.Batch345.certificate4142,MergedCutCells.Batch345.certificate4143],(12527302198200351329/500000000000000000),none,(1/2),(4968597688898031243/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1184 : certificate1184.NumericValid := by decide +kernel
theorem cellsSound1184 : ∀ c∈certificate1184.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4142,MergedCutCells.Batch345.certificate4143], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4143,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1184 : ∀ c∈certificate1184.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4142,MergedCutCells.Batch345.certificate4143], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4142,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4143,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1184 : ∀ c∈certificate1184.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4142,MergedCutCells.Batch345.certificate4143], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1184 : ∀ c∈certificate1184.cells, c.population=certificate1184.population := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4142,MergedCutCells.Batch345.certificate4143], c.population=PopulationCertificates.Batch039.certificate789
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1184 {x : ℝ} (hx : certificate1184.interval.Contains x) : ∃ c∈certificate1184.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1184 numericValid1184 hx

def certificate1185 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate790,PopulationCertificates.Batch039.certificate790,[MergedCutCells.Batch345.certificate4144,MergedCutCells.Batch345.certificate4145],(22526053143828977/31250000000000000),(some (68502017/62500000)),(1/2),(828075166841955821/1000000000000000000),(some (16156953843917183/125000000000000000)),(some (28433971537209159/1000000000000000000))⟩
theorem numericValid1185 : certificate1185.NumericValid := by decide +kernel
theorem cellsSound1185 : ∀ c∈certificate1185.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4144,MergedCutCells.Batch345.certificate4145], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4145,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1185 : ∀ c∈certificate1185.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4144,MergedCutCells.Batch345.certificate4145], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4144,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4145,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1185 : ∀ c∈certificate1185.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4144,MergedCutCells.Batch345.certificate4145], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid396,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy019.valid396,List.forall_mem_nil _⟩⟩
theorem populationMatches1185 : ∀ c∈certificate1185.cells, c.population=certificate1185.population := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4144,MergedCutCells.Batch345.certificate4145], c.population=PopulationCertificates.Batch039.certificate790
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1185 {x : ℝ} (hx : certificate1185.interval.Contains x) : ∃ c∈certificate1185.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1185 numericValid1185 hx

def certificate1186 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate790,PopulationCertificates.Batch039.certificate790,[MergedCutCells.Batch345.certificate4146,MergedCutCells.Batch345.certificate4147,MergedCutCells.Batch345.certificate4148,MergedCutCells.Batch345.certificate4149],(68502017/62500000),none,(1/2),(204253673452680889/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1186 : certificate1186.NumericValid := by decide +kernel
theorem cellsSound1186 : ∀ c∈certificate1186.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4146,MergedCutCells.Batch345.certificate4147,MergedCutCells.Batch345.certificate4148,MergedCutCells.Batch345.certificate4149], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4147,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4149,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1186 : ∀ c∈certificate1186.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4146,MergedCutCells.Batch345.certificate4147,MergedCutCells.Batch345.certificate4148,MergedCutCells.Batch345.certificate4149], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4146,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4147,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4148,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4149,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1186 : ∀ c∈certificate1186.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4146,MergedCutCells.Batch345.certificate4147,MergedCutCells.Batch345.certificate4148,MergedCutCells.Batch345.certificate4149], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1186 : ∀ c∈certificate1186.cells, c.population=certificate1186.population := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4146,MergedCutCells.Batch345.certificate4147,MergedCutCells.Batch345.certificate4148,MergedCutCells.Batch345.certificate4149], c.population=PopulationCertificates.Batch039.certificate790
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1186 {x : ℝ} (hx : certificate1186.interval.Contains x) : ∃ c∈certificate1186.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1186 numericValid1186 hx

def certificate1187 : RatCutGroup := ⟨GeometryCertificates.Batch039.certificate791,PopulationCertificates.Batch039.certificate791,[MergedCutCells.Batch345.certificate4150,MergedCutCells.Batch345.certificate4151],(12479702866627355967/500000000000000000),none,(1/2),(1003993788937938867/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1187 : certificate1187.NumericValid := by decide +kernel
theorem cellsSound1187 : ∀ c∈certificate1187.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4150,MergedCutCells.Batch345.certificate4151], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4150,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.sound4151,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1187 : ∀ c∈certificate1187.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4150,MergedCutCells.Batch345.certificate4151], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4150,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch345.numericValid4151,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1187 : ∀ c∈certificate1187.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4150,MergedCutCells.Batch345.certificate4151], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1187 : ∀ c∈certificate1187.cells, c.population=certificate1187.population := by
  change ∀ c∈[MergedCutCells.Batch345.certificate4150,MergedCutCells.Batch345.certificate4151], c.population=PopulationCertificates.Batch039.certificate791
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1187 {x : ℝ} (hx : certificate1187.interval.Contains x) : ∃ c∈certificate1187.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1187 numericValid1187 hx

end Cycle12.MergedCutGroups.Batch098
