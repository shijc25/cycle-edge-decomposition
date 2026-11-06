import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch032
import Cycle12.GeometryCertificates.Batch033
import Cycle12.MergedCutCells.Batch304
import Cycle12.MergedCutCells.Batch305
import Cycle12.MergedCutCells.Batch306
import Cycle12.PopulationCertificates.Batch032
import Cycle12.PopulationCertificates.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch082

def certificate984 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate656,PopulationCertificates.Batch032.certificate656,[MergedCutCells.Batch304.certificate3651,MergedCutCells.Batch304.certificate3652],(224960613978373/390625000000000),(some (1332067533/1000000000)),(1/2),(151326000042023259/500000000000000000),(some (76927210192623/62500000000000000)),(some (123048184451893/1000000000000000000))⟩
theorem numericValid984 : certificate984.NumericValid := by decide +kernel
theorem cellsSound984 : ∀ c∈certificate984.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3651,MergedCutCells.Batch304.certificate3652], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3651,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3652,List.forall_mem_nil _⟩⟩
theorem cellsNumeric984 : ∀ c∈certificate984.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3651,MergedCutCells.Batch304.certificate3652], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3651,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3652,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid984 : ∀ c∈certificate984.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3651,MergedCutCells.Batch304.certificate3652], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid329,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid329,List.forall_mem_nil _⟩⟩
theorem populationMatches984 : ∀ c∈certificate984.cells, c.population=certificate984.population := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3651,MergedCutCells.Batch304.certificate3652], c.population=PopulationCertificates.Batch032.certificate656
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers984 {x : ℝ} (hx : certificate984.interval.Contains x) : ∃ c∈certificate984.cells, c.region.interval.Contains x := rat_cut_group_covers certificate984 numericValid984 hx

def certificate985 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate656,PopulationCertificates.Batch032.certificate656,[MergedCutCells.Batch304.certificate3653,MergedCutCells.Batch304.certificate3654,MergedCutCells.Batch304.certificate3655],(1332067533/1000000000),none,(1/2),(151365752768544949/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid985 : certificate985.NumericValid := by decide +kernel
theorem cellsSound985 : ∀ c∈certificate985.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3653,MergedCutCells.Batch304.certificate3654,MergedCutCells.Batch304.certificate3655], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3653,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3654,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3655,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric985 : ∀ c∈certificate985.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3653,MergedCutCells.Batch304.certificate3654,MergedCutCells.Batch304.certificate3655], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3653,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3654,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3655,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid985 : ∀ c∈certificate985.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3653,MergedCutCells.Batch304.certificate3654,MergedCutCells.Batch304.certificate3655], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches985 : ∀ c∈certificate985.cells, c.population=certificate985.population := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3653,MergedCutCells.Batch304.certificate3654,MergedCutCells.Batch304.certificate3655], c.population=PopulationCertificates.Batch032.certificate656
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers985 {x : ℝ} (hx : certificate985.interval.Contains x) : ∃ c∈certificate985.cells, c.region.interval.Contains x := rat_cut_group_covers certificate985 numericValid985 hx

def certificate986 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate657,PopulationCertificates.Batch032.certificate657,[MergedCutCells.Batch304.certificate3656,MergedCutCells.Batch304.certificate3657],(14665424617935302959/1000000000000000000),none,(1/2),(459156851752475389/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid986 : certificate986.NumericValid := by decide +kernel
theorem cellsSound986 : ∀ c∈certificate986.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3656,MergedCutCells.Batch304.certificate3657], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3656,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3657,List.forall_mem_nil _⟩⟩
theorem cellsNumeric986 : ∀ c∈certificate986.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3656,MergedCutCells.Batch304.certificate3657], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3656,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3657,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid986 : ∀ c∈certificate986.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3656,MergedCutCells.Batch304.certificate3657], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches986 : ∀ c∈certificate986.cells, c.population=certificate986.population := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3656,MergedCutCells.Batch304.certificate3657], c.population=PopulationCertificates.Batch032.certificate657
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers986 {x : ℝ} (hx : certificate986.interval.Contains x) : ∃ c∈certificate986.cells, c.region.interval.Contains x := rat_cut_group_covers certificate986 numericValid986 hx

def certificate987 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate658,PopulationCertificates.Batch032.certificate658,[MergedCutCells.Batch304.certificate3658,MergedCutCells.Batch304.certificate3659],(567569639520166127/1000000000000000000),(some (134310811/100000000)),(1/2),(294858311401855713/1000000000000000000),(some (1818087569129089/1000000000000000000)),(some (95005437970157/500000000000000000))⟩
theorem numericValid987 : certificate987.NumericValid := by decide +kernel
theorem cellsSound987 : ∀ c∈certificate987.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3658,MergedCutCells.Batch304.certificate3659], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3658,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3659,List.forall_mem_nil _⟩⟩
theorem cellsNumeric987 : ∀ c∈certificate987.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3658,MergedCutCells.Batch304.certificate3659], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3658,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3659,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid987 : ∀ c∈certificate987.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3658,MergedCutCells.Batch304.certificate3659], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid330,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid330,List.forall_mem_nil _⟩⟩
theorem populationMatches987 : ∀ c∈certificate987.cells, c.population=certificate987.population := by
  change ∀ c∈[MergedCutCells.Batch304.certificate3658,MergedCutCells.Batch304.certificate3659], c.population=PopulationCertificates.Batch032.certificate658
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers987 {x : ℝ} (hx : certificate987.interval.Contains x) : ∃ c∈certificate987.cells, c.region.interval.Contains x := rat_cut_group_covers certificate987 numericValid987 hx

def certificate988 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate658,PopulationCertificates.Batch032.certificate658,[MergedCutCells.Batch305.certificate3660,MergedCutCells.Batch305.certificate3661,MergedCutCells.Batch305.certificate3662],(134310811/100000000),none,(1/2),(58977537434560569/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid988 : certificate988.NumericValid := by decide +kernel
theorem cellsSound988 : ∀ c∈certificate988.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3660,MergedCutCells.Batch305.certificate3661,MergedCutCells.Batch305.certificate3662], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3660,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3662,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric988 : ∀ c∈certificate988.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3660,MergedCutCells.Batch305.certificate3661,MergedCutCells.Batch305.certificate3662], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3660,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3661,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3662,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid988 : ∀ c∈certificate988.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3660,MergedCutCells.Batch305.certificate3661,MergedCutCells.Batch305.certificate3662], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches988 : ∀ c∈certificate988.cells, c.population=certificate988.population := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3660,MergedCutCells.Batch305.certificate3661,MergedCutCells.Batch305.certificate3662], c.population=PopulationCertificates.Batch032.certificate658
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers988 {x : ℝ} (hx : certificate988.interval.Contains x) : ∃ c∈certificate988.cells, c.region.interval.Contains x := rat_cut_group_covers certificate988 numericValid988 hx

def certificate989 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate659,PopulationCertificates.Batch032.certificate659,[MergedCutCells.Batch305.certificate3663,MergedCutCells.Batch305.certificate3664],(741274775824710977/50000000000000000),none,(1/2),(3734202569391995613/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid989 : certificate989.NumericValid := by decide +kernel
theorem cellsSound989 : ∀ c∈certificate989.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3663,MergedCutCells.Batch305.certificate3664], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3663,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3664,List.forall_mem_nil _⟩⟩
theorem cellsNumeric989 : ∀ c∈certificate989.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3663,MergedCutCells.Batch305.certificate3664], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3663,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3664,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid989 : ∀ c∈certificate989.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3663,MergedCutCells.Batch305.certificate3664], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches989 : ∀ c∈certificate989.cells, c.population=certificate989.population := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3663,MergedCutCells.Batch305.certificate3664], c.population=PopulationCertificates.Batch032.certificate659
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers989 {x : ℝ} (hx : certificate989.interval.Contains x) : ∃ c∈certificate989.cells, c.region.interval.Contains x := rat_cut_group_covers certificate989 numericValid989 hx

def certificate990 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate660,PopulationCertificates.Batch033.certificate660,[MergedCutCells.Batch305.certificate3665,MergedCutCells.Batch305.certificate3666],(573473255664974163/1000000000000000000),(some (663726727/500000000)),(1/2),(2381263546204539/8000000000000000),(some (1084958578944437/500000000000000000)),(some (4631370286433/20000000000000000))⟩
theorem numericValid990 : certificate990.NumericValid := by decide +kernel
theorem cellsSound990 : ∀ c∈certificate990.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3665,MergedCutCells.Batch305.certificate3666], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3665,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3666,List.forall_mem_nil _⟩⟩
theorem cellsNumeric990 : ∀ c∈certificate990.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3665,MergedCutCells.Batch305.certificate3666], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3665,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3666,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid990 : ∀ c∈certificate990.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3665,MergedCutCells.Batch305.certificate3666], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid331,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid331,List.forall_mem_nil _⟩⟩
theorem populationMatches990 : ∀ c∈certificate990.cells, c.population=certificate990.population := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3665,MergedCutCells.Batch305.certificate3666], c.population=PopulationCertificates.Batch033.certificate660
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers990 {x : ℝ} (hx : certificate990.interval.Contains x) : ∃ c∈certificate990.cells, c.region.interval.Contains x := rat_cut_group_covers certificate990 numericValid990 hx

def certificate991 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate660,PopulationCertificates.Batch033.certificate660,[MergedCutCells.Batch305.certificate3667,MergedCutCells.Batch305.certificate3668,MergedCutCells.Batch305.certificate3669],(663726727/500000000),none,(1/2),(36778737731190133/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid991 : certificate991.NumericValid := by decide +kernel
theorem cellsSound991 : ∀ c∈certificate991.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3667,MergedCutCells.Batch305.certificate3668,MergedCutCells.Batch305.certificate3669], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3667,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3668,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3669,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric991 : ∀ c∈certificate991.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3667,MergedCutCells.Batch305.certificate3668,MergedCutCells.Batch305.certificate3669], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3667,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3668,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3669,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid991 : ∀ c∈certificate991.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3667,MergedCutCells.Batch305.certificate3668,MergedCutCells.Batch305.certificate3669], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches991 : ∀ c∈certificate991.cells, c.population=certificate991.population := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3667,MergedCutCells.Batch305.certificate3668,MergedCutCells.Batch305.certificate3669], c.population=PopulationCertificates.Batch033.certificate660
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers991 {x : ℝ} (hx : certificate991.interval.Contains x) : ∃ c∈certificate991.cells, c.region.interval.Contains x := rat_cut_group_covers certificate991 numericValid991 hx

def certificate992 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate661,PopulationCertificates.Batch033.certificate661,[MergedCutCells.Batch305.certificate3670,MergedCutCells.Batch305.certificate3671],(3022679692638752243/200000000000000000),none,(1/2),(3808275513206285021/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid992 : certificate992.NumericValid := by decide +kernel
theorem cellsSound992 : ∀ c∈certificate992.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3670,MergedCutCells.Batch305.certificate3671], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.sound3671,List.forall_mem_nil _⟩⟩
theorem cellsNumeric992 : ∀ c∈certificate992.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3670,MergedCutCells.Batch305.certificate3671], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3670,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch305.numericValid3671,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid992 : ∀ c∈certificate992.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3670,MergedCutCells.Batch305.certificate3671], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches992 : ∀ c∈certificate992.cells, c.population=certificate992.population := by
  change ∀ c∈[MergedCutCells.Batch305.certificate3670,MergedCutCells.Batch305.certificate3671], c.population=PopulationCertificates.Batch033.certificate661
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers992 {x : ℝ} (hx : certificate992.interval.Contains x) : ∃ c∈certificate992.cells, c.region.interval.Contains x := rat_cut_group_covers certificate992 numericValid992 hx

def certificate993 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate662,PopulationCertificates.Batch033.certificate662,[MergedCutCells.Batch306.certificate3672,MergedCutCells.Batch306.certificate3673],(28628253842838461/50000000000000000),(some (1319940661/1000000000)),(1/2),(291110619993959889/1000000000000000000),(some (2538669010748779/1000000000000000000)),(some (276104559413631/1000000000000000000))⟩
theorem numericValid993 : certificate993.NumericValid := by decide +kernel
theorem cellsSound993 : ∀ c∈certificate993.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3672,MergedCutCells.Batch306.certificate3673], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3672,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3673,List.forall_mem_nil _⟩⟩
theorem cellsNumeric993 : ∀ c∈certificate993.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3672,MergedCutCells.Batch306.certificate3673], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3672,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3673,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid993 : ∀ c∈certificate993.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3672,MergedCutCells.Batch306.certificate3673], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid332,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid332,List.forall_mem_nil _⟩⟩
theorem populationMatches993 : ∀ c∈certificate993.cells, c.population=certificate993.population := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3672,MergedCutCells.Batch306.certificate3673], c.population=PopulationCertificates.Batch033.certificate662
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers993 {x : ℝ} (hx : certificate993.interval.Contains x) : ∃ c∈certificate993.cells, c.region.interval.Contains x := rat_cut_group_covers certificate993 numericValid993 hx

def certificate994 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate662,PopulationCertificates.Batch033.certificate662,[MergedCutCells.Batch306.certificate3674,MergedCutCells.Batch306.certificate3675,MergedCutCells.Batch306.certificate3676],(1319940661/1000000000),none,(1/2),(29104163020040161/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid994 : certificate994.NumericValid := by decide +kernel
theorem cellsSound994 : ∀ c∈certificate994.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3674,MergedCutCells.Batch306.certificate3675,MergedCutCells.Batch306.certificate3676], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3675,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3676,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric994 : ∀ c∈certificate994.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3674,MergedCutCells.Batch306.certificate3675,MergedCutCells.Batch306.certificate3676], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3674,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3675,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3676,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid994 : ∀ c∈certificate994.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3674,MergedCutCells.Batch306.certificate3675,MergedCutCells.Batch306.certificate3676], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches994 : ∀ c∈certificate994.cells, c.population=certificate994.population := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3674,MergedCutCells.Batch306.certificate3675,MergedCutCells.Batch306.certificate3676], c.population=PopulationCertificates.Batch033.certificate662
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers994 {x : ℝ} (hx : certificate994.interval.Contains x) : ∃ c∈certificate994.cells, c.region.interval.Contains x := rat_cut_group_covers certificate994 numericValid994 hx

def certificate995 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate663,PopulationCertificates.Batch033.certificate663,[MergedCutCells.Batch306.certificate3677,MergedCutCells.Batch306.certificate3678],(3784903387793341031/250000000000000000),none,(1/2),(766963719913666343/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid995 : certificate995.NumericValid := by decide +kernel
theorem cellsSound995 : ∀ c∈certificate995.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3677,MergedCutCells.Batch306.certificate3678], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3677,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3678,List.forall_mem_nil _⟩⟩
theorem cellsNumeric995 : ∀ c∈certificate995.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3677,MergedCutCells.Batch306.certificate3678], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3677,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3678,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid995 : ∀ c∈certificate995.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3677,MergedCutCells.Batch306.certificate3678], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches995 : ∀ c∈certificate995.cells, c.population=certificate995.population := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3677,MergedCutCells.Batch306.certificate3678], c.population=PopulationCertificates.Batch033.certificate663
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers995 {x : ℝ} (hx : certificate995.interval.Contains x) : ∃ c∈certificate995.cells, c.region.interval.Contains x := rat_cut_group_covers certificate995 numericValid995 hx

end Cycle12.MergedCutGroups.Batch082
