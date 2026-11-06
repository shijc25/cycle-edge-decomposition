import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch031
import Cycle12.MergedCutCells.Batch287
import Cycle12.MergedCutCells.Batch288
import Cycle12.MergedCutCells.Batch289
import Cycle12.MergedCutCells.Batch290
import Cycle12.MergedCutCells.Batch291
import Cycle12.MergedCutCells.Batch292
import Cycle12.PopulationCertificates.Batch031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch078

def certificate936 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate624,PopulationCertificates.Batch031.certificate624,[MergedCutCells.Batch287.certificate3453,MergedCutCells.Batch287.certificate3454,MergedCutCells.Batch287.certificate3455],(896061214226425569/1000000000000000000),(some (1091602423/1000000000)),(1/2),(1061227711046514683/500000000000000000),(some (45700172827692899/125000000000000000)),(some (11933672840703037/100000000000000000))⟩
theorem numericValid936 : certificate936.NumericValid := by decide +kernel
theorem cellsSound936 : ∀ c∈certificate936.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3453,MergedCutCells.Batch287.certificate3454,MergedCutCells.Batch287.certificate3455], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3454,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.sound3455,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric936 : ∀ c∈certificate936.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3453,MergedCutCells.Batch287.certificate3454,MergedCutCells.Batch287.certificate3455], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3453,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3454,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch287.numericValid3455,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid936 : ∀ c∈certificate936.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3453,MergedCutCells.Batch287.certificate3454,MergedCutCells.Batch287.certificate3455], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid313,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid313,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid313,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches936 : ∀ c∈certificate936.cells, c.population=certificate936.population := by
  change ∀ c∈[MergedCutCells.Batch287.certificate3453,MergedCutCells.Batch287.certificate3454,MergedCutCells.Batch287.certificate3455], c.population=PopulationCertificates.Batch031.certificate624
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers936 {x : ℝ} (hx : certificate936.interval.Contains x) : ∃ c∈certificate936.cells, c.region.interval.Contains x := rat_cut_group_covers certificate936 numericValid936 hx

def certificate937 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate624,PopulationCertificates.Batch031.certificate624,[MergedCutCells.Batch288.certificate3456,MergedCutCells.Batch288.certificate3457,MergedCutCells.Batch288.certificate3458,MergedCutCells.Batch288.certificate3459,MergedCutCells.Batch288.certificate3460,MergedCutCells.Batch288.certificate3461,MergedCutCells.Batch288.certificate3462,MergedCutCells.Batch288.certificate3463],(1091602423/1000000000),none,(1/2),(1044648573630990089/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid937 : certificate937.NumericValid := by decide +kernel
theorem cellsSound937 : ∀ c∈certificate937.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3456,MergedCutCells.Batch288.certificate3457,MergedCutCells.Batch288.certificate3458,MergedCutCells.Batch288.certificate3459,MergedCutCells.Batch288.certificate3460,MergedCutCells.Batch288.certificate3461,MergedCutCells.Batch288.certificate3462,MergedCutCells.Batch288.certificate3463], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3456,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3457,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3460,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3461,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3462,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3463,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric937 : ∀ c∈certificate937.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3456,MergedCutCells.Batch288.certificate3457,MergedCutCells.Batch288.certificate3458,MergedCutCells.Batch288.certificate3459,MergedCutCells.Batch288.certificate3460,MergedCutCells.Batch288.certificate3461,MergedCutCells.Batch288.certificate3462,MergedCutCells.Batch288.certificate3463], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3456,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3457,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3458,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3459,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3460,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3461,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3462,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3463,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid937 : ∀ c∈certificate937.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3456,MergedCutCells.Batch288.certificate3457,MergedCutCells.Batch288.certificate3458,MergedCutCells.Batch288.certificate3459,MergedCutCells.Batch288.certificate3460,MergedCutCells.Batch288.certificate3461,MergedCutCells.Batch288.certificate3462,MergedCutCells.Batch288.certificate3463], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches937 : ∀ c∈certificate937.cells, c.population=certificate937.population := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3456,MergedCutCells.Batch288.certificate3457,MergedCutCells.Batch288.certificate3458,MergedCutCells.Batch288.certificate3459,MergedCutCells.Batch288.certificate3460,MergedCutCells.Batch288.certificate3461,MergedCutCells.Batch288.certificate3462,MergedCutCells.Batch288.certificate3463], c.population=PopulationCertificates.Batch031.certificate624
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers937 {x : ℝ} (hx : certificate937.interval.Contains x) : ∃ c∈certificate937.cells, c.region.interval.Contains x := rat_cut_group_covers certificate937 numericValid937 hx

def certificate938 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate625,PopulationCertificates.Batch031.certificate625,[MergedCutCells.Batch288.certificate3464,MergedCutCells.Batch288.certificate3465,MergedCutCells.Batch288.certificate3466],(141608737833819783/15625000000000000),none,(1/2),(772353778684050199/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid938 : certificate938.NumericValid := by decide +kernel
theorem cellsSound938 : ∀ c∈certificate938.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3464,MergedCutCells.Batch288.certificate3465,MergedCutCells.Batch288.certificate3466], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3464,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3466,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric938 : ∀ c∈certificate938.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3464,MergedCutCells.Batch288.certificate3465,MergedCutCells.Batch288.certificate3466], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3464,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3465,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3466,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid938 : ∀ c∈certificate938.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3464,MergedCutCells.Batch288.certificate3465,MergedCutCells.Batch288.certificate3466], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches938 : ∀ c∈certificate938.cells, c.population=certificate938.population := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3464,MergedCutCells.Batch288.certificate3465,MergedCutCells.Batch288.certificate3466], c.population=PopulationCertificates.Batch031.certificate625
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers938 {x : ℝ} (hx : certificate938.interval.Contains x) : ∃ c∈certificate938.cells, c.region.interval.Contains x := rat_cut_group_covers certificate938 numericValid938 hx

def certificate939 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate626,PopulationCertificates.Batch031.certificate626,[MergedCutCells.Batch288.certificate3467,MergedCutCells.Batch289.certificate3468,MergedCutCells.Batch289.certificate3469],(900312930561580787/1000000000000000000),(some (68533869/62500000)),(1/2),(546374990993033459/250000000000000000),(some (73547012125000361/200000000000000000)),(some (30101741681722529/250000000000000000))⟩
theorem numericValid939 : certificate939.NumericValid := by decide +kernel
theorem cellsSound939 : ∀ c∈certificate939.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3467,MergedCutCells.Batch289.certificate3468,MergedCutCells.Batch289.certificate3469], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.sound3467,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3468,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3469,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric939 : ∀ c∈certificate939.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3467,MergedCutCells.Batch289.certificate3468,MergedCutCells.Batch289.certificate3469], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch288.numericValid3467,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3468,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3469,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid939 : ∀ c∈certificate939.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3467,MergedCutCells.Batch289.certificate3468,MergedCutCells.Batch289.certificate3469], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid314,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid314,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid314,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches939 : ∀ c∈certificate939.cells, c.population=certificate939.population := by
  change ∀ c∈[MergedCutCells.Batch288.certificate3467,MergedCutCells.Batch289.certificate3468,MergedCutCells.Batch289.certificate3469], c.population=PopulationCertificates.Batch031.certificate626
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers939 {x : ℝ} (hx : certificate939.interval.Contains x) : ∃ c∈certificate939.cells, c.region.interval.Contains x := rat_cut_group_covers certificate939 numericValid939 hx

def certificate940 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate626,PopulationCertificates.Batch031.certificate626,[MergedCutCells.Batch289.certificate3470,MergedCutCells.Batch289.certificate3471,MergedCutCells.Batch289.certificate3472,MergedCutCells.Batch289.certificate3473,MergedCutCells.Batch289.certificate3474,MergedCutCells.Batch289.certificate3475],(68533869/62500000),none,(1/2),(214664563022466357/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid940 : certificate940.NumericValid := by decide +kernel
theorem cellsSound940 : ∀ c∈certificate940.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch289.certificate3470,MergedCutCells.Batch289.certificate3471,MergedCutCells.Batch289.certificate3472,MergedCutCells.Batch289.certificate3473,MergedCutCells.Batch289.certificate3474,MergedCutCells.Batch289.certificate3475], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3470,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3472,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3474,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3475,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric940 : ∀ c∈certificate940.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch289.certificate3470,MergedCutCells.Batch289.certificate3471,MergedCutCells.Batch289.certificate3472,MergedCutCells.Batch289.certificate3473,MergedCutCells.Batch289.certificate3474,MergedCutCells.Batch289.certificate3475], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3470,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3471,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3472,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3473,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3474,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3475,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid940 : ∀ c∈certificate940.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch289.certificate3470,MergedCutCells.Batch289.certificate3471,MergedCutCells.Batch289.certificate3472,MergedCutCells.Batch289.certificate3473,MergedCutCells.Batch289.certificate3474,MergedCutCells.Batch289.certificate3475], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches940 : ∀ c∈certificate940.cells, c.population=certificate940.population := by
  change ∀ c∈[MergedCutCells.Batch289.certificate3470,MergedCutCells.Batch289.certificate3471,MergedCutCells.Batch289.certificate3472,MergedCutCells.Batch289.certificate3473,MergedCutCells.Batch289.certificate3474,MergedCutCells.Batch289.certificate3475], c.population=PopulationCertificates.Batch031.certificate626
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers940 {x : ℝ} (hx : certificate940.interval.Contains x) : ∃ c∈certificate940.cells, c.region.interval.Contains x := rat_cut_group_covers certificate940 numericValid940 hx

def certificate941 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate627,PopulationCertificates.Batch031.certificate627,[MergedCutCells.Batch289.certificate3476,MergedCutCells.Batch289.certificate3477,MergedCutCells.Batch289.certificate3478,MergedCutCells.Batch289.certificate3479],(2275889851150464741/250000000000000000),none,(1/2),(7844246250724147/1000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid941 : certificate941.NumericValid := by decide +kernel
theorem cellsSound941 : ∀ c∈certificate941.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch289.certificate3476,MergedCutCells.Batch289.certificate3477,MergedCutCells.Batch289.certificate3478,MergedCutCells.Batch289.certificate3479], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3476,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3477,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3478,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.sound3479,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric941 : ∀ c∈certificate941.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch289.certificate3476,MergedCutCells.Batch289.certificate3477,MergedCutCells.Batch289.certificate3478,MergedCutCells.Batch289.certificate3479], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3476,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3477,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3478,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch289.numericValid3479,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid941 : ∀ c∈certificate941.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch289.certificate3476,MergedCutCells.Batch289.certificate3477,MergedCutCells.Batch289.certificate3478,MergedCutCells.Batch289.certificate3479], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches941 : ∀ c∈certificate941.cells, c.population=certificate941.population := by
  change ∀ c∈[MergedCutCells.Batch289.certificate3476,MergedCutCells.Batch289.certificate3477,MergedCutCells.Batch289.certificate3478,MergedCutCells.Batch289.certificate3479], c.population=PopulationCertificates.Batch031.certificate627
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers941 {x : ℝ} (hx : certificate941.interval.Contains x) : ∃ c∈certificate941.cells, c.region.interval.Contains x := rat_cut_group_covers certificate941 numericValid941 hx

def certificate942 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate628,PopulationCertificates.Batch031.certificate628,[MergedCutCells.Batch290.certificate3480,MergedCutCells.Batch290.certificate3481,MergedCutCells.Batch290.certificate3482],(225576739972469611/250000000000000000),(some (1098858119/1000000000)),(1/2),(1110377717312056431/500000000000000000),(some (369916691813639373/1000000000000000000)),(some (15188363798597513/125000000000000000))⟩
theorem numericValid942 : certificate942.NumericValid := by decide +kernel
theorem cellsSound942 : ∀ c∈certificate942.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3480,MergedCutCells.Batch290.certificate3481,MergedCutCells.Batch290.certificate3482], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3481,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3482,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric942 : ∀ c∈certificate942.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3480,MergedCutCells.Batch290.certificate3481,MergedCutCells.Batch290.certificate3482], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3480,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3481,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3482,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid942 : ∀ c∈certificate942.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3480,MergedCutCells.Batch290.certificate3481,MergedCutCells.Batch290.certificate3482], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid315,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid315,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid315,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches942 : ∀ c∈certificate942.cells, c.population=certificate942.population := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3480,MergedCutCells.Batch290.certificate3481,MergedCutCells.Batch290.certificate3482], c.population=PopulationCertificates.Batch031.certificate628
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers942 {x : ℝ} (hx : certificate942.interval.Contains x) : ∃ c∈certificate942.cells, c.region.interval.Contains x := rat_cut_group_covers certificate942 numericValid942 hx

def certificate943 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate628,PopulationCertificates.Batch031.certificate628,[MergedCutCells.Batch290.certificate3483,MergedCutCells.Batch290.certificate3484,MergedCutCells.Batch290.certificate3485,MergedCutCells.Batch290.certificate3486,MergedCutCells.Batch290.certificate3487,MergedCutCells.Batch290.certificate3488],(1098858119/1000000000),none,(1/2),(21871799880357521/10000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid943 : certificate943.NumericValid := by decide +kernel
theorem cellsSound943 : ∀ c∈certificate943.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3483,MergedCutCells.Batch290.certificate3484,MergedCutCells.Batch290.certificate3485,MergedCutCells.Batch290.certificate3486,MergedCutCells.Batch290.certificate3487,MergedCutCells.Batch290.certificate3488], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3483,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3485,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3486,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3487,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3488,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric943 : ∀ c∈certificate943.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3483,MergedCutCells.Batch290.certificate3484,MergedCutCells.Batch290.certificate3485,MergedCutCells.Batch290.certificate3486,MergedCutCells.Batch290.certificate3487,MergedCutCells.Batch290.certificate3488], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3483,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3484,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3485,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3486,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3487,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3488,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid943 : ∀ c∈certificate943.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3483,MergedCutCells.Batch290.certificate3484,MergedCutCells.Batch290.certificate3485,MergedCutCells.Batch290.certificate3486,MergedCutCells.Batch290.certificate3487,MergedCutCells.Batch290.certificate3488], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches943 : ∀ c∈certificate943.cells, c.population=certificate943.population := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3483,MergedCutCells.Batch290.certificate3484,MergedCutCells.Batch290.certificate3485,MergedCutCells.Batch290.certificate3486,MergedCutCells.Batch290.certificate3487,MergedCutCells.Batch290.certificate3488], c.population=PopulationCertificates.Batch031.certificate628
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers943 {x : ℝ} (hx : certificate943.interval.Contains x) : ∃ c∈certificate943.cells, c.region.interval.Contains x := rat_cut_group_covers certificate943 numericValid943 hx

def certificate944 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate629,PopulationCertificates.Batch031.certificate629,[MergedCutCells.Batch290.certificate3489,MergedCutCells.Batch290.certificate3490,MergedCutCells.Batch290.certificate3491,MergedCutCells.Batch291.certificate3492],(9012025976924021861/1000000000000000000),none,(1/2),(7854955709788236443/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid944 : certificate944.NumericValid := by decide +kernel
theorem cellsSound944 : ∀ c∈certificate944.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3489,MergedCutCells.Batch290.certificate3490,MergedCutCells.Batch290.certificate3491,MergedCutCells.Batch291.certificate3492], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3489,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3490,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.sound3491,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3492,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric944 : ∀ c∈certificate944.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3489,MergedCutCells.Batch290.certificate3490,MergedCutCells.Batch290.certificate3491,MergedCutCells.Batch291.certificate3492], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3489,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3490,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch290.numericValid3491,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3492,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid944 : ∀ c∈certificate944.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3489,MergedCutCells.Batch290.certificate3490,MergedCutCells.Batch290.certificate3491,MergedCutCells.Batch291.certificate3492], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches944 : ∀ c∈certificate944.cells, c.population=certificate944.population := by
  change ∀ c∈[MergedCutCells.Batch290.certificate3489,MergedCutCells.Batch290.certificate3490,MergedCutCells.Batch290.certificate3491,MergedCutCells.Batch291.certificate3492], c.population=PopulationCertificates.Batch031.certificate629
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers944 {x : ℝ} (hx : certificate944.interval.Contains x) : ∃ c∈certificate944.cells, c.region.interval.Contains x := rat_cut_group_covers certificate944 numericValid944 hx

def certificate945 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate630,PopulationCertificates.Batch031.certificate630,[MergedCutCells.Batch291.certificate3493,MergedCutCells.Batch291.certificate3494,MergedCutCells.Batch291.certificate3495],(905218131750956357/1000000000000000000),(some (1102239239/1000000000)),(1/2),(452272758328163379/200000000000000000),(some (74416594190050213/200000000000000000)),(some (30651203162804759/250000000000000000))⟩
theorem numericValid945 : certificate945.NumericValid := by decide +kernel
theorem cellsSound945 : ∀ c∈certificate945.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3493,MergedCutCells.Batch291.certificate3494,MergedCutCells.Batch291.certificate3495], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3494,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3495,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric945 : ∀ c∈certificate945.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3493,MergedCutCells.Batch291.certificate3494,MergedCutCells.Batch291.certificate3495], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3493,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3494,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3495,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid945 : ∀ c∈certificate945.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3493,MergedCutCells.Batch291.certificate3494,MergedCutCells.Batch291.certificate3495], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid316,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid316,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid316,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches945 : ∀ c∈certificate945.cells, c.population=certificate945.population := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3493,MergedCutCells.Batch291.certificate3494,MergedCutCells.Batch291.certificate3495], c.population=PopulationCertificates.Batch031.certificate630
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers945 {x : ℝ} (hx : certificate945.interval.Contains x) : ∃ c∈certificate945.cells, c.region.interval.Contains x := rat_cut_group_covers certificate945 numericValid945 hx

def certificate946 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate630,PopulationCertificates.Batch031.certificate630,[MergedCutCells.Batch291.certificate3496,MergedCutCells.Batch291.certificate3497,MergedCutCells.Batch291.certificate3498,MergedCutCells.Batch291.certificate3499,MergedCutCells.Batch291.certificate3500,MergedCutCells.Batch291.certificate3501],(1102239239/1000000000),none,(1/2),(2226437054353790087/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid946 : certificate946.NumericValid := by decide +kernel
theorem cellsSound946 : ∀ c∈certificate946.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3496,MergedCutCells.Batch291.certificate3497,MergedCutCells.Batch291.certificate3498,MergedCutCells.Batch291.certificate3499,MergedCutCells.Batch291.certificate3500,MergedCutCells.Batch291.certificate3501], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3496,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3497,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3499,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3500,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3501,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric946 : ∀ c∈certificate946.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3496,MergedCutCells.Batch291.certificate3497,MergedCutCells.Batch291.certificate3498,MergedCutCells.Batch291.certificate3499,MergedCutCells.Batch291.certificate3500,MergedCutCells.Batch291.certificate3501], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3496,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3497,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3498,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3499,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3500,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3501,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid946 : ∀ c∈certificate946.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3496,MergedCutCells.Batch291.certificate3497,MergedCutCells.Batch291.certificate3498,MergedCutCells.Batch291.certificate3499,MergedCutCells.Batch291.certificate3500,MergedCutCells.Batch291.certificate3501], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches946 : ∀ c∈certificate946.cells, c.population=certificate946.population := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3496,MergedCutCells.Batch291.certificate3497,MergedCutCells.Batch291.certificate3498,MergedCutCells.Batch291.certificate3499,MergedCutCells.Batch291.certificate3500,MergedCutCells.Batch291.certificate3501], c.population=PopulationCertificates.Batch031.certificate630
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers946 {x : ℝ} (hx : certificate946.interval.Contains x) : ∃ c∈certificate946.cells, c.region.interval.Contains x := rat_cut_group_covers certificate946 numericValid946 hx

def certificate947 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate631,PopulationCertificates.Batch031.certificate631,[MergedCutCells.Batch291.certificate3502,MergedCutCells.Batch291.certificate3503,MergedCutCells.Batch292.certificate3504,MergedCutCells.Batch292.certificate3505],(563009772343157197/62500000000000000),none,(1/2),(3953452437210648181/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid947 : certificate947.NumericValid := by decide +kernel
theorem cellsSound947 : ∀ c∈certificate947.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3502,MergedCutCells.Batch291.certificate3503,MergedCutCells.Batch292.certificate3504,MergedCutCells.Batch292.certificate3505], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.sound3503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3504,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3505,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric947 : ∀ c∈certificate947.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3502,MergedCutCells.Batch291.certificate3503,MergedCutCells.Batch292.certificate3504,MergedCutCells.Batch292.certificate3505], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3502,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch291.numericValid3503,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3504,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3505,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid947 : ∀ c∈certificate947.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3502,MergedCutCells.Batch291.certificate3503,MergedCutCells.Batch292.certificate3504,MergedCutCells.Batch292.certificate3505], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches947 : ∀ c∈certificate947.cells, c.population=certificate947.population := by
  change ∀ c∈[MergedCutCells.Batch291.certificate3502,MergedCutCells.Batch291.certificate3503,MergedCutCells.Batch292.certificate3504,MergedCutCells.Batch292.certificate3505], c.population=PopulationCertificates.Batch031.certificate631
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers947 {x : ℝ} (hx : certificate947.interval.Contains x) : ∃ c∈certificate947.cells, c.region.interval.Contains x := rat_cut_group_covers certificate947 numericValid947 hx

end Cycle12.MergedCutGroups.Batch078
