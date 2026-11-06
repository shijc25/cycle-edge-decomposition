import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch033
import Cycle12.MergedCutCells.Batch306
import Cycle12.MergedCutCells.Batch307
import Cycle12.MergedCutCells.Batch308
import Cycle12.PopulationCertificates.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch083

def certificate996 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate664,PopulationCertificates.Batch033.certificate664,[MergedCutCells.Batch306.certificate3679,MergedCutCells.Batch306.certificate3680],(279123745349467/488281250000000),(some (329548943/250000000)),(1/2),(277209254567354963/1000000000000000000),(some (3363244836497269/1000000000000000000)),(some (11838055171093/31250000000000000))⟩
theorem numericValid996 : certificate996.NumericValid := by decide +kernel
theorem cellsSound996 : ∀ c∈certificate996.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3679,MergedCutCells.Batch306.certificate3680], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3680,List.forall_mem_nil _⟩⟩
theorem cellsNumeric996 : ∀ c∈certificate996.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3679,MergedCutCells.Batch306.certificate3680], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3679,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3680,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid996 : ∀ c∈certificate996.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3679,MergedCutCells.Batch306.certificate3680], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid333,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid333,List.forall_mem_nil _⟩⟩
theorem populationMatches996 : ∀ c∈certificate996.cells, c.population=certificate996.population := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3679,MergedCutCells.Batch306.certificate3680], c.population=PopulationCertificates.Batch033.certificate664
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers996 {x : ℝ} (hx : certificate996.interval.Contains x) : ∃ c∈certificate996.cells, c.region.interval.Contains x := rat_cut_group_covers certificate996 numericValid996 hx

def certificate997 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate664,PopulationCertificates.Batch033.certificate664,[MergedCutCells.Batch306.certificate3681,MergedCutCells.Batch306.certificate3682,MergedCutCells.Batch306.certificate3683],(329548943/250000000),none,(1/2),(277176837038664093/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid997 : certificate997.NumericValid := by decide +kernel
theorem cellsSound997 : ∀ c∈certificate997.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3681,MergedCutCells.Batch306.certificate3682,MergedCutCells.Batch306.certificate3683], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3681,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.sound3683,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric997 : ∀ c∈certificate997.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3681,MergedCutCells.Batch306.certificate3682,MergedCutCells.Batch306.certificate3683], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3681,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3682,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch306.numericValid3683,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid997 : ∀ c∈certificate997.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3681,MergedCutCells.Batch306.certificate3682,MergedCutCells.Batch306.certificate3683], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches997 : ∀ c∈certificate997.cells, c.population=certificate997.population := by
  change ∀ c∈[MergedCutCells.Batch306.certificate3681,MergedCutCells.Batch306.certificate3682,MergedCutCells.Batch306.certificate3683], c.population=PopulationCertificates.Batch033.certificate664
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers997 {x : ℝ} (hx : certificate997.interval.Contains x) : ∃ c∈certificate997.cells, c.region.interval.Contains x := rat_cut_group_covers certificate997 numericValid997 hx

def certificate998 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate665,PopulationCertificates.Batch033.certificate665,[MergedCutCells.Batch307.certificate3684,MergedCutCells.Batch307.certificate3685],(3834366140186863407/250000000000000000),none,(1/2),(967796663731544071/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid998 : certificate998.NumericValid := by decide +kernel
theorem cellsSound998 : ∀ c∈certificate998.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3684,MergedCutCells.Batch307.certificate3685], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3684,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3685,List.forall_mem_nil _⟩⟩
theorem cellsNumeric998 : ∀ c∈certificate998.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3684,MergedCutCells.Batch307.certificate3685], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3684,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3685,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid998 : ∀ c∈certificate998.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3684,MergedCutCells.Batch307.certificate3685], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches998 : ∀ c∈certificate998.cells, c.population=certificate998.population := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3684,MergedCutCells.Batch307.certificate3685], c.population=PopulationCertificates.Batch033.certificate665
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers998 {x : ℝ} (hx : certificate998.interval.Contains x) : ∃ c∈certificate998.cells, c.region.interval.Contains x := rat_cut_group_covers certificate998 numericValid998 hx

def certificate999 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate666,PopulationCertificates.Batch033.certificate666,[MergedCutCells.Batch307.certificate3686,MergedCutCells.Batch307.certificate3687],(570997272193723913/1000000000000000000),(some (1316965689/1000000000)),(1/2),(274834143659872699/1000000000000000000),(some (151771826483783/40000000000000000)),(some (434020614724439/1000000000000000000))⟩
theorem numericValid999 : certificate999.NumericValid := by decide +kernel
theorem cellsSound999 : ∀ c∈certificate999.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3686,MergedCutCells.Batch307.certificate3687], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3686,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3687,List.forall_mem_nil _⟩⟩
theorem cellsNumeric999 : ∀ c∈certificate999.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3686,MergedCutCells.Batch307.certificate3687], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3686,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3687,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid999 : ∀ c∈certificate999.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3686,MergedCutCells.Batch307.certificate3687], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid334,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid334,List.forall_mem_nil _⟩⟩
theorem populationMatches999 : ∀ c∈certificate999.cells, c.population=certificate999.population := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3686,MergedCutCells.Batch307.certificate3687], c.population=PopulationCertificates.Batch033.certificate666
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers999 {x : ℝ} (hx : certificate999.interval.Contains x) : ∃ c∈certificate999.cells, c.region.interval.Contains x := rat_cut_group_covers certificate999 numericValid999 hx

def certificate1000 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate666,PopulationCertificates.Batch033.certificate666,[MergedCutCells.Batch307.certificate3688,MergedCutCells.Batch307.certificate3689,MergedCutCells.Batch307.certificate3690],(1316965689/1000000000),none,(1/2),(136779384052885791/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1000 : certificate1000.NumericValid := by decide +kernel
theorem cellsSound1000 : ∀ c∈certificate1000.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3688,MergedCutCells.Batch307.certificate3689,MergedCutCells.Batch307.certificate3690], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3688,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3689,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3690,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1000 : ∀ c∈certificate1000.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3688,MergedCutCells.Batch307.certificate3689,MergedCutCells.Batch307.certificate3690], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3688,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3689,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3690,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1000 : ∀ c∈certificate1000.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3688,MergedCutCells.Batch307.certificate3689,MergedCutCells.Batch307.certificate3690], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1000 : ∀ c∈certificate1000.cells, c.population=certificate1000.population := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3688,MergedCutCells.Batch307.certificate3689,MergedCutCells.Batch307.certificate3690], c.population=PopulationCertificates.Batch033.certificate666
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1000 {x : ℝ} (hx : certificate1000.interval.Contains x) : ∃ c∈certificate1000.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1000 numericValid1000 hx

def certificate1001 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate667,PopulationCertificates.Batch033.certificate667,[MergedCutCells.Batch307.certificate3691,MergedCutCells.Batch307.certificate3692],(15519521894573462301/1000000000000000000),none,(1/2),(492208577243546857/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1001 : certificate1001.NumericValid := by decide +kernel
theorem cellsSound1001 : ∀ c∈certificate1001.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3691,MergedCutCells.Batch307.certificate3692], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3691,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3692,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1001 : ∀ c∈certificate1001.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3691,MergedCutCells.Batch307.certificate3692], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3691,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3692,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1001 : ∀ c∈certificate1001.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3691,MergedCutCells.Batch307.certificate3692], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1001 : ∀ c∈certificate1001.cells, c.population=certificate1001.population := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3691,MergedCutCells.Batch307.certificate3692], c.population=PopulationCertificates.Batch033.certificate667
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1001 {x : ℝ} (hx : certificate1001.interval.Contains x) : ∃ c∈certificate1001.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1001 numericValid1001 hx

def certificate1002 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate668,PopulationCertificates.Batch033.certificate668,[MergedCutCells.Batch307.certificate3693,MergedCutCells.Batch307.certificate3694],(36110906760805059/62500000000000000),(some (1303115919/1000000000)),(1/2),(294262748349348583/1000000000000000000),(some (4237359735691207/1000000000000000000)),(some (491724441634071/1000000000000000000))⟩
theorem numericValid1002 : certificate1002.NumericValid := by decide +kernel
theorem cellsSound1002 : ∀ c∈certificate1002.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3693,MergedCutCells.Batch307.certificate3694], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3693,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3694,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1002 : ∀ c∈certificate1002.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3693,MergedCutCells.Batch307.certificate3694], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3693,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3694,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1002 : ∀ c∈certificate1002.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3693,MergedCutCells.Batch307.certificate3694], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid335,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid335,List.forall_mem_nil _⟩⟩
theorem populationMatches1002 : ∀ c∈certificate1002.cells, c.population=certificate1002.population := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3693,MergedCutCells.Batch307.certificate3694], c.population=PopulationCertificates.Batch033.certificate668
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1002 {x : ℝ} (hx : certificate1002.interval.Contains x) : ∃ c∈certificate1002.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1002 numericValid1002 hx

def certificate1003 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate668,PopulationCertificates.Batch033.certificate668,[MergedCutCells.Batch307.certificate3695,MergedCutCells.Batch308.certificate3696,MergedCutCells.Batch308.certificate3697],(1303115919/1000000000),none,(1/2),(270798999416821811/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1003 : certificate1003.NumericValid := by decide +kernel
theorem cellsSound1003 : ∀ c∈certificate1003.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3695,MergedCutCells.Batch308.certificate3696,MergedCutCells.Batch308.certificate3697], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.sound3695,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3697,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1003 : ∀ c∈certificate1003.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3695,MergedCutCells.Batch308.certificate3696,MergedCutCells.Batch308.certificate3697], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch307.numericValid3695,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3696,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3697,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1003 : ∀ c∈certificate1003.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3695,MergedCutCells.Batch308.certificate3696,MergedCutCells.Batch308.certificate3697], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1003 : ∀ c∈certificate1003.cells, c.population=certificate1003.population := by
  change ∀ c∈[MergedCutCells.Batch307.certificate3695,MergedCutCells.Batch308.certificate3696,MergedCutCells.Batch308.certificate3697], c.population=PopulationCertificates.Batch033.certificate668
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1003 {x : ℝ} (hx : certificate1003.interval.Contains x) : ∃ c∈certificate1003.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1003 numericValid1003 hx

def certificate1004 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate669,PopulationCertificates.Batch033.certificate669,[MergedCutCells.Batch308.certificate3698,MergedCutCells.Batch308.certificate3699],(15663657362314665921/1000000000000000000),none,(1/2),(496972932372224697/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1004 : certificate1004.NumericValid := by decide +kernel
theorem cellsSound1004 : ∀ c∈certificate1004.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3698,MergedCutCells.Batch308.certificate3699], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3699,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1004 : ∀ c∈certificate1004.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3698,MergedCutCells.Batch308.certificate3699], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3698,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3699,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1004 : ∀ c∈certificate1004.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3698,MergedCutCells.Batch308.certificate3699], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1004 : ∀ c∈certificate1004.cells, c.population=certificate1004.population := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3698,MergedCutCells.Batch308.certificate3699], c.population=PopulationCertificates.Batch033.certificate669
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1004 {x : ℝ} (hx : certificate1004.interval.Contains x) : ∃ c∈certificate1004.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1004 numericValid1004 hx

def certificate1005 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate670,PopulationCertificates.Batch033.certificate670,[MergedCutCells.Batch308.certificate3700,MergedCutCells.Batch308.certificate3701],(35657571941267751/62500000000000000),(some (1284102601/1000000000)),(1/2),(51336078428018237/200000000000000000),(some (1314925904882819/250000000000000000)),(some (628227266730579/1000000000000000000))⟩
theorem numericValid1005 : certificate1005.NumericValid := by decide +kernel
theorem cellsSound1005 : ∀ c∈certificate1005.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3700,MergedCutCells.Batch308.certificate3701], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3700,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3701,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1005 : ∀ c∈certificate1005.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3700,MergedCutCells.Batch308.certificate3701], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3700,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3701,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1005 : ∀ c∈certificate1005.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3700,MergedCutCells.Batch308.certificate3701], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid336,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid336,List.forall_mem_nil _⟩⟩
theorem populationMatches1005 : ∀ c∈certificate1005.cells, c.population=certificate1005.population := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3700,MergedCutCells.Batch308.certificate3701], c.population=PopulationCertificates.Batch033.certificate670
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1005 {x : ℝ} (hx : certificate1005.interval.Contains x) : ∃ c∈certificate1005.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1005 numericValid1005 hx

def certificate1006 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate670,PopulationCertificates.Batch033.certificate670,[MergedCutCells.Batch308.certificate3702,MergedCutCells.Batch308.certificate3703,MergedCutCells.Batch308.certificate3704],(1284102601/1000000000),none,(1/2),(256476956955755687/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1006 : certificate1006.NumericValid := by decide +kernel
theorem cellsSound1006 : ∀ c∈certificate1006.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3702,MergedCutCells.Batch308.certificate3703,MergedCutCells.Batch308.certificate3704], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3702,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3703,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3704,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric1006 : ∀ c∈certificate1006.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3702,MergedCutCells.Batch308.certificate3703,MergedCutCells.Batch308.certificate3704], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3702,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3703,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3704,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid1006 : ∀ c∈certificate1006.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3702,MergedCutCells.Batch308.certificate3703,MergedCutCells.Batch308.certificate3704], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches1006 : ∀ c∈certificate1006.cells, c.population=certificate1006.population := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3702,MergedCutCells.Batch308.certificate3703,MergedCutCells.Batch308.certificate3704], c.population=PopulationCertificates.Batch033.certificate670
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers1006 {x : ℝ} (hx : certificate1006.interval.Contains x) : ∃ c∈certificate1006.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1006 numericValid1006 hx

def certificate1007 : RatCutGroup := ⟨GeometryCertificates.Batch033.certificate671,PopulationCertificates.Batch033.certificate671,[MergedCutCells.Batch308.certificate3705,MergedCutCells.Batch308.certificate3706],(31734968662029149/2000000000000000),none,(1/2),(401331821028012033/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1007 : certificate1007.NumericValid := by decide +kernel
theorem cellsSound1007 : ∀ c∈certificate1007.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3705,MergedCutCells.Batch308.certificate3706], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3705,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.sound3706,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1007 : ∀ c∈certificate1007.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3705,MergedCutCells.Batch308.certificate3706], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3705,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch308.numericValid3706,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1007 : ∀ c∈certificate1007.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3705,MergedCutCells.Batch308.certificate3706], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1007 : ∀ c∈certificate1007.cells, c.population=certificate1007.population := by
  change ∀ c∈[MergedCutCells.Batch308.certificate3705,MergedCutCells.Batch308.certificate3706], c.population=PopulationCertificates.Batch033.certificate671
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1007 {x : ℝ} (hx : certificate1007.interval.Contains x) : ∃ c∈certificate1007.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1007 numericValid1007 hx

end Cycle12.MergedCutGroups.Batch083
