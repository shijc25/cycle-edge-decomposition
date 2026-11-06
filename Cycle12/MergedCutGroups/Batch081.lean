import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch032
import Cycle12.MergedCutCells.Batch300
import Cycle12.MergedCutCells.Batch301
import Cycle12.MergedCutCells.Batch302
import Cycle12.MergedCutCells.Batch303
import Cycle12.MergedCutCells.Batch304
import Cycle12.PopulationCertificates.Batch032

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch081

def certificate972 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate648,PopulationCertificates.Batch032.certificate648,[MergedCutCells.Batch300.certificate3603,MergedCutCells.Batch300.certificate3604,MergedCutCells.Batch300.certificate3605],(47288310599252369/50000000000000000),(some (224772041/200000000)),(1/2),(2905751833271513137/1000000000000000000),(some (201475001135006139/500000000000000000)),(some (138893626769609231/1000000000000000000))⟩
theorem numericValid972 : certificate972.NumericValid := by decide +kernel
theorem cellsSound972 : ∀ c∈certificate972.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3603,MergedCutCells.Batch300.certificate3604,MergedCutCells.Batch300.certificate3605], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3605,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric972 : ∀ c∈certificate972.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3603,MergedCutCells.Batch300.certificate3604,MergedCutCells.Batch300.certificate3605], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3603,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3604,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3605,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid972 : ∀ c∈certificate972.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3603,MergedCutCells.Batch300.certificate3604,MergedCutCells.Batch300.certificate3605], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid325,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid325,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid325,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches972 : ∀ c∈certificate972.cells, c.population=certificate972.population := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3603,MergedCutCells.Batch300.certificate3604,MergedCutCells.Batch300.certificate3605], c.population=PopulationCertificates.Batch032.certificate648
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers972 {x : ℝ} (hx : certificate972.interval.Contains x) : ∃ c∈certificate972.cells, c.region.interval.Contains x := rat_cut_group_covers certificate972 numericValid972 hx

def certificate973 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate648,PopulationCertificates.Batch032.certificate648,[MergedCutCells.Batch300.certificate3606,MergedCutCells.Batch300.certificate3607,MergedCutCells.Batch300.certificate3608,MergedCutCells.Batch300.certificate3609,MergedCutCells.Batch300.certificate3610,MergedCutCells.Batch300.certificate3611],(224772041/200000000),none,(1/2),(89695094005571947/31250000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid973 : certificate973.NumericValid := by decide +kernel
theorem cellsSound973 : ∀ c∈certificate973.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3606,MergedCutCells.Batch300.certificate3607,MergedCutCells.Batch300.certificate3608,MergedCutCells.Batch300.certificate3609,MergedCutCells.Batch300.certificate3610,MergedCutCells.Batch300.certificate3611], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3606,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3608,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3609,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3610,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.sound3611,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric973 : ∀ c∈certificate973.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3606,MergedCutCells.Batch300.certificate3607,MergedCutCells.Batch300.certificate3608,MergedCutCells.Batch300.certificate3609,MergedCutCells.Batch300.certificate3610,MergedCutCells.Batch300.certificate3611], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3606,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3607,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3608,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3609,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3610,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch300.numericValid3611,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid973 : ∀ c∈certificate973.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3606,MergedCutCells.Batch300.certificate3607,MergedCutCells.Batch300.certificate3608,MergedCutCells.Batch300.certificate3609,MergedCutCells.Batch300.certificate3610,MergedCutCells.Batch300.certificate3611], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches973 : ∀ c∈certificate973.cells, c.population=certificate973.population := by
  change ∀ c∈[MergedCutCells.Batch300.certificate3606,MergedCutCells.Batch300.certificate3607,MergedCutCells.Batch300.certificate3608,MergedCutCells.Batch300.certificate3609,MergedCutCells.Batch300.certificate3610,MergedCutCells.Batch300.certificate3611], c.population=PopulationCertificates.Batch032.certificate648
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers973 {x : ℝ} (hx : certificate973.interval.Contains x) : ∃ c∈certificate973.cells, c.region.interval.Contains x := rat_cut_group_covers certificate973 numericValid973 hx

def certificate974 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate649,PopulationCertificates.Batch032.certificate649,[MergedCutCells.Batch301.certificate3612,MergedCutCells.Batch301.certificate3613,MergedCutCells.Batch301.certificate3614],(2109938636003019641/250000000000000000),none,(1/2),(8455314617029701707/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid974 : certificate974.NumericValid := by decide +kernel
theorem cellsSound974 : ∀ c∈certificate974.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3612,MergedCutCells.Batch301.certificate3613,MergedCutCells.Batch301.certificate3614], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3612,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3613,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3614,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric974 : ∀ c∈certificate974.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3612,MergedCutCells.Batch301.certificate3613,MergedCutCells.Batch301.certificate3614], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3612,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3613,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3614,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid974 : ∀ c∈certificate974.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3612,MergedCutCells.Batch301.certificate3613,MergedCutCells.Batch301.certificate3614], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches974 : ∀ c∈certificate974.cells, c.population=certificate974.population := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3612,MergedCutCells.Batch301.certificate3613,MergedCutCells.Batch301.certificate3614], c.population=PopulationCertificates.Batch032.certificate649
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers974 {x : ℝ} (hx : certificate974.interval.Contains x) : ∃ c∈certificate974.cells, c.region.interval.Contains x := rat_cut_group_covers certificate974 numericValid974 hx

def certificate975 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate650,PopulationCertificates.Batch032.certificate650,[MergedCutCells.Batch301.certificate3615,MergedCutCells.Batch301.certificate3616],(952759383479646093/1000000000000000000),(some (1104321179/1000000000)),(1/2),(3017606104975052797/1000000000000000000),(some (50676852839653951/125000000000000000)),(some (140248772671899331/1000000000000000000))⟩
theorem numericValid975 : certificate975.NumericValid := by decide +kernel
theorem cellsSound975 : ∀ c∈certificate975.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3615,MergedCutCells.Batch301.certificate3616], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3615,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3616,List.forall_mem_nil _⟩⟩
theorem cellsNumeric975 : ∀ c∈certificate975.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3615,MergedCutCells.Batch301.certificate3616], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3615,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3616,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid975 : ∀ c∈certificate975.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3615,MergedCutCells.Batch301.certificate3616], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid326,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid326,List.forall_mem_nil _⟩⟩
theorem populationMatches975 : ∀ c∈certificate975.cells, c.population=certificate975.population := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3615,MergedCutCells.Batch301.certificate3616], c.population=PopulationCertificates.Batch032.certificate650
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers975 {x : ℝ} (hx : certificate975.interval.Contains x) : ∃ c∈certificate975.cells, c.region.interval.Contains x := rat_cut_group_covers certificate975 numericValid975 hx

def certificate976 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate650,PopulationCertificates.Batch032.certificate650,[MergedCutCells.Batch301.certificate3617,MergedCutCells.Batch301.certificate3618,MergedCutCells.Batch301.certificate3619,MergedCutCells.Batch301.certificate3620,MergedCutCells.Batch301.certificate3621,MergedCutCells.Batch301.certificate3622,MergedCutCells.Batch301.certificate3623],(1104321179/1000000000),none,(1/2),(2963899908516037709/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid976 : certificate976.NumericValid := by decide +kernel
theorem cellsSound976 : ∀ c∈certificate976.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3617,MergedCutCells.Batch301.certificate3618,MergedCutCells.Batch301.certificate3619,MergedCutCells.Batch301.certificate3620,MergedCutCells.Batch301.certificate3621,MergedCutCells.Batch301.certificate3622,MergedCutCells.Batch301.certificate3623], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3617,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3619,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3620,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3622,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.sound3623,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric976 : ∀ c∈certificate976.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3617,MergedCutCells.Batch301.certificate3618,MergedCutCells.Batch301.certificate3619,MergedCutCells.Batch301.certificate3620,MergedCutCells.Batch301.certificate3621,MergedCutCells.Batch301.certificate3622,MergedCutCells.Batch301.certificate3623], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3617,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3618,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3619,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3620,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3621,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3622,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch301.numericValid3623,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid976 : ∀ c∈certificate976.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3617,MergedCutCells.Batch301.certificate3618,MergedCutCells.Batch301.certificate3619,MergedCutCells.Batch301.certificate3620,MergedCutCells.Batch301.certificate3621,MergedCutCells.Batch301.certificate3622,MergedCutCells.Batch301.certificate3623], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches976 : ∀ c∈certificate976.cells, c.population=certificate976.population := by
  change ∀ c∈[MergedCutCells.Batch301.certificate3617,MergedCutCells.Batch301.certificate3618,MergedCutCells.Batch301.certificate3619,MergedCutCells.Batch301.certificate3620,MergedCutCells.Batch301.certificate3621,MergedCutCells.Batch301.certificate3622,MergedCutCells.Batch301.certificate3623], c.population=PopulationCertificates.Batch032.certificate650
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers976 {x : ℝ} (hx : certificate976.interval.Contains x) : ∃ c∈certificate976.cells, c.region.interval.Contains x := rat_cut_group_covers certificate976 numericValid976 hx

def certificate977 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate651,PopulationCertificates.Batch032.certificate651,[MergedCutCells.Batch302.certificate3624,MergedCutCells.Batch302.certificate3625,MergedCutCells.Batch302.certificate3626],(8428943732599404107/1000000000000000000),none,(1/2),(4285760453226846469/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid977 : certificate977.NumericValid := by decide +kernel
theorem cellsSound977 : ∀ c∈certificate977.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3624,MergedCutCells.Batch302.certificate3625,MergedCutCells.Batch302.certificate3626], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3624,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3626,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric977 : ∀ c∈certificate977.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3624,MergedCutCells.Batch302.certificate3625,MergedCutCells.Batch302.certificate3626], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3624,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3625,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3626,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid977 : ∀ c∈certificate977.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3624,MergedCutCells.Batch302.certificate3625,MergedCutCells.Batch302.certificate3626], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches977 : ∀ c∈certificate977.cells, c.population=certificate977.population := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3624,MergedCutCells.Batch302.certificate3625,MergedCutCells.Batch302.certificate3626], c.population=PopulationCertificates.Batch032.certificate651
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers977 {x : ℝ} (hx : certificate977.interval.Contains x) : ∃ c∈certificate977.cells, c.region.interval.Contains x := rat_cut_group_covers certificate977 numericValid977 hx

def certificate978 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate652,PopulationCertificates.Batch032.certificate652,[MergedCutCells.Batch302.certificate3627,MergedCutCells.Batch302.certificate3628],(478138917894872639/500000000000000000),(some (1108255987/1000000000)),(1/2),(155079482385969401/50000000000000000),(some (81869495924473399/200000000000000000)),(some (3560711624202423/25000000000000000))⟩
theorem numericValid978 : certificate978.NumericValid := by decide +kernel
theorem cellsSound978 : ∀ c∈certificate978.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3627,MergedCutCells.Batch302.certificate3628], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3628,List.forall_mem_nil _⟩⟩
theorem cellsNumeric978 : ∀ c∈certificate978.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3627,MergedCutCells.Batch302.certificate3628], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3627,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3628,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid978 : ∀ c∈certificate978.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3627,MergedCutCells.Batch302.certificate3628], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid327,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid327,List.forall_mem_nil _⟩⟩
theorem populationMatches978 : ∀ c∈certificate978.cells, c.population=certificate978.population := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3627,MergedCutCells.Batch302.certificate3628], c.population=PopulationCertificates.Batch032.certificate652
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers978 {x : ℝ} (hx : certificate978.interval.Contains x) : ∃ c∈certificate978.cells, c.region.interval.Contains x := rat_cut_group_covers certificate978 numericValid978 hx

def certificate979 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate652,PopulationCertificates.Batch032.certificate652,[MergedCutCells.Batch302.certificate3629,MergedCutCells.Batch302.certificate3630,MergedCutCells.Batch302.certificate3631,MergedCutCells.Batch302.certificate3632,MergedCutCells.Batch302.certificate3633,MergedCutCells.Batch302.certificate3634],(1108255987/1000000000),none,(1/2),(3058468909579423981/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid979 : certificate979.NumericValid := by decide +kernel
theorem cellsSound979 : ∀ c∈certificate979.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3629,MergedCutCells.Batch302.certificate3630,MergedCutCells.Batch302.certificate3631,MergedCutCells.Batch302.certificate3632,MergedCutCells.Batch302.certificate3633,MergedCutCells.Batch302.certificate3634], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3630,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3631,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3632,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3634,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric979 : ∀ c∈certificate979.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3629,MergedCutCells.Batch302.certificate3630,MergedCutCells.Batch302.certificate3631,MergedCutCells.Batch302.certificate3632,MergedCutCells.Batch302.certificate3633,MergedCutCells.Batch302.certificate3634], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3629,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3630,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3631,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3632,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3633,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3634,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid979 : ∀ c∈certificate979.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3629,MergedCutCells.Batch302.certificate3630,MergedCutCells.Batch302.certificate3631,MergedCutCells.Batch302.certificate3632,MergedCutCells.Batch302.certificate3633,MergedCutCells.Batch302.certificate3634], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches979 : ∀ c∈certificate979.cells, c.population=certificate979.population := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3629,MergedCutCells.Batch302.certificate3630,MergedCutCells.Batch302.certificate3631,MergedCutCells.Batch302.certificate3632,MergedCutCells.Batch302.certificate3633,MergedCutCells.Batch302.certificate3634], c.population=PopulationCertificates.Batch032.certificate652
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers979 {x : ℝ} (hx : certificate979.interval.Contains x) : ∃ c∈certificate979.cells, c.region.interval.Contains x := rat_cut_group_covers certificate979 numericValid979 hx

def certificate980 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate653,PopulationCertificates.Batch032.certificate653,[MergedCutCells.Batch302.certificate3635,MergedCutCells.Batch303.certificate3636,MergedCutCells.Batch303.certificate3637,MergedCutCells.Batch303.certificate3638],(4170495489663091047/500000000000000000),none,(1/2),(2163228613512149109/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid980 : certificate980.NumericValid := by decide +kernel
theorem cellsSound980 : ∀ c∈certificate980.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3635,MergedCutCells.Batch303.certificate3636,MergedCutCells.Batch303.certificate3637,MergedCutCells.Batch303.certificate3638], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.sound3635,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3636,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3637,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3638,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric980 : ∀ c∈certificate980.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3635,MergedCutCells.Batch303.certificate3636,MergedCutCells.Batch303.certificate3637,MergedCutCells.Batch303.certificate3638], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch302.numericValid3635,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3636,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3637,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3638,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid980 : ∀ c∈certificate980.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3635,MergedCutCells.Batch303.certificate3636,MergedCutCells.Batch303.certificate3637,MergedCutCells.Batch303.certificate3638], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches980 : ∀ c∈certificate980.cells, c.population=certificate980.population := by
  change ∀ c∈[MergedCutCells.Batch302.certificate3635,MergedCutCells.Batch303.certificate3636,MergedCutCells.Batch303.certificate3637,MergedCutCells.Batch303.certificate3638], c.population=PopulationCertificates.Batch032.certificate653
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers980 {x : ℝ} (hx : certificate980.interval.Contains x) : ∃ c∈certificate980.cells, c.region.interval.Contains x := rat_cut_group_covers certificate980 numericValid980 hx

def certificate981 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate654,PopulationCertificates.Batch032.certificate654,[MergedCutCells.Batch303.certificate3639,MergedCutCells.Batch303.certificate3640],(961884343835720827/1000000000000000000),(some (278631223/250000000)),(1/2),(402634633915556141/125000000000000000),(some (41356471496255293/100000000000000000)),(some (144790213801511433/1000000000000000000))⟩
theorem numericValid981 : certificate981.NumericValid := by decide +kernel
theorem cellsSound981 : ∀ c∈certificate981.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3639,MergedCutCells.Batch303.certificate3640], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3639,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3640,List.forall_mem_nil _⟩⟩
theorem cellsNumeric981 : ∀ c∈certificate981.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3639,MergedCutCells.Batch303.certificate3640], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3639,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3640,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid981 : ∀ c∈certificate981.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3639,MergedCutCells.Batch303.certificate3640], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid328,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid328,List.forall_mem_nil _⟩⟩
theorem populationMatches981 : ∀ c∈certificate981.cells, c.population=certificate981.population := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3639,MergedCutCells.Batch303.certificate3640], c.population=PopulationCertificates.Batch032.certificate654
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers981 {x : ℝ} (hx : certificate981.interval.Contains x) : ∃ c∈certificate981.cells, c.region.interval.Contains x := rat_cut_group_covers certificate981 numericValid981 hx

def certificate982 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate654,PopulationCertificates.Batch032.certificate654,[MergedCutCells.Batch303.certificate3641,MergedCutCells.Batch303.certificate3642,MergedCutCells.Batch303.certificate3643,MergedCutCells.Batch303.certificate3644,MergedCutCells.Batch303.certificate3645,MergedCutCells.Batch303.certificate3646],(278631223/250000000),none,(1/2),(638114096014833167/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid982 : certificate982.NumericValid := by decide +kernel
theorem cellsSound982 : ∀ c∈certificate982.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3641,MergedCutCells.Batch303.certificate3642,MergedCutCells.Batch303.certificate3643,MergedCutCells.Batch303.certificate3644,MergedCutCells.Batch303.certificate3645,MergedCutCells.Batch303.certificate3646], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3641,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3642,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3643,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3644,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3645,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3646,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric982 : ∀ c∈certificate982.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3641,MergedCutCells.Batch303.certificate3642,MergedCutCells.Batch303.certificate3643,MergedCutCells.Batch303.certificate3644,MergedCutCells.Batch303.certificate3645,MergedCutCells.Batch303.certificate3646], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3641,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3642,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3643,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3644,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3645,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3646,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid982 : ∀ c∈certificate982.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3641,MergedCutCells.Batch303.certificate3642,MergedCutCells.Batch303.certificate3643,MergedCutCells.Batch303.certificate3644,MergedCutCells.Batch303.certificate3645,MergedCutCells.Batch303.certificate3646], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches982 : ∀ c∈certificate982.cells, c.population=certificate982.population := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3641,MergedCutCells.Batch303.certificate3642,MergedCutCells.Batch303.certificate3643,MergedCutCells.Batch303.certificate3644,MergedCutCells.Batch303.certificate3645,MergedCutCells.Batch303.certificate3646], c.population=PopulationCertificates.Batch032.certificate654
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers982 {x : ℝ} (hx : certificate982.interval.Contains x) : ∃ c∈certificate982.cells, c.region.interval.Contains x := rat_cut_group_covers certificate982 numericValid982 hx

def certificate983 : RatCutGroup := ⟨GeometryCertificates.Batch032.certificate655,PopulationCertificates.Batch032.certificate655,[MergedCutCells.Batch303.certificate3647,MergedCutCells.Batch304.certificate3648,MergedCutCells.Batch304.certificate3649,MergedCutCells.Batch304.certificate3650],(4104041610675860181/500000000000000000),none,(1/2),(4366067138457158071/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid983 : certificate983.NumericValid := by decide +kernel
theorem cellsSound983 : ∀ c∈certificate983.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3647,MergedCutCells.Batch304.certificate3648,MergedCutCells.Batch304.certificate3649,MergedCutCells.Batch304.certificate3650], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.sound3647,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3648,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.sound3650,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric983 : ∀ c∈certificate983.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3647,MergedCutCells.Batch304.certificate3648,MergedCutCells.Batch304.certificate3649,MergedCutCells.Batch304.certificate3650], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch303.numericValid3647,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3648,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3649,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch304.numericValid3650,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid983 : ∀ c∈certificate983.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3647,MergedCutCells.Batch304.certificate3648,MergedCutCells.Batch304.certificate3649,MergedCutCells.Batch304.certificate3650], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches983 : ∀ c∈certificate983.cells, c.population=certificate983.population := by
  change ∀ c∈[MergedCutCells.Batch303.certificate3647,MergedCutCells.Batch304.certificate3648,MergedCutCells.Batch304.certificate3649,MergedCutCells.Batch304.certificate3650], c.population=PopulationCertificates.Batch032.certificate655
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers983 {x : ℝ} (hx : certificate983.interval.Contains x) : ∃ c∈certificate983.cells, c.region.interval.Contains x := rat_cut_group_covers certificate983 numericValid983 hx

end Cycle12.MergedCutGroups.Batch081
