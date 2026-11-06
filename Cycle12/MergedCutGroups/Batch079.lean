import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch031
import Cycle12.MergedCutCells.Batch292
import Cycle12.MergedCutCells.Batch293
import Cycle12.MergedCutCells.Batch294
import Cycle12.MergedCutCells.Batch295
import Cycle12.MergedCutCells.Batch296
import Cycle12.PopulationCertificates.Batch031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch079

def certificate948 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate632,PopulationCertificates.Batch031.certificate632,[MergedCutCells.Batch292.certificate3506,MergedCutCells.Batch292.certificate3507,MergedCutCells.Batch292.certificate3508],(908476588575388149/1000000000000000000),(some (1106023111/1000000000)),(1/2),(2302814780715395317/1000000000000000000),(some (374275791357347431/1000000000000000000)),(some (15465249466064187/125000000000000000))⟩
theorem numericValid948 : certificate948.NumericValid := by decide +kernel
theorem cellsSound948 : ∀ c∈certificate948.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3506,MergedCutCells.Batch292.certificate3507,MergedCutCells.Batch292.certificate3508], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3507,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3508,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric948 : ∀ c∈certificate948.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3506,MergedCutCells.Batch292.certificate3507,MergedCutCells.Batch292.certificate3508], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3506,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3507,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3508,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid948 : ∀ c∈certificate948.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3506,MergedCutCells.Batch292.certificate3507,MergedCutCells.Batch292.certificate3508], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid317,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid317,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid317,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches948 : ∀ c∈certificate948.cells, c.population=certificate948.population := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3506,MergedCutCells.Batch292.certificate3507,MergedCutCells.Batch292.certificate3508], c.population=PopulationCertificates.Batch031.certificate632
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers948 {x : ℝ} (hx : certificate948.interval.Contains x) : ∃ c∈certificate948.cells, c.region.interval.Contains x := rat_cut_group_covers certificate948 numericValid948 hx

def certificate949 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate632,PopulationCertificates.Batch031.certificate632,[MergedCutCells.Batch292.certificate3509,MergedCutCells.Batch292.certificate3510,MergedCutCells.Batch292.certificate3511,MergedCutCells.Batch292.certificate3512,MergedCutCells.Batch292.certificate3513,MergedCutCells.Batch292.certificate3514],(1106023111/1000000000),none,(1/2),(1131213515641522247/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid949 : certificate949.NumericValid := by decide +kernel
theorem cellsSound949 : ∀ c∈certificate949.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3509,MergedCutCells.Batch292.certificate3510,MergedCutCells.Batch292.certificate3511,MergedCutCells.Batch292.certificate3512,MergedCutCells.Batch292.certificate3513,MergedCutCells.Batch292.certificate3514], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3509,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3510,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3512,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3513,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3514,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric949 : ∀ c∈certificate949.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3509,MergedCutCells.Batch292.certificate3510,MergedCutCells.Batch292.certificate3511,MergedCutCells.Batch292.certificate3512,MergedCutCells.Batch292.certificate3513,MergedCutCells.Batch292.certificate3514], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3509,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3510,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3511,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3512,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3513,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3514,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid949 : ∀ c∈certificate949.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3509,MergedCutCells.Batch292.certificate3510,MergedCutCells.Batch292.certificate3511,MergedCutCells.Batch292.certificate3512,MergedCutCells.Batch292.certificate3513,MergedCutCells.Batch292.certificate3514], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches949 : ∀ c∈certificate949.cells, c.population=certificate949.population := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3509,MergedCutCells.Batch292.certificate3510,MergedCutCells.Batch292.certificate3511,MergedCutCells.Batch292.certificate3512,MergedCutCells.Batch292.certificate3513,MergedCutCells.Batch292.certificate3514], c.population=PopulationCertificates.Batch031.certificate632
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers949 {x : ℝ} (hx : certificate949.interval.Contains x) : ∃ c∈certificate949.cells, c.region.interval.Contains x := rat_cut_group_covers certificate949 numericValid949 hx

def certificate950 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate633,PopulationCertificates.Batch031.certificate633,[MergedCutCells.Batch292.certificate3515,MergedCutCells.Batch293.certificate3516,MergedCutCells.Batch293.certificate3517],(562764825433633173/62500000000000000),none,(1/2),(497493604072548711/62500000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid950 : certificate950.NumericValid := by decide +kernel
theorem cellsSound950 : ∀ c∈certificate950.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3515,MergedCutCells.Batch293.certificate3516,MergedCutCells.Batch293.certificate3517], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.sound3515,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3516,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3517,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric950 : ∀ c∈certificate950.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3515,MergedCutCells.Batch293.certificate3516,MergedCutCells.Batch293.certificate3517], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch292.numericValid3515,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3516,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3517,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid950 : ∀ c∈certificate950.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3515,MergedCutCells.Batch293.certificate3516,MergedCutCells.Batch293.certificate3517], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches950 : ∀ c∈certificate950.cells, c.population=certificate950.population := by
  change ∀ c∈[MergedCutCells.Batch292.certificate3515,MergedCutCells.Batch293.certificate3516,MergedCutCells.Batch293.certificate3517], c.population=PopulationCertificates.Batch031.certificate633
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers950 {x : ℝ} (hx : certificate950.interval.Contains x) : ∃ c∈certificate950.cells, c.region.interval.Contains x := rat_cut_group_covers certificate950 numericValid950 hx

def certificate951 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate634,PopulationCertificates.Batch031.certificate634,[MergedCutCells.Batch293.certificate3518,MergedCutCells.Batch293.certificate3519,MergedCutCells.Batch293.certificate3520],(227655927595654521/250000000000000000),(some (221703221/200000000)),(1/2),(467939239624648189/200000000000000000),(some (47058203087937727/125000000000000000)),(some (24968711337512169/200000000000000000))⟩
theorem numericValid951 : certificate951.NumericValid := by decide +kernel
theorem cellsSound951 : ∀ c∈certificate951.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3518,MergedCutCells.Batch293.certificate3519,MergedCutCells.Batch293.certificate3520], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3518,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3519,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3520,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric951 : ∀ c∈certificate951.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3518,MergedCutCells.Batch293.certificate3519,MergedCutCells.Batch293.certificate3520], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3518,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3519,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3520,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid951 : ∀ c∈certificate951.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3518,MergedCutCells.Batch293.certificate3519,MergedCutCells.Batch293.certificate3520], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid318,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid318,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid318,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches951 : ∀ c∈certificate951.cells, c.population=certificate951.population := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3518,MergedCutCells.Batch293.certificate3519,MergedCutCells.Batch293.certificate3520], c.population=PopulationCertificates.Batch031.certificate634
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers951 {x : ℝ} (hx : certificate951.interval.Contains x) : ∃ c∈certificate951.cells, c.region.interval.Contains x := rat_cut_group_covers certificate951 numericValid951 hx

def certificate952 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate634,PopulationCertificates.Batch031.certificate634,[MergedCutCells.Batch293.certificate3521,MergedCutCells.Batch293.certificate3522,MergedCutCells.Batch293.certificate3523,MergedCutCells.Batch293.certificate3524,MergedCutCells.Batch293.certificate3525,MergedCutCells.Batch293.certificate3526],(221703221/200000000),none,(1/2),(2304273349197414681/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid952 : certificate952.NumericValid := by decide +kernel
theorem cellsSound952 : ∀ c∈certificate952.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3521,MergedCutCells.Batch293.certificate3522,MergedCutCells.Batch293.certificate3523,MergedCutCells.Batch293.certificate3524,MergedCutCells.Batch293.certificate3525,MergedCutCells.Batch293.certificate3526], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3521,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3522,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3523,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3525,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3526,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric952 : ∀ c∈certificate952.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3521,MergedCutCells.Batch293.certificate3522,MergedCutCells.Batch293.certificate3523,MergedCutCells.Batch293.certificate3524,MergedCutCells.Batch293.certificate3525,MergedCutCells.Batch293.certificate3526], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3521,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3522,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3523,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3524,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3525,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3526,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid952 : ∀ c∈certificate952.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3521,MergedCutCells.Batch293.certificate3522,MergedCutCells.Batch293.certificate3523,MergedCutCells.Batch293.certificate3524,MergedCutCells.Batch293.certificate3525,MergedCutCells.Batch293.certificate3526], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches952 : ∀ c∈certificate952.cells, c.population=certificate952.population := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3521,MergedCutCells.Batch293.certificate3522,MergedCutCells.Batch293.certificate3523,MergedCutCells.Batch293.certificate3524,MergedCutCells.Batch293.certificate3525,MergedCutCells.Batch293.certificate3526], c.population=PopulationCertificates.Batch031.certificate634
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers952 {x : ℝ} (hx : certificate952.interval.Contains x) : ∃ c∈certificate952.cells, c.region.interval.Contains x := rat_cut_group_covers certificate952 numericValid952 hx

def certificate953 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate635,PopulationCertificates.Batch031.certificate635,[MergedCutCells.Batch293.certificate3527,MergedCutCells.Batch294.certificate3528,MergedCutCells.Batch294.certificate3529],(35657154427738453/4000000000000000),none,(1/2),(996413296212681437/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid953 : certificate953.NumericValid := by decide +kernel
theorem cellsSound953 : ∀ c∈certificate953.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3527,MergedCutCells.Batch294.certificate3528,MergedCutCells.Batch294.certificate3529], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.sound3527,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3529,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric953 : ∀ c∈certificate953.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3527,MergedCutCells.Batch294.certificate3528,MergedCutCells.Batch294.certificate3529], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch293.numericValid3527,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3528,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3529,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid953 : ∀ c∈certificate953.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3527,MergedCutCells.Batch294.certificate3528,MergedCutCells.Batch294.certificate3529], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches953 : ∀ c∈certificate953.cells, c.population=certificate953.population := by
  change ∀ c∈[MergedCutCells.Batch293.certificate3527,MergedCutCells.Batch294.certificate3528,MergedCutCells.Batch294.certificate3529], c.population=PopulationCertificates.Batch031.certificate635
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers953 {x : ℝ} (hx : certificate953.interval.Contains x) : ∃ c∈certificate953.cells, c.region.interval.Contains x := rat_cut_group_covers certificate953 numericValid953 hx

def certificate954 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate636,PopulationCertificates.Batch031.certificate636,[MergedCutCells.Batch294.certificate3530,MergedCutCells.Batch294.certificate3531,MergedCutCells.Batch294.certificate3532],(914079590199266343/1000000000000000000),(some (1112528109/1000000000)),(1/2),(2384173367176441531/1000000000000000000),(some (47334100342225849/125000000000000000)),(some (62990007780174409/500000000000000000))⟩
theorem numericValid954 : certificate954.NumericValid := by decide +kernel
theorem cellsSound954 : ∀ c∈certificate954.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3530,MergedCutCells.Batch294.certificate3531,MergedCutCells.Batch294.certificate3532], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3530,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3531,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3532,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric954 : ∀ c∈certificate954.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3530,MergedCutCells.Batch294.certificate3531,MergedCutCells.Batch294.certificate3532], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3530,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3531,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3532,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid954 : ∀ c∈certificate954.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3530,MergedCutCells.Batch294.certificate3531,MergedCutCells.Batch294.certificate3532], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid319,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid319,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy015.valid319,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches954 : ∀ c∈certificate954.cells, c.population=certificate954.population := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3530,MergedCutCells.Batch294.certificate3531,MergedCutCells.Batch294.certificate3532], c.population=PopulationCertificates.Batch031.certificate636
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers954 {x : ℝ} (hx : certificate954.interval.Contains x) : ∃ c∈certificate954.cells, c.region.interval.Contains x := rat_cut_group_covers certificate954 numericValid954 hx

def certificate955 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate636,PopulationCertificates.Batch031.certificate636,[MergedCutCells.Batch294.certificate3533,MergedCutCells.Batch294.certificate3534,MergedCutCells.Batch294.certificate3535,MergedCutCells.Batch294.certificate3536,MergedCutCells.Batch294.certificate3537,MergedCutCells.Batch294.certificate3538],(1112528109/1000000000),none,(1/2),(2344795559115886591/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid955 : certificate955.NumericValid := by decide +kernel
theorem cellsSound955 : ∀ c∈certificate955.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3533,MergedCutCells.Batch294.certificate3534,MergedCutCells.Batch294.certificate3535,MergedCutCells.Batch294.certificate3536,MergedCutCells.Batch294.certificate3537,MergedCutCells.Batch294.certificate3538], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3533,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3534,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3535,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3536,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3537,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3538,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric955 : ∀ c∈certificate955.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3533,MergedCutCells.Batch294.certificate3534,MergedCutCells.Batch294.certificate3535,MergedCutCells.Batch294.certificate3536,MergedCutCells.Batch294.certificate3537,MergedCutCells.Batch294.certificate3538], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3533,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3534,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3535,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3536,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3537,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3538,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid955 : ∀ c∈certificate955.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3533,MergedCutCells.Batch294.certificate3534,MergedCutCells.Batch294.certificate3535,MergedCutCells.Batch294.certificate3536,MergedCutCells.Batch294.certificate3537,MergedCutCells.Batch294.certificate3538], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches955 : ∀ c∈certificate955.cells, c.population=certificate955.population := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3533,MergedCutCells.Batch294.certificate3534,MergedCutCells.Batch294.certificate3535,MergedCutCells.Batch294.certificate3536,MergedCutCells.Batch294.certificate3537,MergedCutCells.Batch294.certificate3538], c.population=PopulationCertificates.Batch031.certificate636
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers955 {x : ℝ} (hx : certificate955.interval.Contains x) : ∃ c∈certificate955.cells, c.region.interval.Contains x := rat_cut_group_covers certificate955 numericValid955 hx

def certificate956 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate637,PopulationCertificates.Batch031.certificate637,[MergedCutCells.Batch294.certificate3539,MergedCutCells.Batch295.certificate3540,MergedCutCells.Batch295.certificate3541],(1782052406425489109/200000000000000000),none,(1/2),(802433822406630871/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid956 : certificate956.NumericValid := by decide +kernel
theorem cellsSound956 : ∀ c∈certificate956.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3539,MergedCutCells.Batch295.certificate3540,MergedCutCells.Batch295.certificate3541], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.sound3539,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3540,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3541,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric956 : ∀ c∈certificate956.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3539,MergedCutCells.Batch295.certificate3540,MergedCutCells.Batch295.certificate3541], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch294.numericValid3539,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3540,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3541,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid956 : ∀ c∈certificate956.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3539,MergedCutCells.Batch295.certificate3540,MergedCutCells.Batch295.certificate3541], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches956 : ∀ c∈certificate956.cells, c.population=certificate956.population := by
  change ∀ c∈[MergedCutCells.Batch294.certificate3539,MergedCutCells.Batch295.certificate3540,MergedCutCells.Batch295.certificate3541], c.population=PopulationCertificates.Batch031.certificate637
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers956 {x : ℝ} (hx : certificate956.interval.Contains x) : ∃ c∈certificate956.cells, c.region.interval.Contains x := rat_cut_group_covers certificate956 numericValid956 hx

def certificate957 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate638,PopulationCertificates.Batch031.certificate638,[MergedCutCells.Batch295.certificate3542,MergedCutCells.Batch295.certificate3543,MergedCutCells.Batch295.certificate3544],(915535368917868489/1000000000000000000),(some (139277243/125000000)),(1/2),(1212236395640730787/500000000000000000),(some (19137047141475659/50000000000000000)),(some (128090658636100143/1000000000000000000))⟩
theorem numericValid957 : certificate957.NumericValid := by decide +kernel
theorem cellsSound957 : ∀ c∈certificate957.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3542,MergedCutCells.Batch295.certificate3543,MergedCutCells.Batch295.certificate3544], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3542,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3543,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3544,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric957 : ∀ c∈certificate957.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3542,MergedCutCells.Batch295.certificate3543,MergedCutCells.Batch295.certificate3544], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3542,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3543,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3544,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid957 : ∀ c∈certificate957.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3542,MergedCutCells.Batch295.certificate3543,MergedCutCells.Batch295.certificate3544], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid320,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid320,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy016.valid320,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches957 : ∀ c∈certificate957.cells, c.population=certificate957.population := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3542,MergedCutCells.Batch295.certificate3543,MergedCutCells.Batch295.certificate3544], c.population=PopulationCertificates.Batch031.certificate638
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers957 {x : ℝ} (hx : certificate957.interval.Contains x) : ∃ c∈certificate957.cells, c.region.interval.Contains x := rat_cut_group_covers certificate957 numericValid957 hx

def certificate958 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate638,PopulationCertificates.Batch031.certificate638,[MergedCutCells.Batch295.certificate3545,MergedCutCells.Batch295.certificate3546,MergedCutCells.Batch295.certificate3547,MergedCutCells.Batch295.certificate3548,MergedCutCells.Batch295.certificate3549,MergedCutCells.Batch295.certificate3550],(139277243/125000000),none,(1/2),(2406003788275828611/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid958 : certificate958.NumericValid := by decide +kernel
theorem cellsSound958 : ∀ c∈certificate958.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3545,MergedCutCells.Batch295.certificate3546,MergedCutCells.Batch295.certificate3547,MergedCutCells.Batch295.certificate3548,MergedCutCells.Batch295.certificate3549,MergedCutCells.Batch295.certificate3550], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3545,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3546,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3547,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3548,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3549,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3550,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric958 : ∀ c∈certificate958.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3545,MergedCutCells.Batch295.certificate3546,MergedCutCells.Batch295.certificate3547,MergedCutCells.Batch295.certificate3548,MergedCutCells.Batch295.certificate3549,MergedCutCells.Batch295.certificate3550], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3545,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3546,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3547,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3548,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3549,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3550,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid958 : ∀ c∈certificate958.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3545,MergedCutCells.Batch295.certificate3546,MergedCutCells.Batch295.certificate3547,MergedCutCells.Batch295.certificate3548,MergedCutCells.Batch295.certificate3549,MergedCutCells.Batch295.certificate3550], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches958 : ∀ c∈certificate958.cells, c.population=certificate958.population := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3545,MergedCutCells.Batch295.certificate3546,MergedCutCells.Batch295.certificate3547,MergedCutCells.Batch295.certificate3548,MergedCutCells.Batch295.certificate3549,MergedCutCells.Batch295.certificate3550], c.population=PopulationCertificates.Batch031.certificate638
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers958 {x : ℝ} (hx : certificate958.interval.Contains x) : ∃ c∈certificate958.cells, c.region.interval.Contains x := rat_cut_group_covers certificate958 numericValid958 hx

def certificate959 : RatCutGroup := ⟨GeometryCertificates.Batch031.certificate639,PopulationCertificates.Batch031.certificate639,[MergedCutCells.Batch295.certificate3551,MergedCutCells.Batch296.certificate3552,MergedCutCells.Batch296.certificate3553,MergedCutCells.Batch296.certificate3554],(4428758446641500551/500000000000000000),none,(1/2),(1612641045088631153/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid959 : certificate959.NumericValid := by decide +kernel
theorem cellsSound959 : ∀ c∈certificate959.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3551,MergedCutCells.Batch296.certificate3552,MergedCutCells.Batch296.certificate3553,MergedCutCells.Batch296.certificate3554], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.sound3551,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3552,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3553,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.sound3554,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric959 : ∀ c∈certificate959.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3551,MergedCutCells.Batch296.certificate3552,MergedCutCells.Batch296.certificate3553,MergedCutCells.Batch296.certificate3554], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch295.numericValid3551,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3552,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3553,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch296.numericValid3554,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid959 : ∀ c∈certificate959.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3551,MergedCutCells.Batch296.certificate3552,MergedCutCells.Batch296.certificate3553,MergedCutCells.Batch296.certificate3554], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches959 : ∀ c∈certificate959.cells, c.population=certificate959.population := by
  change ∀ c∈[MergedCutCells.Batch295.certificate3551,MergedCutCells.Batch296.certificate3552,MergedCutCells.Batch296.certificate3553,MergedCutCells.Batch296.certificate3554], c.population=PopulationCertificates.Batch031.certificate639
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers959 {x : ℝ} (hx : certificate959.interval.Contains x) : ∃ c∈certificate959.cells, c.region.interval.Contains x := rat_cut_group_covers certificate959 numericValid959 hx

end Cycle12.MergedCutGroups.Batch079
