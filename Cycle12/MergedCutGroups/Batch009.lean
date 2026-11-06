import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch003
import Cycle12.MergedCutCells.Batch030
import Cycle12.MergedCutCells.Batch031
import Cycle12.MergedCutCells.Batch032
import Cycle12.MergedCutCells.Batch033
import Cycle12.MergedCutCells.Batch034
import Cycle12.PopulationCertificates.Batch003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch009

def certificate108 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate72,PopulationCertificates.Batch003.certificate72,[MergedCutCells.Batch030.certificate363,MergedCutCells.Batch030.certificate364,MergedCutCells.Batch030.certificate365],(750212234961350807/1000000000000000000),(some (491481851/500000000)),(1/2),(2507060120370563/12500000000000000),(some (446455282849278177/1000000000000000000)),(some (164129963818970093/1000000000000000000))⟩
theorem numericValid108 : certificate108.NumericValid := by decide +kernel
theorem cellsSound108 : ∀ c∈certificate108.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch030.certificate363,MergedCutCells.Batch030.certificate364,MergedCutCells.Batch030.certificate365], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound363,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound365,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric108 : ∀ c∈certificate108.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch030.certificate363,MergedCutCells.Batch030.certificate364,MergedCutCells.Batch030.certificate365], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid363,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid364,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid365,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid108 : ∀ c∈certificate108.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch030.certificate363,MergedCutCells.Batch030.certificate364,MergedCutCells.Batch030.certificate365], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid37,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid37,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid37,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches108 : ∀ c∈certificate108.cells, c.population=certificate108.population := by
  change ∀ c∈[MergedCutCells.Batch030.certificate363,MergedCutCells.Batch030.certificate364,MergedCutCells.Batch030.certificate365], c.population=PopulationCertificates.Batch003.certificate72
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers108 {x : ℝ} (hx : certificate108.interval.Contains x) : ∃ c∈certificate108.cells, c.region.interval.Contains x := rat_cut_group_covers certificate108 numericValid108 hx

def certificate109 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate72,PopulationCertificates.Batch003.certificate72,[MergedCutCells.Batch030.certificate366,MergedCutCells.Batch030.certificate367,MergedCutCells.Batch030.certificate368,MergedCutCells.Batch030.certificate369,MergedCutCells.Batch030.certificate370,MergedCutCells.Batch030.certificate371,MergedCutCells.Batch031.certificate372],(491481851/500000000),none,(1/2),(29774589914817143/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid109 : certificate109.NumericValid := by decide +kernel
theorem cellsSound109 : ∀ c∈certificate109.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch030.certificate366,MergedCutCells.Batch030.certificate367,MergedCutCells.Batch030.certificate368,MergedCutCells.Batch030.certificate369,MergedCutCells.Batch030.certificate370,MergedCutCells.Batch030.certificate371,MergedCutCells.Batch031.certificate372], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound366,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound367,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound369,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound370,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.sound371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound372,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric109 : ∀ c∈certificate109.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch030.certificate366,MergedCutCells.Batch030.certificate367,MergedCutCells.Batch030.certificate368,MergedCutCells.Batch030.certificate369,MergedCutCells.Batch030.certificate370,MergedCutCells.Batch030.certificate371,MergedCutCells.Batch031.certificate372], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid366,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid367,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid368,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid369,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid370,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch030.numericValid371,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid372,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid109 : ∀ c∈certificate109.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch030.certificate366,MergedCutCells.Batch030.certificate367,MergedCutCells.Batch030.certificate368,MergedCutCells.Batch030.certificate369,MergedCutCells.Batch030.certificate370,MergedCutCells.Batch030.certificate371,MergedCutCells.Batch031.certificate372], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches109 : ∀ c∈certificate109.cells, c.population=certificate109.population := by
  change ∀ c∈[MergedCutCells.Batch030.certificate366,MergedCutCells.Batch030.certificate367,MergedCutCells.Batch030.certificate368,MergedCutCells.Batch030.certificate369,MergedCutCells.Batch030.certificate370,MergedCutCells.Batch030.certificate371,MergedCutCells.Batch031.certificate372], c.population=PopulationCertificates.Batch003.certificate72
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers109 {x : ℝ} (hx : certificate109.interval.Contains x) : ∃ c∈certificate109.cells, c.region.interval.Contains x := rat_cut_group_covers certificate109 numericValid109 hx

def certificate110 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate73,PopulationCertificates.Batch003.certificate73,[MergedCutCells.Batch031.certificate373,MergedCutCells.Batch031.certificate374,MergedCutCells.Batch031.certificate375],(472455735680865129/125000000000000000),none,(1/2),(105906403969932479/200000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid110 : certificate110.NumericValid := by decide +kernel
theorem cellsSound110 : ∀ c∈certificate110.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch031.certificate373,MergedCutCells.Batch031.certificate374,MergedCutCells.Batch031.certificate375], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound373,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound375,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric110 : ∀ c∈certificate110.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch031.certificate373,MergedCutCells.Batch031.certificate374,MergedCutCells.Batch031.certificate375], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid373,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid374,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid375,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid110 : ∀ c∈certificate110.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch031.certificate373,MergedCutCells.Batch031.certificate374,MergedCutCells.Batch031.certificate375], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches110 : ∀ c∈certificate110.cells, c.population=certificate110.population := by
  change ∀ c∈[MergedCutCells.Batch031.certificate373,MergedCutCells.Batch031.certificate374,MergedCutCells.Batch031.certificate375], c.population=PopulationCertificates.Batch003.certificate73
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers110 {x : ℝ} (hx : certificate110.interval.Contains x) : ∃ c∈certificate110.cells, c.region.interval.Contains x := rat_cut_group_covers certificate110 numericValid110 hx

def certificate111 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate74,PopulationCertificates.Batch003.certificate74,[MergedCutCells.Batch031.certificate376,MergedCutCells.Batch031.certificate377,MergedCutCells.Batch031.certificate378],(37756317135587519/50000000000000000),(some (966361547/1000000000)),(1/2),(8629421142737161/40000000000000000),(some (448919174217223923/1000000000000000000)),(some (82824367354056397/500000000000000000))⟩
theorem numericValid111 : certificate111.NumericValid := by decide +kernel
theorem cellsSound111 : ∀ c∈certificate111.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch031.certificate376,MergedCutCells.Batch031.certificate377,MergedCutCells.Batch031.certificate378], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound377,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound378,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric111 : ∀ c∈certificate111.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch031.certificate376,MergedCutCells.Batch031.certificate377,MergedCutCells.Batch031.certificate378], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid376,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid377,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid378,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid111 : ∀ c∈certificate111.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch031.certificate376,MergedCutCells.Batch031.certificate377,MergedCutCells.Batch031.certificate378], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid38,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid38,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid38,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches111 : ∀ c∈certificate111.cells, c.population=certificate111.population := by
  change ∀ c∈[MergedCutCells.Batch031.certificate376,MergedCutCells.Batch031.certificate377,MergedCutCells.Batch031.certificate378], c.population=PopulationCertificates.Batch003.certificate74
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers111 {x : ℝ} (hx : certificate111.interval.Contains x) : ∃ c∈certificate111.cells, c.region.interval.Contains x := rat_cut_group_covers certificate111 numericValid111 hx

def certificate112 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate74,PopulationCertificates.Batch003.certificate74,[MergedCutCells.Batch031.certificate379,MergedCutCells.Batch031.certificate380,MergedCutCells.Batch031.certificate381,MergedCutCells.Batch031.certificate382,MergedCutCells.Batch031.certificate383,MergedCutCells.Batch032.certificate384,MergedCutCells.Batch032.certificate385],(966361547/1000000000),none,(1/2),(14478612610993391/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid112 : certificate112.NumericValid := by decide +kernel
theorem cellsSound112 : ∀ c∈certificate112.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch031.certificate379,MergedCutCells.Batch031.certificate380,MergedCutCells.Batch031.certificate381,MergedCutCells.Batch031.certificate382,MergedCutCells.Batch031.certificate383,MergedCutCells.Batch032.certificate384,MergedCutCells.Batch032.certificate385], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound379,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound380,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound381,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound382,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.sound383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound385,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric112 : ∀ c∈certificate112.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch031.certificate379,MergedCutCells.Batch031.certificate380,MergedCutCells.Batch031.certificate381,MergedCutCells.Batch031.certificate382,MergedCutCells.Batch031.certificate383,MergedCutCells.Batch032.certificate384,MergedCutCells.Batch032.certificate385], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid379,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid380,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid381,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid382,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch031.numericValid383,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid384,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid385,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid112 : ∀ c∈certificate112.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch031.certificate379,MergedCutCells.Batch031.certificate380,MergedCutCells.Batch031.certificate381,MergedCutCells.Batch031.certificate382,MergedCutCells.Batch031.certificate383,MergedCutCells.Batch032.certificate384,MergedCutCells.Batch032.certificate385], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches112 : ∀ c∈certificate112.cells, c.population=certificate112.population := by
  change ∀ c∈[MergedCutCells.Batch031.certificate379,MergedCutCells.Batch031.certificate380,MergedCutCells.Batch031.certificate381,MergedCutCells.Batch031.certificate382,MergedCutCells.Batch031.certificate383,MergedCutCells.Batch032.certificate384,MergedCutCells.Batch032.certificate385], c.population=PopulationCertificates.Batch003.certificate74
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers112 {x : ℝ} (hx : certificate112.interval.Contains x) : ∃ c∈certificate112.cells, c.region.interval.Contains x := rat_cut_group_covers certificate112 numericValid112 hx

def certificate113 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate75,PopulationCertificates.Batch003.certificate75,[MergedCutCells.Batch032.certificate386,MergedCutCells.Batch032.certificate387,MergedCutCells.Batch032.certificate388],(3789725155809587821/1000000000000000000),none,(1/2),(540144568553611929/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid113 : certificate113.NumericValid := by decide +kernel
theorem cellsSound113 : ∀ c∈certificate113.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch032.certificate386,MergedCutCells.Batch032.certificate387,MergedCutCells.Batch032.certificate388], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound386,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound387,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound388,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric113 : ∀ c∈certificate113.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch032.certificate386,MergedCutCells.Batch032.certificate387,MergedCutCells.Batch032.certificate388], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid386,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid387,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid388,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid113 : ∀ c∈certificate113.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch032.certificate386,MergedCutCells.Batch032.certificate387,MergedCutCells.Batch032.certificate388], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches113 : ∀ c∈certificate113.cells, c.population=certificate113.population := by
  change ∀ c∈[MergedCutCells.Batch032.certificate386,MergedCutCells.Batch032.certificate387,MergedCutCells.Batch032.certificate388], c.population=PopulationCertificates.Batch003.certificate75
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers113 {x : ℝ} (hx : certificate113.interval.Contains x) : ∃ c∈certificate113.cells, c.region.interval.Contains x := rat_cut_group_covers certificate113 numericValid113 hx

def certificate114 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate76,PopulationCertificates.Batch003.certificate76,[MergedCutCells.Batch032.certificate389,MergedCutCells.Batch032.certificate390,MergedCutCells.Batch032.certificate391],(757851109289422781/1000000000000000000),(some (38786179/40000000)),(1/2),(14238732696986293/62500000000000000),(some (456395752500717989/1000000000000000000)),(some (85160789914632243/500000000000000000))⟩
theorem numericValid114 : certificate114.NumericValid := by decide +kernel
theorem cellsSound114 : ∀ c∈certificate114.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch032.certificate389,MergedCutCells.Batch032.certificate390,MergedCutCells.Batch032.certificate391], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound389,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound390,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound391,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric114 : ∀ c∈certificate114.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch032.certificate389,MergedCutCells.Batch032.certificate390,MergedCutCells.Batch032.certificate391], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid389,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid390,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid391,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid114 : ∀ c∈certificate114.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch032.certificate389,MergedCutCells.Batch032.certificate390,MergedCutCells.Batch032.certificate391], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid39,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid39,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy001.valid39,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches114 : ∀ c∈certificate114.cells, c.population=certificate114.population := by
  change ∀ c∈[MergedCutCells.Batch032.certificate389,MergedCutCells.Batch032.certificate390,MergedCutCells.Batch032.certificate391], c.population=PopulationCertificates.Batch003.certificate76
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers114 {x : ℝ} (hx : certificate114.interval.Contains x) : ∃ c∈certificate114.cells, c.region.interval.Contains x := rat_cut_group_covers certificate114 numericValid114 hx

def certificate115 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate76,PopulationCertificates.Batch003.certificate76,[MergedCutCells.Batch032.certificate392,MergedCutCells.Batch032.certificate393,MergedCutCells.Batch032.certificate394,MergedCutCells.Batch032.certificate395,MergedCutCells.Batch033.certificate396,MergedCutCells.Batch033.certificate397,MergedCutCells.Batch033.certificate398],(38786179/40000000),none,(1/2),(21805264938658173/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid115 : certificate115.NumericValid := by decide +kernel
theorem cellsSound115 : ∀ c∈certificate115.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch032.certificate392,MergedCutCells.Batch032.certificate393,MergedCutCells.Batch032.certificate394,MergedCutCells.Batch032.certificate395,MergedCutCells.Batch033.certificate396,MergedCutCells.Batch033.certificate397,MergedCutCells.Batch033.certificate398], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound392,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound393,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound394,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.sound395,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound397,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound398,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric115 : ∀ c∈certificate115.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch032.certificate392,MergedCutCells.Batch032.certificate393,MergedCutCells.Batch032.certificate394,MergedCutCells.Batch032.certificate395,MergedCutCells.Batch033.certificate396,MergedCutCells.Batch033.certificate397,MergedCutCells.Batch033.certificate398], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid392,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid393,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid394,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch032.numericValid395,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid396,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid397,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid398,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid115 : ∀ c∈certificate115.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch032.certificate392,MergedCutCells.Batch032.certificate393,MergedCutCells.Batch032.certificate394,MergedCutCells.Batch032.certificate395,MergedCutCells.Batch033.certificate396,MergedCutCells.Batch033.certificate397,MergedCutCells.Batch033.certificate398], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches115 : ∀ c∈certificate115.cells, c.population=certificate115.population := by
  change ∀ c∈[MergedCutCells.Batch032.certificate392,MergedCutCells.Batch032.certificate393,MergedCutCells.Batch032.certificate394,MergedCutCells.Batch032.certificate395,MergedCutCells.Batch033.certificate396,MergedCutCells.Batch033.certificate397,MergedCutCells.Batch033.certificate398], c.population=PopulationCertificates.Batch003.certificate76
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers115 {x : ℝ} (hx : certificate115.interval.Contains x) : ∃ c∈certificate115.cells, c.region.interval.Contains x := rat_cut_group_covers certificate115 numericValid115 hx

def certificate116 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate77,PopulationCertificates.Batch003.certificate77,[MergedCutCells.Batch033.certificate399,MergedCutCells.Batch033.certificate400,MergedCutCells.Batch033.certificate401],(3751702829296014991/1000000000000000000),none,(1/2),(534177359081348929/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid116 : certificate116.NumericValid := by decide +kernel
theorem cellsSound116 : ∀ c∈certificate116.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch033.certificate399,MergedCutCells.Batch033.certificate400,MergedCutCells.Batch033.certificate401], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound399,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound400,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound401,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric116 : ∀ c∈certificate116.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch033.certificate399,MergedCutCells.Batch033.certificate400,MergedCutCells.Batch033.certificate401], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid399,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid400,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid401,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid116 : ∀ c∈certificate116.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch033.certificate399,MergedCutCells.Batch033.certificate400,MergedCutCells.Batch033.certificate401], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches116 : ∀ c∈certificate116.cells, c.population=certificate116.population := by
  change ∀ c∈[MergedCutCells.Batch033.certificate399,MergedCutCells.Batch033.certificate400,MergedCutCells.Batch033.certificate401], c.population=PopulationCertificates.Batch003.certificate77
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers116 {x : ℝ} (hx : certificate116.interval.Contains x) : ∃ c∈certificate116.cells, c.region.interval.Contains x := rat_cut_group_covers certificate116 numericValid116 hx

def certificate117 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate78,PopulationCertificates.Batch003.certificate78,[MergedCutCells.Batch033.certificate402,MergedCutCells.Batch033.certificate403,MergedCutCells.Batch033.certificate404],(380737921344653721/500000000000000000),(some (974034011/1000000000)),(1/2),(115028724055474621/500000000000000000),(some (232185071544772997/500000000000000000)),(some (5481734931488071/31250000000000000))⟩
theorem numericValid117 : certificate117.NumericValid := by decide +kernel
theorem cellsSound117 : ∀ c∈certificate117.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch033.certificate402,MergedCutCells.Batch033.certificate403,MergedCutCells.Batch033.certificate404], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound402,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound403,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound404,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric117 : ∀ c∈certificate117.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch033.certificate402,MergedCutCells.Batch033.certificate403,MergedCutCells.Batch033.certificate404], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid402,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid403,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid404,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid117 : ∀ c∈certificate117.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch033.certificate402,MergedCutCells.Batch033.certificate403,MergedCutCells.Batch033.certificate404], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid40,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid40,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy002.valid40,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches117 : ∀ c∈certificate117.cells, c.population=certificate117.population := by
  change ∀ c∈[MergedCutCells.Batch033.certificate402,MergedCutCells.Batch033.certificate403,MergedCutCells.Batch033.certificate404], c.population=PopulationCertificates.Batch003.certificate78
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers117 {x : ℝ} (hx : certificate117.interval.Contains x) : ∃ c∈certificate117.cells, c.region.interval.Contains x := rat_cut_group_covers certificate117 numericValid117 hx

def certificate118 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate78,PopulationCertificates.Batch003.certificate78,[MergedCutCells.Batch033.certificate405,MergedCutCells.Batch033.certificate406,MergedCutCells.Batch033.certificate407,MergedCutCells.Batch034.certificate408,MergedCutCells.Batch034.certificate409,MergedCutCells.Batch034.certificate410],(974034011/1000000000),none,(1/2),(86499668673224943/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid118 : certificate118.NumericValid := by decide +kernel
theorem cellsSound118 : ∀ c∈certificate118.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch033.certificate405,MergedCutCells.Batch033.certificate406,MergedCutCells.Batch033.certificate407,MergedCutCells.Batch034.certificate408,MergedCutCells.Batch034.certificate409,MergedCutCells.Batch034.certificate410], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound405,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound406,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.sound407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound408,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound409,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound410,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsNumeric118 : ∀ c∈certificate118.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch033.certificate405,MergedCutCells.Batch033.certificate406,MergedCutCells.Batch033.certificate407,MergedCutCells.Batch034.certificate408,MergedCutCells.Batch034.certificate409,MergedCutCells.Batch034.certificate410], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid405,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid406,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch033.numericValid407,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid408,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid409,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid410,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid118 : ∀ c∈certificate118.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch033.certificate405,MergedCutCells.Batch033.certificate406,MergedCutCells.Batch033.certificate407,MergedCutCells.Batch034.certificate408,MergedCutCells.Batch034.certificate409,MergedCutCells.Batch034.certificate410], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem populationMatches118 : ∀ c∈certificate118.cells, c.population=certificate118.population := by
  change ∀ c∈[MergedCutCells.Batch033.certificate405,MergedCutCells.Batch033.certificate406,MergedCutCells.Batch033.certificate407,MergedCutCells.Batch034.certificate408,MergedCutCells.Batch034.certificate409,MergedCutCells.Batch034.certificate410], c.population=PopulationCertificates.Batch003.certificate78
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem covers118 {x : ℝ} (hx : certificate118.interval.Contains x) : ∃ c∈certificate118.cells, c.region.interval.Contains x := rat_cut_group_covers certificate118 numericValid118 hx

def certificate119 : RatCutGroup := ⟨GeometryCertificates.Batch003.certificate79,PopulationCertificates.Batch003.certificate79,[MergedCutCells.Batch034.certificate411,MergedCutCells.Batch034.certificate412,MergedCutCells.Batch034.certificate413,MergedCutCells.Batch034.certificate414],(942492059316894563/250000000000000000),none,(1/2),(278190992531952069/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid119 : certificate119.NumericValid := by decide +kernel
theorem cellsSound119 : ∀ c∈certificate119.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch034.certificate411,MergedCutCells.Batch034.certificate412,MergedCutCells.Batch034.certificate413,MergedCutCells.Batch034.certificate414], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound411,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound413,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.sound414,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric119 : ∀ c∈certificate119.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch034.certificate411,MergedCutCells.Batch034.certificate412,MergedCutCells.Batch034.certificate413,MergedCutCells.Batch034.certificate414], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid411,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid412,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid413,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch034.numericValid414,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid119 : ∀ c∈certificate119.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch034.certificate411,MergedCutCells.Batch034.certificate412,MergedCutCells.Batch034.certificate413,MergedCutCells.Batch034.certificate414], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches119 : ∀ c∈certificate119.cells, c.population=certificate119.population := by
  change ∀ c∈[MergedCutCells.Batch034.certificate411,MergedCutCells.Batch034.certificate412,MergedCutCells.Batch034.certificate413,MergedCutCells.Batch034.certificate414], c.population=PopulationCertificates.Batch003.certificate79
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers119 {x : ℝ} (hx : certificate119.interval.Contains x) : ∃ c∈certificate119.cells, c.region.interval.Contains x := rat_cut_group_covers certificate119 numericValid119 hx

end Cycle12.MergedCutGroups.Batch009
