import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch009
import Cycle12.MergedCutCells.Batch089
import Cycle12.MergedCutCells.Batch090
import Cycle12.MergedCutCells.Batch091
import Cycle12.MergedCutCells.Batch092
import Cycle12.MergedCutCells.Batch093
import Cycle12.PopulationCertificates.Batch009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch023

def certificate276 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate184,PopulationCertificates.Batch009.certificate184,[MergedCutCells.Batch089.certificate1071,MergedCutCells.Batch089.certificate1072,MergedCutCells.Batch089.certificate1073,MergedCutCells.Batch089.certificate1074,MergedCutCells.Batch089.certificate1075,MergedCutCells.Batch089.certificate1076,MergedCutCells.Batch089.certificate1077,MergedCutCells.Batch089.certificate1078,MergedCutCells.Batch089.certificate1079],(105493064316875119/125000000000000000),(some 64),(1/2),(230303300333540023/500000000000000000),(some (69314718055994531/100000000000000000)),(some (1430380936749828801/1000000000000000000))⟩
theorem numericValid276 : certificate276.NumericValid := by decide +kernel
theorem cellsSound276 : ∀ c∈certificate276.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch089.certificate1071,MergedCutCells.Batch089.certificate1072,MergedCutCells.Batch089.certificate1073,MergedCutCells.Batch089.certificate1074,MergedCutCells.Batch089.certificate1075,MergedCutCells.Batch089.certificate1076,MergedCutCells.Batch089.certificate1077,MergedCutCells.Batch089.certificate1078,MergedCutCells.Batch089.certificate1079], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1071,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1072,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1074,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1075,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1077,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1078,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.sound1079,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric276 : ∀ c∈certificate276.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch089.certificate1071,MergedCutCells.Batch089.certificate1072,MergedCutCells.Batch089.certificate1073,MergedCutCells.Batch089.certificate1074,MergedCutCells.Batch089.certificate1075,MergedCutCells.Batch089.certificate1076,MergedCutCells.Batch089.certificate1077,MergedCutCells.Batch089.certificate1078,MergedCutCells.Batch089.certificate1079], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1071,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1072,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1073,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1074,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1075,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1076,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1077,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1078,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch089.numericValid1079,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid276 : ∀ c∈certificate276.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch089.certificate1071,MergedCutCells.Batch089.certificate1072,MergedCutCells.Batch089.certificate1073,MergedCutCells.Batch089.certificate1074,MergedCutCells.Batch089.certificate1075,MergedCutCells.Batch089.certificate1076,MergedCutCells.Batch089.certificate1077,MergedCutCells.Batch089.certificate1078,MergedCutCells.Batch089.certificate1079], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid93,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches276 : ∀ c∈certificate276.cells, c.population=certificate276.population := by
  change ∀ c∈[MergedCutCells.Batch089.certificate1071,MergedCutCells.Batch089.certificate1072,MergedCutCells.Batch089.certificate1073,MergedCutCells.Batch089.certificate1074,MergedCutCells.Batch089.certificate1075,MergedCutCells.Batch089.certificate1076,MergedCutCells.Batch089.certificate1077,MergedCutCells.Batch089.certificate1078,MergedCutCells.Batch089.certificate1079], c.population=PopulationCertificates.Batch009.certificate184
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers276 {x : ℝ} (hx : certificate276.interval.Contains x) : ∃ c∈certificate276.cells, c.region.interval.Contains x := rat_cut_group_covers certificate276 numericValid276 hx

def certificate277 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate184,PopulationCertificates.Batch009.certificate184,[MergedCutCells.Batch090.certificate1080],64,none,(1/2),(1101826190497185269/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid277 : certificate277.NumericValid := by decide +kernel
theorem cellsSound277 : ∀ c∈certificate277.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1080], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1080,List.forall_mem_nil _⟩
theorem cellsNumeric277 : ∀ c∈certificate277.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1080], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1080,List.forall_mem_nil _⟩
theorem cellsEntropyValid277 : ∀ c∈certificate277.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1080], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches277 : ∀ c∈certificate277.cells, c.population=certificate277.population := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1080], c.population=PopulationCertificates.Batch009.certificate184
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers277 {x : ℝ} (hx : certificate277.interval.Contains x) : ∃ c∈certificate277.cells, c.region.interval.Contains x := rat_cut_group_covers certificate277 numericValid277 hx

def certificate278 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate185,PopulationCertificates.Batch009.certificate185,[MergedCutCells.Batch090.certificate1081,MergedCutCells.Batch090.certificate1082,MergedCutCells.Batch090.certificate1083,MergedCutCells.Batch090.certificate1084],(3634330415175817653/1000000000000000000),none,(1/2),(679455940027663909/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid278 : certificate278.NumericValid := by decide +kernel
theorem cellsSound278 : ∀ c∈certificate278.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1081,MergedCutCells.Batch090.certificate1082,MergedCutCells.Batch090.certificate1083,MergedCutCells.Batch090.certificate1084], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1083,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1084,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric278 : ∀ c∈certificate278.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1081,MergedCutCells.Batch090.certificate1082,MergedCutCells.Batch090.certificate1083,MergedCutCells.Batch090.certificate1084], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1081,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1082,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1083,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1084,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid278 : ∀ c∈certificate278.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1081,MergedCutCells.Batch090.certificate1082,MergedCutCells.Batch090.certificate1083,MergedCutCells.Batch090.certificate1084], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches278 : ∀ c∈certificate278.cells, c.population=certificate278.population := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1081,MergedCutCells.Batch090.certificate1082,MergedCutCells.Batch090.certificate1083,MergedCutCells.Batch090.certificate1084], c.population=PopulationCertificates.Batch009.certificate185
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers278 {x : ℝ} (hx : certificate278.interval.Contains x) : ∃ c∈certificate278.cells, c.region.interval.Contains x := rat_cut_group_covers certificate278 numericValid278 hx

def certificate279 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate186,PopulationCertificates.Batch009.certificate186,[MergedCutCells.Batch090.certificate1085,MergedCutCells.Batch090.certificate1086,MergedCutCells.Batch090.certificate1087,MergedCutCells.Batch090.certificate1088,MergedCutCells.Batch090.certificate1089,MergedCutCells.Batch090.certificate1090,MergedCutCells.Batch090.certificate1091],(425082802043160739/500000000000000000),(some 64),(1/2),(116603857487016391/250000000000000000),(some (69314718055994531/100000000000000000)),(some (1432800548637217321/1000000000000000000))⟩
theorem numericValid279 : certificate279.NumericValid := by decide +kernel
theorem cellsSound279 : ∀ c∈certificate279.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1085,MergedCutCells.Batch090.certificate1086,MergedCutCells.Batch090.certificate1087,MergedCutCells.Batch090.certificate1088,MergedCutCells.Batch090.certificate1089,MergedCutCells.Batch090.certificate1090,MergedCutCells.Batch090.certificate1091], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1085,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1087,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1088,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1089,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1090,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.sound1091,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric279 : ∀ c∈certificate279.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1085,MergedCutCells.Batch090.certificate1086,MergedCutCells.Batch090.certificate1087,MergedCutCells.Batch090.certificate1088,MergedCutCells.Batch090.certificate1089,MergedCutCells.Batch090.certificate1090,MergedCutCells.Batch090.certificate1091], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1085,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1086,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1087,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1088,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1089,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1090,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch090.numericValid1091,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid279 : ∀ c∈certificate279.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1085,MergedCutCells.Batch090.certificate1086,MergedCutCells.Batch090.certificate1087,MergedCutCells.Batch090.certificate1088,MergedCutCells.Batch090.certificate1089,MergedCutCells.Batch090.certificate1090,MergedCutCells.Batch090.certificate1091], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid94,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid94,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid94,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid94,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid94,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid94,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid94,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches279 : ∀ c∈certificate279.cells, c.population=certificate279.population := by
  change ∀ c∈[MergedCutCells.Batch090.certificate1085,MergedCutCells.Batch090.certificate1086,MergedCutCells.Batch090.certificate1087,MergedCutCells.Batch090.certificate1088,MergedCutCells.Batch090.certificate1089,MergedCutCells.Batch090.certificate1090,MergedCutCells.Batch090.certificate1091], c.population=PopulationCertificates.Batch009.certificate186
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers279 {x : ℝ} (hx : certificate279.interval.Contains x) : ∃ c∈certificate279.cells, c.region.interval.Contains x := rat_cut_group_covers certificate279 numericValid279 hx

def certificate280 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate186,PopulationCertificates.Batch009.certificate186,[MergedCutCells.Batch091.certificate1092],64,none,(1/2),(556905840737508399/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid280 : certificate280.NumericValid := by decide +kernel
theorem cellsSound280 : ∀ c∈certificate280.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1092], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1092,List.forall_mem_nil _⟩
theorem cellsNumeric280 : ∀ c∈certificate280.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1092], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1092,List.forall_mem_nil _⟩
theorem cellsEntropyValid280 : ∀ c∈certificate280.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1092], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches280 : ∀ c∈certificate280.cells, c.population=certificate280.population := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1092], c.population=PopulationCertificates.Batch009.certificate186
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers280 {x : ℝ} (hx : certificate280.interval.Contains x) : ∃ c∈certificate280.cells, c.region.interval.Contains x := rat_cut_group_covers certificate280 numericValid280 hx

def certificate281 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate187,PopulationCertificates.Batch009.certificate187,[MergedCutCells.Batch091.certificate1093,MergedCutCells.Batch091.certificate1094,MergedCutCells.Batch091.certificate1095,MergedCutCells.Batch091.certificate1096],(3641594569279167081/1000000000000000000),none,(1/2),(696192465345029667/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid281 : certificate281.NumericValid := by decide +kernel
theorem cellsSound281 : ∀ c∈certificate281.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1093,MergedCutCells.Batch091.certificate1094,MergedCutCells.Batch091.certificate1095,MergedCutCells.Batch091.certificate1096], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1093,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1095,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1096,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric281 : ∀ c∈certificate281.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1093,MergedCutCells.Batch091.certificate1094,MergedCutCells.Batch091.certificate1095,MergedCutCells.Batch091.certificate1096], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1093,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1094,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1095,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1096,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid281 : ∀ c∈certificate281.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1093,MergedCutCells.Batch091.certificate1094,MergedCutCells.Batch091.certificate1095,MergedCutCells.Batch091.certificate1096], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches281 : ∀ c∈certificate281.cells, c.population=certificate281.population := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1093,MergedCutCells.Batch091.certificate1094,MergedCutCells.Batch091.certificate1095,MergedCutCells.Batch091.certificate1096], c.population=PopulationCertificates.Batch009.certificate187
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers281 {x : ℝ} (hx : certificate281.interval.Contains x) : ∃ c∈certificate281.cells, c.region.interval.Contains x := rat_cut_group_covers certificate281 numericValid281 hx

def certificate282 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate188,PopulationCertificates.Batch009.certificate188,[MergedCutCells.Batch091.certificate1097,MergedCutCells.Batch091.certificate1098,MergedCutCells.Batch091.certificate1099,MergedCutCells.Batch091.certificate1100,MergedCutCells.Batch091.certificate1101,MergedCutCells.Batch091.certificate1102,MergedCutCells.Batch091.certificate1103],(843544728118831303/1000000000000000000),(some 64),(1/2),(94749229933225023/200000000000000000),(some (69314718055994531/100000000000000000)),(some (1433851065939527119/1000000000000000000))⟩
theorem numericValid282 : certificate282.NumericValid := by decide +kernel
theorem cellsSound282 : ∀ c∈certificate282.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1097,MergedCutCells.Batch091.certificate1098,MergedCutCells.Batch091.certificate1099,MergedCutCells.Batch091.certificate1100,MergedCutCells.Batch091.certificate1101,MergedCutCells.Batch091.certificate1102,MergedCutCells.Batch091.certificate1103], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1097,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1098,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1099,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1101,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1102,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.sound1103,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric282 : ∀ c∈certificate282.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1097,MergedCutCells.Batch091.certificate1098,MergedCutCells.Batch091.certificate1099,MergedCutCells.Batch091.certificate1100,MergedCutCells.Batch091.certificate1101,MergedCutCells.Batch091.certificate1102,MergedCutCells.Batch091.certificate1103], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1097,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1098,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1099,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1100,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1101,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1102,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch091.numericValid1103,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid282 : ∀ c∈certificate282.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1097,MergedCutCells.Batch091.certificate1098,MergedCutCells.Batch091.certificate1099,MergedCutCells.Batch091.certificate1100,MergedCutCells.Batch091.certificate1101,MergedCutCells.Batch091.certificate1102,MergedCutCells.Batch091.certificate1103], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid95,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid95,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid95,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid95,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid95,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid95,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid95,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches282 : ∀ c∈certificate282.cells, c.population=certificate282.population := by
  change ∀ c∈[MergedCutCells.Batch091.certificate1097,MergedCutCells.Batch091.certificate1098,MergedCutCells.Batch091.certificate1099,MergedCutCells.Batch091.certificate1100,MergedCutCells.Batch091.certificate1101,MergedCutCells.Batch091.certificate1102,MergedCutCells.Batch091.certificate1103], c.population=PopulationCertificates.Batch009.certificate188
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem covers282 {x : ℝ} (hx : certificate282.interval.Contains x) : ∃ c∈certificate282.cells, c.region.interval.Contains x := rat_cut_group_covers certificate282 numericValid282 hx

def certificate283 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate188,PopulationCertificates.Batch009.certificate188,[MergedCutCells.Batch092.certificate1104],64,none,(1/2),(57115466084015839/50000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid283 : certificate283.NumericValid := by decide +kernel
theorem cellsSound283 : ∀ c∈certificate283.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1104], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1104,List.forall_mem_nil _⟩
theorem cellsNumeric283 : ∀ c∈certificate283.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1104], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1104,List.forall_mem_nil _⟩
theorem cellsEntropyValid283 : ∀ c∈certificate283.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1104], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches283 : ∀ c∈certificate283.cells, c.population=certificate283.population := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1104], c.population=PopulationCertificates.Batch009.certificate188
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers283 {x : ℝ} (hx : certificate283.interval.Contains x) : ∃ c∈certificate283.cells, c.region.interval.Contains x := rat_cut_group_covers certificate283 numericValid283 hx

def certificate284 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate189,PopulationCertificates.Batch009.certificate189,[MergedCutCells.Batch092.certificate1105,MergedCutCells.Batch092.certificate1106,MergedCutCells.Batch092.certificate1107],(1823396241416605989/500000000000000000),none,(1/2),(710600906126415799/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid284 : certificate284.NumericValid := by decide +kernel
theorem cellsSound284 : ∀ c∈certificate284.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1105,MergedCutCells.Batch092.certificate1106,MergedCutCells.Batch092.certificate1107], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1105,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1107,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric284 : ∀ c∈certificate284.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1105,MergedCutCells.Batch092.certificate1106,MergedCutCells.Batch092.certificate1107], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1105,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1106,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1107,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid284 : ∀ c∈certificate284.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1105,MergedCutCells.Batch092.certificate1106,MergedCutCells.Batch092.certificate1107], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches284 : ∀ c∈certificate284.cells, c.population=certificate284.population := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1105,MergedCutCells.Batch092.certificate1106,MergedCutCells.Batch092.certificate1107], c.population=PopulationCertificates.Batch009.certificate189
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers284 {x : ℝ} (hx : certificate284.interval.Contains x) : ∃ c∈certificate284.cells, c.region.interval.Contains x := rat_cut_group_covers certificate284 numericValid284 hx

def certificate285 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate190,PopulationCertificates.Batch009.certificate190,[MergedCutCells.Batch092.certificate1108,MergedCutCells.Batch092.certificate1109,MergedCutCells.Batch092.certificate1110,MergedCutCells.Batch092.certificate1111,MergedCutCells.Batch092.certificate1112,MergedCutCells.Batch092.certificate1113,MergedCutCells.Batch092.certificate1114,MergedCutCells.Batch092.certificate1115],(850165604274620639/1000000000000000000),(some 64),(1/2),(242878138415670607/500000000000000000),(some (69314718055994531/100000000000000000)),(some (1436452467997062969/1000000000000000000))⟩
theorem numericValid285 : certificate285.NumericValid := by decide +kernel
theorem cellsSound285 : ∀ c∈certificate285.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1108,MergedCutCells.Batch092.certificate1109,MergedCutCells.Batch092.certificate1110,MergedCutCells.Batch092.certificate1111,MergedCutCells.Batch092.certificate1112,MergedCutCells.Batch092.certificate1113,MergedCutCells.Batch092.certificate1114,MergedCutCells.Batch092.certificate1115], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1109,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1110,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1111,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1114,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.sound1115,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsNumeric285 : ∀ c∈certificate285.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1108,MergedCutCells.Batch092.certificate1109,MergedCutCells.Batch092.certificate1110,MergedCutCells.Batch092.certificate1111,MergedCutCells.Batch092.certificate1112,MergedCutCells.Batch092.certificate1113,MergedCutCells.Batch092.certificate1114,MergedCutCells.Batch092.certificate1115], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1108,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1109,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1110,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1111,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1112,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1113,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1114,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch092.numericValid1115,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem cellsEntropyValid285 : ∀ c∈certificate285.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1108,MergedCutCells.Batch092.certificate1109,MergedCutCells.Batch092.certificate1110,MergedCutCells.Batch092.certificate1111,MergedCutCells.Batch092.certificate1112,MergedCutCells.Batch092.certificate1113,MergedCutCells.Batch092.certificate1114,MergedCutCells.Batch092.certificate1115], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid96,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid96,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid96,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid96,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid96,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid96,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid96,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy004.valid96,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem populationMatches285 : ∀ c∈certificate285.cells, c.population=certificate285.population := by
  change ∀ c∈[MergedCutCells.Batch092.certificate1108,MergedCutCells.Batch092.certificate1109,MergedCutCells.Batch092.certificate1110,MergedCutCells.Batch092.certificate1111,MergedCutCells.Batch092.certificate1112,MergedCutCells.Batch092.certificate1113,MergedCutCells.Batch092.certificate1114,MergedCutCells.Batch092.certificate1115], c.population=PopulationCertificates.Batch009.certificate190
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem covers285 {x : ℝ} (hx : certificate285.interval.Contains x) : ∃ c∈certificate285.cells, c.region.interval.Contains x := rat_cut_group_covers certificate285 numericValid285 hx

def certificate286 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate190,PopulationCertificates.Batch009.certificate190,[MergedCutCells.Batch093.certificate1116],64,none,(1/2),(115642507753051841/100000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid286 : certificate286.NumericValid := by decide +kernel
theorem cellsSound286 : ∀ c∈certificate286.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1116], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1116,List.forall_mem_nil _⟩
theorem cellsNumeric286 : ∀ c∈certificate286.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1116], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1116,List.forall_mem_nil _⟩
theorem cellsEntropyValid286 : ∀ c∈certificate286.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1116], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩
theorem populationMatches286 : ∀ c∈certificate286.cells, c.population=certificate286.population := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1116], c.population=PopulationCertificates.Batch009.certificate190
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩
theorem covers286 {x : ℝ} (hx : certificate286.interval.Contains x) : ∃ c∈certificate286.cells, c.region.interval.Contains x := rat_cut_group_covers certificate286 numericValid286 hx

def certificate287 : RatCutGroup := ⟨GeometryCertificates.Batch009.certificate191,PopulationCertificates.Batch009.certificate191,[MergedCutCells.Batch093.certificate1117,MergedCutCells.Batch093.certificate1118,MergedCutCells.Batch093.certificate1119],(114126274841736759/31250000000000000),none,(1/2),(364020305149299321/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid287 : certificate287.NumericValid := by decide +kernel
theorem cellsSound287 : ∀ c∈certificate287.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1117,MergedCutCells.Batch093.certificate1118,MergedCutCells.Batch093.certificate1119], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1117,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.sound1119,List.forall_mem_nil _⟩⟩⟩
theorem cellsNumeric287 : ∀ c∈certificate287.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1117,MergedCutCells.Batch093.certificate1118,MergedCutCells.Batch093.certificate1119], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1117,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1118,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch093.numericValid1119,List.forall_mem_nil _⟩⟩⟩
theorem cellsEntropyValid287 : ∀ c∈certificate287.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1117,MergedCutCells.Batch093.certificate1118,MergedCutCells.Batch093.certificate1119], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩
theorem populationMatches287 : ∀ c∈certificate287.cells, c.population=certificate287.population := by
  change ∀ c∈[MergedCutCells.Batch093.certificate1117,MergedCutCells.Batch093.certificate1118,MergedCutCells.Batch093.certificate1119], c.population=PopulationCertificates.Batch009.certificate191
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩
theorem covers287 {x : ℝ} (hx : certificate287.interval.Contains x) : ∃ c∈certificate287.cells, c.region.interval.Contains x := rat_cut_group_covers certificate287 numericValid287 hx

end Cycle12.MergedCutGroups.Batch023
