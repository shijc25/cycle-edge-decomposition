import Cycle12.RationalCutGroup
import Cycle12.GeometryCertificates.Batch040
import Cycle12.MergedCutCells.Batch348
import Cycle12.MergedCutCells.Batch349
import Cycle12.MergedCutCells.Batch350
import Cycle12.MergedCutCells.Batch351
import Cycle12.PopulationCertificates.Batch040

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutGroups.Batch100

def certificate1200 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate800,PopulationCertificates.Batch040.certificate800,[MergedCutCells.Batch348.certificate4185,MergedCutCells.Batch348.certificate4186],(376521057256508759/500000000000000000),(some (558840663/500000000)),(1/2),(274581119548321441/250000000000000000),(some (69316647004864347/500000000000000000)),(some (15562791199386269/500000000000000000))⟩
theorem numericValid1200 : certificate1200.NumericValid := by decide +kernel
theorem cellsSound1200 : ∀ c∈certificate1200.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4185,MergedCutCells.Batch348.certificate4186], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4185,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4186,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1200 : ∀ c∈certificate1200.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4185,MergedCutCells.Batch348.certificate4186], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4185,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4186,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1200 : ∀ c∈certificate1200.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4185,MergedCutCells.Batch348.certificate4186], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid401,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid401,List.forall_mem_nil _⟩⟩
theorem populationMatches1200 : ∀ c∈certificate1200.cells, c.population=certificate1200.population := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4185,MergedCutCells.Batch348.certificate4186], c.population=PopulationCertificates.Batch040.certificate800
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1200 {x : ℝ} (hx : certificate1200.interval.Contains x) : ∃ c∈certificate1200.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1200 numericValid1200 hx

def certificate1201 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate800,PopulationCertificates.Batch040.certificate800,[MergedCutCells.Batch348.certificate4187,MergedCutCells.Batch349.certificate4188,MergedCutCells.Batch349.certificate4189,MergedCutCells.Batch349.certificate4190],(558840663/500000000),none,(1/2),(543024340053038461/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1201 : certificate1201.NumericValid := by decide +kernel
theorem cellsSound1201 : ∀ c∈certificate1201.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4187,MergedCutCells.Batch349.certificate4188,MergedCutCells.Batch349.certificate4189,MergedCutCells.Batch349.certificate4190], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.sound4187,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4189,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4190,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1201 : ∀ c∈certificate1201.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4187,MergedCutCells.Batch349.certificate4188,MergedCutCells.Batch349.certificate4189,MergedCutCells.Batch349.certificate4190], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch348.numericValid4187,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4188,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4189,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4190,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1201 : ∀ c∈certificate1201.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4187,MergedCutCells.Batch349.certificate4188,MergedCutCells.Batch349.certificate4189,MergedCutCells.Batch349.certificate4190], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1201 : ∀ c∈certificate1201.cells, c.population=certificate1201.population := by
  change ∀ c∈[MergedCutCells.Batch348.certificate4187,MergedCutCells.Batch349.certificate4188,MergedCutCells.Batch349.certificate4189,MergedCutCells.Batch349.certificate4190], c.population=PopulationCertificates.Batch040.certificate800
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1201 {x : ℝ} (hx : certificate1201.interval.Contains x) : ∃ c∈certificate1201.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1201 numericValid1201 hx

def certificate1202 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate801,PopulationCertificates.Batch040.certificate801,[MergedCutCells.Batch349.certificate4191,MergedCutCells.Batch349.certificate4192],(12235101886610639769/500000000000000000),none,(1/2),(10567318817565724559/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1202 : certificate1202.NumericValid := by decide +kernel
theorem cellsSound1202 : ∀ c∈certificate1202.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4191,MergedCutCells.Batch349.certificate4192], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4192,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1202 : ∀ c∈certificate1202.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4191,MergedCutCells.Batch349.certificate4192], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4191,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4192,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1202 : ∀ c∈certificate1202.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4191,MergedCutCells.Batch349.certificate4192], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1202 : ∀ c∈certificate1202.cells, c.population=certificate1202.population := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4191,MergedCutCells.Batch349.certificate4192], c.population=PopulationCertificates.Batch040.certificate801
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1202 {x : ℝ} (hx : certificate1202.interval.Contains x) : ∃ c∈certificate1202.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1202 numericValid1202 hx

def certificate1203 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate802,PopulationCertificates.Batch040.certificate802,[MergedCutCells.Batch349.certificate4193,MergedCutCells.Batch349.certificate4194],(189810403037833391/250000000000000000),(some (274665013/250000000)),(1/2),(1159625226306058749/1000000000000000000),(some (17475478169730961/125000000000000000)),(some (15733299768234913/500000000000000000))⟩
theorem numericValid1203 : certificate1203.NumericValid := by decide +kernel
theorem cellsSound1203 : ∀ c∈certificate1203.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4193,MergedCutCells.Batch349.certificate4194], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4194,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1203 : ∀ c∈certificate1203.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4193,MergedCutCells.Batch349.certificate4194], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4193,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4194,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1203 : ∀ c∈certificate1203.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4193,MergedCutCells.Batch349.certificate4194], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid402,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid402,List.forall_mem_nil _⟩⟩
theorem populationMatches1203 : ∀ c∈certificate1203.cells, c.population=certificate1203.population := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4193,MergedCutCells.Batch349.certificate4194], c.population=PopulationCertificates.Batch040.certificate802
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1203 {x : ℝ} (hx : certificate1203.interval.Contains x) : ∃ c∈certificate1203.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1203 numericValid1203 hx

def certificate1204 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate802,PopulationCertificates.Batch040.certificate802,[MergedCutCells.Batch349.certificate4195,MergedCutCells.Batch349.certificate4196,MergedCutCells.Batch349.certificate4197,MergedCutCells.Batch349.certificate4198],(274665013/250000000),none,(1/2),(286949688457331203/250000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1204 : certificate1204.NumericValid := by decide +kernel
theorem cellsSound1204 : ∀ c∈certificate1204.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4195,MergedCutCells.Batch349.certificate4196,MergedCutCells.Batch349.certificate4197,MergedCutCells.Batch349.certificate4198], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4196,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4198,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1204 : ∀ c∈certificate1204.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4195,MergedCutCells.Batch349.certificate4196,MergedCutCells.Batch349.certificate4197,MergedCutCells.Batch349.certificate4198], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4195,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4196,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4197,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4198,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1204 : ∀ c∈certificate1204.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4195,MergedCutCells.Batch349.certificate4196,MergedCutCells.Batch349.certificate4197,MergedCutCells.Batch349.certificate4198], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1204 : ∀ c∈certificate1204.cells, c.population=certificate1204.population := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4195,MergedCutCells.Batch349.certificate4196,MergedCutCells.Batch349.certificate4197,MergedCutCells.Batch349.certificate4198], c.population=PopulationCertificates.Batch040.certificate802
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1204 {x : ℝ} (hx : certificate1204.interval.Contains x) : ∃ c∈certificate1204.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1204 numericValid1204 hx

def certificate1205 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate803,PopulationCertificates.Batch040.certificate803,[MergedCutCells.Batch349.certificate4199,MergedCutCells.Batch350.certificate4200],(24382391481740573173/1000000000000000000),none,(1/2),(10679967677515771327/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1205 : certificate1205.NumericValid := by decide +kernel
theorem cellsSound1205 : ∀ c∈certificate1205.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4199,MergedCutCells.Batch350.certificate4200], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.sound4199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4200,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1205 : ∀ c∈certificate1205.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4199,MergedCutCells.Batch350.certificate4200], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch349.numericValid4199,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4200,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1205 : ∀ c∈certificate1205.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4199,MergedCutCells.Batch350.certificate4200], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1205 : ∀ c∈certificate1205.cells, c.population=certificate1205.population := by
  change ∀ c∈[MergedCutCells.Batch349.certificate4199,MergedCutCells.Batch350.certificate4200], c.population=PopulationCertificates.Batch040.certificate803
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1205 {x : ℝ} (hx : certificate1205.interval.Contains x) : ∃ c∈certificate1205.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1205 numericValid1205 hx

def certificate1206 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate804,PopulationCertificates.Batch040.certificate804,[MergedCutCells.Batch350.certificate4201,MergedCutCells.Batch350.certificate4202],(9575579054213887/12500000000000000),(some (1107682883/1000000000)),(1/2),(305936374597833691/250000000000000000),(some (35463898141040483/250000000000000000)),(some (16033523349843003/500000000000000000))⟩
theorem numericValid1206 : certificate1206.NumericValid := by decide +kernel
theorem cellsSound1206 : ∀ c∈certificate1206.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4201,MergedCutCells.Batch350.certificate4202], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4202,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1206 : ∀ c∈certificate1206.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4201,MergedCutCells.Batch350.certificate4202], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4201,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4202,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1206 : ∀ c∈certificate1206.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4201,MergedCutCells.Batch350.certificate4202], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid403,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid403,List.forall_mem_nil _⟩⟩
theorem populationMatches1206 : ∀ c∈certificate1206.cells, c.population=certificate1206.population := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4201,MergedCutCells.Batch350.certificate4202], c.population=PopulationCertificates.Batch040.certificate804
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1206 {x : ℝ} (hx : certificate1206.interval.Contains x) : ∃ c∈certificate1206.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1206 numericValid1206 hx

def certificate1207 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate804,PopulationCertificates.Batch040.certificate804,[MergedCutCells.Batch350.certificate4203,MergedCutCells.Batch350.certificate4204,MergedCutCells.Batch350.certificate4205,MergedCutCells.Batch350.certificate4206],(1107682883/1000000000),none,(1/2),(1210886517218607731/1000000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1207 : certificate1207.NumericValid := by decide +kernel
theorem cellsSound1207 : ∀ c∈certificate1207.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4203,MergedCutCells.Batch350.certificate4204,MergedCutCells.Batch350.certificate4205,MergedCutCells.Batch350.certificate4206], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4203,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4205,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4206,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1207 : ∀ c∈certificate1207.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4203,MergedCutCells.Batch350.certificate4204,MergedCutCells.Batch350.certificate4205,MergedCutCells.Batch350.certificate4206], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4203,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4204,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4205,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4206,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1207 : ∀ c∈certificate1207.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4203,MergedCutCells.Batch350.certificate4204,MergedCutCells.Batch350.certificate4205,MergedCutCells.Batch350.certificate4206], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1207 : ∀ c∈certificate1207.cells, c.population=certificate1207.population := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4203,MergedCutCells.Batch350.certificate4204,MergedCutCells.Batch350.certificate4205,MergedCutCells.Batch350.certificate4206], c.population=PopulationCertificates.Batch040.certificate804
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1207 {x : ℝ} (hx : certificate1207.interval.Contains x) : ∃ c∈certificate1207.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1207 numericValid1207 hx

def certificate1208 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate805,PopulationCertificates.Batch040.certificate805,[MergedCutCells.Batch350.certificate4207,MergedCutCells.Batch350.certificate4208],(24176869402093797779/1000000000000000000),none,(1/2),(86264723555063367/8000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1208 : certificate1208.NumericValid := by decide +kernel
theorem cellsSound1208 : ∀ c∈certificate1208.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4207,MergedCutCells.Batch350.certificate4208], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4208,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1208 : ∀ c∈certificate1208.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4207,MergedCutCells.Batch350.certificate4208], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4207,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4208,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1208 : ∀ c∈certificate1208.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4207,MergedCutCells.Batch350.certificate4208], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1208 : ∀ c∈certificate1208.cells, c.population=certificate1208.population := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4207,MergedCutCells.Batch350.certificate4208], c.population=PopulationCertificates.Batch040.certificate805
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1208 {x : ℝ} (hx : certificate1208.interval.Contains x) : ∃ c∈certificate1208.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1208 numericValid1208 hx

def certificate1209 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate806,PopulationCertificates.Batch040.certificate806,[MergedCutCells.Batch350.certificate4209,MergedCutCells.Batch350.certificate4210],(386260172534300773/500000000000000000),(some (1118558783/1000000000)),(1/2),(1287766647315599463/1000000000000000000),(some (17997258947422233/125000000000000000)),(some (32691795390576027/1000000000000000000))⟩
theorem numericValid1209 : certificate1209.NumericValid := by decide +kernel
theorem cellsSound1209 : ∀ c∈certificate1209.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4209,MergedCutCells.Batch350.certificate4210], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4209,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4210,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1209 : ∀ c∈certificate1209.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4209,MergedCutCells.Batch350.certificate4210], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4209,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4210,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1209 : ∀ c∈certificate1209.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4209,MergedCutCells.Batch350.certificate4210], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid404,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy020.valid404,List.forall_mem_nil _⟩⟩
theorem populationMatches1209 : ∀ c∈certificate1209.cells, c.population=certificate1209.population := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4209,MergedCutCells.Batch350.certificate4210], c.population=PopulationCertificates.Batch040.certificate806
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1209 {x : ℝ} (hx : certificate1209.interval.Contains x) : ∃ c∈certificate1209.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1209 numericValid1209 hx

def certificate1210 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate806,PopulationCertificates.Batch040.certificate806,[MergedCutCells.Batch350.certificate4211,MergedCutCells.Batch351.certificate4212,MergedCutCells.Batch351.certificate4213,MergedCutCells.Batch351.certificate4214],(1118558783/1000000000),none,(1/2),(159444820437457211/125000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1210 : certificate1210.NumericValid := by decide +kernel
theorem cellsSound1210 : ∀ c∈certificate1210.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4211,MergedCutCells.Batch351.certificate4212,MergedCutCells.Batch351.certificate4213,MergedCutCells.Batch351.certificate4214], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.sound4211,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4212,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4214,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsNumeric1210 : ∀ c∈certificate1210.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4211,MergedCutCells.Batch351.certificate4212,MergedCutCells.Batch351.certificate4213,MergedCutCells.Batch351.certificate4214], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch350.numericValid4211,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4212,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4213,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4214,List.forall_mem_nil _⟩⟩⟩⟩
theorem cellsEntropyValid1210 : ∀ c∈certificate1210.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4211,MergedCutCells.Batch351.certificate4212,MergedCutCells.Batch351.certificate4213,MergedCutCells.Batch351.certificate4214], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩⟩⟩
theorem populationMatches1210 : ∀ c∈certificate1210.cells, c.population=certificate1210.population := by
  change ∀ c∈[MergedCutCells.Batch350.certificate4211,MergedCutCells.Batch351.certificate4212,MergedCutCells.Batch351.certificate4213,MergedCutCells.Batch351.certificate4214], c.population=PopulationCertificates.Batch040.certificate806
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩⟩⟩
theorem covers1210 {x : ℝ} (hx : certificate1210.interval.Contains x) : ∃ c∈certificate1210.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1210 numericValid1210 hx

def certificate1211 : RatCutGroup := ⟨GeometryCertificates.Batch040.certificate807,PopulationCertificates.Batch040.certificate807,[MergedCutCells.Batch351.certificate4215,MergedCutCells.Batch351.certificate4216],(4818381862134559887/200000000000000000),none,(1/2),(5449642436972574613/500000000000000000),(some (69314718055994531/100000000000000000)),(some 1)⟩
theorem numericValid1211 : certificate1211.NumericValid := by decide +kernel
theorem cellsSound1211 : ∀ c∈certificate1211.cells, c.Sound := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4215,MergedCutCells.Batch351.certificate4216], c.Sound
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.sound4216,List.forall_mem_nil _⟩⟩
theorem cellsNumeric1211 : ∀ c∈certificate1211.cells, c.NumericValid := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4215,MergedCutCells.Batch351.certificate4216], c.NumericValid
  exact List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4215,List.forall_mem_cons.mpr ⟨MergedCutCells.Batch351.numericValid4216,List.forall_mem_nil _⟩⟩
theorem cellsEntropyValid1211 : ∀ c∈certificate1211.cells, c.entropy.Valid := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4215,MergedCutCells.Batch351.certificate4216], c.entropy.Valid
  exact List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_cons.mpr ⟨CutLabelCertificates.Entropy000.valid1,List.forall_mem_nil _⟩⟩
theorem populationMatches1211 : ∀ c∈certificate1211.cells, c.population=certificate1211.population := by
  change ∀ c∈[MergedCutCells.Batch351.certificate4215,MergedCutCells.Batch351.certificate4216], c.population=PopulationCertificates.Batch040.certificate807
  exact List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_cons.mpr ⟨rfl,List.forall_mem_nil _⟩⟩
theorem covers1211 {x : ℝ} (hx : certificate1211.interval.Contains x) : ∃ c∈certificate1211.cells, c.region.interval.Contains x := rat_cut_group_covers certificate1211 numericValid1211 hx

end Cycle12.MergedCutGroups.Batch100
