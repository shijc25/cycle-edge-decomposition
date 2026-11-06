import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy001
import Cycle12.MergedCutBins.Batch025
import Cycle12.PopulationCertificates.Batch003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch025

def certificate300 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate300,(some (185106521791005281/250000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy001.certificate32,(91342835979586571/500000000000000000)⟩
theorem numericValid300 : certificate300.NumericValid := by decide +kernel
theorem sound300 : certificate300.Sound := rat_cut_cell_certificate_sound certificate300 MergedCutBins.Batch025.valid300 MergedCutBins.Batch025.sound300 CutLabelCertificates.Entropy001.valid32 numericValid300

def certificate301 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate301,(some (434103908976472093/500000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy001.certificate32,(91342835979586571/500000000000000000)⟩
theorem numericValid301 : certificate301.NumericValid := by decide +kernel
theorem sound301 : certificate301.Sound := rat_cut_cell_certificate_sound certificate301 MergedCutBins.Batch025.valid301 MergedCutBins.Batch025.sound301 CutLabelCertificates.Entropy001.valid32 numericValid301

def certificate302 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate302,(some (504399447/500000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy001.certificate32,(91342835979586571/500000000000000000)⟩
theorem numericValid302 : certificate302.NumericValid := by decide +kernel
theorem sound302 : certificate302.Sound := rat_cut_cell_certificate_sound certificate302 MergedCutBins.Batch025.valid302 MergedCutBins.Batch025.sound302 CutLabelCertificates.Entropy001.valid32 numericValid302

def certificate303 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate303,(some (1102393548581141981/1000000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy000.certificate1,(73183042517758373/500000000000000000)⟩
theorem numericValid303 : certificate303.NumericValid := by decide +kernel
theorem sound303 : certificate303.Sound := rat_cut_cell_certificate_sound certificate303 MergedCutBins.Batch025.valid303 MergedCutBins.Batch025.sound303 CutLabelCertificates.Entropy000.valid1 numericValid303

def certificate304 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate304,(some (244369255447659363/100000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy000.certificate1,(73183042517758373/500000000000000000)⟩
theorem numericValid304 : certificate304.NumericValid := by decide +kernel
theorem sound304 : certificate304.Sound := rat_cut_cell_certificate_sound certificate304 MergedCutBins.Batch025.valid304 MergedCutBins.Batch025.sound304 CutLabelCertificates.Entropy000.valid1 numericValid304

def certificate305 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate305,(some (7253414180838573931/500000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy000.certificate1,(73183042517758373/500000000000000000)⟩
theorem numericValid305 : certificate305.NumericValid := by decide +kernel
theorem sound305 : certificate305.Sound := rat_cut_cell_certificate_sound certificate305 MergedCutBins.Batch025.valid305 MergedCutBins.Batch025.sound305 CutLabelCertificates.Entropy000.valid1 numericValid305

def certificate306 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate306,(some (4819395094643600011/200000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy000.certificate1,(73183042517758373/500000000000000000)⟩
theorem numericValid306 : certificate306.NumericValid := by decide +kernel
theorem sound306 : certificate306.Sound := rat_cut_cell_certificate_sound certificate306 MergedCutBins.Batch025.valid306 MergedCutBins.Batch025.sound306 CutLabelCertificates.Entropy000.valid1 numericValid306

def certificate307 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate307,(some (24581324680229681857/1000000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy000.certificate1,(73183042517758373/500000000000000000)⟩
theorem numericValid307 : certificate307.NumericValid := by decide +kernel
theorem sound307 : certificate307.Sound := rat_cut_cell_certificate_sound certificate307 MergedCutBins.Batch025.valid307 MergedCutBins.Batch025.sound307 CutLabelCertificates.Entropy000.valid1 numericValid307

def certificate308 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate308,none,(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate62,CutLabelCertificates.Entropy000.certificate1,(73183042517758373/500000000000000000)⟩
theorem numericValid308 : certificate308.NumericValid := by decide +kernel
theorem sound308 : certificate308.Sound := rat_cut_cell_certificate_sound certificate308 MergedCutBins.Batch025.valid308 MergedCutBins.Batch025.sound308 CutLabelCertificates.Entropy000.valid1 numericValid308

def certificate309 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate309,(some (20988148567539389077/1000000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate63,CutLabelCertificates.Entropy000.certificate1,(82443717406585167/200000000000000000)⟩
theorem numericValid309 : certificate309.NumericValid := by decide +kernel
theorem sound309 : certificate309.Sound := rat_cut_cell_certificate_sound certificate309 MergedCutBins.Batch025.valid309 MergedCutBins.Batch025.sound309 CutLabelCertificates.Entropy000.valid1 numericValid309

def certificate310 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate310,(some (492205096135652021/20000000000000000)),(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate63,CutLabelCertificates.Entropy000.certificate1,(82443717406585167/200000000000000000)⟩
theorem numericValid310 : certificate310.NumericValid := by decide +kernel
theorem sound310 : certificate310.Sound := rat_cut_cell_certificate_sound certificate310 MergedCutBins.Batch025.valid310 MergedCutBins.Batch025.sound310 CutLabelCertificates.Entropy000.valid1 numericValid310

def certificate311 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch025.certificate311,none,(1/2),(49649338197438694597/1000000000000000000)⟩,PopulationCertificates.Batch003.certificate63,CutLabelCertificates.Entropy000.certificate1,(82443717406585167/200000000000000000)⟩
theorem numericValid311 : certificate311.NumericValid := by decide +kernel
theorem sound311 : certificate311.Sound := rat_cut_cell_certificate_sound certificate311 MergedCutBins.Batch025.valid311 MergedCutBins.Batch025.sound311 CutLabelCertificates.Entropy000.valid1 numericValid311

def certificates : List RatCutCellCertificate := [certificate300,certificate301,certificate302,certificate303,certificate304,certificate305,certificate306,certificate307,certificate308,certificate309,certificate310,certificate311]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound300,List.forall_mem_cons.mpr ⟨sound301,List.forall_mem_cons.mpr ⟨sound302,List.forall_mem_cons.mpr ⟨sound303,List.forall_mem_cons.mpr ⟨sound304,List.forall_mem_cons.mpr ⟨sound305,List.forall_mem_cons.mpr ⟨sound306,List.forall_mem_cons.mpr ⟨sound307,List.forall_mem_cons.mpr ⟨sound308,List.forall_mem_cons.mpr ⟨sound309,List.forall_mem_cons.mpr ⟨sound310,List.forall_mem_cons.mpr ⟨sound311,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch025
