import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy024
import Cycle12.CutLabelCertificates.Entropy025
import Cycle12.MergedCutBins.Batch375
import Cycle12.PopulationCertificates.Batch044

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch375

def certificate4500 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4500,(some 64),(1/2),(11416785527815779703113/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate885,CutLabelCertificates.Entropy000.certificate1,(5204302744302063903/1000000000000000000)⟩
theorem numericValid4500 : certificate4500.NumericValid := by decide +kernel
theorem sound4500 : certificate4500.Sound := rat_cut_cell_certificate_sound certificate4500 MergedCutBins.Batch375.valid4500 MergedCutBins.Batch375.sound4500 CutLabelCertificates.Entropy000.valid1 numericValid4500

def certificate4501 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4501,none,(1/2),(11416785527815779703113/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate885,CutLabelCertificates.Entropy000.certificate1,(5204302744302063903/1000000000000000000)⟩
theorem numericValid4501 : certificate4501.NumericValid := by decide +kernel
theorem sound4501 : certificate4501.Sound := rat_cut_cell_certificate_sound certificate4501 MergedCutBins.Batch375.valid4501 MergedCutBins.Batch375.sound4501 CutLabelCertificates.Entropy000.valid1 numericValid4501

def certificate4502 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4502,(some (677110354556920307/1000000000000000000)),(1/40),(11416785527815779703113/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate886,CutLabelCertificates.Entropy024.certificate498,(3688867566187919/62500000000000000)⟩
theorem numericValid4502 : certificate4502.NumericValid := by decide +kernel
theorem sound4502 : certificate4502.Sound := rat_cut_cell_certificate_sound certificate4502 MergedCutBins.Batch375.valid4502 MergedCutBins.Batch375.sound4502 CutLabelCertificates.Entropy024.valid498 numericValid4502

def certificate4503 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4503,(some (279994652487928167/200000000000000000)),(1/40),(11416785527815779703113/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate886,CutLabelCertificates.Entropy024.certificate499,(3688867566187919/62500000000000000)⟩
theorem numericValid4503 : certificate4503.NumericValid := by decide +kernel
theorem sound4503 : certificate4503.Sound := rat_cut_cell_certificate_sound certificate4503 MergedCutBins.Batch375.valid4503 MergedCutBins.Batch375.sound4503 CutLabelCertificates.Entropy024.valid499 numericValid4503

def certificate4504 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4504,(some 64),(1/40),(11416785527815779703113/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate886,CutLabelCertificates.Entropy025.certificate500,(3688867566187919/62500000000000000)⟩
theorem numericValid4504 : certificate4504.NumericValid := by decide +kernel
theorem sound4504 : certificate4504.Sound := rat_cut_cell_certificate_sound certificate4504 MergedCutBins.Batch375.valid4504 MergedCutBins.Batch375.sound4504 CutLabelCertificates.Entropy025.valid500 numericValid4504

def certificate4505 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4505,none,(1/40),(11416785527815779703113/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate886,CutLabelCertificates.Entropy025.certificate501,(3688867566187919/62500000000000000)⟩
theorem numericValid4505 : certificate4505.NumericValid := by decide +kernel
theorem sound4505 : certificate4505.Sound := rat_cut_cell_certificate_sound certificate4505 MergedCutBins.Batch375.valid4505 MergedCutBins.Batch375.sound4505 CutLabelCertificates.Entropy025.valid501 numericValid4505

def certificate4506 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4506,(some (133817455664891127/200000000000000000)),(1/2),(10395149607104828422059/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate887,CutLabelCertificates.Entropy025.certificate502,(626617223272028841/1000000000000000000)⟩
theorem numericValid4506 : certificate4506.NumericValid := by decide +kernel
theorem sound4506 : certificate4506.Sound := rat_cut_cell_certificate_sound certificate4506 MergedCutBins.Batch375.valid4506 MergedCutBins.Batch375.sound4506 CutLabelCertificates.Entropy025.valid502 numericValid4506

def certificate4507 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4507,(some (1254335283/1000000000)),(1/2),(10395149607104828422059/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate887,CutLabelCertificates.Entropy025.certificate502,(626617223272028841/1000000000000000000)⟩
theorem numericValid4507 : certificate4507.NumericValid := by decide +kernel
theorem sound4507 : certificate4507.Sound := rat_cut_cell_certificate_sound certificate4507 MergedCutBins.Batch375.valid4507 MergedCutBins.Batch375.sound4507 CutLabelCertificates.Entropy025.valid502 numericValid4507

def certificate4508 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4508,(some (340178207876436359/125000000000000000)),(1/2),(10395149607104828422059/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate887,CutLabelCertificates.Entropy000.certificate1,(78303921453585939/125000000000000000)⟩
theorem numericValid4508 : certificate4508.NumericValid := by decide +kernel
theorem sound4508 : certificate4508.Sound := rat_cut_cell_certificate_sound certificate4508 MergedCutBins.Batch375.valid4508 MergedCutBins.Batch375.sound4508 CutLabelCertificates.Entropy000.valid1 numericValid4508

def certificate4509 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4509,(some 64),(1/2),(10395149607104828422059/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate887,CutLabelCertificates.Entropy000.certificate1,(78303921453585939/125000000000000000)⟩
theorem numericValid4509 : certificate4509.NumericValid := by decide +kernel
theorem sound4509 : certificate4509.Sound := rat_cut_cell_certificate_sound certificate4509 MergedCutBins.Batch375.valid4509 MergedCutBins.Batch375.sound4509 CutLabelCertificates.Entropy000.valid1 numericValid4509

def certificate4510 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4510,none,(1/2),(10395149607104828422059/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate887,CutLabelCertificates.Entropy000.certificate1,(78303921453585939/125000000000000000)⟩
theorem numericValid4510 : certificate4510.NumericValid := by decide +kernel
theorem sound4510 : certificate4510.Sound := rat_cut_cell_certificate_sound certificate4510 MergedCutBins.Batch375.valid4510 MergedCutBins.Batch375.sound4510 CutLabelCertificates.Entropy000.valid1 numericValid4510

def certificate4511 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch375.certificate4511,(some 64),(1/2),(10395149607104828422059/1000000000000000000)⟩,PopulationCertificates.Batch044.certificate888,CutLabelCertificates.Entropy000.certificate1,(1326307174468684249/250000000000000000)⟩
theorem numericValid4511 : certificate4511.NumericValid := by decide +kernel
theorem sound4511 : certificate4511.Sound := rat_cut_cell_certificate_sound certificate4511 MergedCutBins.Batch375.valid4511 MergedCutBins.Batch375.sound4511 CutLabelCertificates.Entropy000.valid1 numericValid4511

def certificates : List RatCutCellCertificate := [certificate4500,certificate4501,certificate4502,certificate4503,certificate4504,certificate4505,certificate4506,certificate4507,certificate4508,certificate4509,certificate4510,certificate4511]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4500,List.forall_mem_cons.mpr ⟨sound4501,List.forall_mem_cons.mpr ⟨sound4502,List.forall_mem_cons.mpr ⟨sound4503,List.forall_mem_cons.mpr ⟨sound4504,List.forall_mem_cons.mpr ⟨sound4505,List.forall_mem_cons.mpr ⟨sound4506,List.forall_mem_cons.mpr ⟨sound4507,List.forall_mem_cons.mpr ⟨sound4508,List.forall_mem_cons.mpr ⟨sound4509,List.forall_mem_cons.mpr ⟨sound4510,List.forall_mem_cons.mpr ⟨sound4511,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch375
