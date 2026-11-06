import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy017
import Cycle12.MergedCutBins.Batch311
import Cycle12.PopulationCertificates.Batch033
import Cycle12.PopulationCertificates.Batch034

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch311

def certificate3732 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3732,none,(1/2),(9615687695137442862049/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate678,CutLabelCertificates.Entropy000.certificate1,(246181843958942019/1000000000000000000)⟩
theorem numericValid3732 : certificate3732.NumericValid := by decide +kernel
theorem sound3732 : certificate3732.Sound := rat_cut_cell_certificate_sound certificate3732 MergedCutBins.Batch311.valid3732 MergedCutBins.Batch311.sound3732 CutLabelCertificates.Entropy000.valid1 numericValid3732

def certificate3733 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3733,(some 64),(1/2),(9615687695137442862049/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate679,CutLabelCertificates.Entropy000.certificate1,(4191982881283105809/1000000000000000000)⟩
theorem numericValid3733 : certificate3733.NumericValid := by decide +kernel
theorem sound3733 : certificate3733.Sound := rat_cut_cell_certificate_sound certificate3733 MergedCutBins.Batch311.valid3733 MergedCutBins.Batch311.sound3733 CutLabelCertificates.Entropy000.valid1 numericValid3733

def certificate3734 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3734,none,(1/2),(9615687695137442862049/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate679,CutLabelCertificates.Entropy000.certificate1,(4191982881283105809/1000000000000000000)⟩
theorem numericValid3734 : certificate3734.NumericValid := by decide +kernel
theorem sound3734 : certificate3734.Sound := rat_cut_cell_certificate_sound certificate3734 MergedCutBins.Batch311.valid3734 MergedCutBins.Batch311.sound3734 CutLabelCertificates.Entropy000.valid1 numericValid3734

def certificate3735 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3735,(some (612664887465086327/1000000000000000000)),(1/2),(1608641976552844326253/200000000000000000)⟩,PopulationCertificates.Batch034.certificate680,CutLabelCertificates.Entropy017.certificate341,(58171467245995049/250000000000000000)⟩
theorem numericValid3735 : certificate3735.NumericValid := by decide +kernel
theorem sound3735 : certificate3735.Sound := rat_cut_cell_certificate_sound certificate3735 MergedCutBins.Batch311.valid3735 MergedCutBins.Batch311.sound3735 CutLabelCertificates.Entropy017.valid341 numericValid3735

def certificate3736 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3736,(some (637634967/500000000)),(1/2),(1608641976552844326253/200000000000000000)⟩,PopulationCertificates.Batch034.certificate680,CutLabelCertificates.Entropy017.certificate341,(58171467245995049/250000000000000000)⟩
theorem numericValid3736 : certificate3736.NumericValid := by decide +kernel
theorem sound3736 : certificate3736.Sound := rat_cut_cell_certificate_sound certificate3736 MergedCutBins.Batch311.valid3736 MergedCutBins.Batch311.sound3736 CutLabelCertificates.Entropy017.valid341 numericValid3736

def certificate3737 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3737,(some (1185495281932855619/500000000000000000)),(1/2),(1608641976552844326253/200000000000000000)⟩,PopulationCertificates.Batch034.certificate680,CutLabelCertificates.Entropy000.certificate1,(115846422143237133/500000000000000000)⟩
theorem numericValid3737 : certificate3737.NumericValid := by decide +kernel
theorem sound3737 : certificate3737.Sound := rat_cut_cell_certificate_sound certificate3737 MergedCutBins.Batch311.valid3737 MergedCutBins.Batch311.sound3737 CutLabelCertificates.Entropy000.valid1 numericValid3737

def certificate3738 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3738,(some 64),(1/2),(1608641976552844326253/200000000000000000)⟩,PopulationCertificates.Batch034.certificate680,CutLabelCertificates.Entropy000.certificate1,(115846422143237133/500000000000000000)⟩
theorem numericValid3738 : certificate3738.NumericValid := by decide +kernel
theorem sound3738 : certificate3738.Sound := rat_cut_cell_certificate_sound certificate3738 MergedCutBins.Batch311.valid3738 MergedCutBins.Batch311.sound3738 CutLabelCertificates.Entropy000.valid1 numericValid3738

def certificate3739 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3739,none,(1/2),(1608641976552844326253/200000000000000000)⟩,PopulationCertificates.Batch034.certificate680,CutLabelCertificates.Entropy000.certificate1,(115846422143237133/500000000000000000)⟩
theorem numericValid3739 : certificate3739.NumericValid := by decide +kernel
theorem sound3739 : certificate3739.Sound := rat_cut_cell_certificate_sound certificate3739 MergedCutBins.Batch311.valid3739 MergedCutBins.Batch311.sound3739 CutLabelCertificates.Entropy000.valid1 numericValid3739

def certificate3740 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3740,(some 64),(1/2),(1608641976552844326253/200000000000000000)⟩,PopulationCertificates.Batch034.certificate681,CutLabelCertificates.Entropy000.certificate1,(4231423392491740957/1000000000000000000)⟩
theorem numericValid3740 : certificate3740.NumericValid := by decide +kernel
theorem sound3740 : certificate3740.Sound := rat_cut_cell_certificate_sound certificate3740 MergedCutBins.Batch311.valid3740 MergedCutBins.Batch311.sound3740 CutLabelCertificates.Entropy000.valid1 numericValid3740

def certificate3741 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3741,none,(1/2),(1608641976552844326253/200000000000000000)⟩,PopulationCertificates.Batch034.certificate681,CutLabelCertificates.Entropy000.certificate1,(4231423392491740957/1000000000000000000)⟩
theorem numericValid3741 : certificate3741.NumericValid := by decide +kernel
theorem sound3741 : certificate3741.Sound := rat_cut_cell_certificate_sound certificate3741 MergedCutBins.Batch311.valid3741 MergedCutBins.Batch311.sound3741 CutLabelCertificates.Entropy000.valid1 numericValid3741

def certificate3742 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3742,(some (72081281836079233/125000000000000000)),(1/2),(7395724679333802015673/1000000000000000000)⟩,PopulationCertificates.Batch034.certificate682,CutLabelCertificates.Entropy017.certificate342,(5703923786603057/25000000000000000)⟩
theorem numericValid3742 : certificate3742.NumericValid := by decide +kernel
theorem sound3742 : certificate3742.Sound := rat_cut_cell_certificate_sound certificate3742 MergedCutBins.Batch311.valid3742 MergedCutBins.Batch311.sound3742 CutLabelCertificates.Entropy017.valid342 numericValid3742

def certificate3743 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch311.certificate3743,(some (1274340723/1000000000)),(1/2),(7395724679333802015673/1000000000000000000)⟩,PopulationCertificates.Batch034.certificate682,CutLabelCertificates.Entropy017.certificate342,(5703923786603057/25000000000000000)⟩
theorem numericValid3743 : certificate3743.NumericValid := by decide +kernel
theorem sound3743 : certificate3743.Sound := rat_cut_cell_certificate_sound certificate3743 MergedCutBins.Batch311.valid3743 MergedCutBins.Batch311.sound3743 CutLabelCertificates.Entropy017.valid342 numericValid3743

def certificates : List RatCutCellCertificate := [certificate3732,certificate3733,certificate3734,certificate3735,certificate3736,certificate3737,certificate3738,certificate3739,certificate3740,certificate3741,certificate3742,certificate3743]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3732,List.forall_mem_cons.mpr ⟨sound3733,List.forall_mem_cons.mpr ⟨sound3734,List.forall_mem_cons.mpr ⟨sound3735,List.forall_mem_cons.mpr ⟨sound3736,List.forall_mem_cons.mpr ⟨sound3737,List.forall_mem_cons.mpr ⟨sound3738,List.forall_mem_cons.mpr ⟨sound3739,List.forall_mem_cons.mpr ⟨sound3740,List.forall_mem_cons.mpr ⟨sound3741,List.forall_mem_cons.mpr ⟨sound3742,List.forall_mem_cons.mpr ⟨sound3743,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch311
