import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy016
import Cycle12.CutLabelCertificates.Entropy017
import Cycle12.MergedCutBins.Batch310
import Cycle12.PopulationCertificates.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch310

def certificate3720 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3720,none,(1/2),(1460960179092951431811/125000000000000000)⟩,PopulationCertificates.Batch033.certificate675,CutLabelCertificates.Entropy000.certificate1,(4122174822523816401/1000000000000000000)⟩
theorem numericValid3720 : certificate3720.NumericValid := by decide +kernel
theorem sound3720 : certificate3720.Sound := rat_cut_cell_certificate_sound certificate3720 MergedCutBins.Batch310.valid3720 MergedCutBins.Batch310.sound3720 CutLabelCertificates.Entropy000.valid1 numericValid3720

def certificate3721 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3721,(some (574592304218321427/1000000000000000000)),(1/2),(10577178583233964451179/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate676,CutLabelCertificates.Entropy016.certificate339,(248992177853145753/1000000000000000000)⟩
theorem numericValid3721 : certificate3721.NumericValid := by decide +kernel
theorem sound3721 : certificate3721.Sound := rat_cut_cell_certificate_sound certificate3721 MergedCutBins.Batch310.valid3721 MergedCutBins.Batch310.sound3721 CutLabelCertificates.Entropy016.valid339 numericValid3721

def certificate3722 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3722,(some (128108629/100000000)),(1/2),(10577178583233964451179/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate676,CutLabelCertificates.Entropy016.certificate339,(248992177853145753/1000000000000000000)⟩
theorem numericValid3722 : certificate3722.NumericValid := by decide +kernel
theorem sound3722 : certificate3722.Sound := rat_cut_cell_certificate_sound certificate3722 MergedCutBins.Batch310.valid3722 MergedCutBins.Batch310.sound3722 CutLabelCertificates.Entropy016.valid339 numericValid3722

def certificate3723 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3723,(some (1469045034877317089/500000000000000000)),(1/2),(10577178583233964451179/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate676,CutLabelCertificates.Entropy000.certificate1,(248685906629875489/1000000000000000000)⟩
theorem numericValid3723 : certificate3723.NumericValid := by decide +kernel
theorem sound3723 : certificate3723.Sound := rat_cut_cell_certificate_sound certificate3723 MergedCutBins.Batch310.valid3723 MergedCutBins.Batch310.sound3723 CutLabelCertificates.Entropy000.valid1 numericValid3723

def certificate3724 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3724,(some 64),(1/2),(10577178583233964451179/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate676,CutLabelCertificates.Entropy000.certificate1,(248685906629875489/1000000000000000000)⟩
theorem numericValid3724 : certificate3724.NumericValid := by decide +kernel
theorem sound3724 : certificate3724.Sound := rat_cut_cell_certificate_sound certificate3724 MergedCutBins.Batch310.valid3724 MergedCutBins.Batch310.sound3724 CutLabelCertificates.Entropy000.valid1 numericValid3724

def certificate3725 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3725,none,(1/2),(10577178583233964451179/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate676,CutLabelCertificates.Entropy000.certificate1,(248685906629875489/1000000000000000000)⟩
theorem numericValid3725 : certificate3725.NumericValid := by decide +kernel
theorem sound3725 : certificate3725.Sound := rat_cut_cell_certificate_sound certificate3725 MergedCutBins.Batch310.valid3725 MergedCutBins.Batch310.sound3725 CutLabelCertificates.Entropy000.valid1 numericValid3725

def certificate3726 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3726,(some 64),(1/2),(10577178583233964451179/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate677,CutLabelCertificates.Entropy000.certificate1,(2075865006267290361/500000000000000000)⟩
theorem numericValid3726 : certificate3726.NumericValid := by decide +kernel
theorem sound3726 : certificate3726.Sound := rat_cut_cell_certificate_sound certificate3726 MergedCutBins.Batch310.valid3726 MergedCutBins.Batch310.sound3726 CutLabelCertificates.Entropy000.valid1 numericValid3726

def certificate3727 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3727,none,(1/2),(10577178583233964451179/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate677,CutLabelCertificates.Entropy000.certificate1,(2075865006267290361/500000000000000000)⟩
theorem numericValid3727 : certificate3727.NumericValid := by decide +kernel
theorem sound3727 : certificate3727.Sound := rat_cut_cell_certificate_sound certificate3727 MergedCutBins.Batch310.valid3727 MergedCutBins.Batch310.sound3727 CutLabelCertificates.Entropy000.valid1 numericValid3727

def certificate3728 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3728,(some (304630007906055871/500000000000000000)),(1/2),(9615687695137442862049/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate678,CutLabelCertificates.Entropy017.certificate340,(123213566226027329/500000000000000000)⟩
theorem numericValid3728 : certificate3728.NumericValid := by decide +kernel
theorem sound3728 : certificate3728.Sound := rat_cut_cell_certificate_sound certificate3728 MergedCutBins.Batch310.valid3728 MergedCutBins.Batch310.sound3728 CutLabelCertificates.Entropy017.valid340 numericValid3728

def certificate3729 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3729,(some (319975293/250000000)),(1/2),(9615687695137442862049/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate678,CutLabelCertificates.Entropy017.certificate340,(123213566226027329/500000000000000000)⟩
theorem numericValid3729 : certificate3729.NumericValid := by decide +kernel
theorem sound3729 : certificate3729.Sound := rat_cut_cell_certificate_sound certificate3729 MergedCutBins.Batch310.valid3729 MergedCutBins.Batch310.sound3729 CutLabelCertificates.Entropy017.valid340 numericValid3729

def certificate3730 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3730,(some (569699199724457869/200000000000000000)),(1/2),(9615687695137442862049/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate678,CutLabelCertificates.Entropy000.certificate1,(246181843958942019/1000000000000000000)⟩
theorem numericValid3730 : certificate3730.NumericValid := by decide +kernel
theorem sound3730 : certificate3730.Sound := rat_cut_cell_certificate_sound certificate3730 MergedCutBins.Batch310.valid3730 MergedCutBins.Batch310.sound3730 CutLabelCertificates.Entropy000.valid1 numericValid3730

def certificate3731 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch310.certificate3731,(some 64),(1/2),(9615687695137442862049/1000000000000000000)⟩,PopulationCertificates.Batch033.certificate678,CutLabelCertificates.Entropy000.certificate1,(246181843958942019/1000000000000000000)⟩
theorem numericValid3731 : certificate3731.NumericValid := by decide +kernel
theorem sound3731 : certificate3731.Sound := rat_cut_cell_certificate_sound certificate3731 MergedCutBins.Batch310.valid3731 MergedCutBins.Batch310.sound3731 CutLabelCertificates.Entropy000.valid1 numericValid3731

def certificates : List RatCutCellCertificate := [certificate3720,certificate3721,certificate3722,certificate3723,certificate3724,certificate3725,certificate3726,certificate3727,certificate3728,certificate3729,certificate3730,certificate3731]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3720,List.forall_mem_cons.mpr ⟨sound3721,List.forall_mem_cons.mpr ⟨sound3722,List.forall_mem_cons.mpr ⟨sound3723,List.forall_mem_cons.mpr ⟨sound3724,List.forall_mem_cons.mpr ⟨sound3725,List.forall_mem_cons.mpr ⟨sound3726,List.forall_mem_cons.mpr ⟨sound3727,List.forall_mem_cons.mpr ⟨sound3728,List.forall_mem_cons.mpr ⟨sound3729,List.forall_mem_cons.mpr ⟨sound3730,List.forall_mem_cons.mpr ⟨sound3731,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch310
