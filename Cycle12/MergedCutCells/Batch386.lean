import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy027
import Cycle12.CutLabelCertificates.Entropy028
import Cycle12.MergedCutBins.Batch386
import Cycle12.PopulationCertificates.Batch046

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch386

def certificate4632 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4632,(some (1060871578718660359/250000000000000000)),(1/2),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate920,CutLabelCertificates.Entropy000.certificate1,(11381630810841243/62500000000000000)⟩
theorem numericValid4632 : certificate4632.NumericValid := by decide +kernel
theorem sound4632 : certificate4632.Sound := rat_cut_cell_certificate_sound certificate4632 MergedCutBins.Batch386.valid4632 MergedCutBins.Batch386.sound4632 CutLabelCertificates.Entropy000.valid1 numericValid4632

def certificate4633 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4633,(some 64),(1/2),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate920,CutLabelCertificates.Entropy000.certificate1,(11381630810841243/62500000000000000)⟩
theorem numericValid4633 : certificate4633.NumericValid := by decide +kernel
theorem sound4633 : certificate4633.Sound := rat_cut_cell_certificate_sound certificate4633 MergedCutBins.Batch386.valid4633 MergedCutBins.Batch386.sound4633 CutLabelCertificates.Entropy000.valid1 numericValid4633

def certificate4634 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4634,none,(1/2),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate920,CutLabelCertificates.Entropy000.certificate1,(11381630810841243/62500000000000000)⟩
theorem numericValid4634 : certificate4634.NumericValid := by decide +kernel
theorem sound4634 : certificate4634.Sound := rat_cut_cell_certificate_sound certificate4634 MergedCutBins.Batch386.valid4634 MergedCutBins.Batch386.sound4634 CutLabelCertificates.Entropy000.valid1 numericValid4634

def certificate4635 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4635,(some 64),(1/2),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate921,CutLabelCertificates.Entropy000.certificate1,(6603816615917731873/1000000000000000000)⟩
theorem numericValid4635 : certificate4635.NumericValid := by decide +kernel
theorem sound4635 : certificate4635.Sound := rat_cut_cell_certificate_sound certificate4635 MergedCutBins.Batch386.valid4635 MergedCutBins.Batch386.sound4635 CutLabelCertificates.Entropy000.valid1 numericValid4635

def certificate4636 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4636,none,(1/2),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate921,CutLabelCertificates.Entropy000.certificate1,(6603816615917731873/1000000000000000000)⟩
theorem numericValid4636 : certificate4636.NumericValid := by decide +kernel
theorem sound4636 : certificate4636.Sound := rat_cut_cell_certificate_sound certificate4636 MergedCutBins.Batch386.valid4636 MergedCutBins.Batch386.sound4636 CutLabelCertificates.Entropy000.valid1 numericValid4636

def certificate4637 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4637,(some (683734374045798823/1000000000000000000)),(1/40),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate922,CutLabelCertificates.Entropy027.certificate558,(730658993302199/25000000000000000)⟩
theorem numericValid4637 : certificate4637.NumericValid := by decide +kernel
theorem sound4637 : certificate4637.Sound := rat_cut_cell_certificate_sound certificate4637 MergedCutBins.Batch386.valid4637 MergedCutBins.Batch386.sound4637 CutLabelCertificates.Entropy027.valid558 numericValid4637

def certificate4638 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4638,(some (978265798653258317/1000000000000000000)),(1/40),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate922,CutLabelCertificates.Entropy027.certificate559,(730658993302199/25000000000000000)⟩
theorem numericValid4638 : certificate4638.NumericValid := by decide +kernel
theorem sound4638 : certificate4638.Sound := rat_cut_cell_certificate_sound certificate4638 MergedCutBins.Batch386.valid4638 MergedCutBins.Batch386.sound4638 CutLabelCertificates.Entropy027.valid559 numericValid4638

def certificate4639 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4639,(some (624738920791720057/50000000000000000)),(1/40),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate922,CutLabelCertificates.Entropy028.certificate560,(730658993302199/25000000000000000)⟩
theorem numericValid4639 : certificate4639.NumericValid := by decide +kernel
theorem sound4639 : certificate4639.Sound := rat_cut_cell_certificate_sound certificate4639 MergedCutBins.Batch386.valid4639 MergedCutBins.Batch386.sound4639 CutLabelCertificates.Entropy028.valid560 numericValid4639

def certificate4640 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4640,none,(1/40),(4501536247443668921467/1000000000000000000)⟩,PopulationCertificates.Batch046.certificate922,CutLabelCertificates.Entropy028.certificate561,(730658993302199/25000000000000000)⟩
theorem numericValid4640 : certificate4640.NumericValid := by decide +kernel
theorem sound4640 : certificate4640.Sound := rat_cut_cell_certificate_sound certificate4640 MergedCutBins.Batch386.valid4640 MergedCutBins.Batch386.sound4640 CutLabelCertificates.Entropy028.valid561 numericValid4640

def certificate4641 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4641,(some (293883819027395747/500000000000000000)),(1/2),(1056487743880087529817/250000000000000000)⟩,PopulationCertificates.Batch046.certificate923,CutLabelCertificates.Entropy028.certificate562,(185878905760727011/1000000000000000000)⟩
theorem numericValid4641 : certificate4641.NumericValid := by decide +kernel
theorem sound4641 : certificate4641.Sound := rat_cut_cell_certificate_sound certificate4641 MergedCutBins.Batch386.valid4641 MergedCutBins.Batch386.sound4641 CutLabelCertificates.Entropy028.valid562 numericValid4641

def certificate4642 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4642,(some (7273571/6250000)),(1/2),(1056487743880087529817/250000000000000000)⟩,PopulationCertificates.Batch046.certificate923,CutLabelCertificates.Entropy028.certificate562,(185878905760727011/1000000000000000000)⟩
theorem numericValid4642 : certificate4642.NumericValid := by decide +kernel
theorem sound4642 : certificate4642.Sound := rat_cut_cell_certificate_sound certificate4642 MergedCutBins.Batch386.valid4642 MergedCutBins.Batch386.sound4642 CutLabelCertificates.Entropy028.valid562 numericValid4642

def certificate4643 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch386.certificate4643,(some (290044921433168459/125000000000000000)),(1/2),(1056487743880087529817/250000000000000000)⟩,PopulationCertificates.Batch046.certificate923,CutLabelCertificates.Entropy000.certificate1,(11569434109559203/62500000000000000)⟩
theorem numericValid4643 : certificate4643.NumericValid := by decide +kernel
theorem sound4643 : certificate4643.Sound := rat_cut_cell_certificate_sound certificate4643 MergedCutBins.Batch386.valid4643 MergedCutBins.Batch386.sound4643 CutLabelCertificates.Entropy000.valid1 numericValid4643

def certificates : List RatCutCellCertificate := [certificate4632,certificate4633,certificate4634,certificate4635,certificate4636,certificate4637,certificate4638,certificate4639,certificate4640,certificate4641,certificate4642,certificate4643]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4632,List.forall_mem_cons.mpr ⟨sound4633,List.forall_mem_cons.mpr ⟨sound4634,List.forall_mem_cons.mpr ⟨sound4635,List.forall_mem_cons.mpr ⟨sound4636,List.forall_mem_cons.mpr ⟨sound4637,List.forall_mem_cons.mpr ⟨sound4638,List.forall_mem_cons.mpr ⟨sound4639,List.forall_mem_cons.mpr ⟨sound4640,List.forall_mem_cons.mpr ⟨sound4641,List.forall_mem_cons.mpr ⟨sound4642,List.forall_mem_cons.mpr ⟨sound4643,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch386
