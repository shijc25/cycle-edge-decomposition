import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy012
import Cycle12.MergedCutBins.Batch231
import Cycle12.PopulationCertificates.Batch024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch231

def certificate2772 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2772,(some 64),(1/2),(9244737841268092559/500000000000000000)⟩,PopulationCertificates.Batch024.certificate482,CutLabelCertificates.Entropy012.certificate242,(258034105618073437/100000000000000000)⟩
theorem numericValid2772 : certificate2772.NumericValid := by decide +kernel
theorem sound2772 : certificate2772.Sound := rat_cut_cell_certificate_sound certificate2772 MergedCutBins.Batch231.valid2772 MergedCutBins.Batch231.sound2772 CutLabelCertificates.Entropy012.valid242 numericValid2772

def certificate2773 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2773,none,(1/2),(9244737841268092559/500000000000000000)⟩,PopulationCertificates.Batch024.certificate482,CutLabelCertificates.Entropy000.certificate1,(706804780999062673/200000000000000000)⟩
theorem numericValid2773 : certificate2773.NumericValid := by decide +kernel
theorem sound2773 : certificate2773.Sound := rat_cut_cell_certificate_sound certificate2773 MergedCutBins.Batch231.valid2773 MergedCutBins.Batch231.sound2773 CutLabelCertificates.Entropy000.valid1 numericValid2773

def certificate2774 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2774,(some (1050564851917780599/125000000000000000)),(1/2),(9244737841268092559/500000000000000000)⟩,PopulationCertificates.Batch024.certificate483,CutLabelCertificates.Entropy000.certificate1,(2314723971122881623/500000000000000000)⟩
theorem numericValid2774 : certificate2774.NumericValid := by decide +kernel
theorem sound2774 : certificate2774.Sound := rat_cut_cell_certificate_sound certificate2774 MergedCutBins.Batch231.valid2774 MergedCutBins.Batch231.sound2774 CutLabelCertificates.Entropy000.valid1 numericValid2774

def certificate2775 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2775,(some (1820177911354143533/200000000000000000)),(1/2),(9244737841268092559/500000000000000000)⟩,PopulationCertificates.Batch024.certificate483,CutLabelCertificates.Entropy000.certificate1,(2314723971122881623/500000000000000000)⟩
theorem numericValid2775 : certificate2775.NumericValid := by decide +kernel
theorem sound2775 : certificate2775.Sound := rat_cut_cell_certificate_sound certificate2775 MergedCutBins.Batch231.valid2775 MergedCutBins.Batch231.sound2775 CutLabelCertificates.Entropy000.valid1 numericValid2775

def certificate2776 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2776,(some (4595949226169212421/500000000000000000)),(1/2),(9244737841268092559/500000000000000000)⟩,PopulationCertificates.Batch024.certificate483,CutLabelCertificates.Entropy000.certificate1,(2314723971122881623/500000000000000000)⟩
theorem numericValid2776 : certificate2776.NumericValid := by decide +kernel
theorem sound2776 : certificate2776.Sound := rat_cut_cell_certificate_sound certificate2776 MergedCutBins.Batch231.valid2776 MergedCutBins.Batch231.sound2776 CutLabelCertificates.Entropy000.valid1 numericValid2776

def certificate2777 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2777,none,(1/2),(9244737841268092559/500000000000000000)⟩,PopulationCertificates.Batch024.certificate483,CutLabelCertificates.Entropy000.certificate1,(2314723971122881623/500000000000000000)⟩
theorem numericValid2777 : certificate2777.NumericValid := by decide +kernel
theorem sound2777 : certificate2777.Sound := rat_cut_cell_certificate_sound certificate2777 MergedCutBins.Batch231.valid2777 MergedCutBins.Batch231.sound2777 CutLabelCertificates.Entropy000.valid1 numericValid2777

def certificate2778 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2778,(some (32601151352612423/50000000000000000)),(1/2),(18754004729170961038089/1000000000000000000)⟩,PopulationCertificates.Batch024.certificate484,CutLabelCertificates.Entropy012.certificate243,(303229611556218821/1000000000000000000)⟩
theorem numericValid2778 : certificate2778.NumericValid := by decide +kernel
theorem sound2778 : certificate2778.Sound := rat_cut_cell_certificate_sound certificate2778 MergedCutBins.Batch231.valid2778 MergedCutBins.Batch231.sound2778 CutLabelCertificates.Entropy012.valid243 numericValid2778

def certificate2779 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2779,(some (663189157/500000000)),(1/2),(18754004729170961038089/1000000000000000000)⟩,PopulationCertificates.Batch024.certificate484,CutLabelCertificates.Entropy012.certificate243,(303229611556218821/1000000000000000000)⟩
theorem numericValid2779 : certificate2779.NumericValid := by decide +kernel
theorem sound2779 : certificate2779.Sound := rat_cut_cell_certificate_sound certificate2779 MergedCutBins.Batch231.valid2779 MergedCutBins.Batch231.sound2779 CutLabelCertificates.Entropy012.valid243 numericValid2779

def certificate2780 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2780,(some (4692033581625323731/500000000000000000)),(1/2),(18754004729170961038089/1000000000000000000)⟩,PopulationCertificates.Batch024.certificate484,CutLabelCertificates.Entropy000.certificate1,(15156643958549851/50000000000000000)⟩
theorem numericValid2780 : certificate2780.NumericValid := by decide +kernel
theorem sound2780 : certificate2780.Sound := rat_cut_cell_certificate_sound certificate2780 MergedCutBins.Batch231.valid2780 MergedCutBins.Batch231.sound2780 CutLabelCertificates.Entropy000.valid1 numericValid2780

def certificate2781 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2781,(some 64),(1/2),(18754004729170961038089/1000000000000000000)⟩,PopulationCertificates.Batch024.certificate484,CutLabelCertificates.Entropy000.certificate1,(15156643958549851/50000000000000000)⟩
theorem numericValid2781 : certificate2781.NumericValid := by decide +kernel
theorem sound2781 : certificate2781.Sound := rat_cut_cell_certificate_sound certificate2781 MergedCutBins.Batch231.valid2781 MergedCutBins.Batch231.sound2781 CutLabelCertificates.Entropy000.valid1 numericValid2781

def certificate2782 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2782,none,(1/2),(18754004729170961038089/1000000000000000000)⟩,PopulationCertificates.Batch024.certificate484,CutLabelCertificates.Entropy000.certificate1,(15156643958549851/50000000000000000)⟩
theorem numericValid2782 : certificate2782.NumericValid := by decide +kernel
theorem sound2782 : certificate2782.Sound := rat_cut_cell_certificate_sound certificate2782 MergedCutBins.Batch231.valid2782 MergedCutBins.Batch231.sound2782 CutLabelCertificates.Entropy000.valid1 numericValid2782

def certificate2783 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch231.certificate2783,(some 64),(1/2),(18754004729170961038089/1000000000000000000)⟩,PopulationCertificates.Batch024.certificate485,CutLabelCertificates.Entropy000.certificate1,(245129135385415361/100000000000000000)⟩
theorem numericValid2783 : certificate2783.NumericValid := by decide +kernel
theorem sound2783 : certificate2783.Sound := rat_cut_cell_certificate_sound certificate2783 MergedCutBins.Batch231.valid2783 MergedCutBins.Batch231.sound2783 CutLabelCertificates.Entropy000.valid1 numericValid2783

def certificates : List RatCutCellCertificate := [certificate2772,certificate2773,certificate2774,certificate2775,certificate2776,certificate2777,certificate2778,certificate2779,certificate2780,certificate2781,certificate2782,certificate2783]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2772,List.forall_mem_cons.mpr ⟨sound2773,List.forall_mem_cons.mpr ⟨sound2774,List.forall_mem_cons.mpr ⟨sound2775,List.forall_mem_cons.mpr ⟨sound2776,List.forall_mem_cons.mpr ⟨sound2777,List.forall_mem_cons.mpr ⟨sound2778,List.forall_mem_cons.mpr ⟨sound2779,List.forall_mem_cons.mpr ⟨sound2780,List.forall_mem_cons.mpr ⟨sound2781,List.forall_mem_cons.mpr ⟨sound2782,List.forall_mem_cons.mpr ⟨sound2783,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch231
