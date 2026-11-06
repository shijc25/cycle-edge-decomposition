import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy032
import Cycle12.MergedCutBins.Batch404
import Cycle12.PopulationCertificates.Batch048
import Cycle12.PopulationCertificates.Batch049

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch404

def certificate4848 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4848,(some (223072449910813581/250000000000000000)),(1/40),(1413622755423419206487/500000000000000000)⟩,PopulationCertificates.Batch048.certificate979,CutLabelCertificates.Entropy032.certificate654,(22702593133631731/1000000000000000000)⟩
theorem numericValid4848 : certificate4848.NumericValid := by decide +kernel
theorem sound4848 : certificate4848.Sound := rat_cut_cell_certificate_sound certificate4848 MergedCutBins.Batch404.valid4848 MergedCutBins.Batch404.sound4848 CutLabelCertificates.Entropy032.valid654 numericValid4848

def certificate4849 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4849,(some (5735916568025511783/1000000000000000000)),(1/40),(1413622755423419206487/500000000000000000)⟩,PopulationCertificates.Batch048.certificate979,CutLabelCertificates.Entropy032.certificate655,(22702593133631731/1000000000000000000)⟩
theorem numericValid4849 : certificate4849.NumericValid := by decide +kernel
theorem sound4849 : certificate4849.Sound := rat_cut_cell_certificate_sound certificate4849 MergedCutBins.Batch404.valid4849 MergedCutBins.Batch404.sound4849 CutLabelCertificates.Entropy032.valid655 numericValid4849

def certificate4850 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4850,none,(1/40),(1413622755423419206487/500000000000000000)⟩,PopulationCertificates.Batch048.certificate979,CutLabelCertificates.Entropy032.certificate656,(22702593133631731/1000000000000000000)⟩
theorem numericValid4850 : certificate4850.NumericValid := by decide +kernel
theorem sound4850 : certificate4850.Sound := rat_cut_cell_certificate_sound certificate4850 MergedCutBins.Batch404.valid4850 MergedCutBins.Batch404.sound4850 CutLabelCertificates.Entropy032.valid656 numericValid4850

def certificate4851 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4851,(some (295021159594385543/500000000000000000)),(1/2),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate980,CutLabelCertificates.Entropy032.certificate657,(75831402927857607/1000000000000000000)⟩
theorem numericValid4851 : certificate4851.NumericValid := by decide +kernel
theorem sound4851 : certificate4851.Sound := rat_cut_cell_certificate_sound certificate4851 MergedCutBins.Batch404.valid4851 MergedCutBins.Batch404.sound4851 CutLabelCertificates.Entropy032.valid657 numericValid4851

def certificate4852 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4852,(some (1134155683/1000000000)),(1/2),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate980,CutLabelCertificates.Entropy032.certificate657,(75831402927857607/1000000000000000000)⟩
theorem numericValid4852 : certificate4852.NumericValid := by decide +kernel
theorem sound4852 : certificate4852.Sound := rat_cut_cell_certificate_sound certificate4852 MergedCutBins.Batch404.valid4852 MergedCutBins.Batch404.sound4852 CutLabelCertificates.Entropy032.valid657 numericValid4852

def certificate4853 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4853,(some (402632012090329139/100000000000000000)),(1/2),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate980,CutLabelCertificates.Entropy000.certificate1,(37317571513129757/500000000000000000)⟩
theorem numericValid4853 : certificate4853.NumericValid := by decide +kernel
theorem sound4853 : certificate4853.Sound := rat_cut_cell_certificate_sound certificate4853 MergedCutBins.Batch404.valid4853 MergedCutBins.Batch404.sound4853 CutLabelCertificates.Entropy000.valid1 numericValid4853

def certificate4854 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4854,(some 64),(1/2),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate980,CutLabelCertificates.Entropy000.certificate1,(37317571513129757/500000000000000000)⟩
theorem numericValid4854 : certificate4854.NumericValid := by decide +kernel
theorem sound4854 : certificate4854.Sound := rat_cut_cell_certificate_sound certificate4854 MergedCutBins.Batch404.valid4854 MergedCutBins.Batch404.sound4854 CutLabelCertificates.Entropy000.valid1 numericValid4854

def certificate4855 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4855,none,(1/2),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate980,CutLabelCertificates.Entropy000.certificate1,(37317571513129757/500000000000000000)⟩
theorem numericValid4855 : certificate4855.NumericValid := by decide +kernel
theorem sound4855 : certificate4855.Sound := rat_cut_cell_certificate_sound certificate4855 MergedCutBins.Batch404.valid4855 MergedCutBins.Batch404.sound4855 CutLabelCertificates.Entropy000.valid1 numericValid4855

def certificate4856 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4856,(some 64),(1/2),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate981,CutLabelCertificates.Entropy000.certificate1,(7909279511593036239/1000000000000000000)⟩
theorem numericValid4856 : certificate4856.NumericValid := by decide +kernel
theorem sound4856 : certificate4856.Sound := rat_cut_cell_certificate_sound certificate4856 MergedCutBins.Batch404.valid4856 MergedCutBins.Batch404.sound4856 CutLabelCertificates.Entropy000.valid1 numericValid4856

def certificate4857 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4857,none,(1/2),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate981,CutLabelCertificates.Entropy000.certificate1,(7909279511593036239/1000000000000000000)⟩
theorem numericValid4857 : certificate4857.NumericValid := by decide +kernel
theorem sound4857 : certificate4857.Sound := rat_cut_cell_certificate_sound certificate4857 MergedCutBins.Batch404.valid4857 MergedCutBins.Batch404.sound4857 CutLabelCertificates.Entropy000.valid1 numericValid4857

def certificate4858 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4858,(some (699668974387979993/1000000000000000000)),(1/40),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate982,CutLabelCertificates.Entropy032.certificate658,(6894741878854521/250000000000000000)⟩
theorem numericValid4858 : certificate4858.NumericValid := by decide +kernel
theorem sound4858 : certificate4858.Sound := rat_cut_cell_certificate_sound certificate4858 MergedCutBins.Batch404.valid4858 MergedCutBins.Batch404.sound4858 CutLabelCertificates.Entropy032.valid658 numericValid4858

def certificate4859 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch404.certificate4859,(some (224319469669009731/250000000000000000)),(1/40),(167661534521558025279/62500000000000000)⟩,PopulationCertificates.Batch049.certificate982,CutLabelCertificates.Entropy032.certificate659,(6894741878854521/250000000000000000)⟩
theorem numericValid4859 : certificate4859.NumericValid := by decide +kernel
theorem sound4859 : certificate4859.Sound := rat_cut_cell_certificate_sound certificate4859 MergedCutBins.Batch404.valid4859 MergedCutBins.Batch404.sound4859 CutLabelCertificates.Entropy032.valid659 numericValid4859

def certificates : List RatCutCellCertificate := [certificate4848,certificate4849,certificate4850,certificate4851,certificate4852,certificate4853,certificate4854,certificate4855,certificate4856,certificate4857,certificate4858,certificate4859]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4848,List.forall_mem_cons.mpr ⟨sound4849,List.forall_mem_cons.mpr ⟨sound4850,List.forall_mem_cons.mpr ⟨sound4851,List.forall_mem_cons.mpr ⟨sound4852,List.forall_mem_cons.mpr ⟨sound4853,List.forall_mem_cons.mpr ⟨sound4854,List.forall_mem_cons.mpr ⟨sound4855,List.forall_mem_cons.mpr ⟨sound4856,List.forall_mem_cons.mpr ⟨sound4857,List.forall_mem_cons.mpr ⟨sound4858,List.forall_mem_cons.mpr ⟨sound4859,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch404
