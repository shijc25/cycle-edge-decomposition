import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.MergedCutBins.Batch000
import Cycle12.PopulationCertificates.Batch000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch000

def certificate0 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate0,(some (318188191847170663/500000000000000000)),(1/2),(418570030056423833731/62500000000000000)⟩,PopulationCertificates.Batch000.certificate0,CutLabelCertificates.Entropy000.certificate0,(132302451142289787/1000000000000000000)⟩
theorem numericValid0 : certificate0.NumericValid := by decide +kernel
theorem sound0 : certificate0.Sound := rat_cut_cell_certificate_sound certificate0 MergedCutBins.Batch000.valid0 MergedCutBins.Batch000.sound0 CutLabelCertificates.Entropy000.valid0 numericValid0

def certificate1 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate1,(some (1309610447/1000000000)),(1/2),(418570030056423833731/62500000000000000)⟩,PopulationCertificates.Batch000.certificate0,CutLabelCertificates.Entropy000.certificate0,(132302451142289787/1000000000000000000)⟩
theorem numericValid1 : certificate1.NumericValid := by decide +kernel
theorem sound1 : certificate1.Sound := rat_cut_cell_certificate_sound certificate1 MergedCutBins.Batch000.valid1 MergedCutBins.Batch000.sound1 CutLabelCertificates.Entropy000.valid0 numericValid1

def certificate2 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate2,(some (4893230564416370337/1000000000000000000)),(1/2),(418570030056423833731/62500000000000000)⟩,PopulationCertificates.Batch000.certificate0,CutLabelCertificates.Entropy000.certificate1,(65929795097944263/500000000000000000)⟩
theorem numericValid2 : certificate2.NumericValid := by decide +kernel
theorem sound2 : certificate2.Sound := rat_cut_cell_certificate_sound certificate2 MergedCutBins.Batch000.valid2 MergedCutBins.Batch000.sound2 CutLabelCertificates.Entropy000.valid1 numericValid2

def certificate3 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate3,(some 64),(1/2),(418570030056423833731/62500000000000000)⟩,PopulationCertificates.Batch000.certificate0,CutLabelCertificates.Entropy000.certificate1,(65929795097944263/500000000000000000)⟩
theorem numericValid3 : certificate3.NumericValid := by decide +kernel
theorem sound3 : certificate3.Sound := rat_cut_cell_certificate_sound certificate3 MergedCutBins.Batch000.valid3 MergedCutBins.Batch000.sound3 CutLabelCertificates.Entropy000.valid1 numericValid3

def certificate4 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate4,none,(1/2),(418570030056423833731/62500000000000000)⟩,PopulationCertificates.Batch000.certificate0,CutLabelCertificates.Entropy000.certificate1,(65929795097944263/500000000000000000)⟩
theorem numericValid4 : certificate4.NumericValid := by decide +kernel
theorem sound4 : certificate4.Sound := rat_cut_cell_certificate_sound certificate4 MergedCutBins.Batch000.valid4 MergedCutBins.Batch000.sound4 CutLabelCertificates.Entropy000.valid1 numericValid4

def certificate5 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate5,(some 64),(1/2),(418570030056423833731/62500000000000000)⟩,PopulationCertificates.Batch000.certificate1,CutLabelCertificates.Entropy000.certificate1,(15292040964488061/125000000000000000)⟩
theorem numericValid5 : certificate5.NumericValid := by decide +kernel
theorem sound5 : certificate5.Sound := rat_cut_cell_certificate_sound certificate5 MergedCutBins.Batch000.valid5 MergedCutBins.Batch000.sound5 CutLabelCertificates.Entropy000.valid1 numericValid5

def certificate6 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate6,none,(1/2),(418570030056423833731/62500000000000000)⟩,PopulationCertificates.Batch000.certificate1,CutLabelCertificates.Entropy000.certificate1,(15292040964488061/125000000000000000)⟩
theorem numericValid6 : certificate6.NumericValid := by decide +kernel
theorem sound6 : certificate6.Sound := rat_cut_cell_certificate_sound certificate6 MergedCutBins.Batch000.valid6 MergedCutBins.Batch000.sound6 CutLabelCertificates.Entropy000.valid1 numericValid6

def certificate7 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate7,(some (608818170029686007/1000000000000000000)),(1/2),(13394240961805562679393/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate2,CutLabelCertificates.Entropy000.certificate2,(39294127764886041/500000000000000000)⟩
theorem numericValid7 : certificate7.NumericValid := by decide +kernel
theorem sound7 : certificate7.Sound := rat_cut_cell_certificate_sound certificate7 MergedCutBins.Batch000.valid7 MergedCutBins.Batch000.sound7 CutLabelCertificates.Entropy000.valid2 numericValid7

def certificate8 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate8,(some (649702233/500000000)),(1/2),(13394240961805562679393/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate2,CutLabelCertificates.Entropy000.certificate2,(39294127764886041/500000000000000000)⟩
theorem numericValid8 : certificate8.NumericValid := by decide +kernel
theorem sound8 : certificate8.Sound := rat_cut_cell_certificate_sound certificate8 MergedCutBins.Batch000.valid8 MergedCutBins.Batch000.sound8 CutLabelCertificates.Entropy000.valid2 numericValid8

def certificate9 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate9,(some (1924765956298637353/250000000000000000)),(1/2),(13394240961805562679393/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate2,CutLabelCertificates.Entropy000.certificate1,(39170222563158317/500000000000000000)⟩
theorem numericValid9 : certificate9.NumericValid := by decide +kernel
theorem sound9 : certificate9.Sound := rat_cut_cell_certificate_sound certificate9 MergedCutBins.Batch000.valid9 MergedCutBins.Batch000.sound9 CutLabelCertificates.Entropy000.valid1 numericValid9

def certificate10 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate10,(some 64),(1/2),(13394240961805562679393/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate2,CutLabelCertificates.Entropy000.certificate1,(39170222563158317/500000000000000000)⟩
theorem numericValid10 : certificate10.NumericValid := by decide +kernel
theorem sound10 : certificate10.Sound := rat_cut_cell_certificate_sound certificate10 MergedCutBins.Batch000.valid10 MergedCutBins.Batch000.sound10 CutLabelCertificates.Entropy000.valid1 numericValid10

def certificate11 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch000.certificate11,none,(1/2),(13394240961805562679393/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate2,CutLabelCertificates.Entropy000.certificate1,(39170222563158317/500000000000000000)⟩
theorem numericValid11 : certificate11.NumericValid := by decide +kernel
theorem sound11 : certificate11.Sound := rat_cut_cell_certificate_sound certificate11 MergedCutBins.Batch000.valid11 MergedCutBins.Batch000.sound11 CutLabelCertificates.Entropy000.valid1 numericValid11

def certificates : List RatCutCellCertificate := [certificate0,certificate1,certificate2,certificate3,certificate4,certificate5,certificate6,certificate7,certificate8,certificate9,certificate10,certificate11]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_cons.mpr ⟨sound7,List.forall_mem_cons.mpr ⟨sound8,List.forall_mem_cons.mpr ⟨sound9,List.forall_mem_cons.mpr ⟨sound10,List.forall_mem_cons.mpr ⟨sound11,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch000
