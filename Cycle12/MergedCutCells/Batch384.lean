import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy027
import Cycle12.MergedCutBins.Batch384
import Cycle12.PopulationCertificates.Batch045

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch384

def certificate4608 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4608,(some (1182925567/1000000000)),(1/2),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate914,CutLabelCertificates.Entropy027.certificate547,(176818934891587333/1000000000000000000)⟩
theorem numericValid4608 : certificate4608.NumericValid := by decide +kernel
theorem sound4608 : certificate4608.Sound := rat_cut_cell_certificate_sound certificate4608 MergedCutBins.Batch384.valid4608 MergedCutBins.Batch384.sound4608 CutLabelCertificates.Entropy027.valid547 numericValid4608

def certificate4609 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4609,(some (2193629522490192573/500000000000000000)),(1/2),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate914,CutLabelCertificates.Entropy000.certificate1,(88142697592018479/500000000000000000)⟩
theorem numericValid4609 : certificate4609.NumericValid := by decide +kernel
theorem sound4609 : certificate4609.Sound := rat_cut_cell_certificate_sound certificate4609 MergedCutBins.Batch384.valid4609 MergedCutBins.Batch384.sound4609 CutLabelCertificates.Entropy000.valid1 numericValid4609

def certificate4610 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4610,(some 64),(1/2),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate914,CutLabelCertificates.Entropy000.certificate1,(88142697592018479/500000000000000000)⟩
theorem numericValid4610 : certificate4610.NumericValid := by decide +kernel
theorem sound4610 : certificate4610.Sound := rat_cut_cell_certificate_sound certificate4610 MergedCutBins.Batch384.valid4610 MergedCutBins.Batch384.sound4610 CutLabelCertificates.Entropy000.valid1 numericValid4610

def certificate4611 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4611,none,(1/2),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate914,CutLabelCertificates.Entropy000.certificate1,(88142697592018479/500000000000000000)⟩
theorem numericValid4611 : certificate4611.NumericValid := by decide +kernel
theorem sound4611 : certificate4611.Sound := rat_cut_cell_certificate_sound certificate4611 MergedCutBins.Batch384.valid4611 MergedCutBins.Batch384.sound4611 CutLabelCertificates.Entropy000.valid1 numericValid4611

def certificate4612 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4612,(some 64),(1/2),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate915,CutLabelCertificates.Entropy000.certificate1,(6349512610549344373/1000000000000000000)⟩
theorem numericValid4612 : certificate4612.NumericValid := by decide +kernel
theorem sound4612 : certificate4612.Sound := rat_cut_cell_certificate_sound certificate4612 MergedCutBins.Batch384.valid4612 MergedCutBins.Batch384.sound4612 CutLabelCertificates.Entropy000.valid1 numericValid4612

def certificate4613 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4613,none,(1/2),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate915,CutLabelCertificates.Entropy000.certificate1,(6349512610549344373/1000000000000000000)⟩
theorem numericValid4613 : certificate4613.NumericValid := by decide +kernel
theorem sound4613 : certificate4613.Sound := rat_cut_cell_certificate_sound certificate4613 MergedCutBins.Batch384.valid4613 MergedCutBins.Batch384.sound4613 CutLabelCertificates.Entropy000.valid1 numericValid4613

def certificate4614 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4614,(some (676417168949609379/1000000000000000000)),(1/40),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate916,CutLabelCertificates.Entropy027.certificate548,(21129981921430323/1000000000000000000)⟩
theorem numericValid4614 : certificate4614.NumericValid := by decide +kernel
theorem sound4614 : certificate4614.Sound := rat_cut_cell_certificate_sound certificate4614 MergedCutBins.Batch384.valid4614 MergedCutBins.Batch384.sound4614 CutLabelCertificates.Entropy027.valid548 numericValid4614

def certificate4615 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4615,(some (987249281075864947/1000000000000000000)),(1/40),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate916,CutLabelCertificates.Entropy027.certificate549,(21129981921430323/1000000000000000000)⟩
theorem numericValid4615 : certificate4615.NumericValid := by decide +kernel
theorem sound4615 : certificate4615.Sound := rat_cut_cell_certificate_sound certificate4615 MergedCutBins.Batch384.valid4615 MergedCutBins.Batch384.sound4615 CutLabelCertificates.Entropy027.valid549 numericValid4615

def certificate4616 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4616,(some (3517010256148624557/250000000000000000)),(1/40),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate916,CutLabelCertificates.Entropy027.certificate550,(21129981921430323/1000000000000000000)⟩
theorem numericValid4616 : certificate4616.NumericValid := by decide +kernel
theorem sound4616 : certificate4616.Sound := rat_cut_cell_certificate_sound certificate4616 MergedCutBins.Batch384.valid4616 MergedCutBins.Batch384.sound4616 CutLabelCertificates.Entropy027.valid550 numericValid4616

def certificate4617 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4617,none,(1/40),(5134451270410500746393/1000000000000000000)⟩,PopulationCertificates.Batch045.certificate916,CutLabelCertificates.Entropy027.certificate551,(21129981921430323/1000000000000000000)⟩
theorem numericValid4617 : certificate4617.NumericValid := by decide +kernel
theorem sound4617 : certificate4617.Sound := rat_cut_cell_certificate_sound certificate4617 MergedCutBins.Batch384.valid4617 MergedCutBins.Batch384.sound4617 CutLabelCertificates.Entropy027.valid551 numericValid4617

def certificate4618 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4618,(some (297846440575956193/500000000000000000)),(1/2),(960649900360527327901/200000000000000000)⟩,PopulationCertificates.Batch045.certificate917,CutLabelCertificates.Entropy027.certificate552,(179811600127770707/1000000000000000000)⟩
theorem numericValid4618 : certificate4618.NumericValid := by decide +kernel
theorem sound4618 : certificate4618.Sound := rat_cut_cell_certificate_sound certificate4618 MergedCutBins.Batch384.valid4618 MergedCutBins.Batch384.sound4618 CutLabelCertificates.Entropy027.valid552 numericValid4618

def certificate4619 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch384.certificate4619,(some (593102819/500000000)),(1/2),(960649900360527327901/200000000000000000)⟩,PopulationCertificates.Batch045.certificate917,CutLabelCertificates.Entropy027.certificate552,(179811600127770707/1000000000000000000)⟩
theorem numericValid4619 : certificate4619.NumericValid := by decide +kernel
theorem sound4619 : certificate4619.Sound := rat_cut_cell_certificate_sound certificate4619 MergedCutBins.Batch384.valid4619 MergedCutBins.Batch384.sound4619 CutLabelCertificates.Entropy027.valid552 numericValid4619

def certificates : List RatCutCellCertificate := [certificate4608,certificate4609,certificate4610,certificate4611,certificate4612,certificate4613,certificate4614,certificate4615,certificate4616,certificate4617,certificate4618,certificate4619]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4608,List.forall_mem_cons.mpr ⟨sound4609,List.forall_mem_cons.mpr ⟨sound4610,List.forall_mem_cons.mpr ⟨sound4611,List.forall_mem_cons.mpr ⟨sound4612,List.forall_mem_cons.mpr ⟨sound4613,List.forall_mem_cons.mpr ⟨sound4614,List.forall_mem_cons.mpr ⟨sound4615,List.forall_mem_cons.mpr ⟨sound4616,List.forall_mem_cons.mpr ⟨sound4617,List.forall_mem_cons.mpr ⟨sound4618,List.forall_mem_cons.mpr ⟨sound4619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch384
