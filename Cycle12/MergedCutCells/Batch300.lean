import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy016
import Cycle12.MergedCutBins.Batch300
import Cycle12.PopulationCertificates.Batch032

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch300

def certificate3600 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3600,(some (22962109234296582469/1000000000000000000)),(1/2),(4970158454520361661/100000000000000000)⟩,PopulationCertificates.Batch032.certificate647,CutLabelCertificates.Entropy000.certificate1,(8381091284213893679/1000000000000000000)⟩
theorem numericValid3600 : certificate3600.NumericValid := by decide +kernel
theorem sound3600 : certificate3600.Sound := rat_cut_cell_certificate_sound certificate3600 MergedCutBins.Batch300.valid3600 MergedCutBins.Batch300.sound3600 CutLabelCertificates.Entropy000.valid1 numericValid3600

def certificate3601 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3601,(some (2461848906903219223/100000000000000000)),(1/2),(4970158454520361661/100000000000000000)⟩,PopulationCertificates.Batch032.certificate647,CutLabelCertificates.Entropy000.certificate1,(8381091284213893679/1000000000000000000)⟩
theorem numericValid3601 : certificate3601.NumericValid := by decide +kernel
theorem sound3601 : certificate3601.Sound := rat_cut_cell_certificate_sound certificate3601 MergedCutBins.Batch300.valid3601 MergedCutBins.Batch300.sound3601 CutLabelCertificates.Entropy000.valid1 numericValid3601

def certificate3602 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3602,none,(1/2),(4970158454520361661/100000000000000000)⟩,PopulationCertificates.Batch032.certificate647,CutLabelCertificates.Entropy000.certificate1,(8381091284213893679/1000000000000000000)⟩
theorem numericValid3602 : certificate3602.NumericValid := by decide +kernel
theorem sound3602 : certificate3602.Sound := rat_cut_cell_certificate_sound certificate3602 MergedCutBins.Batch300.valid3602 MergedCutBins.Batch300.sound3602 CutLabelCertificates.Entropy000.valid1 numericValid3602

def certificate3603 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3603,(some (477611937052448927/500000000000000000)),(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy016.certificate325,(2905751833271513137/1000000000000000000)⟩
theorem numericValid3603 : certificate3603.NumericValid := by decide +kernel
theorem sound3603 : certificate3603.Sound := rat_cut_cell_certificate_sound certificate3603 MergedCutBins.Batch300.valid3603 MergedCutBins.Batch300.sound3603 CutLabelCertificates.Entropy016.valid325 numericValid3603

def certificate3604 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3604,(some (138623157908005783/125000000000000000)),(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy016.certificate325,(2905751833271513137/1000000000000000000)⟩
theorem numericValid3604 : certificate3604.NumericValid := by decide +kernel
theorem sound3604 : certificate3604.Sound := rat_cut_cell_certificate_sound certificate3604 MergedCutBins.Batch300.valid3604 MergedCutBins.Batch300.sound3604 CutLabelCertificates.Entropy016.valid325 numericValid3604

def certificate3605 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3605,(some (224772041/200000000)),(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy016.certificate325,(2905751833271513137/1000000000000000000)⟩
theorem numericValid3605 : certificate3605.NumericValid := by decide +kernel
theorem sound3605 : certificate3605.Sound := rat_cut_cell_certificate_sound certificate3605 MergedCutBins.Batch300.valid3605 MergedCutBins.Batch300.sound3605 CutLabelCertificates.Entropy016.valid325 numericValid3605

def certificate3606 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3606,(some (1380371545414808781/1000000000000000000)),(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy000.certificate1,(89695094005571947/31250000000000000)⟩
theorem numericValid3606 : certificate3606.NumericValid := by decide +kernel
theorem sound3606 : certificate3606.Sound := rat_cut_cell_certificate_sound certificate3606 MergedCutBins.Batch300.valid3606 MergedCutBins.Batch300.sound3606 CutLabelCertificates.Entropy000.valid1 numericValid3606

def certificate3607 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3607,(some (4693804246680911631/1000000000000000000)),(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy000.certificate1,(89695094005571947/31250000000000000)⟩
theorem numericValid3607 : certificate3607.NumericValid := by decide +kernel
theorem sound3607 : certificate3607.Sound := rat_cut_cell_certificate_sound certificate3607 MergedCutBins.Batch300.valid3607 MergedCutBins.Batch300.sound3607 CutLabelCertificates.Entropy000.valid1 numericValid3607

def certificate3608 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3608,(some (19669929269450821779/1000000000000000000)),(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy000.certificate1,(89695094005571947/31250000000000000)⟩
theorem numericValid3608 : certificate3608.NumericValid := by decide +kernel
theorem sound3608 : certificate3608.Sound := rat_cut_cell_certificate_sound certificate3608 MergedCutBins.Batch300.valid3608 MergedCutBins.Batch300.sound3608 CutLabelCertificates.Entropy000.valid1 numericValid3608

def certificate3609 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3609,(some (24001051781064880131/1000000000000000000)),(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy000.certificate1,(89695094005571947/31250000000000000)⟩
theorem numericValid3609 : certificate3609.NumericValid := by decide +kernel
theorem sound3609 : certificate3609.Sound := rat_cut_cell_certificate_sound certificate3609 MergedCutBins.Batch300.valid3609 MergedCutBins.Batch300.sound3609 CutLabelCertificates.Entropy000.valid1 numericValid3609

def certificate3610 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3610,(some (24241062298875528933/1000000000000000000)),(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy000.certificate1,(89695094005571947/31250000000000000)⟩
theorem numericValid3610 : certificate3610.NumericValid := by decide +kernel
theorem sound3610 : certificate3610.Sound := rat_cut_cell_certificate_sound certificate3610 MergedCutBins.Batch300.valid3610 MergedCutBins.Batch300.sound3610 CutLabelCertificates.Entropy000.valid1 numericValid3610

def certificate3611 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch300.certificate3611,none,(1/2),(24400471323788476259/500000000000000000)⟩,PopulationCertificates.Batch032.certificate648,CutLabelCertificates.Entropy000.certificate1,(89695094005571947/31250000000000000)⟩
theorem numericValid3611 : certificate3611.NumericValid := by decide +kernel
theorem sound3611 : certificate3611.Sound := rat_cut_cell_certificate_sound certificate3611 MergedCutBins.Batch300.valid3611 MergedCutBins.Batch300.sound3611 CutLabelCertificates.Entropy000.valid1 numericValid3611

def certificates : List RatCutCellCertificate := [certificate3600,certificate3601,certificate3602,certificate3603,certificate3604,certificate3605,certificate3606,certificate3607,certificate3608,certificate3609,certificate3610,certificate3611]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3600,List.forall_mem_cons.mpr ⟨sound3601,List.forall_mem_cons.mpr ⟨sound3602,List.forall_mem_cons.mpr ⟨sound3603,List.forall_mem_cons.mpr ⟨sound3604,List.forall_mem_cons.mpr ⟨sound3605,List.forall_mem_cons.mpr ⟨sound3606,List.forall_mem_cons.mpr ⟨sound3607,List.forall_mem_cons.mpr ⟨sound3608,List.forall_mem_cons.mpr ⟨sound3609,List.forall_mem_cons.mpr ⟨sound3610,List.forall_mem_cons.mpr ⟨sound3611,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch300
