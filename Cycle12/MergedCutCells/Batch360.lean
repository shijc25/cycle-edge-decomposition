import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy021
import Cycle12.MergedCutBins.Batch360
import Cycle12.PopulationCertificates.Batch041

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch360

def certificate4320 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4320,(some 64),(1/2),(47800972580928223399921/200000000000000000)⟩,PopulationCertificates.Batch041.certificate833,CutLabelCertificates.Entropy000.certificate1,(64699425982000971/250000000000000000)⟩
theorem numericValid4320 : certificate4320.NumericValid := by decide +kernel
theorem sound4320 : certificate4320.Sound := rat_cut_cell_certificate_sound certificate4320 MergedCutBins.Batch360.valid4320 MergedCutBins.Batch360.sound4320 CutLabelCertificates.Entropy000.valid1 numericValid4320

def certificate4321 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4321,none,(1/2),(47800972580928223399921/200000000000000000)⟩,PopulationCertificates.Batch041.certificate833,CutLabelCertificates.Entropy000.certificate1,(64699425982000971/250000000000000000)⟩
theorem numericValid4321 : certificate4321.NumericValid := by decide +kernel
theorem sound4321 : certificate4321.Sound := rat_cut_cell_certificate_sound certificate4321 MergedCutBins.Batch360.valid4321 MergedCutBins.Batch360.sound4321 CutLabelCertificates.Entropy000.valid1 numericValid4321

def certificate4322 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4322,(some 64),(1/2),(47800972580928223399921/200000000000000000)⟩,PopulationCertificates.Batch041.certificate834,CutLabelCertificates.Entropy000.certificate1,(74723760560611343/20000000000000000)⟩
theorem numericValid4322 : certificate4322.NumericValid := by decide +kernel
theorem sound4322 : certificate4322.Sound := rat_cut_cell_certificate_sound certificate4322 MergedCutBins.Batch360.valid4322 MergedCutBins.Batch360.sound4322 CutLabelCertificates.Entropy000.valid1 numericValid4322

def certificate4323 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4323,none,(1/2),(47800972580928223399921/200000000000000000)⟩,PopulationCertificates.Batch041.certificate834,CutLabelCertificates.Entropy000.certificate1,(74723760560611343/20000000000000000)⟩
theorem numericValid4323 : certificate4323.NumericValid := by decide +kernel
theorem sound4323 : certificate4323.Sound := rat_cut_cell_certificate_sound certificate4323 MergedCutBins.Batch360.valid4323 MergedCutBins.Batch360.sound4323 CutLabelCertificates.Entropy000.valid1 numericValid4323

def certificate4324 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4324,(some (351530288930629119/500000000000000000)),(1/40),(47800972580928223399921/200000000000000000)⟩,PopulationCertificates.Batch041.certificate835,CutLabelCertificates.Entropy021.certificate421,(215367022813617973/1000000000000000000)⟩
theorem numericValid4324 : certificate4324.NumericValid := by decide +kernel
theorem sound4324 : certificate4324.Sound := rat_cut_cell_certificate_sound certificate4324 MergedCutBins.Batch360.valid4324 MergedCutBins.Batch360.sound4324 CutLabelCertificates.Entropy021.valid421 numericValid4324

def certificate4325 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4325,(some (12346628938005746127/1000000000000000000)),(1/40),(47800972580928223399921/200000000000000000)⟩,PopulationCertificates.Batch041.certificate835,CutLabelCertificates.Entropy021.certificate422,(215367022813617973/1000000000000000000)⟩
theorem numericValid4325 : certificate4325.NumericValid := by decide +kernel
theorem sound4325 : certificate4325.Sound := rat_cut_cell_certificate_sound certificate4325 MergedCutBins.Batch360.valid4325 MergedCutBins.Batch360.sound4325 CutLabelCertificates.Entropy021.valid422 numericValid4325

def certificate4326 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4326,none,(1/40),(47800972580928223399921/200000000000000000)⟩,PopulationCertificates.Batch041.certificate835,CutLabelCertificates.Entropy021.certificate423,(215367022813617973/1000000000000000000)⟩
theorem numericValid4326 : certificate4326.NumericValid := by decide +kernel
theorem sound4326 : certificate4326.Sound := rat_cut_cell_certificate_sound certificate4326 MergedCutBins.Batch360.valid4326 MergedCutBins.Batch360.sound4326 CutLabelCertificates.Entropy021.valid423 numericValid4326

def certificate4327 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4327,(some (469879277107253903/500000000000000000)),(1/2),(82624014196148766232829/500000000000000000)⟩,PopulationCertificates.Batch041.certificate836,CutLabelCertificates.Entropy021.certificate424,(291784888571140469/1000000000000000000)⟩
theorem numericValid4327 : certificate4327.NumericValid := by decide +kernel
theorem sound4327 : certificate4327.Sound := rat_cut_cell_certificate_sound certificate4327 MergedCutBins.Batch360.valid4327 MergedCutBins.Batch360.sound4327 CutLabelCertificates.Entropy021.valid424 numericValid4327

def certificate4328 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4328,(some (648171963/500000000)),(1/2),(82624014196148766232829/500000000000000000)⟩,PopulationCertificates.Batch041.certificate836,CutLabelCertificates.Entropy021.certificate424,(291784888571140469/1000000000000000000)⟩
theorem numericValid4328 : certificate4328.NumericValid := by decide +kernel
theorem sound4328 : certificate4328.Sound := rat_cut_cell_certificate_sound certificate4328 MergedCutBins.Batch360.valid4328 MergedCutBins.Batch360.sound4328 CutLabelCertificates.Entropy021.valid424 numericValid4328

def certificate4329 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4329,(some (21448346863995491271/500000000000000000)),(1/2),(82624014196148766232829/500000000000000000)⟩,PopulationCertificates.Batch041.certificate836,CutLabelCertificates.Entropy000.certificate1,(34392647024070967/125000000000000000)⟩
theorem numericValid4329 : certificate4329.NumericValid := by decide +kernel
theorem sound4329 : certificate4329.Sound := rat_cut_cell_certificate_sound certificate4329 MergedCutBins.Batch360.valid4329 MergedCutBins.Batch360.sound4329 CutLabelCertificates.Entropy000.valid1 numericValid4329

def certificate4330 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4330,(some 64),(1/2),(82624014196148766232829/500000000000000000)⟩,PopulationCertificates.Batch041.certificate836,CutLabelCertificates.Entropy000.certificate1,(34392647024070967/125000000000000000)⟩
theorem numericValid4330 : certificate4330.NumericValid := by decide +kernel
theorem sound4330 : certificate4330.Sound := rat_cut_cell_certificate_sound certificate4330 MergedCutBins.Batch360.valid4330 MergedCutBins.Batch360.sound4330 CutLabelCertificates.Entropy000.valid1 numericValid4330

def certificate4331 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch360.certificate4331,none,(1/2),(82624014196148766232829/500000000000000000)⟩,PopulationCertificates.Batch041.certificate836,CutLabelCertificates.Entropy000.certificate1,(34392647024070967/125000000000000000)⟩
theorem numericValid4331 : certificate4331.NumericValid := by decide +kernel
theorem sound4331 : certificate4331.Sound := rat_cut_cell_certificate_sound certificate4331 MergedCutBins.Batch360.valid4331 MergedCutBins.Batch360.sound4331 CutLabelCertificates.Entropy000.valid1 numericValid4331

def certificates : List RatCutCellCertificate := [certificate4320,certificate4321,certificate4322,certificate4323,certificate4324,certificate4325,certificate4326,certificate4327,certificate4328,certificate4329,certificate4330,certificate4331]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4320,List.forall_mem_cons.mpr ⟨sound4321,List.forall_mem_cons.mpr ⟨sound4322,List.forall_mem_cons.mpr ⟨sound4323,List.forall_mem_cons.mpr ⟨sound4324,List.forall_mem_cons.mpr ⟨sound4325,List.forall_mem_cons.mpr ⟨sound4326,List.forall_mem_cons.mpr ⟨sound4327,List.forall_mem_cons.mpr ⟨sound4328,List.forall_mem_cons.mpr ⟨sound4329,List.forall_mem_cons.mpr ⟨sound4330,List.forall_mem_cons.mpr ⟨sound4331,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch360
