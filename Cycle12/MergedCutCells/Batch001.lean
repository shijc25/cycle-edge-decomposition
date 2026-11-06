import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.MergedCutBins.Batch001
import Cycle12.PopulationCertificates.Batch000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch001

def certificate12 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate12,(some 64),(1/2),(13394240961805562679393/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate3,CutLabelCertificates.Entropy000.certificate1,(590814516901912601/500000000000000000)⟩
theorem numericValid12 : certificate12.NumericValid := by decide +kernel
theorem sound12 : certificate12.Sound := rat_cut_cell_certificate_sound certificate12 MergedCutBins.Batch001.valid12 MergedCutBins.Batch001.sound12 CutLabelCertificates.Entropy000.valid1 numericValid12

def certificate13 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate13,none,(1/2),(13394240961805562679393/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate3,CutLabelCertificates.Entropy000.certificate1,(590814516901912601/500000000000000000)⟩
theorem numericValid13 : certificate13.NumericValid := by decide +kernel
theorem sound13 : certificate13.Sound := rat_cut_cell_certificate_sound certificate13 MergedCutBins.Batch001.valid13 MergedCutBins.Batch001.sound13 CutLabelCertificates.Entropy000.valid1 numericValid13

def certificate14 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate14,(some (585871170671687059/1000000000000000000)),(1/2),(3750800945834192207617/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate4,CutLabelCertificates.Entropy000.certificate3,(278893336885000097/1000000000000000000)⟩
theorem numericValid14 : certificate14.NumericValid := by decide +kernel
theorem sound14 : certificate14.Sound := rat_cut_cell_certificate_sound certificate14 MergedCutBins.Batch001.valid14 MergedCutBins.Batch001.sound14 CutLabelCertificates.Entropy000.valid3 numericValid14

def certificate15 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate15,(some (1312491441/1000000000)),(1/2),(3750800945834192207617/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate4,CutLabelCertificates.Entropy000.certificate3,(278893336885000097/1000000000000000000)⟩
theorem numericValid15 : certificate15.NumericValid := by decide +kernel
theorem sound15 : certificate15.Sound := rat_cut_cell_certificate_sound certificate15 MergedCutBins.Batch001.valid15 MergedCutBins.Batch001.sound15 CutLabelCertificates.Entropy000.valid3 numericValid15

def certificate16 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate16,(some (318006261291378333/100000000000000000)),(1/2),(3750800945834192207617/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate4,CutLabelCertificates.Entropy000.certificate1,(138854341844570393/500000000000000000)⟩
theorem numericValid16 : certificate16.NumericValid := by decide +kernel
theorem sound16 : certificate16.Sound := rat_cut_cell_certificate_sound certificate16 MergedCutBins.Batch001.valid16 MergedCutBins.Batch001.sound16 CutLabelCertificates.Entropy000.valid1 numericValid16

def certificate17 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate17,(some 64),(1/2),(3750800945834192207617/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate4,CutLabelCertificates.Entropy000.certificate1,(138854341844570393/500000000000000000)⟩
theorem numericValid17 : certificate17.NumericValid := by decide +kernel
theorem sound17 : certificate17.Sound := rat_cut_cell_certificate_sound certificate17 MergedCutBins.Batch001.valid17 MergedCutBins.Batch001.sound17 CutLabelCertificates.Entropy000.valid1 numericValid17

def certificate18 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate18,none,(1/2),(3750800945834192207617/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate4,CutLabelCertificates.Entropy000.certificate1,(138854341844570393/500000000000000000)⟩
theorem numericValid18 : certificate18.NumericValid := by decide +kernel
theorem sound18 : certificate18.Sound := rat_cut_cell_certificate_sound certificate18 MergedCutBins.Batch001.valid18 MergedCutBins.Batch001.sound18 CutLabelCertificates.Entropy000.valid1 numericValid18

def certificate19 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate19,(some 64),(1/2),(3750800945834192207617/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate5,CutLabelCertificates.Entropy000.certificate1,(19995601932044001/125000000000000000)⟩
theorem numericValid19 : certificate19.NumericValid := by decide +kernel
theorem sound19 : certificate19.Sound := rat_cut_cell_certificate_sound certificate19 MergedCutBins.Batch001.valid19 MergedCutBins.Batch001.sound19 CutLabelCertificates.Entropy000.valid1 numericValid19

def certificate20 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate20,none,(1/2),(3750800945834192207617/1000000000000000000)⟩,PopulationCertificates.Batch000.certificate5,CutLabelCertificates.Entropy000.certificate1,(19995601932044001/125000000000000000)⟩
theorem numericValid20 : certificate20.NumericValid := by decide +kernel
theorem sound20 : certificate20.Sound := rat_cut_cell_certificate_sound certificate20 MergedCutBins.Batch001.valid20 MergedCutBins.Batch001.sound20 CutLabelCertificates.Entropy000.valid1 numericValid20

def certificate21 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate21,(some (315061887006083071/500000000000000000)),(1/2),(597512157261602792499/250000000000000000)⟩,PopulationCertificates.Batch000.certificate6,CutLabelCertificates.Entropy000.certificate4,(275924382801026929/1000000000000000000)⟩
theorem numericValid21 : certificate21.NumericValid := by decide +kernel
theorem sound21 : certificate21.Sound := rat_cut_cell_certificate_sound certificate21 MergedCutBins.Batch001.valid21 MergedCutBins.Batch001.sound21 CutLabelCertificates.Entropy000.valid4 numericValid21

def certificate22 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate22,(some (1315913273/1000000000)),(1/2),(597512157261602792499/250000000000000000)⟩,PopulationCertificates.Batch000.certificate6,CutLabelCertificates.Entropy000.certificate4,(275924382801026929/1000000000000000000)⟩
theorem numericValid22 : certificate22.NumericValid := by decide +kernel
theorem sound22 : certificate22.Sound := rat_cut_cell_certificate_sound certificate22 MergedCutBins.Batch001.valid22 MergedCutBins.Batch001.sound22 CutLabelCertificates.Entropy000.valid4 numericValid22

def certificate23 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch001.certificate23,(some (4132049451178336111/1000000000000000000)),(1/2),(597512157261602792499/250000000000000000)⟩,PopulationCertificates.Batch000.certificate6,CutLabelCertificates.Entropy000.certificate1,(274860770125611531/1000000000000000000)⟩
theorem numericValid23 : certificate23.NumericValid := by decide +kernel
theorem sound23 : certificate23.Sound := rat_cut_cell_certificate_sound certificate23 MergedCutBins.Batch001.valid23 MergedCutBins.Batch001.sound23 CutLabelCertificates.Entropy000.valid1 numericValid23

def certificates : List RatCutCellCertificate := [certificate12,certificate13,certificate14,certificate15,certificate16,certificate17,certificate18,certificate19,certificate20,certificate21,certificate22,certificate23]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound12,List.forall_mem_cons.mpr ⟨sound13,List.forall_mem_cons.mpr ⟨sound14,List.forall_mem_cons.mpr ⟨sound15,List.forall_mem_cons.mpr ⟨sound16,List.forall_mem_cons.mpr ⟨sound17,List.forall_mem_cons.mpr ⟨sound18,List.forall_mem_cons.mpr ⟨sound19,List.forall_mem_cons.mpr ⟨sound20,List.forall_mem_cons.mpr ⟨sound21,List.forall_mem_cons.mpr ⟨sound22,List.forall_mem_cons.mpr ⟨sound23,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch001
