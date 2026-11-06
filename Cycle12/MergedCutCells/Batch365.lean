import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy022
import Cycle12.MergedCutBins.Batch365
import Cycle12.PopulationCertificates.Batch042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch365

def certificate4380 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4380,none,(1/2),(9615687695137442862049/200000000000000000)⟩,PopulationCertificates.Batch042.certificate851,CutLabelCertificates.Entropy000.certificate1,(918762188964881/2500000000000000)⟩
theorem numericValid4380 : certificate4380.NumericValid := by decide +kernel
theorem sound4380 : certificate4380.Sound := rat_cut_cell_certificate_sound certificate4380 MergedCutBins.Batch365.valid4380 MergedCutBins.Batch365.sound4380 CutLabelCertificates.Entropy000.valid1 numericValid4380

def certificate4381 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4381,(some 64),(1/2),(9615687695137442862049/200000000000000000)⟩,PopulationCertificates.Batch042.certificate852,CutLabelCertificates.Entropy000.certificate1,(262407316934197613/62500000000000000)⟩
theorem numericValid4381 : certificate4381.NumericValid := by decide +kernel
theorem sound4381 : certificate4381.Sound := rat_cut_cell_certificate_sound certificate4381 MergedCutBins.Batch365.valid4381 MergedCutBins.Batch365.sound4381 CutLabelCertificates.Entropy000.valid1 numericValid4381

def certificate4382 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4382,none,(1/2),(9615687695137442862049/200000000000000000)⟩,PopulationCertificates.Batch042.certificate852,CutLabelCertificates.Entropy000.certificate1,(262407316934197613/62500000000000000)⟩
theorem numericValid4382 : certificate4382.NumericValid := by decide +kernel
theorem sound4382 : certificate4382.Sound := rat_cut_cell_certificate_sound certificate4382 MergedCutBins.Batch365.valid4382 MergedCutBins.Batch365.sound4382 CutLabelCertificates.Entropy000.valid1 numericValid4382

def certificate4383 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4383,(some (690985546291581551/1000000000000000000)),(1/40),(9615687695137442862049/200000000000000000)⟩,PopulationCertificates.Batch042.certificate853,CutLabelCertificates.Entropy022.certificate445,(143737708694100737/1000000000000000000)⟩
theorem numericValid4383 : certificate4383.NumericValid := by decide +kernel
theorem sound4383 : certificate4383.Sound := rat_cut_cell_certificate_sound certificate4383 MergedCutBins.Batch365.valid4383 MergedCutBins.Batch365.sound4383 CutLabelCertificates.Entropy022.valid445 numericValid4383

def certificate4384 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4384,(some (1731815092875262851/500000000000000000)),(1/40),(9615687695137442862049/200000000000000000)⟩,PopulationCertificates.Batch042.certificate853,CutLabelCertificates.Entropy022.certificate446,(143737708694100737/1000000000000000000)⟩
theorem numericValid4384 : certificate4384.NumericValid := by decide +kernel
theorem sound4384 : certificate4384.Sound := rat_cut_cell_certificate_sound certificate4384 MergedCutBins.Batch365.valid4384 MergedCutBins.Batch365.sound4384 CutLabelCertificates.Entropy022.valid446 numericValid4384

def certificate4385 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4385,none,(1/40),(9615687695137442862049/200000000000000000)⟩,PopulationCertificates.Batch042.certificate853,CutLabelCertificates.Entropy022.certificate447,(143737708694100737/1000000000000000000)⟩
theorem numericValid4385 : certificate4385.NumericValid := by decide +kernel
theorem sound4385 : certificate4385.Sound := rat_cut_cell_certificate_sound certificate4385 MergedCutBins.Batch365.valid4385 MergedCutBins.Batch365.sound4385 CutLabelCertificates.Entropy022.valid447 numericValid4385

def certificate4386 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4386,(some (78355927085392651/100000000000000000)),(1/2),(20108024706910554078163/500000000000000000)⟩,PopulationCertificates.Batch042.certificate854,CutLabelCertificates.Entropy022.certificate448,(384338207369636977/1000000000000000000)⟩
theorem numericValid4386 : certificate4386.NumericValid := by decide +kernel
theorem sound4386 : certificate4386.Sound := rat_cut_cell_certificate_sound certificate4386 MergedCutBins.Batch365.valid4386 MergedCutBins.Batch365.sound4386 CutLabelCertificates.Entropy022.valid448 numericValid4386

def certificate4387 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4387,(some (127792047/100000000)),(1/2),(20108024706910554078163/500000000000000000)⟩,PopulationCertificates.Batch042.certificate854,CutLabelCertificates.Entropy022.certificate448,(384338207369636977/1000000000000000000)⟩
theorem numericValid4387 : certificate4387.NumericValid := by decide +kernel
theorem sound4387 : certificate4387.Sound := rat_cut_cell_certificate_sound certificate4387 MergedCutBins.Batch365.valid4387 MergedCutBins.Batch365.sound4387 CutLabelCertificates.Entropy022.valid448 numericValid4387

def certificate4388 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4388,(some (783698448536299053/125000000000000000)),(1/2),(20108024706910554078163/500000000000000000)⟩,PopulationCertificates.Batch042.certificate854,CutLabelCertificates.Entropy000.certificate1,(24025538855675017/62500000000000000)⟩
theorem numericValid4388 : certificate4388.NumericValid := by decide +kernel
theorem sound4388 : certificate4388.Sound := rat_cut_cell_certificate_sound certificate4388 MergedCutBins.Batch365.valid4388 MergedCutBins.Batch365.sound4388 CutLabelCertificates.Entropy000.valid1 numericValid4388

def certificate4389 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4389,(some 64),(1/2),(20108024706910554078163/500000000000000000)⟩,PopulationCertificates.Batch042.certificate854,CutLabelCertificates.Entropy000.certificate1,(24025538855675017/62500000000000000)⟩
theorem numericValid4389 : certificate4389.NumericValid := by decide +kernel
theorem sound4389 : certificate4389.Sound := rat_cut_cell_certificate_sound certificate4389 MergedCutBins.Batch365.valid4389 MergedCutBins.Batch365.sound4389 CutLabelCertificates.Entropy000.valid1 numericValid4389

def certificate4390 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4390,none,(1/2),(20108024706910554078163/500000000000000000)⟩,PopulationCertificates.Batch042.certificate854,CutLabelCertificates.Entropy000.certificate1,(24025538855675017/62500000000000000)⟩
theorem numericValid4390 : certificate4390.NumericValid := by decide +kernel
theorem sound4390 : certificate4390.Sound := rat_cut_cell_certificate_sound certificate4390 MergedCutBins.Batch365.valid4390 MergedCutBins.Batch365.sound4390 CutLabelCertificates.Entropy000.valid1 numericValid4390

def certificate4391 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch365.certificate4391,(some 64),(1/2),(20108024706910554078163/500000000000000000)⟩,PopulationCertificates.Batch042.certificate855,CutLabelCertificates.Entropy000.certificate1,(4297928419283098053/1000000000000000000)⟩
theorem numericValid4391 : certificate4391.NumericValid := by decide +kernel
theorem sound4391 : certificate4391.Sound := rat_cut_cell_certificate_sound certificate4391 MergedCutBins.Batch365.valid4391 MergedCutBins.Batch365.sound4391 CutLabelCertificates.Entropy000.valid1 numericValid4391

def certificates : List RatCutCellCertificate := [certificate4380,certificate4381,certificate4382,certificate4383,certificate4384,certificate4385,certificate4386,certificate4387,certificate4388,certificate4389,certificate4390,certificate4391]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4380,List.forall_mem_cons.mpr ⟨sound4381,List.forall_mem_cons.mpr ⟨sound4382,List.forall_mem_cons.mpr ⟨sound4383,List.forall_mem_cons.mpr ⟨sound4384,List.forall_mem_cons.mpr ⟨sound4385,List.forall_mem_cons.mpr ⟨sound4386,List.forall_mem_cons.mpr ⟨sound4387,List.forall_mem_cons.mpr ⟨sound4388,List.forall_mem_cons.mpr ⟨sound4389,List.forall_mem_cons.mpr ⟨sound4390,List.forall_mem_cons.mpr ⟨sound4391,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch365
