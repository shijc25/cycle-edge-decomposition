import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy006
import Cycle12.MergedCutBins.Batch120
import Cycle12.PopulationCertificates.Batch012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch120

def certificate1440 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1440,(some 64),(1/2),(368004969325543779/31250000000000000)⟩,PopulationCertificates.Batch012.certificate246,CutLabelCertificates.Entropy006.certificate124,(3190659987223477/3906250000000000)⟩
theorem numericValid1440 : certificate1440.NumericValid := by decide +kernel
theorem sound1440 : certificate1440.Sound := rat_cut_cell_certificate_sound certificate1440 MergedCutBins.Batch120.valid1440 MergedCutBins.Batch120.sound1440 CutLabelCertificates.Entropy006.valid124 numericValid1440

def certificate1441 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1441,none,(1/2),(368004969325543779/31250000000000000)⟩,PopulationCertificates.Batch012.certificate246,CutLabelCertificates.Entropy000.certificate1,(1897718095599499641/1000000000000000000)⟩
theorem numericValid1441 : certificate1441.NumericValid := by decide +kernel
theorem sound1441 : certificate1441.Sound := rat_cut_cell_certificate_sound certificate1441 MergedCutBins.Batch120.valid1441 MergedCutBins.Batch120.sound1441 CutLabelCertificates.Entropy000.valid1 numericValid1441

def certificate1442 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1442,(some (2763058751942193919/500000000000000000)),(1/2),(368004969325543779/31250000000000000)⟩,PopulationCertificates.Batch012.certificate247,CutLabelCertificates.Entropy000.certificate1,(931607308798583453/1000000000000000000)⟩
theorem numericValid1442 : certificate1442.NumericValid := by decide +kernel
theorem sound1442 : certificate1442.Sound := rat_cut_cell_certificate_sound certificate1442 MergedCutBins.Batch120.valid1442 MergedCutBins.Batch120.sound1442 CutLabelCertificates.Entropy000.valid1 numericValid1442

def certificate1443 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1443,(some (5808005034616017409/1000000000000000000)),(1/2),(368004969325543779/31250000000000000)⟩,PopulationCertificates.Batch012.certificate247,CutLabelCertificates.Entropy000.certificate1,(931607308798583453/1000000000000000000)⟩
theorem numericValid1443 : certificate1443.NumericValid := by decide +kernel
theorem sound1443 : certificate1443.Sound := rat_cut_cell_certificate_sound certificate1443 MergedCutBins.Batch120.valid1443 MergedCutBins.Batch120.sound1443 CutLabelCertificates.Entropy000.valid1 numericValid1443

def certificate1444 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1444,(some (366630317810136099/62500000000000000)),(1/2),(368004969325543779/31250000000000000)⟩,PopulationCertificates.Batch012.certificate247,CutLabelCertificates.Entropy000.certificate1,(931607308798583453/1000000000000000000)⟩
theorem numericValid1444 : certificate1444.NumericValid := by decide +kernel
theorem sound1444 : certificate1444.Sound := rat_cut_cell_certificate_sound certificate1444 MergedCutBins.Batch120.valid1444 MergedCutBins.Batch120.sound1444 CutLabelCertificates.Entropy000.valid1 numericValid1444

def certificate1445 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1445,none,(1/2),(368004969325543779/31250000000000000)⟩,PopulationCertificates.Batch012.certificate247,CutLabelCertificates.Entropy000.certificate1,(931607308798583453/1000000000000000000)⟩
theorem numericValid1445 : certificate1445.NumericValid := by decide +kernel
theorem sound1445 : certificate1445.Sound := rat_cut_cell_certificate_sound certificate1445 MergedCutBins.Batch120.valid1445 MergedCutBins.Batch120.sound1445 CutLabelCertificates.Entropy000.valid1 numericValid1445

def certificate1446 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1446,(some (266499314423326043/200000000000000000)),(1/2),(2343874737817172533/200000000000000000)⟩,PopulationCertificates.Batch012.certificate248,CutLabelCertificates.Entropy006.certificate125,(166701729060973669/200000000000000000)⟩
theorem numericValid1446 : certificate1446.NumericValid := by decide +kernel
theorem sound1446 : certificate1446.Sound := rat_cut_cell_certificate_sound certificate1446 MergedCutBins.Batch120.valid1446 MergedCutBins.Batch120.sound1446 CutLabelCertificates.Entropy006.valid125 numericValid1446

def certificate1447 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1447,(some (1506568056689173993/500000000000000000)),(1/2),(2343874737817172533/200000000000000000)⟩,PopulationCertificates.Batch012.certificate248,CutLabelCertificates.Entropy006.certificate125,(166701729060973669/200000000000000000)⟩
theorem numericValid1447 : certificate1447.NumericValid := by decide +kernel
theorem sound1447 : certificate1447.Sound := rat_cut_cell_certificate_sound certificate1447 MergedCutBins.Batch120.valid1447 MergedCutBins.Batch120.sound1447 CutLabelCertificates.Entropy006.valid125 numericValid1447

def certificate1448 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1448,(some (1276414031759378767/250000000000000000)),(1/2),(2343874737817172533/200000000000000000)⟩,PopulationCertificates.Batch012.certificate248,CutLabelCertificates.Entropy006.certificate125,(166701729060973669/200000000000000000)⟩
theorem numericValid1448 : certificate1448.NumericValid := by decide +kernel
theorem sound1448 : certificate1448.Sound := rat_cut_cell_certificate_sound certificate1448 MergedCutBins.Batch120.valid1448 MergedCutBins.Batch120.sound1448 CutLabelCertificates.Entropy006.valid125 numericValid1448

def certificate1449 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1449,(some (1424054732473396967/250000000000000000)),(1/2),(2343874737817172533/200000000000000000)⟩,PopulationCertificates.Batch012.certificate248,CutLabelCertificates.Entropy006.certificate125,(166701729060973669/200000000000000000)⟩
theorem numericValid1449 : certificate1449.NumericValid := by decide +kernel
theorem sound1449 : certificate1449.Sound := rat_cut_cell_certificate_sound certificate1449 MergedCutBins.Batch120.valid1449 MergedCutBins.Batch120.sound1449 CutLabelCertificates.Entropy006.valid125 numericValid1449

def certificate1450 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1450,(some (1162142586076889797/200000000000000000)),(1/2),(2343874737817172533/200000000000000000)⟩,PopulationCertificates.Batch012.certificate248,CutLabelCertificates.Entropy006.certificate125,(166701729060973669/200000000000000000)⟩
theorem numericValid1450 : certificate1450.NumericValid := by decide +kernel
theorem sound1450 : certificate1450.Sound := rat_cut_cell_certificate_sound certificate1450 MergedCutBins.Batch120.valid1450 MergedCutBins.Batch120.sound1450 CutLabelCertificates.Entropy006.valid125 numericValid1450

def certificate1451 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch120.certificate1451,(some 64),(1/2),(2343874737817172533/200000000000000000)⟩,PopulationCertificates.Batch012.certificate248,CutLabelCertificates.Entropy006.certificate125,(166701729060973669/200000000000000000)⟩
theorem numericValid1451 : certificate1451.NumericValid := by decide +kernel
theorem sound1451 : certificate1451.Sound := rat_cut_cell_certificate_sound certificate1451 MergedCutBins.Batch120.valid1451 MergedCutBins.Batch120.sound1451 CutLabelCertificates.Entropy006.valid125 numericValid1451

def certificates : List RatCutCellCertificate := [certificate1440,certificate1441,certificate1442,certificate1443,certificate1444,certificate1445,certificate1446,certificate1447,certificate1448,certificate1449,certificate1450,certificate1451]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1440,List.forall_mem_cons.mpr ⟨sound1441,List.forall_mem_cons.mpr ⟨sound1442,List.forall_mem_cons.mpr ⟨sound1443,List.forall_mem_cons.mpr ⟨sound1444,List.forall_mem_cons.mpr ⟨sound1445,List.forall_mem_cons.mpr ⟨sound1446,List.forall_mem_cons.mpr ⟨sound1447,List.forall_mem_cons.mpr ⟨sound1448,List.forall_mem_cons.mpr ⟨sound1449,List.forall_mem_cons.mpr ⟨sound1450,List.forall_mem_cons.mpr ⟨sound1451,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch120
