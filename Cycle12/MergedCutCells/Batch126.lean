import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy006
import Cycle12.MergedCutBins.Batch126
import Cycle12.PopulationCertificates.Batch012
import Cycle12.PopulationCertificates.Batch013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch126

def certificate1512 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1512,(some (5675810807006000941/1000000000000000000)),(1/2),(11386162437257547639/1000000000000000000)⟩,PopulationCertificates.Batch012.certificate259,CutLabelCertificates.Entropy000.certificate1,(228032116474001041/250000000000000000)⟩
theorem numericValid1512 : certificate1512.NumericValid := by decide +kernel
theorem sound1512 : certificate1512.Sound := rat_cut_cell_certificate_sound certificate1512 MergedCutBins.Batch126.valid1512 MergedCutBins.Batch126.sound1512 CutLabelCertificates.Entropy000.valid1 numericValid1512

def certificate1513 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1513,none,(1/2),(11386162437257547639/1000000000000000000)⟩,PopulationCertificates.Batch012.certificate259,CutLabelCertificates.Entropy000.certificate1,(228032116474001041/250000000000000000)⟩
theorem numericValid1513 : certificate1513.NumericValid := by decide +kernel
theorem sound1513 : certificate1513.Sound := rat_cut_cell_certificate_sound certificate1513 MergedCutBins.Batch126.valid1513 MergedCutBins.Batch126.sound1513 CutLabelCertificates.Entropy000.valid1 numericValid1513

def certificate1514 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1514,(some (1290749874291714133/1000000000000000000)),(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate260,CutLabelCertificates.Entropy006.certificate131,(89377670384855449/100000000000000000)⟩
theorem numericValid1514 : certificate1514.NumericValid := by decide +kernel
theorem sound1514 : certificate1514.Sound := rat_cut_cell_certificate_sound certificate1514 MergedCutBins.Batch126.valid1514 MergedCutBins.Batch126.sound1514 CutLabelCertificates.Entropy006.valid131 numericValid1514

def certificate1515 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1515,(some (560969490821295313/200000000000000000)),(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate260,CutLabelCertificates.Entropy006.certificate131,(89377670384855449/100000000000000000)⟩
theorem numericValid1515 : certificate1515.NumericValid := by decide +kernel
theorem sound1515 : certificate1515.Sound := rat_cut_cell_certificate_sound certificate1515 MergedCutBins.Batch126.valid1515 MergedCutBins.Batch126.sound1515 CutLabelCertificates.Entropy006.valid131 numericValid1515

def certificate1516 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1516,(some (4848247749263962729/1000000000000000000)),(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate260,CutLabelCertificates.Entropy006.certificate131,(89377670384855449/100000000000000000)⟩
theorem numericValid1516 : certificate1516.NumericValid := by decide +kernel
theorem sound1516 : certificate1516.Sound := rat_cut_cell_certificate_sound certificate1516 MergedCutBins.Batch126.valid1516 MergedCutBins.Batch126.sound1516 CutLabelCertificates.Entropy006.valid131 numericValid1516

def certificate1517 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1517,(some (1365781729037904797/250000000000000000)),(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate260,CutLabelCertificates.Entropy006.certificate131,(89377670384855449/100000000000000000)⟩
theorem numericValid1517 : certificate1517.NumericValid := by decide +kernel
theorem sound1517 : certificate1517.Sound := rat_cut_cell_certificate_sound certificate1517 MergedCutBins.Batch126.valid1517 MergedCutBins.Batch126.sound1517 CutLabelCertificates.Entropy006.valid131 numericValid1517

def certificate1518 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1518,(some (2814332562418964701/500000000000000000)),(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate260,CutLabelCertificates.Entropy006.certificate131,(89377670384855449/100000000000000000)⟩
theorem numericValid1518 : certificate1518.NumericValid := by decide +kernel
theorem sound1518 : certificate1518.Sound := rat_cut_cell_certificate_sound certificate1518 MergedCutBins.Batch126.valid1518 MergedCutBins.Batch126.sound1518 CutLabelCertificates.Entropy006.valid131 numericValid1518

def certificate1519 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1519,(some 64),(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate260,CutLabelCertificates.Entropy006.certificate131,(89377670384855449/100000000000000000)⟩
theorem numericValid1519 : certificate1519.NumericValid := by decide +kernel
theorem sound1519 : certificate1519.Sound := rat_cut_cell_certificate_sound certificate1519 MergedCutBins.Batch126.valid1519 MergedCutBins.Batch126.sound1519 CutLabelCertificates.Entropy006.valid131 numericValid1519

def certificate1520 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1520,none,(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate260,CutLabelCertificates.Entropy000.certificate1,(1019023435684070647/500000000000000000)⟩
theorem numericValid1520 : certificate1520.NumericValid := by decide +kernel
theorem sound1520 : certificate1520.Sound := rat_cut_cell_certificate_sound certificate1520 MergedCutBins.Batch126.valid1520 MergedCutBins.Batch126.sound1520 CutLabelCertificates.Entropy000.valid1 numericValid1520

def certificate1521 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1521,(some (5287978870260534287/1000000000000000000)),(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate261,CutLabelCertificates.Entropy000.certificate1,(889875822348817769/1000000000000000000)⟩
theorem numericValid1521 : certificate1521.NumericValid := by decide +kernel
theorem sound1521 : certificate1521.Sound := rat_cut_cell_certificate_sound certificate1521 MergedCutBins.Batch126.valid1521 MergedCutBins.Batch126.sound1521 CutLabelCertificates.Entropy000.valid1 numericValid1521

def certificate1522 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1522,(some (28066480633669341/5000000000000000)),(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate261,CutLabelCertificates.Entropy000.certificate1,(889875822348817769/1000000000000000000)⟩
theorem numericValid1522 : certificate1522.NumericValid := by decide +kernel
theorem sound1522 : certificate1522.Sound := rat_cut_cell_certificate_sound certificate1522 MergedCutBins.Batch126.valid1522 MergedCutBins.Batch126.sound1522 CutLabelCertificates.Entropy000.valid1 numericValid1522

def certificate1523 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch126.certificate1523,none,(1/2),(2832962528370347873/250000000000000000)⟩,PopulationCertificates.Batch013.certificate261,CutLabelCertificates.Entropy000.certificate1,(889875822348817769/1000000000000000000)⟩
theorem numericValid1523 : certificate1523.NumericValid := by decide +kernel
theorem sound1523 : certificate1523.Sound := rat_cut_cell_certificate_sound certificate1523 MergedCutBins.Batch126.valid1523 MergedCutBins.Batch126.sound1523 CutLabelCertificates.Entropy000.valid1 numericValid1523

def certificates : List RatCutCellCertificate := [certificate1512,certificate1513,certificate1514,certificate1515,certificate1516,certificate1517,certificate1518,certificate1519,certificate1520,certificate1521,certificate1522,certificate1523]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1512,List.forall_mem_cons.mpr ⟨sound1513,List.forall_mem_cons.mpr ⟨sound1514,List.forall_mem_cons.mpr ⟨sound1515,List.forall_mem_cons.mpr ⟨sound1516,List.forall_mem_cons.mpr ⟨sound1517,List.forall_mem_cons.mpr ⟨sound1518,List.forall_mem_cons.mpr ⟨sound1519,List.forall_mem_cons.mpr ⟨sound1520,List.forall_mem_cons.mpr ⟨sound1521,List.forall_mem_cons.mpr ⟨sound1522,List.forall_mem_cons.mpr ⟨sound1523,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch126
