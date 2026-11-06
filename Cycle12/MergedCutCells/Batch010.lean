import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.MergedCutBins.Batch010
import Cycle12.PopulationCertificates.Batch001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch010

def certificate120 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate120,(some 64),(1/2),(195805185359399352263/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate31,CutLabelCertificates.Entropy000.certificate1,(67040622337005957/200000000000000000)⟩
theorem numericValid120 : certificate120.NumericValid := by decide +kernel
theorem sound120 : certificate120.Sound := rat_cut_cell_certificate_sound certificate120 MergedCutBins.Batch010.valid120 MergedCutBins.Batch010.sound120 CutLabelCertificates.Entropy000.valid1 numericValid120

def certificate121 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate121,none,(1/2),(195805185359399352263/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate31,CutLabelCertificates.Entropy000.certificate1,(67040622337005957/200000000000000000)⟩
theorem numericValid121 : certificate121.NumericValid := by decide +kernel
theorem sound121 : certificate121.Sound := rat_cut_cell_certificate_sound certificate121 MergedCutBins.Batch010.valid121 MergedCutBins.Batch010.sound121 CutLabelCertificates.Entropy000.valid1 numericValid121

def certificate122 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate122,(some (642964773521171531/1000000000000000000)),(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate32,CutLabelCertificates.Entropy000.certificate17,(229067220900134253/1000000000000000000)⟩
theorem numericValid122 : certificate122.NumericValid := by decide +kernel
theorem sound122 : certificate122.Sound := rat_cut_cell_certificate_sound certificate122 MergedCutBins.Batch010.valid122 MergedCutBins.Batch010.sound122 CutLabelCertificates.Entropy000.valid17 numericValid122

def certificate123 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate123,(some (211488065371512657/200000000000000000)),(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate32,CutLabelCertificates.Entropy000.certificate17,(229067220900134253/1000000000000000000)⟩
theorem numericValid123 : certificate123.NumericValid := by decide +kernel
theorem sound123 : certificate123.Sound := rat_cut_cell_certificate_sound certificate123 MergedCutBins.Batch010.valid123 MergedCutBins.Batch010.sound123 CutLabelCertificates.Entropy000.valid17 numericValid123

def certificate124 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate124,(some (1208543893/1000000000)),(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate32,CutLabelCertificates.Entropy000.certificate17,(229067220900134253/1000000000000000000)⟩
theorem numericValid124 : certificate124.NumericValid := by decide +kernel
theorem sound124 : certificate124.Sound := rat_cut_cell_certificate_sound certificate124 MergedCutBins.Batch010.valid124 MergedCutBins.Batch010.sound124 CutLabelCertificates.Entropy000.valid17 numericValid124

def certificate125 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate125,(some (1902028070030364129/1000000000000000000)),(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate32,CutLabelCertificates.Entropy000.certificate1,(53872450301677121/250000000000000000)⟩
theorem numericValid125 : certificate125.NumericValid := by decide +kernel
theorem sound125 : certificate125.Sound := rat_cut_cell_certificate_sound certificate125 MergedCutBins.Batch010.valid125 MergedCutBins.Batch010.sound125 CutLabelCertificates.Entropy000.valid1 numericValid125

def certificate126 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate126,(some (25787951989525619557/1000000000000000000)),(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate32,CutLabelCertificates.Entropy000.certificate1,(53872450301677121/250000000000000000)⟩
theorem numericValid126 : certificate126.NumericValid := by decide +kernel
theorem sound126 : certificate126.Sound := rat_cut_cell_certificate_sound certificate126 MergedCutBins.Batch010.valid126 MergedCutBins.Batch010.sound126 CutLabelCertificates.Entropy000.valid1 numericValid126

def certificate127 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate127,(some 64),(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate32,CutLabelCertificates.Entropy000.certificate1,(53872450301677121/250000000000000000)⟩
theorem numericValid127 : certificate127.NumericValid := by decide +kernel
theorem sound127 : certificate127.Sound := rat_cut_cell_certificate_sound certificate127 MergedCutBins.Batch010.valid127 MergedCutBins.Batch010.sound127 CutLabelCertificates.Entropy000.valid1 numericValid127

def certificate128 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate128,none,(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate32,CutLabelCertificates.Entropy000.certificate1,(53872450301677121/250000000000000000)⟩
theorem numericValid128 : certificate128.NumericValid := by decide +kernel
theorem sound128 : certificate128.Sound := rat_cut_cell_certificate_sound certificate128 MergedCutBins.Batch010.valid128 MergedCutBins.Batch010.sound128 CutLabelCertificates.Entropy000.valid1 numericValid128

def certificate129 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate129,(some 64),(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate33,CutLabelCertificates.Entropy000.certificate1,(369026669387329231/1000000000000000000)⟩
theorem numericValid129 : certificate129.NumericValid := by decide +kernel
theorem sound129 : certificate129.Sound := rat_cut_cell_certificate_sound certificate129 MergedCutBins.Batch010.valid129 MergedCutBins.Batch010.sound129 CutLabelCertificates.Entropy000.valid1 numericValid129

def certificate130 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate130,none,(1/2),(173833819108730224839/1000000000000000000)⟩,PopulationCertificates.Batch001.certificate33,CutLabelCertificates.Entropy000.certificate1,(369026669387329231/1000000000000000000)⟩
theorem numericValid130 : certificate130.NumericValid := by decide +kernel
theorem sound130 : certificate130.Sound := rat_cut_cell_certificate_sound certificate130 MergedCutBins.Batch010.valid130 MergedCutBins.Batch010.sound130 CutLabelCertificates.Entropy000.valid1 numericValid130

def certificate131 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch010.certificate131,(some (650180900073611281/1000000000000000000)),(1/2),(7764035718697559137/50000000000000000)⟩,PopulationCertificates.Batch001.certificate34,CutLabelCertificates.Entropy000.certificate18,(45185238917861759/200000000000000000)⟩
theorem numericValid131 : certificate131.NumericValid := by decide +kernel
theorem sound131 : certificate131.Sound := rat_cut_cell_certificate_sound certificate131 MergedCutBins.Batch010.valid131 MergedCutBins.Batch010.sound131 CutLabelCertificates.Entropy000.valid18 numericValid131

def certificates : List RatCutCellCertificate := [certificate120,certificate121,certificate122,certificate123,certificate124,certificate125,certificate126,certificate127,certificate128,certificate129,certificate130,certificate131]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound120,List.forall_mem_cons.mpr ⟨sound121,List.forall_mem_cons.mpr ⟨sound122,List.forall_mem_cons.mpr ⟨sound123,List.forall_mem_cons.mpr ⟨sound124,List.forall_mem_cons.mpr ⟨sound125,List.forall_mem_cons.mpr ⟨sound126,List.forall_mem_cons.mpr ⟨sound127,List.forall_mem_cons.mpr ⟨sound128,List.forall_mem_cons.mpr ⟨sound129,List.forall_mem_cons.mpr ⟨sound130,List.forall_mem_cons.mpr ⟨sound131,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch010
