import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy009
import Cycle12.MergedCutBins.Batch176
import Cycle12.PopulationCertificates.Batch018
import Cycle12.PopulationCertificates.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch176

def certificate2112 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2112,(some (14868330521212450049/250000000000000000)),(1/2),(40079938802876286037/250000000000000000)⟩,PopulationCertificates.Batch018.certificate378,CutLabelCertificates.Entropy000.certificate1,(75396907248519747/250000000000000000)⟩
theorem numericValid2112 : certificate2112.NumericValid := by decide +kernel
theorem sound2112 : certificate2112.Sound := rat_cut_cell_certificate_sound certificate2112 MergedCutBins.Batch176.valid2112 MergedCutBins.Batch176.sound2112 CutLabelCertificates.Entropy000.valid1 numericValid2112

def certificate2113 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2113,(some 64),(1/2),(40079938802876286037/250000000000000000)⟩,PopulationCertificates.Batch018.certificate378,CutLabelCertificates.Entropy000.certificate1,(75396907248519747/250000000000000000)⟩
theorem numericValid2113 : certificate2113.NumericValid := by decide +kernel
theorem sound2113 : certificate2113.Sound := rat_cut_cell_certificate_sound certificate2113 MergedCutBins.Batch176.valid2113 MergedCutBins.Batch176.sound2113 CutLabelCertificates.Entropy000.valid1 numericValid2113

def certificate2114 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2114,none,(1/2),(40079938802876286037/250000000000000000)⟩,PopulationCertificates.Batch018.certificate378,CutLabelCertificates.Entropy000.certificate1,(75396907248519747/250000000000000000)⟩
theorem numericValid2114 : certificate2114.NumericValid := by decide +kernel
theorem sound2114 : certificate2114.Sound := rat_cut_cell_certificate_sound certificate2114 MergedCutBins.Batch176.valid2114 MergedCutBins.Batch176.sound2114 CutLabelCertificates.Entropy000.valid1 numericValid2114

def certificate2115 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2115,(some 64),(1/2),(40079938802876286037/250000000000000000)⟩,PopulationCertificates.Batch018.certificate379,CutLabelCertificates.Entropy000.certificate1,(1061976940717695947/500000000000000000)⟩
theorem numericValid2115 : certificate2115.NumericValid := by decide +kernel
theorem sound2115 : certificate2115.Sound := rat_cut_cell_certificate_sound certificate2115 MergedCutBins.Batch176.valid2115 MergedCutBins.Batch176.sound2115 CutLabelCertificates.Entropy000.valid1 numericValid2115

def certificate2116 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2116,none,(1/2),(40079938802876286037/250000000000000000)⟩,PopulationCertificates.Batch018.certificate379,CutLabelCertificates.Entropy000.certificate1,(1061976940717695947/500000000000000000)⟩
theorem numericValid2116 : certificate2116.NumericValid := by decide +kernel
theorem sound2116 : certificate2116.Sound := rat_cut_cell_certificate_sound certificate2116 MergedCutBins.Batch176.valid2116 MergedCutBins.Batch176.sound2116 CutLabelCertificates.Entropy000.valid1 numericValid2116

def certificate2117 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2117,(some (676556418166945703/1000000000000000000)),(1/2),(147929067133845158561/1000000000000000000)⟩,PopulationCertificates.Batch019.certificate380,CutLabelCertificates.Entropy009.certificate191,(321623980159204659/1000000000000000000)⟩
theorem numericValid2117 : certificate2117.NumericValid := by decide +kernel
theorem sound2117 : certificate2117.Sound := rat_cut_cell_certificate_sound certificate2117 MergedCutBins.Batch176.valid2117 MergedCutBins.Batch176.sound2117 CutLabelCertificates.Entropy009.valid191 numericValid2117

def certificate2118 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2118,(some (37581087602624771/40000000000000000)),(1/2),(147929067133845158561/1000000000000000000)⟩,PopulationCertificates.Batch019.certificate380,CutLabelCertificates.Entropy009.certificate191,(321623980159204659/1000000000000000000)⟩
theorem numericValid2118 : certificate2118.NumericValid := by decide +kernel
theorem sound2118 : certificate2118.Sound := rat_cut_cell_certificate_sound certificate2118 MergedCutBins.Batch176.valid2118 MergedCutBins.Batch176.sound2118 CutLabelCertificates.Entropy009.valid191 numericValid2118

def certificate2119 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2119,(some (46081389/40000000)),(1/2),(147929067133845158561/1000000000000000000)⟩,PopulationCertificates.Batch019.certificate380,CutLabelCertificates.Entropy009.certificate191,(321623980159204659/1000000000000000000)⟩
theorem numericValid2119 : certificate2119.NumericValid := by decide +kernel
theorem sound2119 : certificate2119.Sound := rat_cut_cell_certificate_sound certificate2119 MergedCutBins.Batch176.valid2119 MergedCutBins.Batch176.sound2119 CutLabelCertificates.Entropy009.valid191 numericValid2119

def certificate2120 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2120,(some (1169444394141894231/1000000000000000000)),(1/2),(147929067133845158561/1000000000000000000)⟩,PopulationCertificates.Batch019.certificate380,CutLabelCertificates.Entropy000.certificate1,(302075743649292669/1000000000000000000)⟩
theorem numericValid2120 : certificate2120.NumericValid := by decide +kernel
theorem sound2120 : certificate2120.Sound := rat_cut_cell_certificate_sound certificate2120 MergedCutBins.Batch176.valid2120 MergedCutBins.Batch176.sound2120 CutLabelCertificates.Entropy000.valid1 numericValid2120

def certificate2121 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2121,(some (1607916668785843771/1000000000000000000)),(1/2),(147929067133845158561/1000000000000000000)⟩,PopulationCertificates.Batch019.certificate380,CutLabelCertificates.Entropy000.certificate1,(302075743649292669/1000000000000000000)⟩
theorem numericValid2121 : certificate2121.NumericValid := by decide +kernel
theorem sound2121 : certificate2121.Sound := rat_cut_cell_certificate_sound certificate2121 MergedCutBins.Batch176.valid2121 MergedCutBins.Batch176.sound2121 CutLabelCertificates.Entropy000.valid1 numericValid2121

def certificate2122 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2122,(some (3809202151733460673/250000000000000000)),(1/2),(147929067133845158561/1000000000000000000)⟩,PopulationCertificates.Batch019.certificate380,CutLabelCertificates.Entropy000.certificate1,(302075743649292669/1000000000000000000)⟩
theorem numericValid2122 : certificate2122.NumericValid := by decide +kernel
theorem sound2122 : certificate2122.Sound := rat_cut_cell_certificate_sound certificate2122 MergedCutBins.Batch176.valid2122 MergedCutBins.Batch176.sound2122 CutLabelCertificates.Entropy000.valid1 numericValid2122

def certificate2123 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch176.certificate2123,(some 64),(1/2),(147929067133845158561/1000000000000000000)⟩,PopulationCertificates.Batch019.certificate380,CutLabelCertificates.Entropy000.certificate1,(302075743649292669/1000000000000000000)⟩
theorem numericValid2123 : certificate2123.NumericValid := by decide +kernel
theorem sound2123 : certificate2123.Sound := rat_cut_cell_certificate_sound certificate2123 MergedCutBins.Batch176.valid2123 MergedCutBins.Batch176.sound2123 CutLabelCertificates.Entropy000.valid1 numericValid2123

def certificates : List RatCutCellCertificate := [certificate2112,certificate2113,certificate2114,certificate2115,certificate2116,certificate2117,certificate2118,certificate2119,certificate2120,certificate2121,certificate2122,certificate2123]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2112,List.forall_mem_cons.mpr ⟨sound2113,List.forall_mem_cons.mpr ⟨sound2114,List.forall_mem_cons.mpr ⟨sound2115,List.forall_mem_cons.mpr ⟨sound2116,List.forall_mem_cons.mpr ⟨sound2117,List.forall_mem_cons.mpr ⟨sound2118,List.forall_mem_cons.mpr ⟨sound2119,List.forall_mem_cons.mpr ⟨sound2120,List.forall_mem_cons.mpr ⟨sound2121,List.forall_mem_cons.mpr ⟨sound2122,List.forall_mem_cons.mpr ⟨sound2123,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch176
