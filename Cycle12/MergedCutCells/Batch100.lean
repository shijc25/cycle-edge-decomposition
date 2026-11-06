import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy005
import Cycle12.MergedCutBins.Batch100
import Cycle12.PopulationCertificates.Batch010

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch100

def certificate1200 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1200,(some (6628873081542781369/1000000000000000000)),(1/2),(14383096214428220263/1000000000000000000)⟩,PopulationCertificates.Batch010.certificate205,CutLabelCertificates.Entropy000.certificate1,(772858681419540277/1000000000000000000)⟩
theorem numericValid1200 : certificate1200.NumericValid := by decide +kernel
theorem sound1200 : certificate1200.Sound := rat_cut_cell_certificate_sound certificate1200 MergedCutBins.Batch100.valid1200 MergedCutBins.Batch100.sound1200 CutLabelCertificates.Entropy000.valid1 numericValid1200

def certificate1201 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1201,(some (7107049175352550317/1000000000000000000)),(1/2),(14383096214428220263/1000000000000000000)⟩,PopulationCertificates.Batch010.certificate205,CutLabelCertificates.Entropy000.certificate1,(772858681419540277/1000000000000000000)⟩
theorem numericValid1201 : certificate1201.NumericValid := by decide +kernel
theorem sound1201 : certificate1201.Sound := rat_cut_cell_certificate_sound certificate1201 MergedCutBins.Batch100.valid1201 MergedCutBins.Batch100.sound1201 CutLabelCertificates.Entropy000.valid1 numericValid1201

def certificate1202 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1202,(some (7178119667106075821/1000000000000000000)),(1/2),(14383096214428220263/1000000000000000000)⟩,PopulationCertificates.Batch010.certificate205,CutLabelCertificates.Entropy000.certificate1,(772858681419540277/1000000000000000000)⟩
theorem numericValid1202 : certificate1202.NumericValid := by decide +kernel
theorem sound1202 : certificate1202.Sound := rat_cut_cell_certificate_sound certificate1202 MergedCutBins.Batch100.valid1202 MergedCutBins.Batch100.sound1202 CutLabelCertificates.Entropy000.valid1 numericValid1202

def certificate1203 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1203,none,(1/2),(14383096214428220263/1000000000000000000)⟩,PopulationCertificates.Batch010.certificate205,CutLabelCertificates.Entropy000.certificate1,(772858681419540277/1000000000000000000)⟩
theorem numericValid1203 : certificate1203.NumericValid := by decide +kernel
theorem sound1203 : certificate1203.Sound := rat_cut_cell_certificate_sound certificate1203 MergedCutBins.Batch100.valid1203 MergedCutBins.Batch100.sound1203 CutLabelCertificates.Entropy000.valid1 numericValid1203

def certificate1204 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1204,(some (920607525318642211/1000000000000000000)),(1/2),(7117676167741895767/500000000000000000)⟩,PopulationCertificates.Batch010.certificate206,CutLabelCertificates.Entropy005.certificate104,(291568168105613787/500000000000000000)⟩
theorem numericValid1204 : certificate1204.NumericValid := by decide +kernel
theorem sound1204 : certificate1204.Sound := rat_cut_cell_certificate_sound certificate1204 MergedCutBins.Batch100.valid1204 MergedCutBins.Batch100.sound1204 CutLabelCertificates.Entropy005.valid104 numericValid1204

def certificate1205 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1205,(some (1370659157315326243/1000000000000000000)),(1/2),(7117676167741895767/500000000000000000)⟩,PopulationCertificates.Batch010.certificate206,CutLabelCertificates.Entropy005.certificate104,(291568168105613787/500000000000000000)⟩
theorem numericValid1205 : certificate1205.NumericValid := by decide +kernel
theorem sound1205 : certificate1205.Sound := rat_cut_cell_certificate_sound certificate1205 MergedCutBins.Batch100.valid1205 MergedCutBins.Batch100.sound1205 CutLabelCertificates.Entropy005.valid104 numericValid1205

def certificate1206 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1206,(some (3356240798408458701/1000000000000000000)),(1/2),(7117676167741895767/500000000000000000)⟩,PopulationCertificates.Batch010.certificate206,CutLabelCertificates.Entropy005.certificate104,(291568168105613787/500000000000000000)⟩
theorem numericValid1206 : certificate1206.NumericValid := by decide +kernel
theorem sound1206 : certificate1206.Sound := rat_cut_cell_certificate_sound certificate1206 MergedCutBins.Batch100.valid1206 MergedCutBins.Batch100.sound1206 CutLabelCertificates.Entropy005.valid104 numericValid1206

def certificate1207 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1207,(some (3079122146917650457/500000000000000000)),(1/2),(7117676167741895767/500000000000000000)⟩,PopulationCertificates.Batch010.certificate206,CutLabelCertificates.Entropy005.certificate104,(291568168105613787/500000000000000000)⟩
theorem numericValid1207 : certificate1207.NumericValid := by decide +kernel
theorem sound1207 : certificate1207.Sound := rat_cut_cell_certificate_sound certificate1207 MergedCutBins.Batch100.valid1207 MergedCutBins.Batch100.sound1207 CutLabelCertificates.Entropy005.valid104 numericValid1207

def certificate1208 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1208,(some (1387852762392198711/200000000000000000)),(1/2),(7117676167741895767/500000000000000000)⟩,PopulationCertificates.Batch010.certificate206,CutLabelCertificates.Entropy005.certificate104,(291568168105613787/500000000000000000)⟩
theorem numericValid1208 : certificate1208.NumericValid := by decide +kernel
theorem sound1208 : certificate1208.Sound := rat_cut_cell_certificate_sound certificate1208 MergedCutBins.Batch100.valid1208 MergedCutBins.Batch100.sound1208 CutLabelCertificates.Entropy005.valid104 numericValid1208

def certificate1209 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1209,(some (3539371507290704763/500000000000000000)),(1/2),(7117676167741895767/500000000000000000)⟩,PopulationCertificates.Batch010.certificate206,CutLabelCertificates.Entropy005.certificate104,(291568168105613787/500000000000000000)⟩
theorem numericValid1209 : certificate1209.NumericValid := by decide +kernel
theorem sound1209 : certificate1209.Sound := rat_cut_cell_certificate_sound certificate1209 MergedCutBins.Batch100.valid1209 MergedCutBins.Batch100.sound1209 CutLabelCertificates.Entropy005.valid104 numericValid1209

def certificate1210 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1210,(some 64),(1/2),(7117676167741895767/500000000000000000)⟩,PopulationCertificates.Batch010.certificate206,CutLabelCertificates.Entropy005.certificate104,(291568168105613787/500000000000000000)⟩
theorem numericValid1210 : certificate1210.NumericValid := by decide +kernel
theorem sound1210 : certificate1210.Sound := rat_cut_cell_certificate_sound certificate1210 MergedCutBins.Batch100.valid1210 MergedCutBins.Batch100.sound1210 CutLabelCertificates.Entropy005.valid104 numericValid1210

def certificate1211 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch100.certificate1211,none,(1/2),(7117676167741895767/500000000000000000)⟩,PopulationCertificates.Batch010.certificate206,CutLabelCertificates.Entropy000.certificate1,(2164950388261713/1562500000000000)⟩
theorem numericValid1211 : certificate1211.NumericValid := by decide +kernel
theorem sound1211 : certificate1211.Sound := rat_cut_cell_certificate_sound certificate1211 MergedCutBins.Batch100.valid1211 MergedCutBins.Batch100.sound1211 CutLabelCertificates.Entropy000.valid1 numericValid1211

def certificates : List RatCutCellCertificate := [certificate1200,certificate1201,certificate1202,certificate1203,certificate1204,certificate1205,certificate1206,certificate1207,certificate1208,certificate1209,certificate1210,certificate1211]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1200,List.forall_mem_cons.mpr ⟨sound1201,List.forall_mem_cons.mpr ⟨sound1202,List.forall_mem_cons.mpr ⟨sound1203,List.forall_mem_cons.mpr ⟨sound1204,List.forall_mem_cons.mpr ⟨sound1205,List.forall_mem_cons.mpr ⟨sound1206,List.forall_mem_cons.mpr ⟨sound1207,List.forall_mem_cons.mpr ⟨sound1208,List.forall_mem_cons.mpr ⟨sound1209,List.forall_mem_cons.mpr ⟨sound1210,List.forall_mem_cons.mpr ⟨sound1211,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch100
