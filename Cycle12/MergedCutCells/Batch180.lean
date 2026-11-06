import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy009
import Cycle12.MergedCutBins.Batch180
import Cycle12.PopulationCertificates.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch180

def certificate2160 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2160,none,(1/2),(29508253281651770749/250000000000000000)⟩,PopulationCertificates.Batch019.certificate386,CutLabelCertificates.Entropy000.certificate1,(323618422076616571/1000000000000000000)⟩
theorem numericValid2160 : certificate2160.NumericValid := by decide +kernel
theorem sound2160 : certificate2160.Sound := rat_cut_cell_certificate_sound certificate2160 MergedCutBins.Batch180.valid2160 MergedCutBins.Batch180.sound2160 CutLabelCertificates.Entropy000.valid1 numericValid2160

def certificate2161 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2161,(some (49788730645417125709/1000000000000000000)),(1/2),(29508253281651770749/250000000000000000)⟩,PopulationCertificates.Batch019.certificate387,CutLabelCertificates.Entropy000.certificate1,(288623000607568891/125000000000000000)⟩
theorem numericValid2161 : certificate2161.NumericValid := by decide +kernel
theorem sound2161 : certificate2161.Sound := rat_cut_cell_certificate_sound certificate2161 MergedCutBins.Batch180.valid2161 MergedCutBins.Batch180.sound2161 CutLabelCertificates.Entropy000.valid1 numericValid2161

def certificate2162 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2162,(some (14595300578168558731/250000000000000000)),(1/2),(29508253281651770749/250000000000000000)⟩,PopulationCertificates.Batch019.certificate387,CutLabelCertificates.Entropy000.certificate1,(288623000607568891/125000000000000000)⟩
theorem numericValid2162 : certificate2162.NumericValid := by decide +kernel
theorem sound2162 : certificate2162.Sound := rat_cut_cell_certificate_sound certificate2162 MergedCutBins.Batch180.valid2162 MergedCutBins.Batch180.sound2162 CutLabelCertificates.Entropy000.valid1 numericValid2162

def certificate2163 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2163,(some (29482507167900488637/500000000000000000)),(1/2),(29508253281651770749/250000000000000000)⟩,PopulationCertificates.Batch019.certificate387,CutLabelCertificates.Entropy000.certificate1,(288623000607568891/125000000000000000)⟩
theorem numericValid2163 : certificate2163.NumericValid := by decide +kernel
theorem sound2163 : certificate2163.Sound := rat_cut_cell_certificate_sound certificate2163 MergedCutBins.Batch180.valid2163 MergedCutBins.Batch180.sound2163 CutLabelCertificates.Entropy000.valid1 numericValid2163

def certificate2164 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2164,none,(1/2),(29508253281651770749/250000000000000000)⟩,PopulationCertificates.Batch019.certificate387,CutLabelCertificates.Entropy000.certificate1,(288623000607568891/125000000000000000)⟩
theorem numericValid2164 : certificate2164.NumericValid := by decide +kernel
theorem sound2164 : certificate2164.Sound := rat_cut_cell_certificate_sound certificate2164 MergedCutBins.Batch180.valid2164 MergedCutBins.Batch180.sound2164 CutLabelCertificates.Entropy000.valid1 numericValid2164

def certificate2165 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2165,(some (351893768726869613/500000000000000000)),(1/2),(54990570427380060659/500000000000000000)⟩,PopulationCertificates.Batch019.certificate388,CutLabelCertificates.Entropy009.certificate195,(87391496010991421/250000000000000000)⟩
theorem numericValid2165 : certificate2165.NumericValid := by decide +kernel
theorem sound2165 : certificate2165.Sound := rat_cut_cell_certificate_sound certificate2165 MergedCutBins.Batch180.valid2165 MergedCutBins.Batch180.sound2165 CutLabelCertificates.Entropy009.valid195 numericValid2165

def certificate2166 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2166,(some (920701104805138633/1000000000000000000)),(1/2),(54990570427380060659/500000000000000000)⟩,PopulationCertificates.Batch019.certificate388,CutLabelCertificates.Entropy009.certificate195,(87391496010991421/250000000000000000)⟩
theorem numericValid2166 : certificate2166.NumericValid := by decide +kernel
theorem sound2166 : certificate2166.Sound := rat_cut_cell_certificate_sound certificate2166 MergedCutBins.Batch180.valid2166 MergedCutBins.Batch180.sound2166 CutLabelCertificates.Entropy009.valid195 numericValid2166

def certificate2167 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2167,(some (142365997/125000000)),(1/2),(54990570427380060659/500000000000000000)⟩,PopulationCertificates.Batch019.certificate388,CutLabelCertificates.Entropy009.certificate195,(87391496010991421/250000000000000000)⟩
theorem numericValid2167 : certificate2167.NumericValid := by decide +kernel
theorem sound2167 : certificate2167.Sound := rat_cut_cell_certificate_sound certificate2167 MergedCutBins.Batch180.valid2167 MergedCutBins.Batch180.sound2167 CutLabelCertificates.Entropy009.valid195 numericValid2167

def certificate2168 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2168,(some (1499222114227079241/1000000000000000000)),(1/2),(54990570427380060659/500000000000000000)⟩,PopulationCertificates.Batch019.certificate388,CutLabelCertificates.Entropy000.certificate1,(16581152643162423/50000000000000000)⟩
theorem numericValid2168 : certificate2168.NumericValid := by decide +kernel
theorem sound2168 : certificate2168.Sound := rat_cut_cell_certificate_sound certificate2168 MergedCutBins.Batch180.valid2168 MergedCutBins.Batch180.sound2168 CutLabelCertificates.Entropy000.valid1 numericValid2168

def certificate2169 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2169,(some (2583167108352489701/250000000000000000)),(1/2),(54990570427380060659/500000000000000000)⟩,PopulationCertificates.Batch019.certificate388,CutLabelCertificates.Entropy000.certificate1,(16581152643162423/50000000000000000)⟩
theorem numericValid2169 : certificate2169.NumericValid := by decide +kernel
theorem sound2169 : certificate2169.Sound := rat_cut_cell_certificate_sound certificate2169 MergedCutBins.Batch180.valid2169 MergedCutBins.Batch180.sound2169 CutLabelCertificates.Entropy000.valid1 numericValid2169

def certificate2170 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2170,(some (12443127746467582883/250000000000000000)),(1/2),(54990570427380060659/500000000000000000)⟩,PopulationCertificates.Batch019.certificate388,CutLabelCertificates.Entropy000.certificate1,(16581152643162423/50000000000000000)⟩
theorem numericValid2170 : certificate2170.NumericValid := by decide +kernel
theorem sound2170 : certificate2170.Sound := rat_cut_cell_certificate_sound certificate2170 MergedCutBins.Batch180.valid2170 MergedCutBins.Batch180.sound2170 CutLabelCertificates.Entropy000.valid1 numericValid2170

def certificate2171 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch180.certificate2171,(some (54435462249766942167/1000000000000000000)),(1/2),(54990570427380060659/500000000000000000)⟩,PopulationCertificates.Batch019.certificate388,CutLabelCertificates.Entropy000.certificate1,(16581152643162423/50000000000000000)⟩
theorem numericValid2171 : certificate2171.NumericValid := by decide +kernel
theorem sound2171 : certificate2171.Sound := rat_cut_cell_certificate_sound certificate2171 MergedCutBins.Batch180.valid2171 MergedCutBins.Batch180.sound2171 CutLabelCertificates.Entropy000.valid1 numericValid2171

def certificates : List RatCutCellCertificate := [certificate2160,certificate2161,certificate2162,certificate2163,certificate2164,certificate2165,certificate2166,certificate2167,certificate2168,certificate2169,certificate2170,certificate2171]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2160,List.forall_mem_cons.mpr ⟨sound2161,List.forall_mem_cons.mpr ⟨sound2162,List.forall_mem_cons.mpr ⟨sound2163,List.forall_mem_cons.mpr ⟨sound2164,List.forall_mem_cons.mpr ⟨sound2165,List.forall_mem_cons.mpr ⟨sound2166,List.forall_mem_cons.mpr ⟨sound2167,List.forall_mem_cons.mpr ⟨sound2168,List.forall_mem_cons.mpr ⟨sound2169,List.forall_mem_cons.mpr ⟨sound2170,List.forall_mem_cons.mpr ⟨sound2171,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch180
