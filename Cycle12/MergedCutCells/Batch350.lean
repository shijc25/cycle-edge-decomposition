import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy020
import Cycle12.MergedCutBins.Batch350
import Cycle12.PopulationCertificates.Batch040

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch350

def certificate4200 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4200,none,(1/2),(48027929815997146389/200000000000000000)⟩,PopulationCertificates.Batch040.certificate803,CutLabelCertificates.Entropy000.certificate1,(10679967677515771327/1000000000000000000)⟩
theorem numericValid4200 : certificate4200.NumericValid := by decide +kernel
theorem sound4200 : certificate4200.Sound := rat_cut_cell_certificate_sound certificate4200 MergedCutBins.Batch350.valid4200 MergedCutBins.Batch350.sound4200 CutLabelCertificates.Entropy000.valid1 numericValid4200

def certificate4201 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4201,(some (77370678758048207/100000000000000000)),(1/2),(117761590184174009281/500000000000000000)⟩,PopulationCertificates.Batch040.certificate804,CutLabelCertificates.Entropy020.certificate403,(305936374597833691/250000000000000000)⟩
theorem numericValid4201 : certificate4201.NumericValid := by decide +kernel
theorem sound4201 : certificate4201.Sound := rat_cut_cell_certificate_sound certificate4201 MergedCutBins.Batch350.valid4201 MergedCutBins.Batch350.sound4201 CutLabelCertificates.Entropy020.valid403 numericValid4201

def certificate4202 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4202,(some (1107682883/1000000000)),(1/2),(117761590184174009281/500000000000000000)⟩,PopulationCertificates.Batch040.certificate804,CutLabelCertificates.Entropy020.certificate403,(305936374597833691/250000000000000000)⟩
theorem numericValid4202 : certificate4202.NumericValid := by decide +kernel
theorem sound4202 : certificate4202.Sound := rat_cut_cell_certificate_sound certificate4202 MergedCutBins.Batch350.valid4202 MergedCutBins.Batch350.sound4202 CutLabelCertificates.Entropy020.valid403 numericValid4202

def certificate4203 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4203,(some (281118113330817939/200000000000000000)),(1/2),(117761590184174009281/500000000000000000)⟩,PopulationCertificates.Batch040.certificate804,CutLabelCertificates.Entropy000.certificate1,(1210886517218607731/1000000000000000000)⟩
theorem numericValid4203 : certificate4203.NumericValid := by decide +kernel
theorem sound4203 : certificate4203.Sound := rat_cut_cell_certificate_sound certificate4203 MergedCutBins.Batch350.valid4203 MergedCutBins.Batch350.sound4203 CutLabelCertificates.Entropy000.valid1 numericValid4203

def certificate4204 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4204,(some (15932137166549552733/1000000000000000000)),(1/2),(117761590184174009281/500000000000000000)⟩,PopulationCertificates.Batch040.certificate804,CutLabelCertificates.Entropy000.certificate1,(1210886517218607731/1000000000000000000)⟩
theorem numericValid4204 : certificate4204.NumericValid := by decide +kernel
theorem sound4204 : certificate4204.Sound := rat_cut_cell_certificate_sound certificate4204 MergedCutBins.Batch350.valid4204 MergedCutBins.Batch350.sound4204 CutLabelCertificates.Entropy000.valid1 numericValid4204

def certificate4205 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4205,(some 64),(1/2),(117761590184174009281/500000000000000000)⟩,PopulationCertificates.Batch040.certificate804,CutLabelCertificates.Entropy000.certificate1,(1210886517218607731/1000000000000000000)⟩
theorem numericValid4205 : certificate4205.NumericValid := by decide +kernel
theorem sound4205 : certificate4205.Sound := rat_cut_cell_certificate_sound certificate4205 MergedCutBins.Batch350.valid4205 MergedCutBins.Batch350.sound4205 CutLabelCertificates.Entropy000.valid1 numericValid4205

def certificate4206 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4206,none,(1/2),(117761590184174009281/500000000000000000)⟩,PopulationCertificates.Batch040.certificate804,CutLabelCertificates.Entropy000.certificate1,(1210886517218607731/1000000000000000000)⟩
theorem numericValid4206 : certificate4206.NumericValid := by decide +kernel
theorem sound4206 : certificate4206.Sound := rat_cut_cell_certificate_sound certificate4206 MergedCutBins.Batch350.valid4206 MergedCutBins.Batch350.sound4206 CutLabelCertificates.Entropy000.valid1 numericValid4206

def certificate4207 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4207,(some 64),(1/2),(117761590184174009281/500000000000000000)⟩,PopulationCertificates.Batch040.certificate805,CutLabelCertificates.Entropy000.certificate1,(86264723555063367/8000000000000000)⟩
theorem numericValid4207 : certificate4207.NumericValid := by decide +kernel
theorem sound4207 : certificate4207.Sound := rat_cut_cell_certificate_sound certificate4207 MergedCutBins.Batch350.valid4207 MergedCutBins.Batch350.sound4207 CutLabelCertificates.Entropy000.valid1 numericValid4207

def certificate4208 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4208,none,(1/2),(117761590184174009281/500000000000000000)⟩,PopulationCertificates.Batch040.certificate805,CutLabelCertificates.Entropy000.certificate1,(86264723555063367/8000000000000000)⟩
theorem numericValid4208 : certificate4208.NumericValid := by decide +kernel
theorem sound4208 : certificate4208.Sound := rat_cut_cell_certificate_sound certificate4208 MergedCutBins.Batch350.valid4208 MergedCutBins.Batch350.sound4208 CutLabelCertificates.Entropy000.valid1 numericValid4208

def certificate4209 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4209,(some (394024002002240219/500000000000000000)),(1/2),(115511784528821437721/500000000000000000)⟩,PopulationCertificates.Batch040.certificate806,CutLabelCertificates.Entropy020.certificate404,(1287766647315599463/1000000000000000000)⟩
theorem numericValid4209 : certificate4209.NumericValid := by decide +kernel
theorem sound4209 : certificate4209.Sound := rat_cut_cell_certificate_sound certificate4209 MergedCutBins.Batch350.valid4209 MergedCutBins.Batch350.sound4209 CutLabelCertificates.Entropy020.valid404 numericValid4209

def certificate4210 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4210,(some (1118558783/1000000000)),(1/2),(115511784528821437721/500000000000000000)⟩,PopulationCertificates.Batch040.certificate806,CutLabelCertificates.Entropy020.certificate404,(1287766647315599463/1000000000000000000)⟩
theorem numericValid4210 : certificate4210.NumericValid := by decide +kernel
theorem sound4210 : certificate4210.Sound := rat_cut_cell_certificate_sound certificate4210 MergedCutBins.Batch350.valid4210 MergedCutBins.Batch350.sound4210 CutLabelCertificates.Entropy020.valid404 numericValid4210

def certificate4211 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch350.certificate4211,(some (1746878002356292423/1000000000000000000)),(1/2),(115511784528821437721/500000000000000000)⟩,PopulationCertificates.Batch040.certificate806,CutLabelCertificates.Entropy000.certificate1,(159444820437457211/125000000000000000)⟩
theorem numericValid4211 : certificate4211.NumericValid := by decide +kernel
theorem sound4211 : certificate4211.Sound := rat_cut_cell_certificate_sound certificate4211 MergedCutBins.Batch350.valid4211 MergedCutBins.Batch350.sound4211 CutLabelCertificates.Entropy000.valid1 numericValid4211

def certificates : List RatCutCellCertificate := [certificate4200,certificate4201,certificate4202,certificate4203,certificate4204,certificate4205,certificate4206,certificate4207,certificate4208,certificate4209,certificate4210,certificate4211]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4200,List.forall_mem_cons.mpr ⟨sound4201,List.forall_mem_cons.mpr ⟨sound4202,List.forall_mem_cons.mpr ⟨sound4203,List.forall_mem_cons.mpr ⟨sound4204,List.forall_mem_cons.mpr ⟨sound4205,List.forall_mem_cons.mpr ⟨sound4206,List.forall_mem_cons.mpr ⟨sound4207,List.forall_mem_cons.mpr ⟨sound4208,List.forall_mem_cons.mpr ⟨sound4209,List.forall_mem_cons.mpr ⟨sound4210,List.forall_mem_cons.mpr ⟨sound4211,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch350
