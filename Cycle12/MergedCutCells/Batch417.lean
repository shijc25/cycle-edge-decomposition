import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy036
import Cycle12.MergedCutBins.Batch417
import Cycle12.PopulationCertificates.Batch050
import Cycle12.PopulationCertificates.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch417

def certificate5004 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5004,(some (10318274047289888517/250000000000000000)),(1/40),(435902475717329878669/250000000000000000)⟩,PopulationCertificates.Batch050.certificate1018,CutLabelCertificates.Entropy036.certificate731,(56193834592772193/1000000000000000000)⟩
theorem numericValid5004 : certificate5004.NumericValid := by decide +kernel
theorem sound5004 : certificate5004.Sound := rat_cut_cell_certificate_sound certificate5004 MergedCutBins.Batch417.valid5004 MergedCutBins.Batch417.sound5004 CutLabelCertificates.Entropy036.valid731 numericValid5004

def certificate5005 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5005,none,(1/40),(435902475717329878669/250000000000000000)⟩,PopulationCertificates.Batch050.certificate1018,CutLabelCertificates.Entropy036.certificate732,(56193834592772193/1000000000000000000)⟩
theorem numericValid5005 : certificate5005.NumericValid := by decide +kernel
theorem sound5005 : certificate5005.Sound := rat_cut_cell_certificate_sound certificate5005 MergedCutBins.Batch417.valid5005 MergedCutBins.Batch417.sound5005 CutLabelCertificates.Entropy036.valid732 numericValid5005

def certificate5006 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5006,(some (311641770526039907/500000000000000000)),(1/2),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch050.certificate1019,CutLabelCertificates.Entropy036.certificate733,(257143543635576573/1000000000000000000)⟩
theorem numericValid5006 : certificate5006.NumericValid := by decide +kernel
theorem sound5006 : certificate5006.Sound := rat_cut_cell_certificate_sound certificate5006 MergedCutBins.Batch417.valid5006 MergedCutBins.Batch417.sound5006 CutLabelCertificates.Entropy036.valid733 numericValid5006

def certificate5007 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5007,(some (1093441681/1000000000)),(1/2),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch050.certificate1019,CutLabelCertificates.Entropy036.certificate733,(257143543635576573/1000000000000000000)⟩
theorem numericValid5007 : certificate5007.NumericValid := by decide +kernel
theorem sound5007 : certificate5007.Sound := rat_cut_cell_certificate_sound certificate5007 MergedCutBins.Batch417.valid5007 MergedCutBins.Batch417.sound5007 CutLabelCertificates.Entropy036.valid733 numericValid5007

def certificate5008 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5008,(some (1038823799398334401/500000000000000000)),(1/2),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch050.certificate1019,CutLabelCertificates.Entropy000.certificate1,(254964904060980961/1000000000000000000)⟩
theorem numericValid5008 : certificate5008.NumericValid := by decide +kernel
theorem sound5008 : certificate5008.Sound := rat_cut_cell_certificate_sound certificate5008 MergedCutBins.Batch417.valid5008 MergedCutBins.Batch417.sound5008 CutLabelCertificates.Entropy000.valid1 numericValid5008

def certificate5009 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5009,(some 64),(1/2),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch050.certificate1019,CutLabelCertificates.Entropy000.certificate1,(254964904060980961/1000000000000000000)⟩
theorem numericValid5009 : certificate5009.NumericValid := by decide +kernel
theorem sound5009 : certificate5009.Sound := rat_cut_cell_certificate_sound certificate5009 MergedCutBins.Batch417.valid5009 MergedCutBins.Batch417.sound5009 CutLabelCertificates.Entropy000.valid1 numericValid5009

def certificate5010 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5010,none,(1/2),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch050.certificate1019,CutLabelCertificates.Entropy000.certificate1,(254964904060980961/1000000000000000000)⟩
theorem numericValid5010 : certificate5010.NumericValid := by decide +kernel
theorem sound5010 : certificate5010.Sound := rat_cut_cell_certificate_sound certificate5010 MergedCutBins.Batch417.valid5010 MergedCutBins.Batch417.sound5010 CutLabelCertificates.Entropy000.valid1 numericValid5010

def certificate5011 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5011,(some 64),(1/2),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch051.certificate1020,CutLabelCertificates.Entropy000.certificate1,(388988218674010603/40000000000000000)⟩
theorem numericValid5011 : certificate5011.NumericValid := by decide +kernel
theorem sound5011 : certificate5011.Sound := rat_cut_cell_certificate_sound certificate5011 MergedCutBins.Batch417.valid5011 MergedCutBins.Batch417.sound5011 CutLabelCertificates.Entropy000.valid1 numericValid5011

def certificate5012 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5012,none,(1/2),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch051.certificate1020,CutLabelCertificates.Entropy000.certificate1,(388988218674010603/40000000000000000)⟩
theorem numericValid5012 : certificate5012.NumericValid := by decide +kernel
theorem sound5012 : certificate5012.Sound := rat_cut_cell_certificate_sound certificate5012 MergedCutBins.Batch417.valid5012 MergedCutBins.Batch417.sound5012 CutLabelCertificates.Entropy000.valid1 numericValid5012

def certificate5013 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5013,(some (182620934977960183/250000000000000000)),(1/40),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch051.certificate1021,CutLabelCertificates.Entropy036.certificate734,(7966079306356201/125000000000000000)⟩
theorem numericValid5013 : certificate5013.NumericValid := by decide +kernel
theorem sound5013 : certificate5013.Sound := rat_cut_cell_certificate_sound certificate5013 MergedCutBins.Batch417.valid5013 MergedCutBins.Batch417.sound5013 CutLabelCertificates.Entropy036.valid734 numericValid5013

def certificate5014 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5014,(some (873766281525702541/1000000000000000000)),(1/40),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch051.certificate1021,CutLabelCertificates.Entropy036.certificate735,(7966079306356201/125000000000000000)⟩
theorem numericValid5014 : certificate5014.NumericValid := by decide +kernel
theorem sound5014 : certificate5014.Sound := rat_cut_cell_certificate_sound certificate5014 MergedCutBins.Batch417.valid5014 MergedCutBins.Batch417.sound5014 CutLabelCertificates.Entropy036.valid735 numericValid5014

def certificate5015 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch417.certificate5015,(some (3381443348407215257/1000000000000000000)),(1/40),(1668693111133782522381/1000000000000000000)⟩,PopulationCertificates.Batch051.certificate1021,CutLabelCertificates.Entropy036.certificate736,(7966079306356201/125000000000000000)⟩
theorem numericValid5015 : certificate5015.NumericValid := by decide +kernel
theorem sound5015 : certificate5015.Sound := rat_cut_cell_certificate_sound certificate5015 MergedCutBins.Batch417.valid5015 MergedCutBins.Batch417.sound5015 CutLabelCertificates.Entropy036.valid736 numericValid5015

def certificates : List RatCutCellCertificate := [certificate5004,certificate5005,certificate5006,certificate5007,certificate5008,certificate5009,certificate5010,certificate5011,certificate5012,certificate5013,certificate5014,certificate5015]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5004,List.forall_mem_cons.mpr ⟨sound5005,List.forall_mem_cons.mpr ⟨sound5006,List.forall_mem_cons.mpr ⟨sound5007,List.forall_mem_cons.mpr ⟨sound5008,List.forall_mem_cons.mpr ⟨sound5009,List.forall_mem_cons.mpr ⟨sound5010,List.forall_mem_cons.mpr ⟨sound5011,List.forall_mem_cons.mpr ⟨sound5012,List.forall_mem_cons.mpr ⟨sound5013,List.forall_mem_cons.mpr ⟨sound5014,List.forall_mem_cons.mpr ⟨sound5015,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch417
