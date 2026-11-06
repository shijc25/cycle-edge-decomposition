import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy013
import Cycle12.MergedCutBins.Batch250
import Cycle12.PopulationCertificates.Batch027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch250

def certificate3000 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3000,none,(1/2),(274952852136900303297/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate543,CutLabelCertificates.Entropy000.certificate1,(848026937815156397/200000000000000000)⟩
theorem numericValid3000 : certificate3000.NumericValid := by decide +kernel
theorem sound3000 : certificate3000.Sound := rat_cut_cell_certificate_sound certificate3000 MergedCutBins.Batch250.valid3000 MergedCutBins.Batch250.sound3000 CutLabelCertificates.Entropy000.valid1 numericValid3000

def certificate3001 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3001,(some (655870518745967157/1000000000000000000)),(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate544,CutLabelCertificates.Entropy013.certificate273,(321141958009973893/1000000000000000000)⟩
theorem numericValid3001 : certificate3001.NumericValid := by decide +kernel
theorem sound3001 : certificate3001.Sound := rat_cut_cell_certificate_sound certificate3001 MergedCutBins.Batch250.valid3001 MergedCutBins.Batch250.sound3001 CutLabelCertificates.Entropy013.valid273 numericValid3001

def certificate3002 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3002,(some (46415577/40000000)),(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate544,CutLabelCertificates.Entropy013.certificate273,(321141958009973893/1000000000000000000)⟩
theorem numericValid3002 : certificate3002.NumericValid := by decide +kernel
theorem sound3002 : certificate3002.Sound := rat_cut_cell_certificate_sound certificate3002 MergedCutBins.Batch250.valid3002 MergedCutBins.Batch250.sound3002 CutLabelCertificates.Entropy013.valid273 numericValid3002

def certificate3003 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3003,(some (1191517806091315851/1000000000000000000)),(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate544,CutLabelCertificates.Entropy000.certificate1,(310757963976864681/1000000000000000000)⟩
theorem numericValid3003 : certificate3003.NumericValid := by decide +kernel
theorem sound3003 : certificate3003.Sound := rat_cut_cell_certificate_sound certificate3003 MergedCutBins.Batch250.valid3003 MergedCutBins.Batch250.sound3003 CutLabelCertificates.Entropy000.valid1 numericValid3003

def certificate3004 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3004,(some (2320772556810957867/1000000000000000000)),(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate544,CutLabelCertificates.Entropy000.certificate1,(310757963976864681/1000000000000000000)⟩
theorem numericValid3004 : certificate3004.NumericValid := by decide +kernel
theorem sound3004 : certificate3004.Sound := rat_cut_cell_certificate_sound certificate3004 MergedCutBins.Batch250.valid3004 MergedCutBins.Batch250.sound3004 CutLabelCertificates.Entropy000.valid1 numericValid3004

def certificate3005 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3005,(some (13462530625480438871/250000000000000000)),(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate544,CutLabelCertificates.Entropy000.certificate1,(310757963976864681/1000000000000000000)⟩
theorem numericValid3005 : certificate3005.NumericValid := by decide +kernel
theorem sound3005 : certificate3005.Sound := rat_cut_cell_certificate_sound certificate3005 MergedCutBins.Batch250.valid3005 MergedCutBins.Batch250.sound3005 CutLabelCertificates.Entropy000.valid1 numericValid3005

def certificate3006 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3006,(some 64),(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate544,CutLabelCertificates.Entropy000.certificate1,(310757963976864681/1000000000000000000)⟩
theorem numericValid3006 : certificate3006.NumericValid := by decide +kernel
theorem sound3006 : certificate3006.Sound := rat_cut_cell_certificate_sound certificate3006 MergedCutBins.Batch250.valid3006 MergedCutBins.Batch250.sound3006 CutLabelCertificates.Entropy000.valid1 numericValid3006

def certificate3007 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3007,none,(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate544,CutLabelCertificates.Entropy000.certificate1,(310757963976864681/1000000000000000000)⟩
theorem numericValid3007 : certificate3007.NumericValid := by decide +kernel
theorem sound3007 : certificate3007.Sound := rat_cut_cell_certificate_sound certificate3007 MergedCutBins.Batch250.valid3007 MergedCutBins.Batch250.sound3007 CutLabelCertificates.Entropy000.valid1 numericValid3007

def certificate3008 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3008,(some 64),(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate545,CutLabelCertificates.Entropy000.certificate1,(4342847664366684611/1000000000000000000)⟩
theorem numericValid3008 : certificate3008.NumericValid := by decide +kernel
theorem sound3008 : certificate3008.Sound := rat_cut_cell_certificate_sound certificate3008 MergedCutBins.Batch250.valid3008 MergedCutBins.Batch250.sound3008 CutLabelCertificates.Entropy000.valid1 numericValid3008

def certificate3009 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3009,none,(1/2),(256722563520525037319/1000000000000000000)⟩,PopulationCertificates.Batch027.certificate545,CutLabelCertificates.Entropy000.certificate1,(4342847664366684611/1000000000000000000)⟩
theorem numericValid3009 : certificate3009.NumericValid := by decide +kernel
theorem sound3009 : certificate3009.Sound := rat_cut_cell_certificate_sound certificate3009 MergedCutBins.Batch250.valid3009 MergedCutBins.Batch250.sound3009 CutLabelCertificates.Entropy000.valid1 numericValid3009

def certificate3010 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3010,(some (81767683440853197/125000000000000000)),(1/2),(9606499003605273279/40000000000000000)⟩,PopulationCertificates.Batch027.certificate546,CutLabelCertificates.Entropy013.certificate274,(327131448247648457/1000000000000000000)⟩
theorem numericValid3010 : certificate3010.NumericValid := by decide +kernel
theorem sound3010 : certificate3010.Sound := rat_cut_cell_certificate_sound certificate3010 MergedCutBins.Batch250.valid3010 MergedCutBins.Batch250.sound3010 CutLabelCertificates.Entropy013.valid274 numericValid3010

def certificate3011 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch250.certificate3011,(some (288356665782585167/250000000000000000)),(1/2),(9606499003605273279/40000000000000000)⟩,PopulationCertificates.Batch027.certificate546,CutLabelCertificates.Entropy013.certificate274,(327131448247648457/1000000000000000000)⟩
theorem numericValid3011 : certificate3011.NumericValid := by decide +kernel
theorem sound3011 : certificate3011.Sound := rat_cut_cell_certificate_sound certificate3011 MergedCutBins.Batch250.valid3011 MergedCutBins.Batch250.sound3011 CutLabelCertificates.Entropy013.valid274 numericValid3011

def certificates : List RatCutCellCertificate := [certificate3000,certificate3001,certificate3002,certificate3003,certificate3004,certificate3005,certificate3006,certificate3007,certificate3008,certificate3009,certificate3010,certificate3011]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3000,List.forall_mem_cons.mpr ⟨sound3001,List.forall_mem_cons.mpr ⟨sound3002,List.forall_mem_cons.mpr ⟨sound3003,List.forall_mem_cons.mpr ⟨sound3004,List.forall_mem_cons.mpr ⟨sound3005,List.forall_mem_cons.mpr ⟨sound3006,List.forall_mem_cons.mpr ⟨sound3007,List.forall_mem_cons.mpr ⟨sound3008,List.forall_mem_cons.mpr ⟨sound3009,List.forall_mem_cons.mpr ⟨sound3010,List.forall_mem_cons.mpr ⟨sound3011,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch250
