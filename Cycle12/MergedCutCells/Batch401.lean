import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy031
import Cycle12.CutLabelCertificates.Entropy032
import Cycle12.MergedCutBins.Batch401
import Cycle12.PopulationCertificates.Batch048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch401

def certificate4812 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4812,(some 64),(1/2),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate969,CutLabelCertificates.Entropy000.certificate1,(7672577332344680001/1000000000000000000)⟩
theorem numericValid4812 : certificate4812.NumericValid := by decide +kernel
theorem sound4812 : certificate4812.Sound := rat_cut_cell_certificate_sound certificate4812 MergedCutBins.Batch401.valid4812 MergedCutBins.Batch401.sound4812 CutLabelCertificates.Entropy000.valid1 numericValid4812

def certificate4813 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4813,none,(1/2),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate969,CutLabelCertificates.Entropy000.certificate1,(7672577332344680001/1000000000000000000)⟩
theorem numericValid4813 : certificate4813.NumericValid := by decide +kernel
theorem sound4813 : certificate4813.Sound := rat_cut_cell_certificate_sound certificate4813 MergedCutBins.Batch401.valid4813 MergedCutBins.Batch401.sound4813 CutLabelCertificates.Entropy000.valid1 numericValid4813

def certificate4814 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4814,(some (173369162863148973/250000000000000000)),(1/40),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate970,CutLabelCertificates.Entropy031.certificate638,(684555967785001/31250000000000000)⟩
theorem numericValid4814 : certificate4814.NumericValid := by decide +kernel
theorem sound4814 : certificate4814.Sound := rat_cut_cell_certificate_sound certificate4814 MergedCutBins.Batch401.valid4814 MergedCutBins.Batch401.sound4814 CutLabelCertificates.Entropy031.valid638 numericValid4814

def certificate4815 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4815,(some (224557503019106389/250000000000000000)),(1/40),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate970,CutLabelCertificates.Entropy031.certificate639,(684555967785001/31250000000000000)⟩
theorem numericValid4815 : certificate4815.NumericValid := by decide +kernel
theorem sound4815 : certificate4815.Sound := rat_cut_cell_certificate_sound certificate4815 MergedCutBins.Batch401.valid4815 MergedCutBins.Batch401.sound4815 CutLabelCertificates.Entropy031.valid639 numericValid4815

def certificate4816 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4816,(some (1547654747693670883/250000000000000000)),(1/40),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate970,CutLabelCertificates.Entropy032.certificate640,(684555967785001/31250000000000000)⟩
theorem numericValid4816 : certificate4816.NumericValid := by decide +kernel
theorem sound4816 : certificate4816.Sound := rat_cut_cell_certificate_sound certificate4816 MergedCutBins.Batch401.valid4816 MergedCutBins.Batch401.sound4816 CutLabelCertificates.Entropy032.valid640 numericValid4816

def certificate4817 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4817,none,(1/40),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate970,CutLabelCertificates.Entropy032.certificate641,(684555967785001/31250000000000000)⟩
theorem numericValid4817 : certificate4817.NumericValid := by decide +kernel
theorem sound4817 : certificate4817.Sound := rat_cut_cell_certificate_sound certificate4817 MergedCutBins.Batch401.valid4817 MergedCutBins.Batch401.sound4817 CutLabelCertificates.Entropy032.valid641 numericValid4817

def certificate4818 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4818,(some (147228371924037353/250000000000000000)),(1/2),(3003289735309396365599/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate971,CutLabelCertificates.Entropy032.certificate642,(211474694168336629/1000000000000000000)⟩
theorem numericValid4818 : certificate4818.NumericValid := by decide +kernel
theorem sound4818 : certificate4818.Sound := rat_cut_cell_certificate_sound certificate4818 MergedCutBins.Batch401.valid4818 MergedCutBins.Batch401.sound4818 CutLabelCertificates.Entropy032.valid642 numericValid4818

def certificate4819 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4819,(some (1132845493/1000000000)),(1/2),(3003289735309396365599/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate971,CutLabelCertificates.Entropy032.certificate642,(211474694168336629/1000000000000000000)⟩
theorem numericValid4819 : certificate4819.NumericValid := by decide +kernel
theorem sound4819 : certificate4819.Sound := rat_cut_cell_certificate_sound certificate4819 MergedCutBins.Batch401.valid4819 MergedCutBins.Batch401.sound4819 CutLabelCertificates.Entropy032.valid642 numericValid4819

def certificate4820 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4820,(some (78856502269970731/50000000000000000)),(1/2),(3003289735309396365599/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate971,CutLabelCertificates.Entropy000.certificate1,(42062414108788971/200000000000000000)⟩
theorem numericValid4820 : certificate4820.NumericValid := by decide +kernel
theorem sound4820 : certificate4820.Sound := rat_cut_cell_certificate_sound certificate4820 MergedCutBins.Batch401.valid4820 MergedCutBins.Batch401.sound4820 CutLabelCertificates.Entropy000.valid1 numericValid4820

def certificate4821 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4821,(some 64),(1/2),(3003289735309396365599/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate971,CutLabelCertificates.Entropy000.certificate1,(42062414108788971/200000000000000000)⟩
theorem numericValid4821 : certificate4821.NumericValid := by decide +kernel
theorem sound4821 : certificate4821.Sound := rat_cut_cell_certificate_sound certificate4821 MergedCutBins.Batch401.valid4821 MergedCutBins.Batch401.sound4821 CutLabelCertificates.Entropy000.valid1 numericValid4821

def certificate4822 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4822,none,(1/2),(3003289735309396365599/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate971,CutLabelCertificates.Entropy000.certificate1,(42062414108788971/200000000000000000)⟩
theorem numericValid4822 : certificate4822.NumericValid := by decide +kernel
theorem sound4822 : certificate4822.Sound := rat_cut_cell_certificate_sound certificate4822 MergedCutBins.Batch401.valid4822 MergedCutBins.Batch401.sound4822 CutLabelCertificates.Entropy000.valid1 numericValid4822

def certificate4823 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch401.certificate4823,(some 64),(1/2),(3003289735309396365599/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate972,CutLabelCertificates.Entropy000.certificate1,(7712236943092629969/1000000000000000000)⟩
theorem numericValid4823 : certificate4823.NumericValid := by decide +kernel
theorem sound4823 : certificate4823.Sound := rat_cut_cell_certificate_sound certificate4823 MergedCutBins.Batch401.valid4823 MergedCutBins.Batch401.sound4823 CutLabelCertificates.Entropy000.valid1 numericValid4823

def certificates : List RatCutCellCertificate := [certificate4812,certificate4813,certificate4814,certificate4815,certificate4816,certificate4817,certificate4818,certificate4819,certificate4820,certificate4821,certificate4822,certificate4823]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4812,List.forall_mem_cons.mpr ⟨sound4813,List.forall_mem_cons.mpr ⟨sound4814,List.forall_mem_cons.mpr ⟨sound4815,List.forall_mem_cons.mpr ⟨sound4816,List.forall_mem_cons.mpr ⟨sound4817,List.forall_mem_cons.mpr ⟨sound4818,List.forall_mem_cons.mpr ⟨sound4819,List.forall_mem_cons.mpr ⟨sound4820,List.forall_mem_cons.mpr ⟨sound4821,List.forall_mem_cons.mpr ⟨sound4822,List.forall_mem_cons.mpr ⟨sound4823,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch401
