import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy031
import Cycle12.MergedCutBins.Batch400
import Cycle12.PopulationCertificates.Batch048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch400

def certificate4800 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4800,none,(1/2),(24522918443256535917/8000000000000000)⟩,PopulationCertificates.Batch048.certificate965,CutLabelCertificates.Entropy000.certificate1,(104040479175117941/500000000000000000)⟩
theorem numericValid4800 : certificate4800.NumericValid := by decide +kernel
theorem sound4800 : certificate4800.Sound := rat_cut_cell_certificate_sound certificate4800 MergedCutBins.Batch400.valid4800 MergedCutBins.Batch400.sound4800 CutLabelCertificates.Entropy000.valid1 numericValid4800

def certificate4801 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4801,(some 64),(1/2),(24522918443256535917/8000000000000000)⟩,PopulationCertificates.Batch048.certificate966,CutLabelCertificates.Entropy000.certificate1,(3816976497117786071/500000000000000000)⟩
theorem numericValid4801 : certificate4801.NumericValid := by decide +kernel
theorem sound4801 : certificate4801.Sound := rat_cut_cell_certificate_sound certificate4801 MergedCutBins.Batch400.valid4801 MergedCutBins.Batch400.sound4801 CutLabelCertificates.Entropy000.valid1 numericValid4801

def certificate4802 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4802,none,(1/2),(24522918443256535917/8000000000000000)⟩,PopulationCertificates.Batch048.certificate966,CutLabelCertificates.Entropy000.certificate1,(3816976497117786071/500000000000000000)⟩
theorem numericValid4802 : certificate4802.NumericValid := by decide +kernel
theorem sound4802 : certificate4802.Sound := rat_cut_cell_certificate_sound certificate4802 MergedCutBins.Batch400.valid4802 MergedCutBins.Batch400.sound4802 CutLabelCertificates.Entropy000.valid1 numericValid4802

def certificate4803 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4803,(some (86568623862604077/125000000000000000)),(1/40),(24522918443256535917/8000000000000000)⟩,PopulationCertificates.Batch048.certificate967,CutLabelCertificates.Entropy031.certificate633,(10381772330787101/500000000000000000)⟩
theorem numericValid4803 : certificate4803.NumericValid := by decide +kernel
theorem sound4803 : certificate4803.Sound := rat_cut_cell_certificate_sound certificate4803 MergedCutBins.Batch400.valid4803 MergedCutBins.Batch400.sound4803 CutLabelCertificates.Entropy031.valid633 numericValid4803

def certificate4804 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4804,(some (112128556736076003/125000000000000000)),(1/40),(24522918443256535917/8000000000000000)⟩,PopulationCertificates.Batch048.certificate967,CutLabelCertificates.Entropy031.certificate634,(10381772330787101/500000000000000000)⟩
theorem numericValid4804 : certificate4804.NumericValid := by decide +kernel
theorem sound4804 : certificate4804.Sound := rat_cut_cell_certificate_sound certificate4804 MergedCutBins.Batch400.valid4804 MergedCutBins.Batch400.sound4804 CutLabelCertificates.Entropy031.valid634 numericValid4804

def certificate4805 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4805,(some (6244161206283470893/1000000000000000000)),(1/40),(24522918443256535917/8000000000000000)⟩,PopulationCertificates.Batch048.certificate967,CutLabelCertificates.Entropy031.certificate635,(10381772330787101/500000000000000000)⟩
theorem numericValid4805 : certificate4805.NumericValid := by decide +kernel
theorem sound4805 : certificate4805.Sound := rat_cut_cell_certificate_sound certificate4805 MergedCutBins.Batch400.valid4805 MergedCutBins.Batch400.sound4805 CutLabelCertificates.Entropy031.valid635 numericValid4805

def certificate4806 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4806,none,(1/40),(24522918443256535917/8000000000000000)⟩,PopulationCertificates.Batch048.certificate967,CutLabelCertificates.Entropy031.certificate636,(10381772330787101/500000000000000000)⟩
theorem numericValid4806 : certificate4806.NumericValid := by decide +kernel
theorem sound4806 : certificate4806.Sound := rat_cut_cell_certificate_sound certificate4806 MergedCutBins.Batch400.valid4806 MergedCutBins.Batch400.sound4806 CutLabelCertificates.Entropy031.valid636 numericValid4806

def certificate4807 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4807,(some (594336762033289571/1000000000000000000)),(1/2),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate968,CutLabelCertificates.Entropy031.certificate637,(26265866917233499/125000000000000000)⟩
theorem numericValid4807 : certificate4807.NumericValid := by decide +kernel
theorem sound4807 : certificate4807.Sound := rat_cut_cell_certificate_sound certificate4807 MergedCutBins.Batch400.valid4807 MergedCutBins.Batch400.sound4807 CutLabelCertificates.Entropy031.valid637 numericValid4807

def certificate4808 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4808,(some (113208361/100000000)),(1/2),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate968,CutLabelCertificates.Entropy031.certificate637,(26265866917233499/125000000000000000)⟩
theorem numericValid4808 : certificate4808.NumericValid := by decide +kernel
theorem sound4808 : certificate4808.Sound := rat_cut_cell_certificate_sound certificate4808 MergedCutBins.Batch400.valid4808 MergedCutBins.Batch400.sound4808 CutLabelCertificates.Entropy031.valid637 numericValid4808

def certificate4809 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4809,(some (1317475344537154837/1000000000000000000)),(1/2),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate968,CutLabelCertificates.Entropy000.certificate1,(104494671041801989/500000000000000000)⟩
theorem numericValid4809 : certificate4809.NumericValid := by decide +kernel
theorem sound4809 : certificate4809.Sound := rat_cut_cell_certificate_sound certificate4809 MergedCutBins.Batch400.valid4809 MergedCutBins.Batch400.sound4809 CutLabelCertificates.Entropy000.valid1 numericValid4809

def certificate4810 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4810,(some 64),(1/2),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate968,CutLabelCertificates.Entropy000.certificate1,(104494671041801989/500000000000000000)⟩
theorem numericValid4810 : certificate4810.NumericValid := by decide +kernel
theorem sound4810 : certificate4810.Sound := rat_cut_cell_certificate_sound certificate4810 MergedCutBins.Batch400.valid4810 MergedCutBins.Batch400.sound4810 CutLabelCertificates.Entropy000.valid1 numericValid4810

def certificate4811 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch400.certificate4811,none,(1/2),(3023785039358298996097/1000000000000000000)⟩,PopulationCertificates.Batch048.certificate968,CutLabelCertificates.Entropy000.certificate1,(104494671041801989/500000000000000000)⟩
theorem numericValid4811 : certificate4811.NumericValid := by decide +kernel
theorem sound4811 : certificate4811.Sound := rat_cut_cell_certificate_sound certificate4811 MergedCutBins.Batch400.valid4811 MergedCutBins.Batch400.sound4811 CutLabelCertificates.Entropy000.valid1 numericValid4811

def certificates : List RatCutCellCertificate := [certificate4800,certificate4801,certificate4802,certificate4803,certificate4804,certificate4805,certificate4806,certificate4807,certificate4808,certificate4809,certificate4810,certificate4811]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4800,List.forall_mem_cons.mpr ⟨sound4801,List.forall_mem_cons.mpr ⟨sound4802,List.forall_mem_cons.mpr ⟨sound4803,List.forall_mem_cons.mpr ⟨sound4804,List.forall_mem_cons.mpr ⟨sound4805,List.forall_mem_cons.mpr ⟨sound4806,List.forall_mem_cons.mpr ⟨sound4807,List.forall_mem_cons.mpr ⟨sound4808,List.forall_mem_cons.mpr ⟨sound4809,List.forall_mem_cons.mpr ⟨sound4810,List.forall_mem_cons.mpr ⟨sound4811,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch400
