import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy041
import Cycle12.MergedCutBins.Batch433
import Cycle12.PopulationCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch433

def certificate5196 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch433.certificate5196,none,(1/2),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1065,CutLabelCertificates.Entropy000.certificate1,(13572631670586502881/1000000000000000000)⟩
theorem numericValid5196 : certificate5196.NumericValid := by decide +kernel
theorem sound5196 : certificate5196.Sound := rat_cut_cell_certificate_sound certificate5196 MergedCutBins.Batch433.valid5196 MergedCutBins.Batch433.sound5196 CutLabelCertificates.Entropy000.valid1 numericValid5196

def certificate5197 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch433.certificate5197,(some (793744195314299953/1000000000000000000)),(1/40),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1066,CutLabelCertificates.Entropy041.certificate824,(240181685145640357/1000000000000000000)⟩
theorem numericValid5197 : certificate5197.NumericValid := by decide +kernel
theorem sound5197 : certificate5197.Sound := rat_cut_cell_certificate_sound certificate5197 MergedCutBins.Batch433.valid5197 MergedCutBins.Batch433.sound5197 CutLabelCertificates.Entropy041.valid824 numericValid5197

def certificate5198 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch433.certificate5198,(some (894410826802112109/1000000000000000000)),(1/40),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1066,CutLabelCertificates.Entropy041.certificate825,(240181685145640357/1000000000000000000)⟩
theorem numericValid5198 : certificate5198.NumericValid := by decide +kernel
theorem sound5198 : certificate5198.Sound := rat_cut_cell_certificate_sound certificate5198 MergedCutBins.Batch433.valid5198 MergedCutBins.Batch433.sound5198 CutLabelCertificates.Entropy041.valid825 numericValid5198

def certificate5199 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch433.certificate5199,(some (2324817846433913189/1000000000000000000)),(1/40),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1066,CutLabelCertificates.Entropy041.certificate826,(240181685145640357/1000000000000000000)⟩
theorem numericValid5199 : certificate5199.NumericValid := by decide +kernel
theorem sound5199 : certificate5199.Sound := rat_cut_cell_certificate_sound certificate5199 MergedCutBins.Batch433.valid5199 MergedCutBins.Batch433.sound5199 CutLabelCertificates.Entropy041.valid826 numericValid5199

def certificate5200 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch433.certificate5200,(some (21596166054526855143/1000000000000000000)),(1/40),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1066,CutLabelCertificates.Entropy041.certificate827,(240181685145640357/1000000000000000000)⟩
theorem numericValid5200 : certificate5200.NumericValid := by decide +kernel
theorem sound5200 : certificate5200.Sound := rat_cut_cell_certificate_sound certificate5200 MergedCutBins.Batch433.valid5200 MergedCutBins.Batch433.sound5200 CutLabelCertificates.Entropy041.valid827 numericValid5200

def certificate5201 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch433.certificate5201,none,(1/40),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1066,CutLabelCertificates.Entropy041.certificate828,(240181685145640357/1000000000000000000)⟩
theorem numericValid5201 : certificate5201.NumericValid := by decide +kernel
theorem sound5201 : certificate5201.Sound := rat_cut_cell_certificate_sound certificate5201 MergedCutBins.Batch433.valid5201 MergedCutBins.Batch433.sound5201 CutLabelCertificates.Entropy041.valid828 numericValid5201

def certificates : List RatCutCellCertificate := [certificate5196,certificate5197,certificate5198,certificate5199,certificate5200,certificate5201]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5196,List.forall_mem_cons.mpr ⟨sound5197,List.forall_mem_cons.mpr ⟨sound5198,List.forall_mem_cons.mpr ⟨sound5199,List.forall_mem_cons.mpr ⟨sound5200,List.forall_mem_cons.mpr ⟨sound5201,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch433
