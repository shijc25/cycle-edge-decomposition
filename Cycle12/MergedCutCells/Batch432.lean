import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy040
import Cycle12.CutLabelCertificates.Entropy041
import Cycle12.MergedCutBins.Batch432
import Cycle12.PopulationCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch432

def certificate5184 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5184,none,(1/2),(958430071261117944869/1000000000000000000)⟩,PopulationCertificates.Batch053.certificate1062,CutLabelCertificates.Entropy000.certificate1,(25897162080199761/1953125000000000)⟩
theorem numericValid5184 : certificate5184.NumericValid := by decide +kernel
theorem sound5184 : certificate5184.Sound := rat_cut_cell_certificate_sound certificate5184 MergedCutBins.Batch432.valid5184 MergedCutBins.Batch432.sound5184 CutLabelCertificates.Entropy000.valid1 numericValid5184

def certificate5185 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5185,(some (394694832020629911/500000000000000000)),(1/40),(958430071261117944869/1000000000000000000)⟩,PopulationCertificates.Batch053.certificate1063,CutLabelCertificates.Entropy040.certificate818,(223674551052766899/1000000000000000000)⟩
theorem numericValid5185 : certificate5185.NumericValid := by decide +kernel
theorem sound5185 : certificate5185.Sound := rat_cut_cell_certificate_sound certificate5185 MergedCutBins.Batch432.valid5185 MergedCutBins.Batch432.sound5185 CutLabelCertificates.Entropy040.valid818 numericValid5185

def certificate5186 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5186,(some (889504031969158061/1000000000000000000)),(1/40),(958430071261117944869/1000000000000000000)⟩,PopulationCertificates.Batch053.certificate1063,CutLabelCertificates.Entropy040.certificate819,(223674551052766899/1000000000000000000)⟩
theorem numericValid5186 : certificate5186.NumericValid := by decide +kernel
theorem sound5186 : certificate5186.Sound := rat_cut_cell_certificate_sound certificate5186 MergedCutBins.Batch432.valid5186 MergedCutBins.Batch432.sound5186 CutLabelCertificates.Entropy040.valid819 numericValid5186

def certificate5187 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5187,(some (2335184384948074459/1000000000000000000)),(1/40),(958430071261117944869/1000000000000000000)⟩,PopulationCertificates.Batch053.certificate1063,CutLabelCertificates.Entropy041.certificate820,(223674551052766899/1000000000000000000)⟩
theorem numericValid5187 : certificate5187.NumericValid := by decide +kernel
theorem sound5187 : certificate5187.Sound := rat_cut_cell_certificate_sound certificate5187 MergedCutBins.Batch432.valid5187 MergedCutBins.Batch432.sound5187 CutLabelCertificates.Entropy041.valid820 numericValid5187

def certificate5188 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5188,(some (10954694820684625103/500000000000000000)),(1/40),(958430071261117944869/1000000000000000000)⟩,PopulationCertificates.Batch053.certificate1063,CutLabelCertificates.Entropy041.certificate821,(223674551052766899/1000000000000000000)⟩
theorem numericValid5188 : certificate5188.NumericValid := by decide +kernel
theorem sound5188 : certificate5188.Sound := rat_cut_cell_certificate_sound certificate5188 MergedCutBins.Batch432.valid5188 MergedCutBins.Batch432.sound5188 CutLabelCertificates.Entropy041.valid821 numericValid5188

def certificate5189 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5189,none,(1/40),(958430071261117944869/1000000000000000000)⟩,PopulationCertificates.Batch053.certificate1063,CutLabelCertificates.Entropy041.certificate822,(223674551052766899/1000000000000000000)⟩
theorem numericValid5189 : certificate5189.NumericValid := by decide +kernel
theorem sound5189 : certificate5189.Sound := rat_cut_cell_certificate_sound certificate5189 MergedCutBins.Batch432.valid5189 MergedCutBins.Batch432.sound5189 CutLabelCertificates.Entropy041.valid822 numericValid5189

def certificate5190 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5190,(some (632011875660177049/1000000000000000000)),(1/2),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1064,CutLabelCertificates.Entropy041.certificate823,(42398842930509253/250000000000000000)⟩
theorem numericValid5190 : certificate5190.NumericValid := by decide +kernel
theorem sound5190 : certificate5190.Sound := rat_cut_cell_certificate_sound certificate5190 MergedCutBins.Batch432.valid5190 MergedCutBins.Batch432.sound5190 CutLabelCertificates.Entropy041.valid823 numericValid5190

def certificate5191 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5191,(some (509516981/500000000)),(1/2),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1064,CutLabelCertificates.Entropy041.certificate823,(42398842930509253/250000000000000000)⟩
theorem numericValid5191 : certificate5191.NumericValid := by decide +kernel
theorem sound5191 : certificate5191.Sound := rat_cut_cell_certificate_sound certificate5191 MergedCutBins.Batch432.valid5191 MergedCutBins.Batch432.sound5191 CutLabelCertificates.Entropy041.valid823 numericValid5191

def certificate5192 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5192,(some (472080828289421167/250000000000000000)),(1/2),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1064,CutLabelCertificates.Entropy000.certificate1,(164964798857652981/1000000000000000000)⟩
theorem numericValid5192 : certificate5192.NumericValid := by decide +kernel
theorem sound5192 : certificate5192.Sound := rat_cut_cell_certificate_sound certificate5192 MergedCutBins.Batch432.valid5192 MergedCutBins.Batch432.sound5192 CutLabelCertificates.Entropy000.valid1 numericValid5192

def certificate5193 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5193,(some 64),(1/2),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1064,CutLabelCertificates.Entropy000.certificate1,(164964798857652981/1000000000000000000)⟩
theorem numericValid5193 : certificate5193.NumericValid := by decide +kernel
theorem sound5193 : certificate5193.Sound := rat_cut_cell_certificate_sound certificate5193 MergedCutBins.Batch432.valid5193 MergedCutBins.Batch432.sound5193 CutLabelCertificates.Entropy000.valid1 numericValid5193

def certificate5194 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5194,none,(1/2),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1064,CutLabelCertificates.Entropy000.certificate1,(164964798857652981/1000000000000000000)⟩
theorem numericValid5194 : certificate5194.NumericValid := by decide +kernel
theorem sound5194 : certificate5194.Sound := rat_cut_cell_certificate_sound certificate5194 MergedCutBins.Batch432.valid5194 MergedCutBins.Batch432.sound5194 CutLabelCertificates.Entropy000.valid1 numericValid5194

def certificate5195 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch432.certificate5195,(some 64),(1/2),(231118446031702313983/250000000000000000)⟩,PopulationCertificates.Batch053.certificate1065,CutLabelCertificates.Entropy000.certificate1,(13572631670586502881/1000000000000000000)⟩
theorem numericValid5195 : certificate5195.NumericValid := by decide +kernel
theorem sound5195 : certificate5195.Sound := rat_cut_cell_certificate_sound certificate5195 MergedCutBins.Batch432.valid5195 MergedCutBins.Batch432.sound5195 CutLabelCertificates.Entropy000.valid1 numericValid5195

def certificates : List RatCutCellCertificate := [certificate5184,certificate5185,certificate5186,certificate5187,certificate5188,certificate5189,certificate5190,certificate5191,certificate5192,certificate5193,certificate5194,certificate5195]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5184,List.forall_mem_cons.mpr ⟨sound5185,List.forall_mem_cons.mpr ⟨sound5186,List.forall_mem_cons.mpr ⟨sound5187,List.forall_mem_cons.mpr ⟨sound5188,List.forall_mem_cons.mpr ⟨sound5189,List.forall_mem_cons.mpr ⟨sound5190,List.forall_mem_cons.mpr ⟨sound5191,List.forall_mem_cons.mpr ⟨sound5192,List.forall_mem_cons.mpr ⟨sound5193,List.forall_mem_cons.mpr ⟨sound5194,List.forall_mem_cons.mpr ⟨sound5195,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch432
