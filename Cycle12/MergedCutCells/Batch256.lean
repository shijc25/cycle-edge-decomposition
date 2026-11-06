import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy014
import Cycle12.MergedCutBins.Batch256
import Cycle12.PopulationCertificates.Batch028

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch256

def certificate3072 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3072,(some (4390532681351679/6250000000000000)),(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate560,CutLabelCertificates.Entropy014.certificate281,(93596184449986847/200000000000000000)⟩
theorem numericValid3072 : certificate3072.NumericValid := by decide +kernel
theorem sound3072 : certificate3072.Sound := rat_cut_cell_certificate_sound certificate3072 MergedCutBins.Batch256.valid3072 MergedCutBins.Batch256.sound3072 CutLabelCertificates.Entropy014.valid281 numericValid3072

def certificate3073 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3073,(some (975534272616118547/1000000000000000000)),(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate560,CutLabelCertificates.Entropy014.certificate281,(93596184449986847/200000000000000000)⟩
theorem numericValid3073 : certificate3073.NumericValid := by decide +kernel
theorem sound3073 : certificate3073.Sound := rat_cut_cell_certificate_sound certificate3073 MergedCutBins.Batch256.valid3073 MergedCutBins.Batch256.sound3073 CutLabelCertificates.Entropy014.valid281 numericValid3073

def certificate3074 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3074,(some (1137049359/1000000000)),(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate560,CutLabelCertificates.Entropy014.certificate281,(93596184449986847/200000000000000000)⟩
theorem numericValid3074 : certificate3074.NumericValid := by decide +kernel
theorem sound3074 : certificate3074.Sound := rat_cut_cell_certificate_sound certificate3074 MergedCutBins.Batch256.valid3074 MergedCutBins.Batch256.sound3074 CutLabelCertificates.Entropy014.valid281 numericValid3074

def certificate3075 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3075,(some (370407898779462677/250000000000000000)),(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate560,CutLabelCertificates.Entropy000.certificate1,(22603395568415959/50000000000000000)⟩
theorem numericValid3075 : certificate3075.NumericValid := by decide +kernel
theorem sound3075 : certificate3075.Sound := rat_cut_cell_certificate_sound certificate3075 MergedCutBins.Batch256.valid3075 MergedCutBins.Batch256.sound3075 CutLabelCertificates.Entropy000.valid1 numericValid3075

def certificate3076 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3076,(some (12965811850686170413/1000000000000000000)),(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate560,CutLabelCertificates.Entropy000.certificate1,(22603395568415959/50000000000000000)⟩
theorem numericValid3076 : certificate3076.NumericValid := by decide +kernel
theorem sound3076 : certificate3076.Sound := rat_cut_cell_certificate_sound certificate3076 MergedCutBins.Batch256.valid3076 MergedCutBins.Batch256.sound3076 CutLabelCertificates.Entropy000.valid1 numericValid3076

def certificate3077 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3077,(some 64),(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate560,CutLabelCertificates.Entropy000.certificate1,(22603395568415959/50000000000000000)⟩
theorem numericValid3077 : certificate3077.NumericValid := by decide +kernel
theorem sound3077 : certificate3077.Sound := rat_cut_cell_certificate_sound certificate3077 MergedCutBins.Batch256.valid3077 MergedCutBins.Batch256.sound3077 CutLabelCertificates.Entropy000.valid1 numericValid3077

def certificate3078 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3078,none,(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate560,CutLabelCertificates.Entropy000.certificate1,(22603395568415959/50000000000000000)⟩
theorem numericValid3078 : certificate3078.NumericValid := by decide +kernel
theorem sound3078 : certificate3078.Sound := rat_cut_cell_certificate_sound certificate3078 MergedCutBins.Batch256.valid3078 MergedCutBins.Batch256.sound3078 CutLabelCertificates.Entropy000.valid1 numericValid3078

def certificate3079 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3079,(some 64),(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate561,CutLabelCertificates.Entropy000.certificate1,(1263998434948575269/250000000000000000)⟩
theorem numericValid3079 : certificate3079.NumericValid := by decide +kernel
theorem sound3079 : certificate3079.Sound := rat_cut_cell_certificate_sound certificate3079 MergedCutBins.Batch256.valid3079 MergedCutBins.Batch256.sound3079 CutLabelCertificates.Entropy000.valid1 numericValid3079

def certificate3080 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3080,none,(1/2),(39386888540114143997/250000000000000000)⟩,PopulationCertificates.Batch028.certificate561,CutLabelCertificates.Entropy000.certificate1,(1263998434948575269/250000000000000000)⟩
theorem numericValid3080 : certificate3080.NumericValid := by decide +kernel
theorem sound3080 : certificate3080.Sound := rat_cut_cell_certificate_sound certificate3080 MergedCutBins.Batch256.valid3080 MergedCutBins.Batch256.sound3080 CutLabelCertificates.Entropy000.valid1 numericValid3080

def certificate3081 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3081,(some (355708515188700351/500000000000000000)),(1/2),(74574689523806123209/500000000000000000)⟩,PopulationCertificates.Batch028.certificate562,CutLabelCertificates.Entropy014.certificate282,(126077050198263333/250000000000000000)⟩
theorem numericValid3081 : certificate3081.NumericValid := by decide +kernel
theorem sound3081 : certificate3081.Sound := rat_cut_cell_certificate_sound certificate3081 MergedCutBins.Batch256.valid3081 MergedCutBins.Batch256.sound3081 CutLabelCertificates.Entropy014.valid282 numericValid3081

def certificate3082 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3082,(some (96847149947097171/100000000000000000)),(1/2),(74574689523806123209/500000000000000000)⟩,PopulationCertificates.Batch028.certificate562,CutLabelCertificates.Entropy014.certificate282,(126077050198263333/250000000000000000)⟩
theorem numericValid3082 : certificate3082.NumericValid := by decide +kernel
theorem sound3082 : certificate3082.Sound := rat_cut_cell_certificate_sound certificate3082 MergedCutBins.Batch256.valid3082 MergedCutBins.Batch256.sound3082 CutLabelCertificates.Entropy014.valid282 numericValid3082

def certificate3083 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch256.certificate3083,(some (56247297/50000000)),(1/2),(74574689523806123209/500000000000000000)⟩,PopulationCertificates.Batch028.certificate562,CutLabelCertificates.Entropy014.certificate282,(126077050198263333/250000000000000000)⟩
theorem numericValid3083 : certificate3083.NumericValid := by decide +kernel
theorem sound3083 : certificate3083.Sound := rat_cut_cell_certificate_sound certificate3083 MergedCutBins.Batch256.valid3083 MergedCutBins.Batch256.sound3083 CutLabelCertificates.Entropy014.valid282 numericValid3083

def certificates : List RatCutCellCertificate := [certificate3072,certificate3073,certificate3074,certificate3075,certificate3076,certificate3077,certificate3078,certificate3079,certificate3080,certificate3081,certificate3082,certificate3083]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3072,List.forall_mem_cons.mpr ⟨sound3073,List.forall_mem_cons.mpr ⟨sound3074,List.forall_mem_cons.mpr ⟨sound3075,List.forall_mem_cons.mpr ⟨sound3076,List.forall_mem_cons.mpr ⟨sound3077,List.forall_mem_cons.mpr ⟨sound3078,List.forall_mem_cons.mpr ⟨sound3079,List.forall_mem_cons.mpr ⟨sound3080,List.forall_mem_cons.mpr ⟨sound3081,List.forall_mem_cons.mpr ⟨sound3082,List.forall_mem_cons.mpr ⟨sound3083,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch256
