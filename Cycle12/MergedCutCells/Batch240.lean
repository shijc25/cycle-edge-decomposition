import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy012
import Cycle12.MergedCutBins.Batch240
import Cycle12.PopulationCertificates.Batch025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch240

def certificate2880 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2880,(some (1779897211625388597/1000000000000000000)),(1/2),(555204668868246689109/500000000000000000)⟩,PopulationCertificates.Batch025.certificate512,CutLabelCertificates.Entropy000.certificate1,(5133829568641977/20000000000000000)⟩
theorem numericValid2880 : certificate2880.NumericValid := by decide +kernel
theorem sound2880 : certificate2880.Sound := rat_cut_cell_certificate_sound certificate2880 MergedCutBins.Batch240.valid2880 MergedCutBins.Batch240.sound2880 CutLabelCertificates.Entropy000.valid1 numericValid2880

def certificate2881 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2881,(some 64),(1/2),(555204668868246689109/500000000000000000)⟩,PopulationCertificates.Batch025.certificate512,CutLabelCertificates.Entropy000.certificate1,(5133829568641977/20000000000000000)⟩
theorem numericValid2881 : certificate2881.NumericValid := by decide +kernel
theorem sound2881 : certificate2881.Sound := rat_cut_cell_certificate_sound certificate2881 MergedCutBins.Batch240.valid2881 MergedCutBins.Batch240.sound2881 CutLabelCertificates.Entropy000.valid1 numericValid2881

def certificate2882 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2882,none,(1/2),(555204668868246689109/500000000000000000)⟩,PopulationCertificates.Batch025.certificate512,CutLabelCertificates.Entropy000.certificate1,(5133829568641977/20000000000000000)⟩
theorem numericValid2882 : certificate2882.NumericValid := by decide +kernel
theorem sound2882 : certificate2882.Sound := rat_cut_cell_certificate_sound certificate2882 MergedCutBins.Batch240.valid2882 MergedCutBins.Batch240.sound2882 CutLabelCertificates.Entropy000.valid1 numericValid2882

def certificate2883 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2883,(some 64),(1/2),(555204668868246689109/500000000000000000)⟩,PopulationCertificates.Batch025.certificate513,CutLabelCertificates.Entropy000.certificate1,(789184652161371487/250000000000000000)⟩
theorem numericValid2883 : certificate2883.NumericValid := by decide +kernel
theorem sound2883 : certificate2883.Sound := rat_cut_cell_certificate_sound certificate2883 MergedCutBins.Batch240.valid2883 MergedCutBins.Batch240.sound2883 CutLabelCertificates.Entropy000.valid1 numericValid2883

def certificate2884 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2884,none,(1/2),(555204668868246689109/500000000000000000)⟩,PopulationCertificates.Batch025.certificate513,CutLabelCertificates.Entropy000.certificate1,(789184652161371487/250000000000000000)⟩
theorem numericValid2884 : certificate2884.NumericValid := by decide +kernel
theorem sound2884 : certificate2884.Sound := rat_cut_cell_certificate_sound certificate2884 MergedCutBins.Batch240.valid2884 MergedCutBins.Batch240.sound2884 CutLabelCertificates.Entropy000.valid1 numericValid2884

def certificate2885 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2885,(some (18719724352628817/31250000000000000)),(1/2),(979025926796996761319/1000000000000000000)⟩,PopulationCertificates.Batch025.certificate514,CutLabelCertificates.Entropy012.certificate258,(262971684547043031/1000000000000000000)⟩
theorem numericValid2885 : certificate2885.NumericValid := by decide +kernel
theorem sound2885 : certificate2885.Sound := rat_cut_cell_certificate_sound certificate2885 MergedCutBins.Batch240.valid2885 MergedCutBins.Batch240.sound2885 CutLabelCertificates.Entropy012.valid258 numericValid2885

def certificate2886 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2886,(some (315616883/250000000)),(1/2),(979025926796996761319/1000000000000000000)⟩,PopulationCertificates.Batch025.certificate514,CutLabelCertificates.Entropy012.certificate258,(262971684547043031/1000000000000000000)⟩
theorem numericValid2886 : certificate2886.NumericValid := by decide +kernel
theorem sound2886 : certificate2886.Sound := rat_cut_cell_certificate_sound certificate2886 MergedCutBins.Batch240.valid2886 MergedCutBins.Batch240.sound2886 CutLabelCertificates.Entropy012.valid258 numericValid2886

def certificate2887 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2887,(some (3032727255683688847/1000000000000000000)),(1/2),(979025926796996761319/1000000000000000000)⟩,PopulationCertificates.Batch025.certificate514,CutLabelCertificates.Entropy000.certificate1,(130016644552240409/500000000000000000)⟩
theorem numericValid2887 : certificate2887.NumericValid := by decide +kernel
theorem sound2887 : certificate2887.Sound := rat_cut_cell_certificate_sound certificate2887 MergedCutBins.Batch240.valid2887 MergedCutBins.Batch240.sound2887 CutLabelCertificates.Entropy000.valid1 numericValid2887

def certificate2888 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2888,(some 64),(1/2),(979025926796996761319/1000000000000000000)⟩,PopulationCertificates.Batch025.certificate514,CutLabelCertificates.Entropy000.certificate1,(130016644552240409/500000000000000000)⟩
theorem numericValid2888 : certificate2888.NumericValid := by decide +kernel
theorem sound2888 : certificate2888.Sound := rat_cut_cell_certificate_sound certificate2888 MergedCutBins.Batch240.valid2888 MergedCutBins.Batch240.sound2888 CutLabelCertificates.Entropy000.valid1 numericValid2888

def certificate2889 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2889,none,(1/2),(979025926796996761319/1000000000000000000)⟩,PopulationCertificates.Batch025.certificate514,CutLabelCertificates.Entropy000.certificate1,(130016644552240409/500000000000000000)⟩
theorem numericValid2889 : certificate2889.NumericValid := by decide +kernel
theorem sound2889 : certificate2889.Sound := rat_cut_cell_certificate_sound certificate2889 MergedCutBins.Batch240.valid2889 MergedCutBins.Batch240.sound2889 CutLabelCertificates.Entropy000.valid1 numericValid2889

def certificate2890 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2890,(some 64),(1/2),(979025926796996761319/1000000000000000000)⟩,PopulationCertificates.Batch025.certificate515,CutLabelCertificates.Entropy000.certificate1,(3234550582181912773/1000000000000000000)⟩
theorem numericValid2890 : certificate2890.NumericValid := by decide +kernel
theorem sound2890 : certificate2890.Sound := rat_cut_cell_certificate_sound certificate2890 MergedCutBins.Batch240.valid2890 MergedCutBins.Batch240.sound2890 CutLabelCertificates.Entropy000.valid1 numericValid2890

def certificate2891 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch240.certificate2891,none,(1/2),(979025926796996761319/1000000000000000000)⟩,PopulationCertificates.Batch025.certificate515,CutLabelCertificates.Entropy000.certificate1,(3234550582181912773/1000000000000000000)⟩
theorem numericValid2891 : certificate2891.NumericValid := by decide +kernel
theorem sound2891 : certificate2891.Sound := rat_cut_cell_certificate_sound certificate2891 MergedCutBins.Batch240.valid2891 MergedCutBins.Batch240.sound2891 CutLabelCertificates.Entropy000.valid1 numericValid2891

def certificates : List RatCutCellCertificate := [certificate2880,certificate2881,certificate2882,certificate2883,certificate2884,certificate2885,certificate2886,certificate2887,certificate2888,certificate2889,certificate2890,certificate2891]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2880,List.forall_mem_cons.mpr ⟨sound2881,List.forall_mem_cons.mpr ⟨sound2882,List.forall_mem_cons.mpr ⟨sound2883,List.forall_mem_cons.mpr ⟨sound2884,List.forall_mem_cons.mpr ⟨sound2885,List.forall_mem_cons.mpr ⟨sound2886,List.forall_mem_cons.mpr ⟨sound2887,List.forall_mem_cons.mpr ⟨sound2888,List.forall_mem_cons.mpr ⟨sound2889,List.forall_mem_cons.mpr ⟨sound2890,List.forall_mem_cons.mpr ⟨sound2891,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch240
