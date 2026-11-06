import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy008
import Cycle12.MergedCutBins.Batch160
import Cycle12.PopulationCertificates.Batch016

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch160

def certificate1920 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1920,(some 64),(1/2),(9412525033197477019/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate330,CutLabelCertificates.Entropy008.certificate166,(1101762941124032817/1000000000000000000)⟩
theorem numericValid1920 : certificate1920.NumericValid := by decide +kernel
theorem sound1920 : certificate1920.Sound := rat_cut_cell_certificate_sound certificate1920 MergedCutBins.Batch160.valid1920 MergedCutBins.Batch160.sound1920 CutLabelCertificates.Entropy008.valid166 numericValid1920

def certificate1921 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1921,none,(1/2),(9412525033197477019/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate330,CutLabelCertificates.Entropy000.certificate1,(104809893297217179/40000000000000000)⟩
theorem numericValid1921 : certificate1921.NumericValid := by decide +kernel
theorem sound1921 : certificate1921.Sound := rat_cut_cell_certificate_sound certificate1921 MergedCutBins.Batch160.valid1921 MergedCutBins.Batch160.sound1921 CutLabelCertificates.Entropy000.valid1 numericValid1921

def certificate1922 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1922,(some (4331361531394973881/1000000000000000000)),(1/2),(9412525033197477019/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate331,CutLabelCertificates.Entropy000.certificate1,(9226002556302373/7812500000000000)⟩
theorem numericValid1922 : certificate1922.NumericValid := by decide +kernel
theorem sound1922 : certificate1922.Sound := rat_cut_cell_certificate_sound certificate1922 MergedCutBins.Batch160.valid1922 MergedCutBins.Batch160.sound1922 CutLabelCertificates.Entropy000.valid1 numericValid1922

def certificate1923 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1923,(some (2321902910282454187/500000000000000000)),(1/2),(9412525033197477019/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate331,CutLabelCertificates.Entropy000.certificate1,(9226002556302373/7812500000000000)⟩
theorem numericValid1923 : certificate1923.NumericValid := by decide +kernel
theorem sound1923 : certificate1923.Sound := rat_cut_cell_certificate_sound certificate1923 MergedCutBins.Batch160.valid1923 MergedCutBins.Batch160.sound1923 CutLabelCertificates.Entropy000.valid1 numericValid1923

def certificate1924 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1924,(some (2345121939385278729/500000000000000000)),(1/2),(9412525033197477019/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate331,CutLabelCertificates.Entropy000.certificate1,(9226002556302373/7812500000000000)⟩
theorem numericValid1924 : certificate1924.NumericValid := by decide +kernel
theorem sound1924 : certificate1924.Sound := rat_cut_cell_certificate_sound certificate1924 MergedCutBins.Batch160.valid1924 MergedCutBins.Batch160.sound1924 CutLabelCertificates.Entropy000.valid1 numericValid1924

def certificate1925 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1925,none,(1/2),(9412525033197477019/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate331,CutLabelCertificates.Entropy000.certificate1,(9226002556302373/7812500000000000)⟩
theorem numericValid1925 : certificate1925.NumericValid := by decide +kernel
theorem sound1925 : certificate1925.Sound := rat_cut_cell_certificate_sound certificate1925 MergedCutBins.Batch160.valid1925 MergedCutBins.Batch160.sound1925 CutLabelCertificates.Entropy000.valid1 numericValid1925

def certificate1926 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1926,(some (1351099432874585923/1000000000000000000)),(1/2),(9244737841268092559/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate332,CutLabelCertificates.Entropy008.certificate167,(288048761278232777/250000000000000000)⟩
theorem numericValid1926 : certificate1926.NumericValid := by decide +kernel
theorem sound1926 : certificate1926.Sound := rat_cut_cell_certificate_sound certificate1926 MergedCutBins.Batch160.valid1926 MergedCutBins.Batch160.sound1926 CutLabelCertificates.Entropy008.valid167 numericValid1926

def certificate1927 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1927,(some (531582560327908387/200000000000000000)),(1/2),(9244737841268092559/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate332,CutLabelCertificates.Entropy008.certificate167,(288048761278232777/250000000000000000)⟩
theorem numericValid1927 : certificate1927.NumericValid := by decide +kernel
theorem sound1927 : certificate1927.Sound := rat_cut_cell_certificate_sound certificate1927 MergedCutBins.Batch160.valid1927 MergedCutBins.Batch160.sound1927 CutLabelCertificates.Entropy008.valid167 numericValid1927

def certificate1928 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1928,(some (4077179214986203741/1000000000000000000)),(1/2),(9244737841268092559/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate332,CutLabelCertificates.Entropy008.certificate167,(288048761278232777/250000000000000000)⟩
theorem numericValid1928 : certificate1928.NumericValid := by decide +kernel
theorem sound1928 : certificate1928.Sound := rat_cut_cell_certificate_sound certificate1928 MergedCutBins.Batch160.valid1928 MergedCutBins.Batch160.sound1928 CutLabelCertificates.Entropy008.valid167 numericValid1928

def certificate1929 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1929,(some (4503742370140446709/1000000000000000000)),(1/2),(9244737841268092559/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate332,CutLabelCertificates.Entropy008.certificate167,(288048761278232777/250000000000000000)⟩
theorem numericValid1929 : certificate1929.NumericValid := by decide +kernel
theorem sound1929 : certificate1929.Sound := rat_cut_cell_certificate_sound certificate1929 MergedCutBins.Batch160.valid1929 MergedCutBins.Batch160.sound1929 CutLabelCertificates.Entropy008.valid167 numericValid1929

def certificate1930 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1930,(some (4594267591780269689/1000000000000000000)),(1/2),(9244737841268092559/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate332,CutLabelCertificates.Entropy008.certificate167,(288048761278232777/250000000000000000)⟩
theorem numericValid1930 : certificate1930.NumericValid := by decide +kernel
theorem sound1930 : certificate1930.Sound := rat_cut_cell_certificate_sound certificate1930 MergedCutBins.Batch160.valid1930 MergedCutBins.Batch160.sound1930 CutLabelCertificates.Entropy008.valid167 numericValid1930

def certificate1931 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch160.certificate1931,(some 64),(1/2),(9244737841268092559/1000000000000000000)⟩,PopulationCertificates.Batch016.certificate332,CutLabelCertificates.Entropy008.certificate167,(288048761278232777/250000000000000000)⟩
theorem numericValid1931 : certificate1931.NumericValid := by decide +kernel
theorem sound1931 : certificate1931.Sound := rat_cut_cell_certificate_sound certificate1931 MergedCutBins.Batch160.valid1931 MergedCutBins.Batch160.sound1931 CutLabelCertificates.Entropy008.valid167 numericValid1931

def certificates : List RatCutCellCertificate := [certificate1920,certificate1921,certificate1922,certificate1923,certificate1924,certificate1925,certificate1926,certificate1927,certificate1928,certificate1929,certificate1930,certificate1931]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1920,List.forall_mem_cons.mpr ⟨sound1921,List.forall_mem_cons.mpr ⟨sound1922,List.forall_mem_cons.mpr ⟨sound1923,List.forall_mem_cons.mpr ⟨sound1924,List.forall_mem_cons.mpr ⟨sound1925,List.forall_mem_cons.mpr ⟨sound1926,List.forall_mem_cons.mpr ⟨sound1927,List.forall_mem_cons.mpr ⟨sound1928,List.forall_mem_cons.mpr ⟨sound1929,List.forall_mem_cons.mpr ⟨sound1930,List.forall_mem_cons.mpr ⟨sound1931,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch160
