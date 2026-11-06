import Cycle12.RationalCutCell
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy008
import Cycle12.CutLabelCertificates.Entropy009
import Cycle12.MergedCutBins.Batch168
import Cycle12.PopulationCertificates.Batch017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutCells.Batch168

def certificate2016 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2016,none,(1/2),(585536924372300477361/1000000000000000000)⟩,PopulationCertificates.Batch017.certificate355,CutLabelCertificates.Entropy000.certificate1,(408213685466685661/250000000000000000)⟩
theorem numericValid2016 : certificate2016.NumericValid := by decide +kernel
theorem sound2016 : certificate2016.Sound := rat_cut_cell_certificate_sound certificate2016 MergedCutBins.Batch168.valid2016 MergedCutBins.Batch168.sound2016 CutLabelCertificates.Entropy000.valid1 numericValid2016

def certificate2017 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2017,(some (156062983662084907/250000000000000000)),(1/2),(253857478123666143223/500000000000000000)⟩,PopulationCertificates.Batch017.certificate356,CutLabelCertificates.Entropy008.certificate179,(139079709123755739/500000000000000000)⟩
theorem numericValid2017 : certificate2017.NumericValid := by decide +kernel
theorem sound2017 : certificate2017.Sound := rat_cut_cell_certificate_sound certificate2017 MergedCutBins.Batch168.valid2017 MergedCutBins.Batch168.sound2017 CutLabelCertificates.Entropy008.valid179 numericValid2017

def certificate2018 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2018,(some (627005863/500000000)),(1/2),(253857478123666143223/500000000000000000)⟩,PopulationCertificates.Batch017.certificate356,CutLabelCertificates.Entropy008.certificate179,(139079709123755739/500000000000000000)⟩
theorem numericValid2018 : certificate2018.NumericValid := by decide +kernel
theorem sound2018 : certificate2018.Sound := rat_cut_cell_certificate_sound certificate2018 MergedCutBins.Batch168.valid2018 MergedCutBins.Batch168.sound2018 CutLabelCertificates.Entropy008.valid179 numericValid2018

def certificate2019 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2019,(some (520218908266473151/250000000000000000)),(1/2),(253857478123666143223/500000000000000000)⟩,PopulationCertificates.Batch017.certificate356,CutLabelCertificates.Entropy000.certificate1,(272969764911629407/1000000000000000000)⟩
theorem numericValid2019 : certificate2019.NumericValid := by decide +kernel
theorem sound2019 : certificate2019.Sound := rat_cut_cell_certificate_sound certificate2019 MergedCutBins.Batch168.valid2019 MergedCutBins.Batch168.sound2019 CutLabelCertificates.Entropy000.valid1 numericValid2019

def certificate2020 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2020,(some 64),(1/2),(253857478123666143223/500000000000000000)⟩,PopulationCertificates.Batch017.certificate356,CutLabelCertificates.Entropy000.certificate1,(272969764911629407/1000000000000000000)⟩
theorem numericValid2020 : certificate2020.NumericValid := by decide +kernel
theorem sound2020 : certificate2020.Sound := rat_cut_cell_certificate_sound certificate2020 MergedCutBins.Batch168.valid2020 MergedCutBins.Batch168.sound2020 CutLabelCertificates.Entropy000.valid1 numericValid2020

def certificate2021 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2021,none,(1/2),(253857478123666143223/500000000000000000)⟩,PopulationCertificates.Batch017.certificate356,CutLabelCertificates.Entropy000.certificate1,(272969764911629407/1000000000000000000)⟩
theorem numericValid2021 : certificate2021.NumericValid := by decide +kernel
theorem sound2021 : certificate2021.Sound := rat_cut_cell_certificate_sound certificate2021 MergedCutBins.Batch168.valid2021 MergedCutBins.Batch168.sound2021 CutLabelCertificates.Entropy000.valid1 numericValid2021

def certificate2022 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2022,(some 64),(1/2),(253857478123666143223/500000000000000000)⟩,PopulationCertificates.Batch017.certificate357,CutLabelCertificates.Entropy000.certificate1,(845196008754462311/500000000000000000)⟩
theorem numericValid2022 : certificate2022.NumericValid := by decide +kernel
theorem sound2022 : certificate2022.Sound := rat_cut_cell_certificate_sound certificate2022 MergedCutBins.Batch168.valid2022 MergedCutBins.Batch168.sound2022 CutLabelCertificates.Entropy000.valid1 numericValid2022

def certificate2023 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2023,none,(1/2),(253857478123666143223/500000000000000000)⟩,PopulationCertificates.Batch017.certificate357,CutLabelCertificates.Entropy000.certificate1,(845196008754462311/500000000000000000)⟩
theorem numericValid2023 : certificate2023.NumericValid := by decide +kernel
theorem sound2023 : certificate2023.Sound := rat_cut_cell_certificate_sound certificate2023 MergedCutBins.Batch168.valid2023 MergedCutBins.Batch168.sound2023 CutLabelCertificates.Entropy000.valid1 numericValid2023

def certificate2024 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2024,(some (9824559035594561/15625000000000000)),(1/2),(444163735094597351287/1000000000000000000)⟩,PopulationCertificates.Batch017.certificate358,CutLabelCertificates.Entropy009.certificate180,(139570561384191427/500000000000000000)⟩
theorem numericValid2024 : certificate2024.NumericValid := by decide +kernel
theorem sound2024 : certificate2024.Sound := rat_cut_cell_certificate_sound certificate2024 MergedCutBins.Batch168.valid2024 MergedCutBins.Batch168.sound2024 CutLabelCertificates.Entropy009.valid180 numericValid2024

def certificate2025 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2025,(some (1235712959/1000000000)),(1/2),(444163735094597351287/1000000000000000000)⟩,PopulationCertificates.Batch017.certificate358,CutLabelCertificates.Entropy009.certificate180,(139570561384191427/500000000000000000)⟩
theorem numericValid2025 : certificate2025.NumericValid := by decide +kernel
theorem sound2025 : certificate2025.Sound := rat_cut_cell_certificate_sound certificate2025 MergedCutBins.Batch168.valid2025 MergedCutBins.Batch168.sound2025 CutLabelCertificates.Entropy009.valid180 numericValid2025

def certificate2026 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2026,(some (362600540441171907/250000000000000000)),(1/2),(444163735094597351287/1000000000000000000)⟩,PopulationCertificates.Batch017.certificate358,CutLabelCertificates.Entropy000.certificate1,(273346118964402429/1000000000000000000)⟩
theorem numericValid2026 : certificate2026.NumericValid := by decide +kernel
theorem sound2026 : certificate2026.Sound := rat_cut_cell_certificate_sound certificate2026 MergedCutBins.Batch168.valid2026 MergedCutBins.Batch168.sound2026 CutLabelCertificates.Entropy000.valid1 numericValid2026

def certificate2027 : RatCutCellCertificate := ⟨⟨MergedCutBins.Batch168.certificate2027,(some (218143309212850761/12500000000000000)),(1/2),(444163735094597351287/1000000000000000000)⟩,PopulationCertificates.Batch017.certificate358,CutLabelCertificates.Entropy000.certificate1,(273346118964402429/1000000000000000000)⟩
theorem numericValid2027 : certificate2027.NumericValid := by decide +kernel
theorem sound2027 : certificate2027.Sound := rat_cut_cell_certificate_sound certificate2027 MergedCutBins.Batch168.valid2027 MergedCutBins.Batch168.sound2027 CutLabelCertificates.Entropy000.valid1 numericValid2027

def certificates : List RatCutCellCertificate := [certificate2016,certificate2017,certificate2018,certificate2019,certificate2020,certificate2021,certificate2022,certificate2023,certificate2024,certificate2025,certificate2026,certificate2027]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2016,List.forall_mem_cons.mpr ⟨sound2017,List.forall_mem_cons.mpr ⟨sound2018,List.forall_mem_cons.mpr ⟨sound2019,List.forall_mem_cons.mpr ⟨sound2020,List.forall_mem_cons.mpr ⟨sound2021,List.forall_mem_cons.mpr ⟨sound2022,List.forall_mem_cons.mpr ⟨sound2023,List.forall_mem_cons.mpr ⟨sound2024,List.forall_mem_cons.mpr ⟨sound2025,List.forall_mem_cons.mpr ⟨sound2026,List.forall_mem_cons.mpr ⟨sound2027,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutCells.Batch168
